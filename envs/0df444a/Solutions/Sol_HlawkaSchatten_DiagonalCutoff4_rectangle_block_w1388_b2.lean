-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1388_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:25:02.146412+00:00
-- url     : https://prove2.me/submissions/9ccd5245-5e8a-4d8f-a8f9-f7e9237ee8ac

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
theorem support_rectangle_w1388_s6_0 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2004886993/10000000000 : ℝ)*x 0 + (5410339463/10000000000 : ℝ)*x 1 + (2622954611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2004886993/10000000000 : ℝ)^1087 ≤ (6110263221599/50000000000000 : ℝ)^831 := by
    have hnat : (2004886993 : ℕ)^1087*50000000000000^831 ≤ 6110263221599^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004886993 10000000000 6110263221599 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410339463/10000000000 : ℝ)^1087 ≤ (2798472151881/6250000000000 : ℝ)^831 := by
    have hnat : (5410339463 : ℕ)^1087*6250000000000^831 ≤ 2798472151881^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410339463 10000000000 2798472151881 6250000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622954611/5000000000 : ℝ)^1087 ≤ (21501959554221/50000000000000 : ℝ)^831 := by
    have hnat : (2622954611 : ℕ)^1087*50000000000000^831 ≤ 21501959554221^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622954611 5000000000 21501959554221 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2004886993/10000000000 : ℝ), (5410339463/10000000000 : ℝ), (2622954611/5000000000 : ℝ)] ![(6110263221599/50000000000000 : ℝ), (2798472151881/6250000000000 : ℝ), (21501959554221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2004886993/10000000000 : ℝ)|^1087 ≤ (6110263221599/50000000000000 : ℝ)^831
        have hw : |(-2004886993/10000000000 : ℝ)|=(2004886993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410339463/10000000000 : ℝ)|^1087 ≤ (2798472151881/6250000000000 : ℝ)^831
        have hw : |(5410339463/10000000000 : ℝ)|=(5410339463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622954611/5000000000 : ℝ)|^1087 ≤ (21501959554221/50000000000000 : ℝ)^831
        have hw : |(2622954611/5000000000 : ℝ)|=(2622954611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s6_1 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337039361/2500000000 : ℝ)*x 0 + (-2088630563/10000000000 : ℝ)*x 1 + (5245909117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337039361/2500000000 : ℝ)^1087 ≤ (11025900616471/25000000000000 : ℝ)^831 := by
    have hnat : (1337039361 : ℕ)^1087*25000000000000^831 ≤ 11025900616471^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337039361 2500000000 11025900616471 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088630563/10000000000 : ℝ)^1087 ≤ (12892479532577/100000000000000 : ℝ)^831 := by
    have hnat : (2088630563 : ℕ)^1087*100000000000000^831 ≤ 12892479532577^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088630563 10000000000 12892479532577 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245909117/10000000000 : ℝ)^1087 ≤ (671936218477/1562500000000 : ℝ)^831 := by
    have hnat : (5245909117 : ℕ)^1087*1562500000000^831 ≤ 671936218477^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245909117 10000000000 671936218477 1562500000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337039361/2500000000 : ℝ), (-2088630563/10000000000 : ℝ), (5245909117/10000000000 : ℝ)] ![(11025900616471/25000000000000 : ℝ), (12892479532577/100000000000000 : ℝ), (671936218477/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337039361/2500000000 : ℝ)|^1087 ≤ (11025900616471/25000000000000 : ℝ)^831
        have hw : |(1337039361/2500000000 : ℝ)|=(1337039361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2088630563/10000000000 : ℝ)|^1087 ≤ (12892479532577/100000000000000 : ℝ)^831
        have hw : |(-2088630563/10000000000 : ℝ)|=(2088630563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245909117/10000000000 : ℝ)|^1087 ≤ (671936218477/1562500000000 : ℝ)^831
        have hw : |(5245909117/10000000000 : ℝ)|=(5245909117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s6_2 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348157083/10000000000 : ℝ)*x 0 + (5245909457/10000000000 : ℝ)*x 1 + (-1044315297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348157083/10000000000 : ℝ)^1087 ≤ (44103598571797/100000000000000 : ℝ)^831 := by
    have hnat : (5348157083 : ℕ)^1087*100000000000000^831 ≤ 44103598571797^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348157083 10000000000 44103598571797 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245909457/10000000000 : ℝ)^1087 ≤ (5375490203543/12500000000000 : ℝ)^831 := by
    have hnat : (5245909457 : ℕ)^1087*12500000000000^831 ≤ 5375490203543^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245909457 10000000000 5375490203543 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044315297/5000000000 : ℝ)^1087 ≤ (12892479782879/100000000000000 : ℝ)^831 := by
    have hnat : (1044315297 : ℕ)^1087*100000000000000^831 ≤ 12892479782879^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044315297 5000000000 12892479782879 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348157083/10000000000 : ℝ), (5245909457/10000000000 : ℝ), (-1044315297/5000000000 : ℝ)] ![(44103598571797/100000000000000 : ℝ), (5375490203543/12500000000000 : ℝ), (12892479782879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348157083/10000000000 : ℝ)|^1087 ≤ (44103598571797/100000000000000 : ℝ)^831
        have hw : |(5348157083/10000000000 : ℝ)|=(5348157083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245909457/10000000000 : ℝ)|^1087 ≤ (5375490203543/12500000000000 : ℝ)^831
        have hw : |(5245909457/10000000000 : ℝ)|=(5245909457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1044315297/5000000000 : ℝ)|^1087 ≤ (12892479782879/100000000000000 : ℝ)^831
        have hw : |(-1044315297/5000000000 : ℝ)|=(1044315297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s6_3 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1078682997/2500000000 : ℝ)*x 0 + (414279993/1000000000 : ℝ)*x 1 + (2246590201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078682997/2500000000 : ℝ)^1087 ≤ (33304027733401/100000000000000 : ℝ)^831 := by
    have hnat : (1078682997 : ℕ)^1087*100000000000000^831 ≤ 33304027733401^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078682997 2500000000 33304027733401 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414279993/1000000000 : ℝ)^1087 ≤ (6315773515299/20000000000000 : ℝ)^831 := by
    have hnat : (414279993 : ℕ)^1087*20000000000000^831 ≤ 6315773515299^831*1000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414279993 1000000000 6315773515299 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246590201/5000000000 : ℝ)^1087 ≤ (35117104669901/100000000000000 : ℝ)^831 := by
    have hnat : (2246590201 : ℕ)^1087*100000000000000^831 ≤ 35117104669901^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246590201 5000000000 35117104669901 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078682997/2500000000 : ℝ), (414279993/1000000000 : ℝ), (2246590201/5000000000 : ℝ)] ![(33304027733401/100000000000000 : ℝ), (6315773515299/20000000000000 : ℝ), (35117104669901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078682997/2500000000 : ℝ)|^1087 ≤ (33304027733401/100000000000000 : ℝ)^831
        have hw : |(1078682997/2500000000 : ℝ)|=(1078682997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(414279993/1000000000 : ℝ)|^1087 ≤ (6315773515299/20000000000000 : ℝ)^831
        have hw : |(414279993/1000000000 : ℝ)|=(414279993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246590201/5000000000 : ℝ)|^1087 ≤ (35117104669901/100000000000000 : ℝ)^831
        have hw : |(2246590201/5000000000 : ℝ)|=(2246590201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s6_4 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-400979807/2000000000 : ℝ)*x 0 + (5246500237/10000000000 : ℝ)*x 1 + (5409745151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (400979807/2000000000 : ℝ)^1087 ≤ (244412449113/2000000000000 : ℝ)^831 := by
    have hnat : (400979807 : ℕ)^1087*2000000000000^831 ≤ 244412449113^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400979807 2000000000 244412449113 2000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246500237/10000000000 : ℝ)^1087 ≤ (21505128332333/50000000000000 : ℝ)^831 := by
    have hnat : (5246500237 : ℕ)^1087*50000000000000^831 ≤ 21505128332333^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246500237 10000000000 21505128332333 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409745151/10000000000 : ℝ)^1087 ≤ (44769120858649/100000000000000 : ℝ)^831 := by
    have hnat : (5409745151 : ℕ)^1087*100000000000000^831 ≤ 44769120858649^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409745151 10000000000 44769120858649 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-400979807/2000000000 : ℝ), (5246500237/10000000000 : ℝ), (5409745151/10000000000 : ℝ)] ![(244412449113/2000000000000 : ℝ), (21505128332333/50000000000000 : ℝ), (44769120858649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-400979807/2000000000 : ℝ)|^1087 ≤ (244412449113/2000000000000 : ℝ)^831
        have hw : |(-400979807/2000000000 : ℝ)|=(400979807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246500237/10000000000 : ℝ)|^1087 ≤ (21505128332333/50000000000000 : ℝ)^831
        have hw : |(5246500237/10000000000 : ℝ)|=(5246500237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409745151/10000000000 : ℝ)|^1087 ≤ (44769120858649/100000000000000 : ℝ)^831
        have hw : |(5409745151/10000000000 : ℝ)|=(5409745151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s6_5 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326396977/2500000000 : ℝ)*x 0 + (-962397409/5000000000 : ℝ)*x 1 + (5409745151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326396977/2500000000 : ℝ)^1087 ≤ (10911242829143/25000000000000 : ℝ)^831 := by
    have hnat : (1326396977 : ℕ)^1087*25000000000000^831 ≤ 10911242829143^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326396977 2500000000 10911242829143 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962397409/5000000000 : ℝ)^1087 ≤ (11585907817419/100000000000000 : ℝ)^831 := by
    have hnat : (962397409 : ℕ)^1087*100000000000000^831 ≤ 11585907817419^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962397409 5000000000 11585907817419 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409745151/10000000000 : ℝ)^1087 ≤ (44769120858649/100000000000000 : ℝ)^831 := by
    have hnat : (5409745151 : ℕ)^1087*100000000000000^831 ≤ 44769120858649^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409745151 10000000000 44769120858649 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326396977/2500000000 : ℝ), (-962397409/5000000000 : ℝ), (5409745151/10000000000 : ℝ)] ![(10911242829143/25000000000000 : ℝ), (11585907817419/100000000000000 : ℝ), (44769120858649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326396977/2500000000 : ℝ)|^1087 ≤ (10911242829143/25000000000000 : ℝ)^831
        have hw : |(1326396977/2500000000 : ℝ)|=(1326396977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-962397409/5000000000 : ℝ)|^1087 ≤ (11585907817419/100000000000000 : ℝ)^831
        have hw : |(-962397409/5000000000 : ℝ)|=(962397409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409745151/10000000000 : ℝ)|^1087 ≤ (44769120858649/100000000000000 : ℝ)^831
        have hw : |(5409745151/10000000000 : ℝ)|=(5409745151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s6_6 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652793949/5000000000 : ℝ)*x 0 + (5409745159/10000000000 : ℝ)*x 1 + (-96239741/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652793949/5000000000 : ℝ)^1087 ≤ (5455621401121/12500000000000 : ℝ)^831 := by
    have hnat : (2652793949 : ℕ)^1087*12500000000000^831 ≤ 5455621401121^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652793949 5000000000 5455621401121 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409745159/10000000000 : ℝ)^1087 ≤ (179076483781/400000000000 : ℝ)^831 := by
    have hnat : (5409745159 : ℕ)^1087*400000000000^831 ≤ 179076483781^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409745159 10000000000 179076483781 400000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96239741/500000000 : ℝ)^1087 ≤ (11585907833167/100000000000000 : ℝ)^831 := by
    have hnat : (96239741 : ℕ)^1087*100000000000000^831 ≤ 11585907833167^831*500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96239741 500000000 11585907833167 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652793949/5000000000 : ℝ), (5409745159/10000000000 : ℝ), (-96239741/500000000 : ℝ)] ![(5455621401121/12500000000000 : ℝ), (179076483781/400000000000 : ℝ), (11585907833167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652793949/5000000000 : ℝ)|^1087 ≤ (5455621401121/12500000000000 : ℝ)^831
        have hw : |(2652793949/5000000000 : ℝ)|=(2652793949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409745159/10000000000 : ℝ)|^1087 ≤ (179076483781/400000000000 : ℝ)^831
        have hw : |(5409745159/10000000000 : ℝ)|=(5409745159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96239741/500000000 : ℝ)|^1087 ≤ (11585907833167/100000000000000 : ℝ)^831
        have hw : |(-96239741/500000000 : ℝ)|=(96239741/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s6_7 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1078689449/2500000000 : ℝ)*x 0 + (140372521/312500000 : ℝ)*x 1 + (4144065317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078689449/2500000000 : ℝ)^1087 ≤ (8326072076119/25000000000000 : ℝ)^831 := by
    have hnat : (1078689449 : ℕ)^1087*25000000000000^831 ≤ 8326072076119^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078689449 2500000000 8326072076119 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140372521/312500000 : ℝ)^1087 ≤ (35104226561339/100000000000000 : ℝ)^831 := by
    have hnat : (140372521 : ℕ)^1087*100000000000000^831 ≤ 35104226561339^831*312500000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140372521 312500000 35104226561339 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4144065317/10000000000 : ℝ)^1087 ≤ (6318297024583/20000000000000 : ℝ)^831 := by
    have hnat : (4144065317 : ℕ)^1087*20000000000000^831 ≤ 6318297024583^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144065317 10000000000 6318297024583 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078689449/2500000000 : ℝ), (140372521/312500000 : ℝ), (4144065317/10000000000 : ℝ)] ![(8326072076119/25000000000000 : ℝ), (35104226561339/100000000000000 : ℝ), (6318297024583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078689449/2500000000 : ℝ)|^1087 ≤ (8326072076119/25000000000000 : ℝ)^831
        have hw : |(1078689449/2500000000 : ℝ)|=(1078689449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140372521/312500000 : ℝ)|^1087 ≤ (35104226561339/100000000000000 : ℝ)^831
        have hw : |(140372521/312500000 : ℝ)|=(140372521/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4144065317/10000000000 : ℝ)|^1087 ≤ (6318297024583/20000000000000 : ℝ)^831
        have hw : |(4144065317/10000000000 : ℝ)|=(4144065317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1388_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (737/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11253/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2947/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (737/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (703/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (737/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (703/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (737/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (703/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (737/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (703/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (737/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (703/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (737/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (703/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (703/6250 : ℝ) ^ (4347/1024 : ℝ) ≤ (1873844181952437/20000000000000000000 : ℝ) := by
    have hpowers : (703/6250 : ℝ)^4347 ≤ (1873844181952437/20000000000000000000 : ℝ)^1024 := by
      have hnat : (703 : ℕ)^4347*20000000000000000000^1024 ≤ 1873844181952437^1024*6250^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        703 6250 1873844181952437 20000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (703/6250 : ℝ)) (X := (1873844181952437/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (737/5000 : ℝ) ^ (4347/1024 : ℝ) ≤ (14761972100373743/50000000000000000000 : ℝ) := by
    have hpowers : (737/5000 : ℝ)^4347 ≤ (14761972100373743/50000000000000000000 : ℝ)^1024 := by
      have hnat : (737 : ℕ)^4347*50000000000000000000^1024 ≤ 14761972100373743^1024*5000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        737 5000 14761972100373743 50000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (737/5000 : ℝ)) (X := (14761972100373743/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001873844181952437/10000000000000000000 : ℝ) ≤ (10000441380038811/10000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (10001873844181952437/10000000000000000000 : ℝ)^1024 ≤ (10000441380038811/10000000000000000 : ℝ)^4347 := by
      have hnat : (10001873844181952437 : ℕ)^1024*10000000000000000^4347 ≤ 10000441380038811^4347*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001873844181952437 10000000000000000000 10000441380038811 10000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000441380038811/10000000000000000 : ℝ)) (X := (10001873844181952437/10000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038893165110509671/100000000000000000000 : ℝ) ≤ (10000916049734133/10000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (100038893165110509671/100000000000000000000 : ℝ)^1024 ≤ (10000916049734133/10000000000000000 : ℝ)^4347 := by
      have hnat : (100038893165110509671 : ℕ)^1024*10000000000000000^4347 ≤ 10000916049734133^4347*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038893165110509671 100000000000000000000 10000916049734133 10000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000916049734133/10000000000000000 : ℝ)) (X := (100038893165110509671/100000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014761972100373743/25000000000000000000 : ℝ) ≤ (2000278143885891/2000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (25014761972100373743/25000000000000000000 : ℝ)^1024 ≤ (2000278143885891/2000000000000000 : ℝ)^4347 := by
      have hnat : (25014761972100373743 : ℕ)^1024*2000000000000000^4347 ≤ 2000278143885891^4347*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014761972100373743 25000000000000000000 2000278143885891 2000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000278143885891/2000000000000000 : ℝ)) (X := (25014761972100373743/25000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1873844181952437/20000000000000000000 : ℝ) ≤ ((38789847921810627/38800000000000000 : ℝ)+2*(26370538629/19400000000000 : ℝ)*(703/6250 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (38789847921810627/38800000000000000 : ℝ)+2*(26370538629/19400000000000 : ℝ)*(703/6250 : ℝ)=(10000441380038811/10000000000000000 : ℝ) by norm_num, show 1+2*(1873844181952437/20000000000000000000 : ℝ)=(10001873844181952437/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14761972100373743/50000000000000000000 : ℝ)+(1873844181952437/20000000000000000000 : ℝ) ≤ ((38789847921810627/38800000000000000 : ℝ)+(26370538629/19400000000000 : ℝ)*((737/5000 : ℝ)+(703/6250 : ℝ)))^(4347/1024 : ℝ) := by
    rw [show (38789847921810627/38800000000000000 : ℝ)+(26370538629/19400000000000 : ℝ)*((737/5000 : ℝ)+(703/6250 : ℝ))=(10000916049734133/10000000000000000 : ℝ) by norm_num, show 1+(14761972100373743/50000000000000000000 : ℝ)+(1873844181952437/20000000000000000000 : ℝ)=(100038893165110509671/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14761972100373743/50000000000000000000 : ℝ) ≤ ((38789847921810627/38800000000000000 : ℝ)+2*(26370538629/19400000000000 : ℝ)*(737/5000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (38789847921810627/38800000000000000 : ℝ)+2*(26370538629/19400000000000 : ℝ)*(737/5000 : ℝ)=(2000278143885891/2000000000000000 : ℝ) by norm_num, show 1+2*(14761972100373743/50000000000000000000 : ℝ)=(25014761972100373743/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38789847921810627/38800000000000000 : ℝ)*(X 1 0+X 2 0)+(26370538629/19400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (737/5000 : ℝ)) (c := (38789847921810627/38800000000000000 : ℝ)) (alpha := (26370538629/19400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38789847921810627/38800000000000000 : ℝ)*(X 0 1+X 2 1)+(26370538629/19400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (737/5000 : ℝ)) (c := (38789847921810627/38800000000000000 : ℝ)) (alpha := (26370538629/19400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38789847921810627/38800000000000000 : ℝ)*(X 0 2+X 1 2)+(26370538629/19400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (737/5000 : ℝ)) (c := (38789847921810627/38800000000000000 : ℝ)) (alpha := (26370538629/19400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2004886993/10000000000 : ℝ)*X 0 0+(5410339463/10000000000 : ℝ)*X 0 1+(2622954611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337039361/2500000000 : ℝ)*X 1 0+(-2088630563/10000000000 : ℝ)*X 1 1+(5245909117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348157083/10000000000 : ℝ)*X 2 0+(5245909457/10000000000 : ℝ)*X 2 1+(-1044315297/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1078682997/2500000000 : ℝ)*X 0 0+(414279993/1000000000 : ℝ)*X 0 1+(2246590201/5000000000 : ℝ)*X 0 2+(1078682997/2500000000 : ℝ)*X 1 0+(414279993/1000000000 : ℝ)*X 1 1+(2246590201/5000000000 : ℝ)*X 1 2+(1078682997/2500000000 : ℝ)*X 2 0+(414279993/1000000000 : ℝ)*X 2 1+(2246590201/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-400979807/2000000000 : ℝ)*X 0 0+(5246500237/10000000000 : ℝ)*X 0 1+(5409745151/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326396977/2500000000 : ℝ)*X 1 0+(-962397409/5000000000 : ℝ)*X 1 1+(5409745151/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652793949/5000000000 : ℝ)*X 2 0+(5409745159/10000000000 : ℝ)*X 2 1+(-96239741/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1078689449/2500000000 : ℝ)*X 0 0+(140372521/312500000 : ℝ)*X 0 1+(4144065317/10000000000 : ℝ)*X 0 2+(1078689449/2500000000 : ℝ)*X 1 0+(140372521/312500000 : ℝ)*X 1 1+(4144065317/10000000000 : ℝ)*X 1 2+(1078689449/2500000000 : ℝ)*X 2 0+(140372521/312500000 : ℝ)*X 2 1+(4144065317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8663164335563304166649547/970000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1088522943/100000000000000 : ℝ)*(base19) + (704261353/100000000000000 : ℝ)*(base23) + (235509/6250000000000 : ℝ)*(lower2) + (8903597/50000000000000 : ℝ)*(lower4) + (86302379/100000000000000 : ℝ)*(lower5) + (2233933168170671/50000000000000 : ℝ)*(major0) + (2233933168170671/50000000000000 : ℝ)*(major1) + (2233933168170671/50000000000000 : ℝ)*(major2) + (760205070773579/12500000000000 : ℝ)*(sp0) + (6081667166108949/100000000000000 : ℝ)*(sp1) + (304083377518527/5000000000000 : ℝ)*(sp2) + (713513092140667/25000000000000 : ℝ)*(sp3) + (1384422163/5000000000000 : ℝ)*(sp4) + (1468973109/12500000000000 : ℝ)*(sp7) + (142703206017377/5000000000000 : ℝ)*(f.failure) + (1520417063657973/25000000000000 : ℝ)*(f.sum) + (5088159666359/485000000000000000000000000 : ℝ)*base65 + (29631042925238717/1940000000000000000000000000000 : ℝ)*base67 + (25862032141078717/1940000000000000000000000000000 : ℝ)*base69 + (20454982620758717/1940000000000000000000000000000 : ℝ)*base71 + (147231532807/242500000000000000000000000 : ℝ)*base73 + (9468272691218717/1940000000000000000000000000000 : ℝ)*base75 + (15282615800598717/1940000000000000000000000000000 : ℝ)*base77 + (1156577409878717/1940000000000000000000000000000 : ℝ)*base79 + (376361493059/485000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2790361/500000000000000000000 : ℝ)*base90 + (2790361/500000000000000000000 : ℝ)*base92 + (2790361/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3262360915447849059222801/485000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72507631/6250000000000 : ℝ)*(base19) + (1256158563/100000000000000 : ℝ)*(base23) + (34201837/25000000000000 : ℝ)*(upper3) + (1227469/2500000000000 : ℝ)*(lower4) + (339937/250000000000 : ℝ)*(upper5) + (2250130477921679/50000000000000 : ℝ)*(major0) + (2250130477921679/50000000000000 : ℝ)*(major1) + (2250130477921679/50000000000000 : ℝ)*(major2) + (4830662103/20000000000000 : ℝ)*(sp1) + (26028103739/100000000000000 : ℝ)*(sp2) + (1225152789736033/20000000000000 : ℝ)*(sp4) + (3062869317623777/50000000000000 : ℝ)*(sp5) + (6125736664417863/100000000000000 : ℝ)*(sp6) + (179672358674331/6250000000000 : ℝ)*(sp7) + (179672358674331/6250000000000 : ℝ)*(f.failure) + (1225152789736033/20000000000000 : ℝ)*(f.sum) + (156060609897/242500000000000000000000000 : ℝ)*base66 + (2680788820915267/1940000000000000000000000000000 : ℝ)*base68 + (22309028762884733/1940000000000000000000000000000 : ℝ)*base69 + (8698036174544733/1940000000000000000000000000000 : ℝ)*base71 + (234204091879/121250000000000000000000000 : ℝ)*base73 + (34244013534524733/1940000000000000000000000000000 : ℝ)*base75 + (14887112213684733/1940000000000000000000000000000 : ℝ)*base77 + (31065829659184733/1940000000000000000000000000000 : ℝ)*base79 + (250393728181/485000000000000000000000000 : ℝ)*base81 + (4715683/625000000000000000000 : ℝ)*base90 + (4715683/625000000000000000000 : ℝ)*base92 + (4715683/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1388_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (737/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1388_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1388_s7_0 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-501222753/2500000000 : ℝ)*x 0 + (5410300777/10000000000 : ℝ)*x 1 + (5245945289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501222753/2500000000 : ℝ)^1087 ≤ (6110279243597/50000000000000 : ℝ)^831 := by
    have hnat : (501222753 : ℕ)^1087*50000000000000^831 ≤ 6110279243597^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501222753 2500000000 6110279243597 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410300777/10000000000 : ℝ)^1087 ≤ (8955027127629/20000000000000 : ℝ)^831 := by
    have hnat : (5410300777 : ℕ)^1087*20000000000000^831 ≤ 8955027127629^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410300777 10000000000 8955027127629 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245945289/10000000000 : ℝ)^1087 ≤ (43004305854829/100000000000000 : ℝ)^831 := by
    have hnat : (5245945289 : ℕ)^1087*100000000000000^831 ≤ 43004305854829^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245945289 10000000000 43004305854829 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-501222753/2500000000 : ℝ), (5410300777/10000000000 : ℝ), (5245945289/10000000000 : ℝ)] ![(6110279243597/50000000000000 : ℝ), (8955027127629/20000000000000 : ℝ), (43004305854829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-501222753/2500000000 : ℝ)|^1087 ≤ (6110279243597/50000000000000 : ℝ)^831
        have hw : |(-501222753/2500000000 : ℝ)|=(501222753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410300777/10000000000 : ℝ)|^1087 ≤ (8955027127629/20000000000000 : ℝ)^831
        have hw : |(5410300777/10000000000 : ℝ)|=(5410300777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245945289/10000000000 : ℝ)|^1087 ≤ (43004305854829/100000000000000 : ℝ)^831
        have hw : |(5245945289/10000000000 : ℝ)|=(5245945289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s7_1 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348147507/10000000000 : ℝ)*x 0 + (-130537237/625000000 : ℝ)*x 1 + (327871581/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348147507/10000000000 : ℝ)^1087 ≤ (44103495276057/100000000000000 : ℝ)^831 := by
    have hnat : (5348147507 : ℕ)^1087*100000000000000^831 ≤ 44103495276057^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348147507 10000000000 44103495276057 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130537237/625000000 : ℝ)^1087 ≤ (6446099391403/50000000000000 : ℝ)^831 := by
    have hnat : (130537237 : ℕ)^1087*50000000000000^831 ≤ 6446099391403^831*625000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130537237 625000000 6446099391403 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327871581/625000000 : ℝ)^1087 ≤ (4300430592989/10000000000000 : ℝ)^831 := by
    have hnat : (327871581 : ℕ)^1087*10000000000000^831 ≤ 4300430592989^831*625000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327871581 625000000 4300430592989 10000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348147507/10000000000 : ℝ), (-130537237/625000000 : ℝ), (327871581/625000000 : ℝ)] ![(44103495276057/100000000000000 : ℝ), (6446099391403/50000000000000 : ℝ), (4300430592989/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348147507/10000000000 : ℝ)|^1087 ≤ (44103495276057/100000000000000 : ℝ)^831
        have hw : |(5348147507/10000000000 : ℝ)|=(5348147507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130537237/625000000 : ℝ)|^1087 ≤ (6446099391403/50000000000000 : ℝ)^831
        have hw : |(-130537237/625000000 : ℝ)|=(130537237/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327871581/625000000 : ℝ)|^1087 ≤ (4300430592989/10000000000000 : ℝ)^831
        have hw : |(327871581/625000000 : ℝ)|=(327871581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s7_2 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674073753/5000000000 : ℝ)*x 0 + (5245945289/10000000000 : ℝ)*x 1 + (-1044297901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674073753/5000000000 : ℝ)^1087 ≤ (4410349526527/10000000000000 : ℝ)^831 := by
    have hnat : (2674073753 : ℕ)^1087*10000000000000^831 ≤ 4410349526527^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674073753 5000000000 4410349526527 10000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245945289/10000000000 : ℝ)^1087 ≤ (43004305854829/100000000000000 : ℝ)^831 := by
    have hnat : (5245945289 : ℕ)^1087*100000000000000^831 ≤ 43004305854829^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245945289 10000000000 43004305854829 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044297901/5000000000 : ℝ)^1087 ≤ (12892198863549/100000000000000 : ℝ)^831 := by
    have hnat : (1044297901 : ℕ)^1087*100000000000000^831 ≤ 12892198863549^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044297901 5000000000 12892198863549 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674073753/5000000000 : ℝ), (5245945289/10000000000 : ℝ), (-1044297901/5000000000 : ℝ)] ![(4410349526527/10000000000000 : ℝ), (43004305854829/100000000000000 : ℝ), (12892198863549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674073753/5000000000 : ℝ)|^1087 ≤ (4410349526527/10000000000000 : ℝ)^831
        have hw : |(2674073753/5000000000 : ℝ)|=(2674073753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245945289/10000000000 : ℝ)|^1087 ≤ (43004305854829/100000000000000 : ℝ)^831
        have hw : |(5245945289/10000000000 : ℝ)|=(5245945289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1044297901/5000000000 : ℝ)|^1087 ≤ (12892198863549/100000000000000 : ℝ)^831
        have hw : |(-1044297901/5000000000 : ℝ)|=(1044297901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s7_3 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4314735459/10000000000 : ℝ)*x 0 + (4142878517/10000000000 : ℝ)*x 1 + (4493100329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314735459/10000000000 : ℝ)^1087 ≤ (16652031389203/50000000000000 : ℝ)^831 := by
    have hnat : (4314735459 : ℕ)^1087*50000000000000^831 ≤ 16652031389203^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314735459 10000000000 16652031389203 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4142878517/10000000000 : ℝ)^1087 ≤ (31579651156041/100000000000000 : ℝ)^831 := by
    have hnat : (4142878517 : ℕ)^1087*100000000000000^831 ≤ 31579651156041^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142878517 10000000000 31579651156041 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493100329/10000000000 : ℝ)^1087 ≤ (7023257211517/20000000000000 : ℝ)^831 := by
    have hnat : (4493100329 : ℕ)^1087*20000000000000^831 ≤ 7023257211517^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493100329 10000000000 7023257211517 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314735459/10000000000 : ℝ), (4142878517/10000000000 : ℝ), (4493100329/10000000000 : ℝ)] ![(16652031389203/50000000000000 : ℝ), (31579651156041/100000000000000 : ℝ), (7023257211517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314735459/10000000000 : ℝ)|^1087 ≤ (16652031389203/50000000000000 : ℝ)^831
        have hw : |(4314735459/10000000000 : ℝ)|=(4314735459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4142878517/10000000000 : ℝ)|^1087 ≤ (31579651156041/100000000000000 : ℝ)^831
        have hw : |(4142878517/10000000000 : ℝ)|=(4142878517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493100329/10000000000 : ℝ)|^1087 ≤ (7023257211517/20000000000000 : ℝ)^831
        have hw : |(4493100329/10000000000 : ℝ)|=(4493100329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s7_4 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1002451353/5000000000 : ℝ)*x 0 + (2623267861/5000000000 : ℝ)*x 1 + (169053353/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1002451353/5000000000 : ℝ)^1087 ≤ (3055162931263/25000000000000 : ℝ)^831 := by
    have hnat : (1002451353 : ℕ)^1087*25000000000000^831 ≤ 3055162931263^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002451353 5000000000 3055162931263 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623267861/5000000000 : ℝ)^1087 ≤ (43010637183467/100000000000000 : ℝ)^831 := by
    have hnat : (2623267861 : ℕ)^1087*100000000000000^831 ≤ 43010637183467^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623267861 5000000000 43010637183467 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169053353/312500000 : ℝ)^1087 ≤ (1790748443059/4000000000000 : ℝ)^831 := by
    have hnat : (169053353 : ℕ)^1087*4000000000000^831 ≤ 1790748443059^831*312500000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169053353 312500000 1790748443059 4000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1002451353/5000000000 : ℝ), (2623267861/5000000000 : ℝ), (169053353/312500000 : ℝ)] ![(3055162931263/25000000000000 : ℝ), (43010637183467/100000000000000 : ℝ), (1790748443059/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1002451353/5000000000 : ℝ)|^1087 ≤ (3055162931263/25000000000000 : ℝ)^831
        have hw : |(-1002451353/5000000000 : ℝ)|=(1002451353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623267861/5000000000 : ℝ)|^1087 ≤ (43010637183467/100000000000000 : ℝ)^831
        have hw : |(2623267861/5000000000 : ℝ)|=(2623267861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169053353/312500000 : ℝ)|^1087 ≤ (1790748443059/4000000000000 : ℝ)^831
        have hw : |(169053353/312500000 : ℝ)|=(169053353/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s7_5 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326399367/2500000000 : ℝ)*x 0 + (-1924833799/10000000000 : ℝ)*x 1 + (1081941459/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326399367/2500000000 : ℝ)^1087 ≤ (8729014837243/20000000000000 : ℝ)^831 := by
    have hnat : (1326399367 : ℕ)^1087*20000000000000^831 ≤ 8729014837243^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326399367 2500000000 8729014837243 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1924833799/10000000000 : ℝ)^1087 ≤ (362069210617/3125000000000 : ℝ)^831 := by
    have hnat : (1924833799 : ℕ)^1087*3125000000000^831 ≤ 362069210617^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924833799 10000000000 362069210617 3125000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081941459/2000000000 : ℝ)^1087 ≤ (895374221313/2000000000000 : ℝ)^831 := by
    have hnat : (1081941459 : ℕ)^1087*2000000000000^831 ≤ 895374221313^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081941459 2000000000 895374221313 2000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326399367/2500000000 : ℝ), (-1924833799/10000000000 : ℝ), (1081941459/2000000000 : ℝ)] ![(8729014837243/20000000000000 : ℝ), (362069210617/3125000000000 : ℝ), (895374221313/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326399367/2500000000 : ℝ)|^1087 ≤ (8729014837243/20000000000000 : ℝ)^831
        have hw : |(1326399367/2500000000 : ℝ)|=(1326399367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1924833799/10000000000 : ℝ)|^1087 ≤ (362069210617/3125000000000 : ℝ)^831
        have hw : |(-1924833799/10000000000 : ℝ)|=(1924833799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081941459/2000000000 : ℝ)|^1087 ≤ (895374221313/2000000000000 : ℝ)^831
        have hw : |(1081941459/2000000000 : ℝ)|=(1081941459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s7_6 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305597467/10000000000 : ℝ)*x 0 + (5409707297/10000000000 : ℝ)*x 1 + (-1924833797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305597467/10000000000 : ℝ)^1087 ≤ (21822537087727/50000000000000 : ℝ)^831 := by
    have hnat : (5305597467 : ℕ)^1087*50000000000000^831 ≤ 21822537087727^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305597467 10000000000 21822537087727 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409707297/10000000000 : ℝ)^1087 ≤ (447687110873/1000000000000 : ℝ)^831 := by
    have hnat : (5409707297 : ℕ)^1087*1000000000000^831 ≤ 447687110873^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409707297 10000000000 447687110873 1000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1924833797/10000000000 : ℝ)^1087 ≤ (11586214723997/100000000000000 : ℝ)^831 := by
    have hnat : (1924833797 : ℕ)^1087*100000000000000^831 ≤ 11586214723997^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924833797 10000000000 11586214723997 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305597467/10000000000 : ℝ), (5409707297/10000000000 : ℝ), (-1924833797/10000000000 : ℝ)] ![(21822537087727/50000000000000 : ℝ), (447687110873/1000000000000 : ℝ), (11586214723997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305597467/10000000000 : ℝ)|^1087 ≤ (21822537087727/50000000000000 : ℝ)^831
        have hw : |(5305597467/10000000000 : ℝ)|=(5305597467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409707297/10000000000 : ℝ)|^1087 ≤ (447687110873/1000000000000 : ℝ)^831
        have hw : |(5409707297/10000000000 : ℝ)|=(5409707297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1924833797/10000000000 : ℝ)|^1087 ≤ (11586214723997/100000000000000 : ℝ)^831
        have hw : |(-1924833797/10000000000 : ℝ)|=(1924833797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s7_7 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2157380191/5000000000 : ℝ)*x 0 + (2245921103/5000000000 : ℝ)*x 1 + (4144143137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157380191/5000000000 : ℝ)^1087 ≤ (1040759825441/3125000000000 : ℝ)^831 := by
    have hnat : (2157380191 : ℕ)^1087*3125000000000^831 ≤ 1040759825441^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157380191 5000000000 1040759825441 3125000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245921103/5000000000 : ℝ)^1087 ≤ (17551712223577/50000000000000 : ℝ)^831 := by
    have hnat : (2245921103 : ℕ)^1087*50000000000000^831 ≤ 17551712223577^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245921103 5000000000 17551712223577 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4144143137/10000000000 : ℝ)^1087 ≤ (31592261127797/100000000000000 : ℝ)^831 := by
    have hnat : (4144143137 : ℕ)^1087*100000000000000^831 ≤ 31592261127797^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144143137 10000000000 31592261127797 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157380191/5000000000 : ℝ), (2245921103/5000000000 : ℝ), (4144143137/10000000000 : ℝ)] ![(1040759825441/3125000000000 : ℝ), (17551712223577/50000000000000 : ℝ), (31592261127797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157380191/5000000000 : ℝ)|^1087 ≤ (1040759825441/3125000000000 : ℝ)^831
        have hw : |(2157380191/5000000000 : ℝ)|=(2157380191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245921103/5000000000 : ℝ)|^1087 ≤ (17551712223577/50000000000000 : ℝ)^831
        have hw : |(2245921103/5000000000 : ℝ)|=(2245921103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4144143137/10000000000 : ℝ)|^1087 ≤ (31592261127797/100000000000000 : ℝ)^831
        have hw : |(4144143137/10000000000 : ℝ)|=(4144143137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1388_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5627/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7367/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2947/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2947/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2947/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2947/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2947/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2947/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11253/100000 : ℝ) ^ (4347/1024 : ℝ) ≤ (1173364236757031/12500000000000000000 : ℝ) := by
    have hpowers : (11253/100000 : ℝ)^4347 ≤ (1173364236757031/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11253 : ℕ)^4347*12500000000000000000^1024 ≤ 1173364236757031^1024*100000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11253 100000 1173364236757031 12500000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11253/100000 : ℝ)) (X := (1173364236757031/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2947/20000 : ℝ) ^ (4347/1024 : ℝ) ≤ (14740726571491351/50000000000000000000 : ℝ) := by
    have hpowers : (2947/20000 : ℝ)^4347 ≤ (14740726571491351/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2947 : ℕ)^4347*50000000000000000000^1024 ≤ 14740726571491351^1024*20000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2947 20000 14740726571491351 50000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2947/20000 : ℝ)) (X := (14740726571491351/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251173364236757031/6250000000000000000 : ℝ) ≤ (400017688539521/400000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (6251173364236757031/6250000000000000000 : ℝ)^1024 ≤ (400017688539521/400000000000000 : ℝ)^4347 := by
      have hnat : (6251173364236757031 : ℕ)^1024*400000000000000^4347 ≤ 400017688539521^4347*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251173364236757031 6250000000000000000 400017688539521 400000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400017688539521/400000000000000 : ℝ)) (X := (6251173364236757031/6250000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000777367340740779/2000000000000000000 : ℝ) ≤ (62505721660953/62500000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (2000777367340740779/2000000000000000000 : ℝ)^1024 ≤ (62505721660953/62500000000000 : ℝ)^4347 := by
      have hnat : (2000777367340740779 : ℕ)^1024*62500000000000^4347 ≤ 62505721660953^4347*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000777367340740779 2000000000000000000 62505721660953 62500000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62505721660953/62500000000000 : ℝ)) (X := (2000777367340740779/2000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014740726571491351/25000000000000000000 : ℝ) ≤ (2000277743603387/2000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (25014740726571491351/25000000000000000000 : ℝ)^1024 ≤ (2000277743603387/2000000000000000 : ℝ)^4347 := by
      have hnat : (25014740726571491351 : ℕ)^1024*2000000000000000^4347 ≤ 2000277743603387^4347*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014740726571491351 25000000000000000000 2000277743603387 2000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000277743603387/2000000000000000 : ℝ)) (X := (25014740726571491351/25000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1173364236757031/12500000000000000000 : ℝ) ≤ ((1740544438595073941/1741000000000000000 : ℝ)+2*(94650452891/69640000000000 : ℝ)*(11253/100000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (1740544438595073941/1741000000000000000 : ℝ)+2*(94650452891/69640000000000 : ℝ)*(11253/100000 : ℝ)=(400017688539521/400000000000000 : ℝ) by norm_num, show 1+2*(1173364236757031/12500000000000000000 : ℝ)=(6251173364236757031/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14740726571491351/50000000000000000000 : ℝ)+(1173364236757031/12500000000000000000 : ℝ) ≤ ((1740544438595073941/1741000000000000000 : ℝ)+(94650452891/69640000000000 : ℝ)*((2947/20000 : ℝ)+(11253/100000 : ℝ)))^(4347/1024 : ℝ) := by
    rw [show (1740544438595073941/1741000000000000000 : ℝ)+(94650452891/69640000000000 : ℝ)*((2947/20000 : ℝ)+(11253/100000 : ℝ))=(62505721660953/62500000000000 : ℝ) by norm_num, show 1+(14740726571491351/50000000000000000000 : ℝ)+(1173364236757031/12500000000000000000 : ℝ)=(2000777367340740779/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14740726571491351/50000000000000000000 : ℝ) ≤ ((1740544438595073941/1741000000000000000 : ℝ)+2*(94650452891/69640000000000 : ℝ)*(2947/20000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (1740544438595073941/1741000000000000000 : ℝ)+2*(94650452891/69640000000000 : ℝ)*(2947/20000 : ℝ)=(2000277743603387/2000000000000000 : ℝ) by norm_num, show 1+2*(14740726571491351/50000000000000000000 : ℝ)=(25014740726571491351/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1740544438595073941/1741000000000000000 : ℝ)*(X 1 0+X 2 0)+(94650452891/69640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (2947/20000 : ℝ)) (c := (1740544438595073941/1741000000000000000 : ℝ)) (alpha := (94650452891/69640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1740544438595073941/1741000000000000000 : ℝ)*(X 0 1+X 2 1)+(94650452891/69640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (2947/20000 : ℝ)) (c := (1740544438595073941/1741000000000000000 : ℝ)) (alpha := (94650452891/69640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1740544438595073941/1741000000000000000 : ℝ)*(X 0 2+X 1 2)+(94650452891/69640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (2947/20000 : ℝ)) (c := (1740544438595073941/1741000000000000000 : ℝ)) (alpha := (94650452891/69640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-501222753/2500000000 : ℝ)*X 0 0+(5410300777/10000000000 : ℝ)*X 0 1+(5245945289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348147507/10000000000 : ℝ)*X 1 0+(-130537237/625000000 : ℝ)*X 1 1+(327871581/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674073753/5000000000 : ℝ)*X 2 0+(5245945289/10000000000 : ℝ)*X 2 1+(-1044297901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314735459/10000000000 : ℝ)*X 0 0+(4142878517/10000000000 : ℝ)*X 0 1+(4493100329/10000000000 : ℝ)*X 0 2+(4314735459/10000000000 : ℝ)*X 1 0+(4142878517/10000000000 : ℝ)*X 1 1+(4493100329/10000000000 : ℝ)*X 1 2+(4314735459/10000000000 : ℝ)*X 2 0+(4142878517/10000000000 : ℝ)*X 2 1+(4493100329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1002451353/5000000000 : ℝ)*X 0 0+(2623267861/5000000000 : ℝ)*X 0 1+(169053353/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326399367/2500000000 : ℝ)*X 1 0+(-1924833799/10000000000 : ℝ)*X 1 1+(1081941459/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305597467/10000000000 : ℝ)*X 2 0+(5409707297/10000000000 : ℝ)*X 2 1+(-1924833797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2157380191/5000000000 : ℝ)*X 0 0+(2245921103/5000000000 : ℝ)*X 0 1+(4144143137/10000000000 : ℝ)*X 0 2+(2157380191/5000000000 : ℝ)*X 1 0+(2245921103/5000000000 : ℝ)*X 1 1+(4144143137/10000000000 : ℝ)*X 1 2+(2157380191/5000000000 : ℝ)*X 2 0+(2245921103/5000000000 : ℝ)*X 2 1+(4144143137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (219943878520983369454201047/43525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94664389/10000000000000 : ℝ)*(base19) + (882450679/100000000000000 : ℝ)*(base23) + (6744607/20000000000000 : ℝ)*(lower2) + (132438769/100000000000000 : ℝ)*(upper3) + (73242359/100000000000000 : ℝ)*(upper5) + (2234941357681437/50000000000000 : ℝ)*(major0) + (2234941357681437/50000000000000 : ℝ)*(major1) + (2234941357681437/50000000000000 : ℝ)*(major2) + (6084393428899529/100000000000000 : ℝ)*(sp0) + (6084412136387303/100000000000000 : ℝ)*(sp1) + (3042206100290257/50000000000000 : ℝ)*(sp2) + (285534213346847/10000000000000 : ℝ)*(sp3) + (1228383229/6250000000000 : ℝ)*(sp4) + (10045783511/100000000000000 : ℝ)*(sp7) + (1427676089625991/50000000000000 : ℝ)*(f.failure) + (6084413083031193/100000000000000 : ℝ)*(f.sum) + (2217542110433/1741000000000000000000000000 : ℝ)*base66 + (850312464823458217/87050000000000000000000000000000 : ℝ)*base67 + (681969049550208217/87050000000000000000000000000000 : ℝ)*base69 + (261716677208658217/87050000000000000000000000000000 : ℝ)*base71 + (9310711401887/1741000000000000000000000000 : ℝ)*base73 + (1316590773306058217/87050000000000000000000000000000 : ℝ)*base75 + (333498589204508217/87050000000000000000000000000000 : ℝ)*base77 + (1336698846533208217/87050000000000000000000000000000 : ℝ)*base79 + (1335985142851/870500000000000000000000000 : ℝ)*base82 + (62485937/5000000000000000000000 : ℝ)*base89 + (62485937/5000000000000000000000 : ℝ)*base91 + (62485937/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25999837757423751959707761/5440625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (408503269/50000000000000 : ℝ)*(base19) + (889574189/100000000000000 : ℝ)*(base23) + (277783087/100000000000000 : ℝ)*(lower1) + (96633981/100000000000000 : ℝ)*(upper3) + (33177371/100000000000000 : ℝ)*(lower4) + (96983119/100000000000000 : ℝ)*(upper5) + (281391966453757/6250000000000 : ℝ)*(major0) + (281391966453757/6250000000000 : ℝ)*(major1) + (281391966453757/6250000000000 : ℝ)*(major2) + (348821739/25000000000000 : ℝ)*(sp2) + (1532125180075371/25000000000000 : ℝ)*(sp4) + (3064249951647473/50000000000000 : ℝ)*(sp5) + (3064249217720169/50000000000000 : ℝ)*(sp6) + (359505255865537/12500000000000 : ℝ)*(sp7) + (359505255865537/12500000000000 : ℝ)*(f.failure) + (1532125180075371/25000000000000 : ℝ)*(f.sum) + (23012449507/6800781250000000000000000 : ℝ)*base66 + (573768558029228663/10881250000000000000000000000000 : ℝ)*base68 + (90743726888428663/10881250000000000000000000000000 : ℝ)*base70 + (299758981176828663/10881250000000000000000000000000 : ℝ)*base72 + (1906505328753/870500000000000000000000000 : ℝ)*base74 + (229182391697533837/10881250000000000000000000000000 : ℝ)*base75 + (15250842206916163/10881250000000000000000000000000 : ℝ)*base78 + (1822524648883837/10881250000000000000000000000000 : ℝ)*base79 + (315413423741/870500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (15186759/1250000000000000000000 : ℝ)*base89 + (15186759/1250000000000000000000 : ℝ)*base91 + (15186759/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1388_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1388_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1388_box_0 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-115075221/625000000 : ℝ)*x 0 + (5388003219/10000000000 : ℝ)*x 1 + (1077600497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (115075221/625000000 : ℝ)^1087 ≤ (2733047482931/25000000000000 : ℝ)^831 := by
    have hnat : (115075221 : ℕ)^1087*25000000000000^831 ≤ 2733047482931^831*625000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115075221 625000000 2733047482931 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388003219/10000000000 : ℝ)^1087 ≤ (44533908992611/100000000000000 : ℝ)^831 := by
    have hnat : (5388003219 : ℕ)^1087*100000000000000^831 ≤ 44533908992611^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388003219 10000000000 44533908992611 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077600497/2000000000 : ℝ)^1087 ≤ (44533901056869/100000000000000 : ℝ)^831 := by
    have hnat : (1077600497 : ℕ)^1087*100000000000000^831 ≤ 44533901056869^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077600497 2000000000 44533901056869 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-115075221/625000000 : ℝ), (5388003219/10000000000 : ℝ), (1077600497/2000000000 : ℝ)] ![(2733047482931/25000000000000 : ℝ), (44533908992611/100000000000000 : ℝ), (44533901056869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-115075221/625000000 : ℝ)|^1087 ≤ (2733047482931/25000000000000 : ℝ)^831
        have hw : |(-115075221/625000000 : ℝ)|=(115075221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388003219/10000000000 : ℝ)|^1087 ≤ (44533908992611/100000000000000 : ℝ)^831
        have hw : |(5388003219/10000000000 : ℝ)|=(5388003219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077600497/2000000000 : ℝ)|^1087 ≤ (44533901056869/100000000000000 : ℝ)^831
        have hw : |(1077600497/2000000000 : ℝ)|=(1077600497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_1 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1057142583/2000000000 : ℝ)*x 0 + (-396311627/2000000000 : ℝ)*x 1 + (269400173/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057142583/2000000000 : ℝ)^1087 ≤ (8686246310929/20000000000000 : ℝ)^831 := by
    have hnat : (1057142583 : ℕ)^1087*20000000000000^831 ≤ 8686246310929^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057142583 2000000000 8686246310929 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (396311627/2000000000 : ℝ)^1087 ≤ (12034856832881/100000000000000 : ℝ)^831 := by
    have hnat : (396311627 : ℕ)^1087*100000000000000^831 ≤ 12034856832881^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396311627 2000000000 12034856832881 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269400173/500000000 : ℝ)^1087 ≤ (5566738949777/12500000000000 : ℝ)^831 := by
    have hnat : (269400173 : ℕ)^1087*12500000000000^831 ≤ 5566738949777^831*500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269400173 500000000 5566738949777 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057142583/2000000000 : ℝ), (-396311627/2000000000 : ℝ), (269400173/500000000 : ℝ)] ![(8686246310929/20000000000000 : ℝ), (12034856832881/100000000000000 : ℝ), (5566738949777/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057142583/2000000000 : ℝ)|^1087 ≤ (8686246310929/20000000000000 : ℝ)^831
        have hw : |(1057142583/2000000000 : ℝ)|=(1057142583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-396311627/2000000000 : ℝ)|^1087 ≤ (12034856832881/100000000000000 : ℝ)^831
        have hw : |(-396311627/2000000000 : ℝ)|=(396311627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269400173/500000000 : ℝ)|^1087 ≤ (5566738949777/12500000000000 : ℝ)^831
        have hw : |(269400173/500000000 : ℝ)|=(269400173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_2 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5285711269/10000000000 : ℝ)*x 0 + (215520173/400000000 : ℝ)*x 1 + (-123847449/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285711269/10000000000 : ℝ)^1087 ≤ (43431213863461/100000000000000 : ℝ)^831 := by
    have hnat : (5285711269 : ℕ)^1087*100000000000000^831 ≤ 43431213863461^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285711269 10000000000 43431213863461 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215520173/400000000 : ℝ)^1087 ≤ (44533920950283/100000000000000 : ℝ)^831 := by
    have hnat : (215520173 : ℕ)^1087*100000000000000^831 ≤ 44533920950283^831*400000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215520173 400000000 44533920950283 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123847449/625000000 : ℝ)^1087 ≤ (12034865166587/100000000000000 : ℝ)^831 := by
    have hnat : (123847449 : ℕ)^1087*100000000000000^831 ≤ 12034865166587^831*625000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123847449 625000000 12034865166587 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285711269/10000000000 : ℝ), (215520173/400000000 : ℝ), (-123847449/625000000 : ℝ)] ![(43431213863461/100000000000000 : ℝ), (44533920950283/100000000000000 : ℝ), (12034865166587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285711269/10000000000 : ℝ)|^1087 ≤ (43431213863461/100000000000000 : ℝ)^831
        have hw : |(5285711269/10000000000 : ℝ)|=(5285711269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215520173/400000000 : ℝ)|^1087 ≤ (44533920950283/100000000000000 : ℝ)^831
        have hw : |(215520173/400000000 : ℝ)|=(215520173/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-123847449/625000000 : ℝ)|^1087 ≤ (12034865166587/100000000000000 : ℝ)^831
        have hw : |(-123847449/625000000 : ℝ)|=(123847449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_3 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (278867791/625000000 : ℝ)*x 0 + (424495087/1000000000 : ℝ)*x 1 + (1061238021/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (278867791/625000000 : ℝ)^1087 ≤ (6959500202761/20000000000000 : ℝ)^831 := by
    have hnat : (278867791 : ℕ)^1087*20000000000000^831 ≤ 6959500202761^831*625000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278867791 625000000 6959500202761 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424495087/1000000000 : ℝ)^1087 ≤ (32601243387053/100000000000000 : ℝ)^831 := by
    have hnat : (424495087 : ℕ)^1087*100000000000000^831 ≤ 32601243387053^831*1000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424495087 1000000000 32601243387053 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061238021/2500000000 : ℝ)^1087 ≤ (4075156947851/12500000000000 : ℝ)^831 := by
    have hnat : (1061238021 : ℕ)^1087*12500000000000^831 ≤ 4075156947851^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061238021 2500000000 4075156947851 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(278867791/625000000 : ℝ), (424495087/1000000000 : ℝ), (1061238021/2500000000 : ℝ)] ![(6959500202761/20000000000000 : ℝ), (32601243387053/100000000000000 : ℝ), (4075156947851/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(278867791/625000000 : ℝ)|^1087 ≤ (6959500202761/20000000000000 : ℝ)^831
        have hw : |(278867791/625000000 : ℝ)|=(278867791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(424495087/1000000000 : ℝ)|^1087 ≤ (32601243387053/100000000000000 : ℝ)^831
        have hw : |(424495087/1000000000 : ℝ)|=(424495087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061238021/2500000000 : ℝ)|^1087 ≤ (4075156947851/12500000000000 : ℝ)^831
        have hw : |(1061238021/2500000000 : ℝ)|=(1061238021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_4 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171321861/10000000000 : ℝ)*x 0 + (2632926779/5000000000 : ℝ)*x 1 + (5265853483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171321861/10000000000 : ℝ)^1087 ≤ (2712837318233/20000000000000 : ℝ)^831 := by
    have hnat : (2171321861 : ℕ)^1087*20000000000000^831 ≤ 2712837318233^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171321861 10000000000 2712837318233 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632926779/5000000000 : ℝ)^1087 ≤ (21608953548721/50000000000000 : ℝ)^831 := by
    have hnat : (2632926779 : ℕ)^1087*50000000000000^831 ≤ 21608953548721^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632926779 5000000000 21608953548721 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265853483/10000000000 : ℝ)^1087 ≤ (43217906292277/100000000000000 : ℝ)^831 := by
    have hnat : (5265853483 : ℕ)^1087*100000000000000^831 ≤ 43217906292277^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265853483 10000000000 43217906292277 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171321861/10000000000 : ℝ), (2632926779/5000000000 : ℝ), (5265853483/10000000000 : ℝ)] ![(2712837318233/20000000000000 : ℝ), (21608953548721/50000000000000 : ℝ), (43217906292277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171321861/10000000000 : ℝ)|^1087 ≤ (2712837318233/20000000000000 : ℝ)^831
        have hw : |(-2171321861/10000000000 : ℝ)|=(2171321861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632926779/5000000000 : ℝ)|^1087 ≤ (21608953548721/50000000000000 : ℝ)^831
        have hw : |(2632926779/5000000000 : ℝ)|=(2632926779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265853483/10000000000 : ℝ)|^1087 ≤ (43217906292277/100000000000000 : ℝ)^831
        have hw : |(5265853483/10000000000 : ℝ)|=(5265853483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_5 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (335708937/625000000 : ℝ)*x 0 + (-1269303/6250000 : ℝ)*x 1 + (5265853503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335708937/625000000 : ℝ)^1087 ≤ (22176935251083/50000000000000 : ℝ)^831 := by
    have hnat : (335708937 : ℕ)^1087*50000000000000^831 ≤ 22176935251083^831*625000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335708937 625000000 22176935251083 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269303/6250000 : ℝ)^1087 ≤ (6214111489627/50000000000000 : ℝ)^831 := by
    have hnat : (1269303 : ℕ)^1087*50000000000000^831 ≤ 6214111489627^831*6250000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269303 6250000 6214111489627 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265853503/10000000000 : ℝ)^1087 ≤ (10804476626747/25000000000000 : ℝ)^831 := by
    have hnat : (5265853503 : ℕ)^1087*25000000000000^831 ≤ 10804476626747^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265853503 10000000000 10804476626747 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335708937/625000000 : ℝ), (-1269303/6250000 : ℝ), (5265853503/10000000000 : ℝ)] ![(22176935251083/50000000000000 : ℝ), (6214111489627/50000000000000 : ℝ), (10804476626747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335708937/625000000 : ℝ)|^1087 ≤ (22176935251083/50000000000000 : ℝ)^831
        have hw : |(335708937/625000000 : ℝ)|=(335708937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1269303/6250000 : ℝ)|^1087 ≤ (6214111489627/50000000000000 : ℝ)^831
        have hw : |(-1269303/6250000 : ℝ)|=(1269303/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265853503/10000000000 : ℝ)|^1087 ≤ (10804476626747/25000000000000 : ℝ)^831
        have hw : |(5265853503/10000000000 : ℝ)|=(5265853503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_6 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1074268573/2000000000 : ℝ)*x 0 + (1053170727/2000000000 : ℝ)*x 1 + (-406176959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074268573/2000000000 : ℝ)^1087 ≤ (22176934565199/50000000000000 : ℝ)^831 := by
    have hnat : (1074268573 : ℕ)^1087*50000000000000^831 ≤ 22176934565199^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074268573 2000000000 22176934565199 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053170727/2000000000 : ℝ)^1087 ≤ (21608953962039/50000000000000 : ℝ)^831 := by
    have hnat : (1053170727 : ℕ)^1087*50000000000000^831 ≤ 21608953962039^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053170727 2000000000 21608953962039 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406176959/2000000000 : ℝ)^1087 ≤ (1242822293923/10000000000000 : ℝ)^831 := by
    have hnat : (406176959 : ℕ)^1087*10000000000000^831 ≤ 1242822293923^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406176959 2000000000 1242822293923 10000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074268573/2000000000 : ℝ), (1053170727/2000000000 : ℝ), (-406176959/2000000000 : ℝ)] ![(22176934565199/50000000000000 : ℝ), (21608953962039/50000000000000 : ℝ), (1242822293923/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074268573/2000000000 : ℝ)|^1087 ≤ (22176934565199/50000000000000 : ℝ)^831
        have hw : |(1074268573/2000000000 : ℝ)|=(1074268573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053170727/2000000000 : ℝ)|^1087 ≤ (21608953962039/50000000000000 : ℝ)^831
        have hw : |(1053170727/2000000000 : ℝ)|=(1053170727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-406176959/2000000000 : ℝ)|^1087 ≤ (1242822293923/10000000000000 : ℝ)^831
        have hw : |(-406176959/2000000000 : ℝ)|=(406176959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_7 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4166594803/10000000000 : ℝ)*x 0 + (4392544337/10000000000 : ℝ)*x 1 + (2196272127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166594803/10000000000 : ℝ)^1087 ≤ (6363266344769/20000000000000 : ℝ)^831 := by
    have hnat : (4166594803 : ℕ)^1087*20000000000000^831 ≤ 6363266344769^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166594803 10000000000 6363266344769 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4392544337/10000000000 : ℝ)^1087 ≤ (106536982963/312500000000 : ℝ)^831 := by
    have hnat : (4392544337 : ℕ)^1087*312500000000^831 ≤ 106536982963^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4392544337 10000000000 106536982963 312500000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196272127/5000000000 : ℝ)^1087 ≤ (34091833705523/100000000000000 : ℝ)^831 := by
    have hnat : (2196272127 : ℕ)^1087*100000000000000^831 ≤ 34091833705523^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196272127 5000000000 34091833705523 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166594803/10000000000 : ℝ), (4392544337/10000000000 : ℝ), (2196272127/5000000000 : ℝ)] ![(6363266344769/20000000000000 : ℝ), (106536982963/312500000000 : ℝ), (34091833705523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166594803/10000000000 : ℝ)|^1087 ≤ (6363266344769/20000000000000 : ℝ)^831
        have hw : |(4166594803/10000000000 : ℝ)|=(4166594803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4392544337/10000000000 : ℝ)|^1087 ≤ (106536982963/312500000000 : ℝ)^831
        have hw : |(4392544337/10000000000 : ℝ)|=(4392544337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2196272127/5000000000 : ℝ)|^1087 ≤ (34091833705523/100000000000000 : ℝ)^831
        have hw : |(2196272127/5000000000 : ℝ)|=(2196272127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_8 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050941503/5000000000 : ℝ)*x 0 + (2590775251/5000000000 : ℝ)*x 1 + (1080400099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050941503/5000000000 : ℝ)^1087 ≤ (1624948472463/12500000000000 : ℝ)^831 := by
    have hnat : (1050941503 : ℕ)^1087*12500000000000^831 ≤ 1624948472463^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050941503 5000000000 1624948472463 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590775251/5000000000 : ℝ)^1087 ≤ (42315109214039/100000000000000 : ℝ)^831 := by
    have hnat : (2590775251 : ℕ)^1087*100000000000000^831 ≤ 42315109214039^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590775251 5000000000 42315109214039 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080400099/2000000000 : ℝ)^1087 ≤ (44685302992079/100000000000000 : ℝ)^831 := by
    have hnat : (1080400099 : ℕ)^1087*100000000000000^831 ≤ 44685302992079^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080400099 2000000000 44685302992079 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050941503/5000000000 : ℝ), (2590775251/5000000000 : ℝ), (1080400099/2000000000 : ℝ)] ![(1624948472463/12500000000000 : ℝ), (42315109214039/100000000000000 : ℝ), (44685302992079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050941503/5000000000 : ℝ)|^1087 ≤ (1624948472463/12500000000000 : ℝ)^831
        have hw : |(-1050941503/5000000000 : ℝ)|=(1050941503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590775251/5000000000 : ℝ)|^1087 ≤ (42315109214039/100000000000000 : ℝ)^831
        have hw : |(2590775251/5000000000 : ℝ)|=(2590775251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080400099/2000000000 : ℝ)|^1087 ≤ (44685302992079/100000000000000 : ℝ)^831
        have hw : |(1080400099/2000000000 : ℝ)|=(1080400099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_9 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2637947643/5000000000 : ℝ)*x 0 + (-987888849/5000000000 : ℝ)*x 1 + (5402000473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637947643/5000000000 : ℝ)^1087 ≤ (10831435504249/25000000000000 : ℝ)^831 := by
    have hnat : (2637947643 : ℕ)^1087*25000000000000^831 ≤ 10831435504249^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637947643 5000000000 10831435504249 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987888849/5000000000 : ℝ)^1087 ≤ (479558208627/4000000000000 : ℝ)^831 := by
    have hnat : (987888849 : ℕ)^1087*4000000000000^831 ≤ 479558208627^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987888849 5000000000 479558208627 4000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402000473/10000000000 : ℝ)^1087 ≤ (2792831422127/6250000000000 : ℝ)^831 := by
    have hnat : (5402000473 : ℕ)^1087*6250000000000^831 ≤ 2792831422127^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402000473 10000000000 2792831422127 6250000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637947643/5000000000 : ℝ), (-987888849/5000000000 : ℝ), (5402000473/10000000000 : ℝ)] ![(10831435504249/25000000000000 : ℝ), (479558208627/4000000000000 : ℝ), (2792831422127/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637947643/5000000000 : ℝ)|^1087 ≤ (10831435504249/25000000000000 : ℝ)^831
        have hw : |(2637947643/5000000000 : ℝ)|=(2637947643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-987888849/5000000000 : ℝ)|^1087 ≤ (479558208627/4000000000000 : ℝ)^831
        have hw : |(-987888849/5000000000 : ℝ)|=(987888849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402000473/10000000000 : ℝ)|^1087 ≤ (2792831422127/6250000000000 : ℝ)^831
        have hw : |(5402000473/10000000000 : ℝ)|=(5402000473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_10 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5275895291/10000000000 : ℝ)*x 0 + (5402000469/10000000000 : ℝ)*x 1 + (-61743053/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275895291/10000000000 : ℝ)^1087 ≤ (8665148414141/20000000000000 : ℝ)^831 := by
    have hnat : (5275895291 : ℕ)^1087*20000000000000^831 ≤ 8665148414141^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275895291 10000000000 8665148414141 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402000469/10000000000 : ℝ)^1087 ≤ (44685302710751/100000000000000 : ℝ)^831 := by
    have hnat : (5402000469 : ℕ)^1087*100000000000000^831 ≤ 44685302710751^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402000469 10000000000 44685302710751 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61743053/312500000 : ℝ)^1087 ≤ (59944775999/500000000000 : ℝ)^831 := by
    have hnat : (61743053 : ℕ)^1087*500000000000^831 ≤ 59944775999^831*312500000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61743053 312500000 59944775999 500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275895291/10000000000 : ℝ), (5402000469/10000000000 : ℝ), (-61743053/312500000 : ℝ)] ![(8665148414141/20000000000000 : ℝ), (44685302710751/100000000000000 : ℝ), (59944775999/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275895291/10000000000 : ℝ)|^1087 ≤ (8665148414141/20000000000000 : ℝ)^831
        have hw : |(5275895291/10000000000 : ℝ)|=(5275895291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402000469/10000000000 : ℝ)|^1087 ≤ (44685302710751/100000000000000 : ℝ)^831
        have hw : |(5402000469/10000000000 : ℝ)|=(5402000469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61743053/312500000 : ℝ)|^1087 ≤ (59944775999/500000000000 : ℝ)^831
        have hw : |(-61743053/312500000 : ℝ)|=(61743053/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_11 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4495164669/10000000000 : ℝ)*x 0 + (4228024199/10000000000 : ℝ)*x 1 + (2114012121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4495164669/10000000000 : ℝ)^1087 ≤ (4392173989013/12500000000000 : ℝ)^831 := by
    have hnat : (4495164669 : ℕ)^1087*12500000000000^831 ≤ 4392173989013^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495164669 10000000000 4392173989013 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228024199/10000000000 : ℝ)^1087 ≤ (8107825955843/25000000000000 : ℝ)^831 := by
    have hnat : (4228024199 : ℕ)^1087*25000000000000^831 ≤ 8107825955843^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228024199 10000000000 8107825955843 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114012121/5000000000 : ℝ)^1087 ≤ (1013478257963/3125000000000 : ℝ)^831 := by
    have hnat : (2114012121 : ℕ)^1087*3125000000000^831 ≤ 1013478257963^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114012121 5000000000 1013478257963 3125000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4495164669/10000000000 : ℝ), (4228024199/10000000000 : ℝ), (2114012121/5000000000 : ℝ)] ![(4392173989013/12500000000000 : ℝ), (8107825955843/25000000000000 : ℝ), (1013478257963/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4495164669/10000000000 : ℝ)|^1087 ≤ (4392173989013/12500000000000 : ℝ)^831
        have hw : |(4495164669/10000000000 : ℝ)|=(4495164669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228024199/10000000000 : ℝ)|^1087 ≤ (8107825955843/25000000000000 : ℝ)^831
        have hw : |(4228024199/10000000000 : ℝ)|=(4228024199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114012121/5000000000 : ℝ)|^1087 ≤ (1013478257963/3125000000000 : ℝ)^831
        have hw : |(2114012121/5000000000 : ℝ)|=(2114012121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_12 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1910892909/10000000000 : ℝ)*x 0 + (5470200073/10000000000 : ℝ)*x 1 + (2627375589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1910892909/10000000000 : ℝ)^1087 ≤ (2295314304089/20000000000000 : ℝ)^831 := by
    have hnat : (1910892909 : ℕ)^1087*20000000000000^831 ≤ 2295314304089^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910892909 10000000000 2295314304089 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470200073/10000000000 : ℝ)^1087 ≤ (45424672564261/100000000000000 : ℝ)^831 := by
    have hnat : (5470200073 : ℕ)^1087*100000000000000^831 ≤ 45424672564261^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470200073 10000000000 45424672564261 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627375589/5000000000 : ℝ)^1087 ≤ (5387344486811/12500000000000 : ℝ)^831 := by
    have hnat : (2627375589 : ℕ)^1087*12500000000000^831 ≤ 5387344486811^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627375589 5000000000 5387344486811 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1910892909/10000000000 : ℝ), (5470200073/10000000000 : ℝ), (2627375589/5000000000 : ℝ)] ![(2295314304089/20000000000000 : ℝ), (45424672564261/100000000000000 : ℝ), (5387344486811/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1910892909/10000000000 : ℝ)|^1087 ≤ (2295314304089/20000000000000 : ℝ)^831
        have hw : |(-1910892909/10000000000 : ℝ)|=(1910892909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470200073/10000000000 : ℝ)|^1087 ≤ (45424672564261/100000000000000 : ℝ)^831
        have hw : |(5470200073/10000000000 : ℝ)|=(5470200073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627375589/5000000000 : ℝ)|^1087 ≤ (5387344486811/12500000000000 : ℝ)^831
        have hw : |(2627375589/5000000000 : ℝ)|=(2627375589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_13 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1075824893/2000000000 : ℝ)*x 0 + (-2035266371/10000000000 : ℝ)*x 1 + (2627375413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075824893/2000000000 : ℝ)^1087 ≤ (44437939494409/100000000000000 : ℝ)^831 := by
    have hnat : (1075824893 : ℕ)^1087*100000000000000^831 ≤ 44437939494409^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075824893 2000000000 44437939494409 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2035266371/10000000000 : ℝ)^1087 ≤ (12463308372549/100000000000000 : ℝ)^831 := by
    have hnat : (2035266371 : ℕ)^1087*100000000000000^831 ≤ 12463308372549^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035266371 10000000000 12463308372549 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627375413/5000000000 : ℝ)^1087 ≤ (43098752118037/100000000000000 : ℝ)^831 := by
    have hnat : (2627375413 : ℕ)^1087*100000000000000^831 ≤ 43098752118037^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627375413 5000000000 43098752118037 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075824893/2000000000 : ℝ), (-2035266371/10000000000 : ℝ), (2627375413/5000000000 : ℝ)] ![(44437939494409/100000000000000 : ℝ), (12463308372549/100000000000000 : ℝ), (43098752118037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075824893/2000000000 : ℝ)|^1087 ≤ (44437939494409/100000000000000 : ℝ)^831
        have hw : |(1075824893/2000000000 : ℝ)|=(1075824893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2035266371/10000000000 : ℝ)|^1087 ≤ (12463308372549/100000000000000 : ℝ)^831
        have hw : |(-2035266371/10000000000 : ℝ)|=(2035266371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627375413/5000000000 : ℝ)|^1087 ≤ (43098752118037/100000000000000 : ℝ)^831
        have hw : |(2627375413/5000000000 : ℝ)|=(2627375413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_14 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (168097647/312500000 : ℝ)*x 0 + (1050950057/2000000000 : ℝ)*x 1 + (-2035266773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168097647/312500000 : ℝ)^1087 ≤ (22218971038539/50000000000000 : ℝ)^831 := by
    have hnat : (168097647 : ℕ)^1087*50000000000000^831 ≤ 22218971038539^831*312500000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168097647 312500000 22218971038539 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050950057/2000000000 : ℝ)^1087 ≤ (43098746313891/100000000000000 : ℝ)^831 := by
    have hnat : (1050950057 : ℕ)^1087*100000000000000^831 ≤ 43098746313891^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050950057 2000000000 43098746313891 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2035266773/10000000000 : ℝ)^1087 ≤ (12463311592629/100000000000000 : ℝ)^831 := by
    have hnat : (2035266773 : ℕ)^1087*100000000000000^831 ≤ 12463311592629^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035266773 10000000000 12463311592629 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168097647/312500000 : ℝ), (1050950057/2000000000 : ℝ), (-2035266773/10000000000 : ℝ)] ![(22218971038539/50000000000000 : ℝ), (43098746313891/100000000000000 : ℝ), (12463311592629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168097647/312500000 : ℝ)|^1087 ≤ (22218971038539/50000000000000 : ℝ)^831
        have hw : |(168097647/312500000 : ℝ)|=(168097647/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050950057/2000000000 : ℝ)|^1087 ≤ (43098746313891/100000000000000 : ℝ)^831
        have hw : |(1050950057/2000000000 : ℝ)|=(1050950057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2035266773/10000000000 : ℝ)|^1087 ≤ (12463311592629/100000000000000 : ℝ)^831
        have hw : |(-2035266773/10000000000 : ℝ)|=(2035266773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_box_15 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1034826393/2500000000 : ℝ)*x 0 + (27537177/62500000 : ℝ)*x 1 + (4405949417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034826393/2500000000 : ℝ)^1087 ≤ (63088060941/200000000000 : ℝ)^831 := by
    have hnat : (1034826393 : ℕ)^1087*200000000000^831 ≤ 63088060941^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034826393 2500000000 63088060941 200000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27537177/62500000 : ℝ)^1087 ≤ (34227979188037/100000000000000 : ℝ)^831 := by
    have hnat : (27537177 : ℕ)^1087*100000000000000^831 ≤ 34227979188037^831*62500000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27537177 62500000 34227979188037 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4405949417/10000000000 : ℝ)^1087 ≤ (1369119613421/4000000000000 : ℝ)^831 := by
    have hnat : (4405949417 : ℕ)^1087*4000000000000^831 ≤ 1369119613421^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405949417 10000000000 1369119613421 4000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034826393/2500000000 : ℝ), (27537177/62500000 : ℝ), (4405949417/10000000000 : ℝ)] ![(63088060941/200000000000 : ℝ), (34227979188037/100000000000000 : ℝ), (1369119613421/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034826393/2500000000 : ℝ)|^1087 ≤ (63088060941/200000000000 : ℝ)^831
        have hw : |(1034826393/2500000000 : ℝ)|=(1034826393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27537177/62500000 : ℝ)|^1087 ≤ (34227979188037/100000000000000 : ℝ)^831
        have hw : |(27537177/62500000 : ℝ)|=(27537177/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4405949417/10000000000 : ℝ)|^1087 ≤ (1369119613421/4000000000000 : ℝ)^831
        have hw : |(4405949417/10000000000 : ℝ)|=(4405949417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1388_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15719/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59031/100000 : ℝ) ∧ (80219/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8453/10000 : ℝ) := by
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
  have lower0 : (5627/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5627/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5627/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5627/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5627/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5627/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5627/50000 : ℝ) ^ (4347/1024 : ℝ) ≤ (9390455553668181/100000000000000000000 : ℝ) := by
    have hpowers : (5627/50000 : ℝ)^4347 ≤ (9390455553668181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5627 : ℕ)^4347*100000000000000000000^1024 ≤ 9390455553668181^1024*50000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5627 50000 9390455553668181 100000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5627/50000 : ℝ)) (X := (9390455553668181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7367/50000 : ℝ) ^ (4347/1024 : ℝ) ≤ (29472960544211539/100000000000000000000 : ℝ) := by
    have hpowers : (7367/50000 : ℝ)^4347 ≤ (29472960544211539/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7367 : ℕ)^4347*100000000000000000000^1024 ≤ 29472960544211539^1024*50000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7367 50000 29472960544211539 100000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7367/50000 : ℝ)) (X := (29472960544211539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009390455553668181/50000000000000000000 : ℝ) ≤ (2000088476064423/2000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (50009390455553668181/50000000000000000000 : ℝ)^1024 ≤ (2000088476064423/2000000000000000 : ℝ)^4347 := by
      have hnat : (50009390455553668181 : ℕ)^1024*2000000000000000^4347 ≤ 2000088476064423^4347*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009390455553668181 50000000000000000000 2000088476064423 2000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000088476064423/2000000000000000 : ℝ)) (X := (50009390455553668181/50000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500971585402446993/2500000000000000000 : ℝ) ≤ (250022883729011/250000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (2500971585402446993/2500000000000000000 : ℝ)^1024 ≤ (250022883729011/250000000000000 : ℝ)^4347 := by
      have hnat : (2500971585402446993 : ℕ)^1024*250000000000000^4347 ≤ 250022883729011^4347*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500971585402446993 2500000000000000000 250022883729011 250000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250022883729011/250000000000000 : ℝ)) (X := (2500971585402446993/2500000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029472960544211539/50000000000000000000 : ℝ) ≤ (2000277663599753/2000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (50029472960544211539/50000000000000000000 : ℝ)^1024 ≤ (2000277663599753/2000000000000000 : ℝ)^4347 := by
      have hnat : (50029472960544211539 : ℕ)^1024*2000000000000000^4347 ≤ 2000277663599753^4347*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029472960544211539 50000000000000000000 2000277663599753 2000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000277663599753/2000000000000000 : ℝ)) (X := (50029472960544211539/50000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9390455553668181/100000000000000000000 : ℝ) ≤ ((347908939009079411/348000000000000000 : ℝ)+2*(18918753533/13920000000000 : ℝ)*(5627/50000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (347908939009079411/348000000000000000 : ℝ)+2*(18918753533/13920000000000 : ℝ)*(5627/50000 : ℝ)=(2000088476064423/2000000000000000 : ℝ) by norm_num, show 1+2*(9390455553668181/100000000000000000000 : ℝ)=(50009390455553668181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29472960544211539/100000000000000000000 : ℝ)+(9390455553668181/100000000000000000000 : ℝ) ≤ ((347908939009079411/348000000000000000 : ℝ)+(18918753533/13920000000000 : ℝ)*((7367/50000 : ℝ)+(5627/50000 : ℝ)))^(4347/1024 : ℝ) := by
    rw [show (347908939009079411/348000000000000000 : ℝ)+(18918753533/13920000000000 : ℝ)*((7367/50000 : ℝ)+(5627/50000 : ℝ))=(250022883729011/250000000000000 : ℝ) by norm_num, show 1+(29472960544211539/100000000000000000000 : ℝ)+(9390455553668181/100000000000000000000 : ℝ)=(2500971585402446993/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29472960544211539/100000000000000000000 : ℝ) ≤ ((347908939009079411/348000000000000000 : ℝ)+2*(18918753533/13920000000000 : ℝ)*(7367/50000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (347908939009079411/348000000000000000 : ℝ)+2*(18918753533/13920000000000 : ℝ)*(7367/50000 : ℝ)=(2000277663599753/2000000000000000 : ℝ) by norm_num, show 1+2*(29472960544211539/100000000000000000000 : ℝ)=(50029472960544211539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (347908939009079411/348000000000000000 : ℝ)*(X 1 0+X 2 0)+(18918753533/13920000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (5627/50000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (347908939009079411/348000000000000000 : ℝ)) (alpha := (18918753533/13920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (347908939009079411/348000000000000000 : ℝ)*(X 0 1+X 2 1)+(18918753533/13920000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (5627/50000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (347908939009079411/348000000000000000 : ℝ)) (alpha := (18918753533/13920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (347908939009079411/348000000000000000 : ℝ)*(X 0 2+X 1 2)+(18918753533/13920000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (5627/50000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (347908939009079411/348000000000000000 : ℝ)) (alpha := (18918753533/13920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-115075221/625000000 : ℝ)*X 0 0+(5388003219/10000000000 : ℝ)*X 0 1+(1077600497/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1057142583/2000000000 : ℝ)*X 1 0+(-396311627/2000000000 : ℝ)*X 1 1+(269400173/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285711269/10000000000 : ℝ)*X 2 0+(215520173/400000000 : ℝ)*X 2 1+(-123847449/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((278867791/625000000 : ℝ)*X 0 0+(424495087/1000000000 : ℝ)*X 0 1+(1061238021/2500000000 : ℝ)*X 0 2+(278867791/625000000 : ℝ)*X 1 0+(424495087/1000000000 : ℝ)*X 1 1+(1061238021/2500000000 : ℝ)*X 1 2+(278867791/625000000 : ℝ)*X 2 0+(424495087/1000000000 : ℝ)*X 2 1+(1061238021/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2171321861/10000000000 : ℝ)*X 0 0+(2632926779/5000000000 : ℝ)*X 0 1+(5265853483/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((335708937/625000000 : ℝ)*X 1 0+(-1269303/6250000 : ℝ)*X 1 1+(5265853503/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1074268573/2000000000 : ℝ)*X 2 0+(1053170727/2000000000 : ℝ)*X 2 1+(-406176959/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4166594803/10000000000 : ℝ)*X 0 0+(4392544337/10000000000 : ℝ)*X 0 1+(2196272127/5000000000 : ℝ)*X 0 2+(4166594803/10000000000 : ℝ)*X 1 0+(4392544337/10000000000 : ℝ)*X 1 1+(2196272127/5000000000 : ℝ)*X 1 2+(4166594803/10000000000 : ℝ)*X 2 0+(4392544337/10000000000 : ℝ)*X 2 1+(2196272127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1050941503/5000000000 : ℝ)*X 0 0+(2590775251/5000000000 : ℝ)*X 0 1+(1080400099/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637947643/5000000000 : ℝ)*X 1 0+(-987888849/5000000000 : ℝ)*X 1 1+(5402000473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275895291/10000000000 : ℝ)*X 2 0+(5402000469/10000000000 : ℝ)*X 2 1+(-61743053/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4495164669/10000000000 : ℝ)*X 0 0+(4228024199/10000000000 : ℝ)*X 0 1+(2114012121/5000000000 : ℝ)*X 0 2+(4495164669/10000000000 : ℝ)*X 1 0+(4228024199/10000000000 : ℝ)*X 1 1+(2114012121/5000000000 : ℝ)*X 1 2+(4495164669/10000000000 : ℝ)*X 2 0+(4228024199/10000000000 : ℝ)*X 2 1+(2114012121/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1910892909/10000000000 : ℝ)*X 0 0+(5470200073/10000000000 : ℝ)*X 0 1+(2627375589/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1075824893/2000000000 : ℝ)*X 1 0+(-2035266371/10000000000 : ℝ)*X 1 1+(2627375413/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((168097647/312500000 : ℝ)*X 2 0+(1050950057/2000000000 : ℝ)*X 2 1+(-2035266773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1034826393/2500000000 : ℝ)*X 0 0+(27537177/62500000 : ℝ)*X 0 1+(4405949417/10000000000 : ℝ)*X 0 2+(1034826393/2500000000 : ℝ)*X 1 0+(27537177/62500000 : ℝ)*X 1 1+(4405949417/10000000000 : ℝ)*X 1 2+(1034826393/2500000000 : ℝ)*X 2 0+(27537177/62500000 : ℝ)*X 2 1+(4405949417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15719/25000 : ℝ) ≤ (-3646673865614134782098260075887/5800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2649307/12500000000000 : ℝ)*(lower0) + (10258363/100000000000000 : ℝ)*(upper3) + (20508559/100000000000000 : ℝ)*(lower4) + (2971857713253083/100000000000000 : ℝ)*(major0) + (2971857713253083/100000000000000 : ℝ)*(major1) + (2971857713253083/100000000000000 : ℝ)*(major2) + (360153179/20000000000000 : ℝ)*(sp1) + (2033127536198549/50000000000000 : ℝ)*(sp4) + (1016563682779893/25000000000000 : ℝ)*(sp5) + (4066236340093923/100000000000000 : ℝ)*(sp6) + (1898404168156441/100000000000000 : ℝ)*(sp7) + (145948837/10000000000000 : ℝ)*(sp8) + (4038358309/20000000000000 : ℝ)*(sp14) + (12622243643/100000000000000 : ℝ)*(sp15) + (474604197600021/25000000000000 : ℝ)*(f.failure) + (1016564132971367/25000000000000 : ℝ)*(f.sum) + (98189111177/696000000000000000000000000 : ℝ)*base66 + (186121203181250887/34800000000000000000000000000000 : ℝ)*base68 + (377778403995650887/34800000000000000000000000000000 : ℝ)*base70 + (176183772967149113/34800000000000000000000000000000 : ℝ)*base71 + (6116403497647/696000000000000000000000000 : ℝ)*base73 + (78112887229250887/34800000000000000000000000000000 : ℝ)*base76 + (136823564697650887/34800000000000000000000000000000 : ℝ)*base78 + (19495849409949113/34800000000000000000000000000000 : ℝ)*base79 + (75190315961/696000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4375853/2500000000000000000000 : ℝ)*base90 + (4375853/2500000000000000000000 : ℝ)*base92 + (4375853/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59031/100000 : ℝ) ≤ (855991261411476742928565226917/1450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73581381/50000000000000 : ℝ)*(lower0) + (269413613/100000000000000 : ℝ)*(upper2) + (123603491/25000000000000 : ℝ)*(lower4) + (760525797331353/25000000000000 : ℝ)*(major0) + (760525797331353/25000000000000 : ℝ)*(major1) + (760525797331353/25000000000000 : ℝ)*(major2) + (4121237623395713/100000000000000 : ℝ)*(sp0) + (4121204606409573/100000000000000 : ℝ)*(sp1) + (824242917667909/20000000000000 : ℝ)*(sp2) + (1943287644405117/100000000000000 : ℝ)*(sp3) + (2146971817/6250000000000 : ℝ)*(sp5) + (243696191/1000000000000 : ℝ)*(sp6) + (908127301/50000000000000 : ℝ)*(sp7) + (333640733/25000000000000 : ℝ)*(sp12) + (971644730329859/50000000000000 : ℝ)*(f.failure) + (824247791591729/20000000000000 : ℝ)*(f.sum) + (800561539133/58000000000000000000000000 : ℝ)*base66 + (32333427797299361/2900000000000000000000000000000 : ℝ)*base67 + (18296705313700639/2900000000000000000000000000000 : ℝ)*base70 + (98560518910299361/2900000000000000000000000000000 : ℝ)*base71 + (105651868261/58000000000000000000000000 : ℝ)*base73 + (9435004489200639/2900000000000000000000000000000 : ℝ)*base76 + (9993024290899361/2900000000000000000000000000000 : ℝ)*base77 + (18051895115499361/2900000000000000000000000000000 : ℝ)*base79 + (25512022813/11600000000000000000000000 : ℝ)*base82 + (40394987/5000000000000000000000 : ℝ)*base90 + (40394987/5000000000000000000000 : ℝ)*base92 + (40394987/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80219/100000 : ℝ) ≤ (186114719858759051453941509/232000000000000000000000000 : ℝ) := by norm_num
    linear_combination (359249/50000000000000 : ℝ)*(upper0) + (3303423/50000000000000 : ℝ)*(lower1) + (2189471/12500000000000 : ℝ)*(lower3) + (107117/800000000000 : ℝ)*(lower5) + (3352124251452201/100000000000000 : ℝ)*(major0) + (3352124251452201/100000000000000 : ℝ)*(major1) + (3352124251452201/100000000000000 : ℝ)*(major2) + (1646148959/100000000000000 : ℝ)*(sp0) + (1155110353/50000000000000 : ℝ)*(sp1) + (4780013549/50000000000000 : ℝ)*(sp3) + (907235187635359/20000000000000 : ℝ)*(sp8) + (4536175274105047/100000000000000 : ℝ)*(sp9) + (4536177584325753/100000000000000 : ℝ)*(sp10) + (2141320737882167/100000000000000 : ℝ)*(sp11) + (428266059581853/20000000000000 : ℝ)*(f.failure) + (4536177584325753/100000000000000 : ℝ)*(f.sum) + (951011376367/232000000000000000000000000 : ℝ)*base65 + (88737249645380463/11600000000000000000000000000000 : ℝ)*base68 + (563024207156580463/11600000000000000000000000000000 : ℝ)*base70 + (25465239422219537/11600000000000000000000000000000 : ℝ)*base71 + (8841070196753/232000000000000000000000000 : ℝ)*base74 + (271275013971819537/11600000000000000000000000000000 : ℝ)*base75 + (47250008206619537/11600000000000000000000000000000 : ℝ)*base77 + (687439674978980463/11600000000000000000000000000000 : ℝ)*base80 + (284231151749/46400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (6895029/2000000000000000000000 : ℝ)*base90 + (6895029/2000000000000000000000 : ℝ)*base92 + (6895029/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-8453/10000 : ℝ) ≤ (-2451285428976759100239856636347/2900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3310741/100000000000000 : ℝ)*(lower1) + (170979623/100000000000000 : ℝ)*(lower3) + (113343067/50000000000000 : ℝ)*(lower4) + (66727161/100000000000000 : ℝ)*(upper5) + (1694568462594777/50000000000000 : ℝ)*(major0) + (1694568462594777/50000000000000 : ℝ)*(major1) + (1694568462594777/50000000000000 : ℝ)*(major2) + (3863107033/100000000000000 : ℝ)*(sp4) + (5423162221/1250000000000 : ℝ)*(sp6) + (13167972917/25000000000000 : ℝ)*(sp7) + (185658870466231/4000000000000 : ℝ)*(sp12) + (580184453095351/12500000000000 : ℝ)*(sp13) + (580130221473141/12500000000000 : ℝ)*(sp14) + (1082460624155281/50000000000000 : ℝ)*(sp15) + (216497392020223/10000000000000 : ℝ)*(f.failure) + (580184453095351/12500000000000 : ℝ)*(f.sum) + (596771078633/116000000000000000000000000 : ℝ)*base66 + (10133698835879551/5800000000000000000000000000000 : ℝ)*base68 + (127532015738120449/5800000000000000000000000000000 : ℝ)*base69 + (15795459565279551/5800000000000000000000000000000 : ℝ)*base72 + (434418082761/116000000000000000000000000 : ℝ)*base74 + (83710228727920449/5800000000000000000000000000000 : ℝ)*base75 + (28621186401120449/5800000000000000000000000000000 : ℝ)*base77 + (22027978076320449/5800000000000000000000000000000 : ℝ)*base79 + (147360280627/23200000000000000000000000 : ℝ)*base81 + (6546439/1000000000000000000000 : ℝ)*base90 + (6546439/1000000000000000000000 : ℝ)*base92 + (6546439/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1388_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15719/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59031/100000 : ℝ) else (80219/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8453/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1388_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1388_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (737/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15719/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59031/100000 : ℝ) else (80219/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8453/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1388_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1388_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1388_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (737/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15719/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59031/100000 : ℝ) else (80219/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8453/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1388_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
