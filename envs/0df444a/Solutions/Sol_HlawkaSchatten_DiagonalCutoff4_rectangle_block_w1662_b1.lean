-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1662_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:55.744627+00:00
-- url     : https://prove2.me/submissions/526804ff-f3b0-4e30-947d-0741247dae2f

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
theorem support_rectangle_w1662_s3_0 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1581625789/10000000000 : ℝ)*x 0 + (217762193/400000000 : ℝ)*x 1 + (5184595033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1581625789/10000000000 : ℝ)^4967 ≤ (4898694923171/50000000000000 : ℝ)^3943 := by
    have hnat : (1581625789 : ℕ)^4967*50000000000000^3943 ≤ 4898694923171^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1581625789 10000000000 4898694923171 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217762193/400000000 : ℝ)^4967 ≤ (23244026985947/50000000000000 : ℝ)^3943 := by
    have hnat : (217762193 : ℕ)^4967*50000000000000^3943 ≤ 23244026985947^3943*400000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217762193 400000000 23244026985947 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184595033/10000000000 : ℝ)^4967 ≤ (43714556174241/100000000000000 : ℝ)^3943 := by
    have hnat : (5184595033 : ℕ)^4967*100000000000000^3943 ≤ 43714556174241^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184595033 10000000000 43714556174241 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1581625789/10000000000 : ℝ), (217762193/400000000 : ℝ), (5184595033/10000000000 : ℝ)] ![(4898694923171/50000000000000 : ℝ), (23244026985947/50000000000000 : ℝ), (43714556174241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1581625789/10000000000 : ℝ)|^4967 ≤ (4898694923171/50000000000000 : ℝ)^3943
        have hw : |(-1581625789/10000000000 : ℝ)|=(1581625789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217762193/400000000 : ℝ)|^4967 ≤ (23244026985947/50000000000000 : ℝ)^3943
        have hw : |(217762193/400000000 : ℝ)|=(217762193/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184595033/10000000000 : ℝ)|^4967 ≤ (43714556174241/100000000000000 : ℝ)^3943
        have hw : |(5184595033/10000000000 : ℝ)|=(5184595033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s3_1 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345936603/10000000000 : ℝ)*x 0 + (-343026323/2000000000 : ℝ)*x 1 + (5184595009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345936603/10000000000 : ℝ)^4967 ≤ (9087017862839/20000000000000 : ℝ)^3943 := by
    have hnat : (5345936603 : ℕ)^4967*20000000000000^3943 ≤ 9087017862839^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345936603 10000000000 9087017862839 20000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343026323/2000000000 : ℝ)^4967 ≤ (10850354749711/100000000000000 : ℝ)^3943 := by
    have hnat : (343026323 : ℕ)^4967*100000000000000^3943 ≤ 10850354749711^3943*2000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343026323 2000000000 10850354749711 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184595009/10000000000 : ℝ)^4967 ≤ (4371455591933/10000000000000 : ℝ)^3943 := by
    have hnat : (5184595009 : ℕ)^4967*10000000000000^3943 ≤ 4371455591933^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184595009 10000000000 4371455591933 10000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345936603/10000000000 : ℝ), (-343026323/2000000000 : ℝ), (5184595009/10000000000 : ℝ)] ![(9087017862839/20000000000000 : ℝ), (10850354749711/100000000000000 : ℝ), (4371455591933/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345936603/10000000000 : ℝ)|^4967 ≤ (9087017862839/20000000000000 : ℝ)^3943
        have hw : |(5345936603/10000000000 : ℝ)|=(5345936603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-343026323/2000000000 : ℝ)|^4967 ≤ (10850354749711/100000000000000 : ℝ)^3943
        have hw : |(-343026323/2000000000 : ℝ)|=(343026323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184595009/10000000000 : ℝ)|^4967 ≤ (4371455591933/10000000000000 : ℝ)^3943
        have hw : |(5184595009/10000000000 : ℝ)|=(5184595009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s3_2 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167060519/312500000 : ℝ)*x 0 + (2592297509/5000000000 : ℝ)*x 1 + (-428782899/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167060519/312500000 : ℝ)^4967 ≤ (22717544683863/50000000000000 : ℝ)^3943 := by
    have hnat : (167060519 : ℕ)^4967*50000000000000^3943 ≤ 22717544683863^3943*312500000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167060519 312500000 22717544683863 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592297509/5000000000 : ℝ)^4967 ≤ (43714556014921/100000000000000 : ℝ)^3943 := by
    have hnat : (2592297509 : ℕ)^4967*100000000000000^3943 ≤ 43714556014921^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592297509 5000000000 43714556014921 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428782899/2500000000 : ℝ)^4967 ≤ (1356294324787/12500000000000 : ℝ)^3943 := by
    have hnat : (428782899 : ℕ)^4967*12500000000000^3943 ≤ 1356294324787^3943*2500000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428782899 2500000000 1356294324787 12500000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167060519/312500000 : ℝ), (2592297509/5000000000 : ℝ), (-428782899/2500000000 : ℝ)] ![(22717544683863/50000000000000 : ℝ), (43714556014921/100000000000000 : ℝ), (1356294324787/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167060519/312500000 : ℝ)|^4967 ≤ (22717544683863/50000000000000 : ℝ)^3943
        have hw : |(167060519/312500000 : ℝ)|=(167060519/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592297509/5000000000 : ℝ)|^4967 ≤ (43714556014921/100000000000000 : ℝ)^3943
        have hw : |(2592297509/5000000000 : ℝ)|=(2592297509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428782899/2500000000 : ℝ)|^4967 ≤ (1356294324787/12500000000000 : ℝ)^3943
        have hw : |(-428782899/2500000000 : ℝ)|=(428782899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s3_3 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208580939/500000000 : ℝ)*x 0 + (1920406411/5000000000 : ℝ)*x 1 + (565282353/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208580939/500000000 : ℝ)^4967 ≤ (33242788223961/100000000000000 : ℝ)^3943 := by
    have hnat : (208580939 : ℕ)^4967*100000000000000^3943 ≤ 33242788223961^3943*500000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208580939 500000000 33242788223961 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1920406411/5000000000 : ℝ)^4967 ≤ (29956945362777/100000000000000 : ℝ)^3943 := by
    have hnat : (1920406411 : ℕ)^4967*100000000000000^3943 ≤ 29956945362777^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920406411 5000000000 29956945362777 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565282353/1250000000 : ℝ)^4967 ≤ (18400133201117/50000000000000 : ℝ)^3943 := by
    have hnat : (565282353 : ℕ)^4967*50000000000000^3943 ≤ 18400133201117^3943*1250000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565282353 1250000000 18400133201117 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208580939/500000000 : ℝ), (1920406411/5000000000 : ℝ), (565282353/1250000000 : ℝ)] ![(33242788223961/100000000000000 : ℝ), (29956945362777/100000000000000 : ℝ), (18400133201117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208580939/500000000 : ℝ)|^4967 ≤ (33242788223961/100000000000000 : ℝ)^3943
        have hw : |(208580939/500000000 : ℝ)|=(208580939/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1920406411/5000000000 : ℝ)|^4967 ≤ (29956945362777/100000000000000 : ℝ)^3943
        have hw : |(1920406411/5000000000 : ℝ)|=(1920406411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565282353/1250000000 : ℝ)|^4967 ≤ (18400133201117/50000000000000 : ℝ)^3943
        have hw : |(565282353/1250000000 : ℝ)|=(565282353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s3_4 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-790844319/5000000000 : ℝ)*x 0 + (2593284599/5000000000 : ℝ)*x 1 + (2721029877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (790844319/5000000000 : ℝ)^4967 ≤ (9797880273653/100000000000000 : ℝ)^3943 := by
    have hnat : (790844319 : ℕ)^4967*100000000000000^3943 ≤ 9797880273653^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790844319 5000000000 9797880273653 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593284599/5000000000 : ℝ)^4967 ≤ (874710509101/2000000000000 : ℝ)^3943 := by
    have hnat : (2593284599 : ℕ)^4967*2000000000000^3943 ≤ 874710509101^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593284599 5000000000 874710509101 2000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721029877/5000000000 : ℝ)^4967 ≤ (23233297128531/50000000000000 : ℝ)^3943 := by
    have hnat : (2721029877 : ℕ)^4967*50000000000000^3943 ≤ 23233297128531^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721029877 5000000000 23233297128531 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-790844319/5000000000 : ℝ), (2593284599/5000000000 : ℝ), (2721029877/5000000000 : ℝ)] ![(9797880273653/100000000000000 : ℝ), (874710509101/2000000000000 : ℝ), (23233297128531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-790844319/5000000000 : ℝ)|^4967 ≤ (9797880273653/100000000000000 : ℝ)^3943
        have hw : |(-790844319/5000000000 : ℝ)|=(790844319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593284599/5000000000 : ℝ)|^4967 ≤ (874710509101/2000000000000 : ℝ)^3943
        have hw : |(2593284599/5000000000 : ℝ)|=(2593284599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721029877/5000000000 : ℝ)|^4967 ≤ (23233297128531/50000000000000 : ℝ)^3943
        have hw : |(2721029877/5000000000 : ℝ)|=(2721029877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s3_5 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319132223/2500000000 : ℝ)*x 0 + (-91104179/625000000 : ℝ)*x 1 + (2721029877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319132223/2500000000 : ℝ)^4967 ≤ (1396664185727/3125000000000 : ℝ)^3943 := by
    have hnat : (1319132223 : ℕ)^4967*3125000000000^3943 ≤ 1396664185727^3943*2500000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319132223 2500000000 1396664185727 3125000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91104179/625000000 : ℝ)^4967 ≤ (4420075893479/50000000000000 : ℝ)^3943 := by
    have hnat : (91104179 : ℕ)^4967*50000000000000^3943 ≤ 4420075893479^3943*625000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91104179 625000000 4420075893479 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721029877/5000000000 : ℝ)^4967 ≤ (23233297128531/50000000000000 : ℝ)^3943 := by
    have hnat : (2721029877 : ℕ)^4967*50000000000000^3943 ≤ 23233297128531^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721029877 5000000000 23233297128531 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319132223/2500000000 : ℝ), (-91104179/625000000 : ℝ), (2721029877/5000000000 : ℝ)] ![(1396664185727/3125000000000 : ℝ), (4420075893479/50000000000000 : ℝ), (23233297128531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319132223/2500000000 : ℝ)|^4967 ≤ (1396664185727/3125000000000 : ℝ)^3943
        have hw : |(1319132223/2500000000 : ℝ)|=(1319132223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91104179/625000000 : ℝ)|^4967 ≤ (4420075893479/50000000000000 : ℝ)^3943
        have hw : |(-91104179/625000000 : ℝ)|=(91104179/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721029877/5000000000 : ℝ)|^4967 ≤ (23233297128531/50000000000000 : ℝ)^3943
        have hw : |(2721029877/5000000000 : ℝ)|=(2721029877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s3_6 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276528779/10000000000 : ℝ)*x 0 + (5442059923/10000000000 : ℝ)*x 1 + (-45552087/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276528779/10000000000 : ℝ)^4967 ≤ (44693252737563/100000000000000 : ℝ)^3943 := by
    have hnat : (5276528779 : ℕ)^4967*100000000000000^3943 ≤ 44693252737563^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276528779 10000000000 44693252737563 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442059923/10000000000 : ℝ)^4967 ≤ (46466596074801/100000000000000 : ℝ)^3943 := by
    have hnat : (5442059923 : ℕ)^4967*100000000000000^3943 ≤ 46466596074801^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442059923 10000000000 46466596074801 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45552087/312500000 : ℝ)^4967 ≤ (552509448487/6250000000000 : ℝ)^3943 := by
    have hnat : (45552087 : ℕ)^4967*6250000000000^3943 ≤ 552509448487^3943*312500000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45552087 312500000 552509448487 6250000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276528779/10000000000 : ℝ), (5442059923/10000000000 : ℝ), (-45552087/312500000 : ℝ)] ![(44693252737563/100000000000000 : ℝ), (46466596074801/100000000000000 : ℝ), (552509448487/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276528779/10000000000 : ℝ)|^4967 ≤ (44693252737563/100000000000000 : ℝ)^3943
        have hw : |(5276528779/10000000000 : ℝ)|=(5276528779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442059923/10000000000 : ℝ)|^4967 ≤ (46466596074801/100000000000000 : ℝ)^3943
        have hw : |(5442059923/10000000000 : ℝ)|=(5442059923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45552087/312500000 : ℝ)|^4967 ≤ (552509448487/6250000000000 : ℝ)^3943
        have hw : |(-45552087/312500000 : ℝ)|=(45552087/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s3_7 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042945863/2500000000 : ℝ)*x 0 + (4517073887/10000000000 : ℝ)*x 1 + (1923026219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042945863/2500000000 : ℝ)^4967 ≤ (33244441259529/100000000000000 : ℝ)^3943 := by
    have hnat : (1042945863 : ℕ)^4967*100000000000000^3943 ≤ 33244441259529^3943*2500000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042945863 2500000000 33244441259529 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517073887/10000000000 : ℝ)^4967 ≤ (36747123932437/100000000000000 : ℝ)^3943 := by
    have hnat : (4517073887 : ℕ)^4967*100000000000000^3943 ≤ 36747123932437^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517073887 10000000000 36747123932437 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1923026219/5000000000 : ℝ)^4967 ≤ (15004217398863/50000000000000 : ℝ)^3943 := by
    have hnat : (1923026219 : ℕ)^4967*50000000000000^3943 ≤ 15004217398863^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923026219 5000000000 15004217398863 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042945863/2500000000 : ℝ), (4517073887/10000000000 : ℝ), (1923026219/5000000000 : ℝ)] ![(33244441259529/100000000000000 : ℝ), (36747123932437/100000000000000 : ℝ), (15004217398863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042945863/2500000000 : ℝ)|^4967 ≤ (33244441259529/100000000000000 : ℝ)^3943
        have hw : |(1042945863/2500000000 : ℝ)|=(1042945863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517073887/10000000000 : ℝ)|^4967 ≤ (36747123932437/100000000000000 : ℝ)^3943
        have hw : |(4517073887/10000000000 : ℝ)|=(4517073887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1923026219/5000000000 : ℝ)|^4967 ≤ (15004217398863/50000000000000 : ℝ)^3943
        have hw : |(1923026219/5000000000 : ℝ)|=(1923026219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1662_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181320169/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16307/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5337/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1341/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2031/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16307/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5337/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16307/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5337/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16307/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5337/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16307/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5337/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16307/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5337/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16307/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5337/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5337/50000 : ℝ) ^ (4963/1024 : ℝ) ≤ (1952599482694141/100000000000000000000 : ℝ) := by
    have hpowers : (5337/50000 : ℝ)^4963 ≤ (1952599482694141/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5337 : ℕ)^4963*100000000000000000000^1024 ≤ 1952599482694141^1024*50000^4963 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5337 50000 1952599482694141 100000000000000000000 4963 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5337/50000 : ℝ)) (X := (1952599482694141/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16307/100000 : ℝ) ^ (4963/1024 : ℝ) ≤ (7613764049014521/50000000000000000000 : ℝ) := by
    have hpowers : (16307/100000 : ℝ)^4963 ≤ (7613764049014521/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16307 : ℕ)^4963*50000000000000000000^1024 ≤ 7613764049014521^1024*100000^4963 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16307 100000 7613764049014521 50000000000000000000 4963 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16307/100000 : ℝ)) (X := (7613764049014521/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001952599482694141/50000000000000000000 : ℝ) ≤ (10000080573479139/10000000000000000 : ℝ) ^ (4963/1024 : ℝ) := by
    have hpowers : (50001952599482694141/50000000000000000000 : ℝ)^1024 ≤ (10000080573479139/10000000000000000 : ℝ)^4963 := by
      have hnat : (50001952599482694141 : ℕ)^1024*10000000000000000^4963 ≤ 10000080573479139^4963*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001952599482694141 50000000000000000000 10000080573479139 10000000000000000 1024 4963 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000080573479139/10000000000000000 : ℝ)) (X := (50001952599482694141/50000000000000000000 : ℝ)) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100017180127580723183/100000000000000000000 : ℝ) ≤ (10000354447942067/10000000000000000 : ℝ) ^ (4963/1024 : ℝ) := by
    have hpowers : (100017180127580723183/100000000000000000000 : ℝ)^1024 ≤ (10000354447942067/10000000000000000 : ℝ)^4963 := by
      have hnat : (100017180127580723183 : ℕ)^1024*10000000000000000^4963 ≤ 10000354447942067^4963*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017180127580723183 100000000000000000000 10000354447942067 10000000000000000 1024 4963 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000354447942067/10000000000000000 : ℝ)) (X := (100017180127580723183/100000000000000000000 : ℝ)) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25007613764049014521/25000000000000000000 : ℝ) ≤ (2000125664480999/2000000000000000 : ℝ) ^ (4963/1024 : ℝ) := by
    have hpowers : (25007613764049014521/25000000000000000000 : ℝ)^1024 ≤ (2000125664480999/2000000000000000 : ℝ)^4963 := by
      have hnat : (25007613764049014521 : ℕ)^1024*2000000000000000^4963 ≤ 2000125664480999^4963*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007613764049014521 25000000000000000000 2000125664480999 2000000000000000 1024 4963 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000125664480999/2000000000000000 : ℝ)) (X := (25007613764049014521/25000000000000000000 : ℝ)) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1952599482694141/100000000000000000000 : ℝ) ≤ ((56324607198373403043/56330000000000000000 : ℝ)+2*(17117153933/35206250000000 : ℝ)*(5337/50000 : ℝ))^(4963/1024 : ℝ) := by
    rw [show (56324607198373403043/56330000000000000000 : ℝ)+2*(17117153933/35206250000000 : ℝ)*(5337/50000 : ℝ)=(10000080573479139/10000000000000000 : ℝ) by norm_num, show 1+2*(1952599482694141/100000000000000000000 : ℝ)=(50001952599482694141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7613764049014521/50000000000000000000 : ℝ)+(1952599482694141/100000000000000000000 : ℝ) ≤ ((56324607198373403043/56330000000000000000 : ℝ)+(17117153933/35206250000000 : ℝ)*((16307/100000 : ℝ)+(5337/50000 : ℝ)))^(4963/1024 : ℝ) := by
    rw [show (56324607198373403043/56330000000000000000 : ℝ)+(17117153933/35206250000000 : ℝ)*((16307/100000 : ℝ)+(5337/50000 : ℝ))=(10000354447942067/10000000000000000 : ℝ) by norm_num, show 1+(7613764049014521/50000000000000000000 : ℝ)+(1952599482694141/100000000000000000000 : ℝ)=(100017180127580723183/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7613764049014521/50000000000000000000 : ℝ) ≤ ((56324607198373403043/56330000000000000000 : ℝ)+2*(17117153933/35206250000000 : ℝ)*(16307/100000 : ℝ))^(4963/1024 : ℝ) := by
    rw [show (56324607198373403043/56330000000000000000 : ℝ)+2*(17117153933/35206250000000 : ℝ)*(16307/100000 : ℝ)=(2000125664480999/2000000000000000 : ℝ) by norm_num, show 1+2*(7613764049014521/50000000000000000000 : ℝ)=(25007613764049014521/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56324607198373403043/56330000000000000000 : ℝ)*(X 1 0+X 2 0)+(17117153933/35206250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4963/1024 : ℝ)) (lo := (5337/50000 : ℝ)) (hi := (16307/100000 : ℝ)) (c := (56324607198373403043/56330000000000000000 : ℝ)) (alpha := (17117153933/35206250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56324607198373403043/56330000000000000000 : ℝ)*(X 0 1+X 2 1)+(17117153933/35206250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4963/1024 : ℝ)) (lo := (5337/50000 : ℝ)) (hi := (16307/100000 : ℝ)) (c := (56324607198373403043/56330000000000000000 : ℝ)) (alpha := (17117153933/35206250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56324607198373403043/56330000000000000000 : ℝ)*(X 0 2+X 1 2)+(17117153933/35206250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4963/1024 : ℝ)) (lo := (5337/50000 : ℝ)) (hi := (16307/100000 : ℝ)) (c := (56324607198373403043/56330000000000000000 : ℝ)) (alpha := (17117153933/35206250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1581625789/10000000000 : ℝ)*X 0 0+(217762193/400000000 : ℝ)*X 0 1+(5184595033/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345936603/10000000000 : ℝ)*X 1 0+(-343026323/2000000000 : ℝ)*X 1 1+(5184595009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167060519/312500000 : ℝ)*X 2 0+(2592297509/5000000000 : ℝ)*X 2 1+(-428782899/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((208580939/500000000 : ℝ)*X 0 0+(1920406411/5000000000 : ℝ)*X 0 1+(565282353/1250000000 : ℝ)*X 0 2+(208580939/500000000 : ℝ)*X 1 0+(1920406411/5000000000 : ℝ)*X 1 1+(565282353/1250000000 : ℝ)*X 1 2+(208580939/500000000 : ℝ)*X 2 0+(1920406411/5000000000 : ℝ)*X 2 1+(565282353/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-790844319/5000000000 : ℝ)*X 0 0+(2593284599/5000000000 : ℝ)*X 0 1+(2721029877/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319132223/2500000000 : ℝ)*X 1 0+(-91104179/625000000 : ℝ)*X 1 1+(2721029877/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276528779/10000000000 : ℝ)*X 2 0+(5442059923/10000000000 : ℝ)*X 2 1+(-45552087/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1042945863/2500000000 : ℝ)*X 0 0+(4517073887/10000000000 : ℝ)*X 0 1+(1923026219/5000000000 : ℝ)*X 0 2+(1042945863/2500000000 : ℝ)*X 1 0+(4517073887/10000000000 : ℝ)*X 1 1+(1923026219/5000000000 : ℝ)*X 1 2+(1042945863/2500000000 : ℝ)*X 2 0+(4517073887/10000000000 : ℝ)*X 2 1+(1923026219/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2365076521451837776738751181/563300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (309757607/50000000000000 : ℝ)*(base19) + (576987909/100000000000000 : ℝ)*(base23) + (6165479/25000000000000 : ℝ)*(lower2) + (88669809/100000000000000 : ℝ)*(upper3) + (35762799/50000000000000 : ℝ)*(upper5) + (532165080500389/20000000000000 : ℝ)*(major0) + (532165080500389/20000000000000 : ℝ)*(major1) + (532165080500389/20000000000000 : ℝ)*(major2) + (1927084698340443/50000000000000 : ℝ)*(sp0) + (1927088280413733/50000000000000 : ℝ)*(sp1) + (3854176603354771/100000000000000 : ℝ)*(sp2) + (146747044513237/10000000000000 : ℝ)*(sp3) + (7783661793/100000000000000 : ℝ)*(sp4) + (607915039/20000000000000 : ℝ)*(sp7) + (366868371176891/25000000000000 : ℝ)*(f.failure) + (96354429508567/2500000000000 : ℝ)*(f.sum) + (144627538367/44007812500000000000000000 : ℝ)*base65 + (2243012235420916273/1126600000000000000000000000000000 : ℝ)*base68 + (1094802223455516273/1126600000000000000000000000000000 : ℝ)*base70 + (4498436358283683727/1126600000000000000000000000000000 : ℝ)*base71 + (4182687141003/5633000000000000000000000000 : ℝ)*base74 + (6118648515159916273/1126600000000000000000000000000000 : ℝ)*base76 + (5125706092001683727/1126600000000000000000000000000000 : ℝ)*base77 + (188436224933316273/1126600000000000000000000000000000 : ℝ)*base80 + (349691349199/112660000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (19985421/2500000000000000000000 : ℝ)*base90 + (19985421/2500000000000000000000 : ℝ)*base92 + (19985421/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1832596497980636543593126419/140825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (997548161/50000000000000 : ℝ)*(base19) + (490235199/25000000000000 : ℝ)*(base23) + (60802339/20000000000000 : ℝ)*(upper3) + (3083731/25000000000000 : ℝ)*(lower4) + (271377089/100000000000000 : ℝ)*(upper5) + (135107590744011/5000000000000 : ℝ)*(major0) + (135107590744011/5000000000000 : ℝ)*(major1) + (135107590744011/5000000000000 : ℝ)*(major2) + (11755809281/50000000000000 : ℝ)*(sp1) + (25510116531/100000000000000 : ℝ)*(sp2) + (978509438923833/25000000000000 : ℝ)*(sp4) + (122312882780639/3125000000000 : ℝ)*(sp5) + (1957005142319003/50000000000000 : ℝ)*(sp6) + (745132720144393/50000000000000 : ℝ)*(sp7) + (745132720144393/50000000000000 : ℝ)*(f.failure) + (978509438923833/25000000000000 : ℝ)*(f.sum) + (18962461739/22003906250000000000000000 : ℝ)*base65 + (296933948892474527/281650000000000000000000000000000 : ℝ)*base68 + (192879713698825473/281650000000000000000000000000000 : ℝ)*base69 + (115124045284874527/281650000000000000000000000000000 : ℝ)*base72 + (1638960062563/352062500000000000000000000 : ℝ)*base74 + (2139706892977525473/281650000000000000000000000000000 : ℝ)*base75 + (84118047367874527/281650000000000000000000000000000 : ℝ)*base78 + (920420402086474527/281650000000000000000000000000000 : ℝ)*base80 + (4270831860109/704125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (43162417/5000000000000000000000 : ℝ)*base89 + (43162417/5000000000000000000000 : ℝ)*base91 + (43162417/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1662_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181320169/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16307/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5337/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2031/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1662_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1662_s4_0 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-395414657/2500000000 : ℝ)*x 0 + (1088776657/2000000000 : ℝ)*x 1 + (2592372317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (395414657/2500000000 : ℝ)^4967 ≤ (9797646097083/100000000000000 : ℝ)^3943 := by
    have hnat : (395414657 : ℕ)^4967*100000000000000^3943 ≤ 9797646097083^3943*2500000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395414657 2500000000 9797646097083 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088776657/2000000000 : ℝ)^4967 ≤ (46486208744523/100000000000000 : ℝ)^3943 := by
    have hnat : (1088776657 : ℕ)^4967*100000000000000^3943 ≤ 46486208744523^3943*2000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088776657 2000000000 46486208744523 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592372317/5000000000 : ℝ)^4967 ≤ (2185807257037/5000000000000 : ℝ)^3943 := by
    have hnat : (2592372317 : ℕ)^4967*5000000000000^3943 ≤ 2185807257037^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592372317 5000000000 2185807257037 5000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-395414657/2500000000 : ℝ), (1088776657/2000000000 : ℝ), (2592372317/5000000000 : ℝ)] ![(9797646097083/100000000000000 : ℝ), (46486208744523/100000000000000 : ℝ), (2185807257037/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-395414657/2500000000 : ℝ)|^4967 ≤ (9797646097083/100000000000000 : ℝ)^3943
        have hw : |(-395414657/2500000000 : ℝ)|=(395414657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088776657/2000000000 : ℝ)|^4967 ≤ (46486208744523/100000000000000 : ℝ)^3943
        have hw : |(1088776657/2000000000 : ℝ)|=(1088776657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592372317/5000000000 : ℝ)|^4967 ≤ (2185807257037/5000000000000 : ℝ)^3943
        have hw : |(2592372317/5000000000 : ℝ)|=(2592372317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s4_1 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53458903/100000000 : ℝ)*x 0 + (-428748591/2500000000 : ℝ)*x 1 + (5184744659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53458903/100000000 : ℝ)^4967 ≤ (1419831049563/3125000000000 : ℝ)^3943 := by
    have hnat : (53458903 : ℕ)^4967*3125000000000^3943 ≤ 1419831049563^3943*100000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53458903 100000000 1419831049563 3125000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428748591/2500000000 : ℝ)^4967 ≤ (10849260982569/100000000000000 : ℝ)^3943 := by
    have hnat : (428748591 : ℕ)^4967*100000000000000^3943 ≤ 10849260982569^3943*2500000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428748591 2500000000 10849260982569 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184744659/10000000000 : ℝ)^4967 ≤ (1748645816251/4000000000000 : ℝ)^3943 := by
    have hnat : (5184744659 : ℕ)^4967*4000000000000^3943 ≤ 1748645816251^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184744659 10000000000 1748645816251 4000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53458903/100000000 : ℝ), (-428748591/2500000000 : ℝ), (5184744659/10000000000 : ℝ)] ![(1419831049563/3125000000000 : ℝ), (10849260982569/100000000000000 : ℝ), (1748645816251/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53458903/100000000 : ℝ)|^4967 ≤ (1419831049563/3125000000000 : ℝ)^3943
        have hw : |(53458903/100000000 : ℝ)|=(53458903/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428748591/2500000000 : ℝ)|^4967 ≤ (10849260982569/100000000000000 : ℝ)^3943
        have hw : |(-428748591/2500000000 : ℝ)|=(428748591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184744659/10000000000 : ℝ)|^4967 ≤ (1748645816251/4000000000000 : ℝ)^3943
        have hw : |(5184744659/10000000000 : ℝ)|=(5184744659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s4_2 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069178053/2000000000 : ℝ)*x 0 + (2592372243/5000000000 : ℝ)*x 1 + (-1714994643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069178053/2000000000 : ℝ)^4967 ≤ (454345932113/1000000000000 : ℝ)^3943 := by
    have hnat : (1069178053 : ℕ)^4967*1000000000000^3943 ≤ 454345932113^3943*2000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069178053 2000000000 454345932113 1000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592372243/5000000000 : ℝ)^4967 ≤ (10929035892193/25000000000000 : ℝ)^3943 := by
    have hnat : (2592372243 : ℕ)^4967*25000000000000^3943 ≤ 10929035892193^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592372243 5000000000 10929035892193 25000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1714994643/10000000000 : ℝ)^4967 ≤ (433970528237/4000000000000 : ℝ)^3943 := by
    have hnat : (1714994643 : ℕ)^4967*4000000000000^3943 ≤ 433970528237^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714994643 10000000000 433970528237 4000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069178053/2000000000 : ℝ), (2592372243/5000000000 : ℝ), (-1714994643/10000000000 : ℝ)] ![(454345932113/1000000000000 : ℝ), (10929035892193/25000000000000 : ℝ), (433970528237/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069178053/2000000000 : ℝ)|^4967 ≤ (454345932113/1000000000000 : ℝ)^3943
        have hw : |(1069178053/2000000000 : ℝ)|=(1069178053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592372243/5000000000 : ℝ)|^4967 ≤ (10929035892193/25000000000000 : ℝ)^3943
        have hw : |(2592372243/5000000000 : ℝ)|=(2592372243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1714994643/10000000000 : ℝ)|^4967 ≤ (433970528237/4000000000000 : ℝ)^3943
        have hw : |(-1714994643/10000000000 : ℝ)|=(1714994643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s4_3 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166865637/400000000 : ℝ)*x 0 + (3841232127/10000000000 : ℝ)*x 1 + (904367047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166865637/400000000 : ℝ)^4967 ≤ (33243010522289/100000000000000 : ℝ)^3943 := by
    have hnat : (166865637 : ℕ)^4967*100000000000000^3943 ≤ 33243010522289^3943*400000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166865637 400000000 33243010522289 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3841232127/10000000000 : ℝ)^4967 ≤ (3745133147519/12500000000000 : ℝ)^3943 := by
    have hnat : (3841232127 : ℕ)^4967*12500000000000^3943 ≤ 3745133147519^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3841232127 10000000000 3745133147519 12500000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904367047/2000000000 : ℝ)^4967 ≤ (2299745267327/6250000000000 : ℝ)^3943 := by
    have hnat : (904367047 : ℕ)^4967*6250000000000^3943 ≤ 2299745267327^3943*2000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904367047 2000000000 2299745267327 6250000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166865637/400000000 : ℝ), (3841232127/10000000000 : ℝ), (904367047/2000000000 : ℝ)] ![(33243010522289/100000000000000 : ℝ), (3745133147519/12500000000000 : ℝ), (2299745267327/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166865637/400000000 : ℝ)|^4967 ≤ (33243010522289/100000000000000 : ℝ)^3943
        have hw : |(166865637/400000000 : ℝ)|=(166865637/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3841232127/10000000000 : ℝ)|^4967 ≤ (3745133147519/12500000000000 : ℝ)^3943
        have hw : |(3841232127/10000000000 : ℝ)|=(3841232127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904367047/2000000000 : ℝ)|^4967 ≤ (2299745267327/6250000000000 : ℝ)^3943
        have hw : |(904367047/2000000000 : ℝ)|=(904367047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s4_4 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1581721107/10000000000 : ℝ)*x 0 + (1037342783/2000000000 : ℝ)*x 1 + (1360473319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1581721107/10000000000 : ℝ)^4967 ≤ (9798133639801/100000000000000 : ℝ)^3943 := by
    have hnat : (1581721107 : ℕ)^4967*100000000000000^3943 ≤ 9798133639801^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1581721107 10000000000 9798133639801 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037342783/2000000000 : ℝ)^4967 ≤ (218685313493/500000000000 : ℝ)^3943 := by
    have hnat : (1037342783 : ℕ)^4967*500000000000^3943 ≤ 218685313493^3943*2000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037342783 2000000000 218685313493 500000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360473319/2500000000 : ℝ)^4967 ≤ (46464803651027/100000000000000 : ℝ)^3943 := by
    have hnat : (1360473319 : ℕ)^4967*100000000000000^3943 ≤ 46464803651027^3943*2500000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360473319 2500000000 46464803651027 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1581721107/10000000000 : ℝ), (1037342783/2000000000 : ℝ), (1360473319/2500000000 : ℝ)] ![(9798133639801/100000000000000 : ℝ), (218685313493/500000000000 : ℝ), (46464803651027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1581721107/10000000000 : ℝ)|^4967 ≤ (9798133639801/100000000000000 : ℝ)^3943
        have hw : |(-1581721107/10000000000 : ℝ)|=(1581721107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037342783/2000000000 : ℝ)|^4967 ≤ (218685313493/500000000000 : ℝ)^3943
        have hw : |(1037342783/2000000000 : ℝ)|=(1037342783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360473319/2500000000 : ℝ)|^4967 ≤ (46464803651027/100000000000000 : ℝ)^3943
        have hw : |(1360473319/2500000000 : ℝ)|=(1360473319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s4_5 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211062739/400000000 : ℝ)*x 0 + (-728922969/5000000000 : ℝ)*x 1 + (2720946647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211062739/400000000 : ℝ)^4967 ≤ (44693676290997/100000000000000 : ℝ)^3943 := by
    have hnat : (211062739 : ℕ)^4967*100000000000000^3943 ≤ 44693676290997^3943*400000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211062739 400000000 44693676290997 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (728922969/5000000000 : ℝ)^4967 ≤ (8841519856851/100000000000000 : ℝ)^3943 := by
    have hnat : (728922969 : ℕ)^4967*100000000000000^3943 ≤ 8841519856851^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728922969 5000000000 8841519856851 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720946647/5000000000 : ℝ)^4967 ≤ (46464803844631/100000000000000 : ℝ)^3943 := by
    have hnat : (2720946647 : ℕ)^4967*100000000000000^3943 ≤ 46464803844631^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720946647 5000000000 46464803844631 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211062739/400000000 : ℝ), (-728922969/5000000000 : ℝ), (2720946647/5000000000 : ℝ)] ![(44693676290997/100000000000000 : ℝ), (8841519856851/100000000000000 : ℝ), (46464803844631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211062739/400000000 : ℝ)|^4967 ≤ (44693676290997/100000000000000 : ℝ)^3943
        have hw : |(211062739/400000000 : ℝ)|=(211062739/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-728922969/5000000000 : ℝ)|^4967 ≤ (8841519856851/100000000000000 : ℝ)^3943
        have hw : |(-728922969/5000000000 : ℝ)|=(728922969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720946647/5000000000 : ℝ)|^4967 ≤ (46464803844631/100000000000000 : ℝ)^3943
        have hw : |(2720946647/5000000000 : ℝ)|=(2720946647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s4_6 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329785529/625000000 : ℝ)*x 0 + (136047333/250000000 : ℝ)*x 1 + (-364461479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329785529/625000000 : ℝ)^4967 ≤ (44693676173627/100000000000000 : ℝ)^3943 := by
    have hnat : (329785529 : ℕ)^4967*100000000000000^3943 ≤ 44693676173627^3943*625000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329785529 625000000 44693676173627 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136047333/250000000 : ℝ)^4967 ≤ (46464804124281/100000000000000 : ℝ)^3943 := by
    have hnat : (136047333 : ℕ)^4967*100000000000000^3943 ≤ 46464804124281^3943*250000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136047333 250000000 46464804124281 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (364461479/2500000000 : ℝ)^4967 ≤ (1105189961097/12500000000000 : ℝ)^3943 := by
    have hnat : (364461479 : ℕ)^4967*12500000000000^3943 ≤ 1105189961097^3943*2500000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364461479 2500000000 1105189961097 12500000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329785529/625000000 : ℝ), (136047333/250000000 : ℝ), (-364461479/2500000000 : ℝ)] ![(44693676173627/100000000000000 : ℝ), (46464804124281/100000000000000 : ℝ), (1105189961097/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329785529/625000000 : ℝ)|^4967 ≤ (44693676173627/100000000000000 : ℝ)^3943
        have hw : |(329785529/625000000 : ℝ)|=(329785529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136047333/250000000 : ℝ)|^4967 ≤ (46464804124281/100000000000000 : ℝ)^3943
        have hw : |(136047333/250000000 : ℝ)|=(136047333/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-364461479/2500000000 : ℝ)|^4967 ≤ (1105189961097/12500000000000 : ℝ)^3943
        have hw : |(-364461479/2500000000 : ℝ)|=(364461479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_s4_7 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2085902647/5000000000 : ℝ)*x 0 + (4516662701/10000000000 : ℝ)*x 1 + (3846458841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085902647/5000000000 : ℝ)^4967 ≤ (6648932103699/20000000000000 : ℝ)^3943 := by
    have hnat : (2085902647 : ℕ)^4967*20000000000000^3943 ≤ 6648932103699^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085902647 5000000000 6648932103699 20000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516662701/10000000000 : ℝ)^4967 ≤ (36742910202203/100000000000000 : ℝ)^3943 := by
    have hnat : (4516662701 : ℕ)^4967*100000000000000^3943 ≤ 36742910202203^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516662701 10000000000 36742910202203 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3846458841/10000000000 : ℝ)^4967 ≤ (30012429260603/100000000000000 : ℝ)^3943 := by
    have hnat : (3846458841 : ℕ)^4967*100000000000000^3943 ≤ 30012429260603^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3846458841 10000000000 30012429260603 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2085902647/5000000000 : ℝ), (4516662701/10000000000 : ℝ), (3846458841/10000000000 : ℝ)] ![(6648932103699/20000000000000 : ℝ), (36742910202203/100000000000000 : ℝ), (30012429260603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2085902647/5000000000 : ℝ)|^4967 ≤ (6648932103699/20000000000000 : ℝ)^3943
        have hw : |(2085902647/5000000000 : ℝ)|=(2085902647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516662701/10000000000 : ℝ)|^4967 ≤ (36742910202203/100000000000000 : ℝ)^3943
        have hw : |(4516662701/10000000000 : ℝ)|=(4516662701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3846458841/10000000000 : ℝ)|^4967 ≤ (30012429260603/100000000000000 : ℝ)^3943
        have hw : |(3846458841/10000000000 : ℝ)|=(3846458841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1662_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181320169/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2031/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10731/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4061/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2031/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1341/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2031/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1341/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2031/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1341/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2031/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1341/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2031/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1341/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2031/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1341/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1341/12500 : ℝ) ^ (4963/1024 : ℝ) ≤ (2000944257352701/100000000000000000000 : ℝ) := by
    have hpowers : (1341/12500 : ℝ)^4963 ≤ (2000944257352701/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1341 : ℕ)^4963*100000000000000000000^1024 ≤ 2000944257352701^1024*12500^4963 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1341 12500 2000944257352701 100000000000000000000 4963 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1341/12500 : ℝ)) (X := (2000944257352701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2031/12500 : ℝ) ^ (4963/1024 : ℝ) ≤ (1496235505699831/10000000000000000000 : ℝ) := by
    have hpowers : (2031/12500 : ℝ)^4963 ≤ (1496235505699831/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2031 : ℕ)^4963*10000000000000000000^1024 ≤ 1496235505699831^1024*12500^4963 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2031 12500 1496235505699831 10000000000000000000 4963 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2031/12500 : ℝ)) (X := (1496235505699831/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002000944257352701/50000000000000000000 : ℝ) ≤ (2500020642095313/2500000000000000 : ℝ) ^ (4963/1024 : ℝ) := by
    have hpowers : (50002000944257352701/50000000000000000000 : ℝ)^1024 ≤ (2500020642095313/2500000000000000 : ℝ)^4963 := by
      have hnat : (50002000944257352701 : ℕ)^1024*2500000000000000^4963 ≤ 2500020642095313^4963*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002000944257352701 50000000000000000000 2500020642095313 2500000000000000 1024 4963 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500020642095313/2500000000000000 : ℝ)) (X := (50002000944257352701/50000000000000000000 : ℝ)) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016963299314351011/100000000000000000000 : ℝ) ≤ (10000349974799503/10000000000000000 : ℝ) ^ (4963/1024 : ℝ) := by
    have hpowers : (100016963299314351011/100000000000000000000 : ℝ)^1024 ≤ (10000349974799503/10000000000000000 : ℝ)^4963 := by
      have hnat : (100016963299314351011 : ℕ)^1024*10000000000000000^4963 ≤ 10000349974799503^4963*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016963299314351011 100000000000000000000 10000349974799503 10000000000000000 1024 4963 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000349974799503/10000000000000000 : ℝ)) (X := (100016963299314351011/100000000000000000000 : ℝ)) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001496235505699831/5000000000000000000 : ℝ) ≤ (5000308690608877/5000000000000000 : ℝ) ^ (4963/1024 : ℝ) := by
    have hpowers : (5001496235505699831/5000000000000000000 : ℝ)^1024 ≤ (5000308690608877/5000000000000000 : ℝ)^4963 := by
      have hnat : (5001496235505699831 : ℕ)^1024*5000000000000000^4963 ≤ 5000308690608877^4963*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001496235505699831 5000000000000000000 5000308690608877 5000000000000000 1024 4963 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000308690608877/5000000000000000 : ℝ)) (X := (5001496235505699831/5000000000000000000 : ℝ)) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2000944257352701/100000000000000000000 : ℝ) ≤ ((1149889964694885783/1150000000000000000 : ℝ)+2*(267406418251/552000000000000 : ℝ)*(1341/12500 : ℝ))^(4963/1024 : ℝ) := by
    rw [show (1149889964694885783/1150000000000000000 : ℝ)+2*(267406418251/552000000000000 : ℝ)*(1341/12500 : ℝ)=(2500020642095313/2500000000000000 : ℝ) by norm_num, show 1+2*(2000944257352701/100000000000000000000 : ℝ)=(50002000944257352701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1496235505699831/10000000000000000000 : ℝ)+(2000944257352701/100000000000000000000 : ℝ) ≤ ((1149889964694885783/1150000000000000000 : ℝ)+(267406418251/552000000000000 : ℝ)*((2031/12500 : ℝ)+(1341/12500 : ℝ)))^(4963/1024 : ℝ) := by
    rw [show (1149889964694885783/1150000000000000000 : ℝ)+(267406418251/552000000000000 : ℝ)*((2031/12500 : ℝ)+(1341/12500 : ℝ))=(10000349974799503/10000000000000000 : ℝ) by norm_num, show 1+(1496235505699831/10000000000000000000 : ℝ)+(2000944257352701/100000000000000000000 : ℝ)=(100016963299314351011/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1496235505699831/10000000000000000000 : ℝ) ≤ ((1149889964694885783/1150000000000000000 : ℝ)+2*(267406418251/552000000000000 : ℝ)*(2031/12500 : ℝ))^(4963/1024 : ℝ) := by
    rw [show (1149889964694885783/1150000000000000000 : ℝ)+2*(267406418251/552000000000000 : ℝ)*(2031/12500 : ℝ)=(5000308690608877/5000000000000000 : ℝ) by norm_num, show 1+2*(1496235505699831/10000000000000000000 : ℝ)=(5001496235505699831/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1149889964694885783/1150000000000000000 : ℝ)*(X 1 0+X 2 0)+(267406418251/552000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4963/1024 : ℝ)) (lo := (1341/12500 : ℝ)) (hi := (2031/12500 : ℝ)) (c := (1149889964694885783/1150000000000000000 : ℝ)) (alpha := (267406418251/552000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1149889964694885783/1150000000000000000 : ℝ)*(X 0 1+X 2 1)+(267406418251/552000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4963/1024 : ℝ)) (lo := (1341/12500 : ℝ)) (hi := (2031/12500 : ℝ)) (c := (1149889964694885783/1150000000000000000 : ℝ)) (alpha := (267406418251/552000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1149889964694885783/1150000000000000000 : ℝ)*(X 0 2+X 1 2)+(267406418251/552000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4963/1024 : ℝ)) (lo := (1341/12500 : ℝ)) (hi := (2031/12500 : ℝ)) (c := (1149889964694885783/1150000000000000000 : ℝ)) (alpha := (267406418251/552000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-395414657/2500000000 : ℝ)*X 0 0+(1088776657/2000000000 : ℝ)*X 0 1+(2592372317/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53458903/100000000 : ℝ)*X 1 0+(-428748591/2500000000 : ℝ)*X 1 1+(5184744659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069178053/2000000000 : ℝ)*X 2 0+(2592372243/5000000000 : ℝ)*X 2 1+(-1714994643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((166865637/400000000 : ℝ)*X 0 0+(3841232127/10000000000 : ℝ)*X 0 1+(904367047/2000000000 : ℝ)*X 0 2+(166865637/400000000 : ℝ)*X 1 0+(3841232127/10000000000 : ℝ)*X 1 1+(904367047/2000000000 : ℝ)*X 1 2+(166865637/400000000 : ℝ)*X 2 0+(3841232127/10000000000 : ℝ)*X 2 1+(904367047/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1581721107/10000000000 : ℝ)*X 0 0+(1037342783/2000000000 : ℝ)*X 0 1+(1360473319/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((211062739/400000000 : ℝ)*X 1 0+(-728922969/5000000000 : ℝ)*X 1 1+(2720946647/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((329785529/625000000 : ℝ)*X 2 0+(136047333/250000000 : ℝ)*X 2 1+(-364461479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2085902647/5000000000 : ℝ)*X 0 0+(4516662701/10000000000 : ℝ)*X 0 1+(3846458841/10000000000 : ℝ)*X 0 2+(2085902647/5000000000 : ℝ)*X 1 0+(4516662701/10000000000 : ℝ)*X 1 1+(3846458841/10000000000 : ℝ)*X 1 2+(2085902647/5000000000 : ℝ)*X 2 0+(4516662701/10000000000 : ℝ)*X 2 1+(3846458841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30157442365440545295963/4600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1036187927/100000000000000 : ℝ)*(base19) + (1005580413/100000000000000 : ℝ)*(base23) + (1450631/12500000000000 : ℝ)*(lower2) + (231763127/100000000000000 : ℝ)*(upper3) + (8748981/100000000000000 : ℝ)*(lower4) + (1332065496021229/50000000000000 : ℝ)*(major0) + (1332065496021229/50000000000000 : ℝ)*(major1) + (1332065496021229/50000000000000 : ℝ)*(major2) + (385895444751443/10000000000000 : ℝ)*(sp0) + (385896417689883/10000000000000 : ℝ)*(sp1) + (482370525938293/12500000000000 : ℝ)*(sp2) + (293857979633821/20000000000000 : ℝ)*(sp3) + (10765572327/100000000000000 : ℝ)*(sp4) + (3327148429/50000000000000 : ℝ)*(sp7) + (1469296552465963/100000000000000 : ℝ)*(f.failure) + (3858965213086757/100000000000000 : ℝ)*(f.sum) + (151005340248079/13800000000000000000000000000 : ℝ)*base65 + (376061854669644329/172500000000000000000000000000000 : ℝ)*base68 + (635302958297855671/172500000000000000000000000000000 : ℝ)*base69 + (918365237327855671/172500000000000000000000000000000 : ℝ)*base71 + (17396763079/13800000000000000000000000000 : ℝ)*base73 + (374306266107144329/172500000000000000000000000000000 : ℝ)*base76 + (1791734089727855671/172500000000000000000000000000000 : ℝ)*base77 + (410714763672144329/172500000000000000000000000000000 : ℝ)*base80 + (18581358408679/13800000000000000000000000000 : ℝ)*base81 + (22092253/10000000000000000000000 : ℝ)*base90 + (22092253/10000000000000000000000 : ℝ)*base92 + (22092253/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9818648430749086860433239/1150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13950159/1250000000000 : ℝ)*(base19) + (253417517/20000000000000 : ℝ)*(base23) + (171716729/50000000000000 : ℝ)*(lower1) + (17231089/10000000000000 : ℝ)*(upper3) + (71416609/100000000000000 : ℝ)*(lower4) + (182439501/100000000000000 : ℝ)*(upper5) + (54108759884963/2000000000000 : ℝ)*(major0) + (54108759884963/2000000000000 : ℝ)*(major1) + (54108759884963/2000000000000 : ℝ)*(major2) + (1819018031/100000000000000 : ℝ)*(sp2) + (1959398950383513/50000000000000 : ℝ)*(sp4) + (1959398392377153/50000000000000 : ℝ)*(sp5) + (391879481466141/10000000000000 : ℝ)*(sp6) + (746038901565371/50000000000000 : ℝ)*(sp7) + (746038901565371/50000000000000 : ℝ)*(f.failure) + (1959398950383513/50000000000000 : ℝ)*(f.sum) + (76390097681/552000000000000000000000000 : ℝ)*base65 + (35304633954949337/6900000000000000000000000000000 : ℝ)*base67 + (113178818719549337/6900000000000000000000000000000 : ℝ)*base69 + (501889323049549337/6900000000000000000000000000000 : ℝ)*base71 + (528437671357/110400000000000000000000000 : ℝ)*base73 + (491111781882349337/6900000000000000000000000000000 : ℝ)*base75 + (67423653225049337/6900000000000000000000000000000 : ℝ)*base77 + (115515467770549337/6900000000000000000000000000000 : ℝ)*base79 + (552688641541/110400000000000000000000000 : ℝ)*base81 + (65732301/5000000000000000000000 : ℝ)*base90 + (65732301/5000000000000000000000 : ℝ)*base92 + (65732301/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1662_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181320169/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2031/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10731/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4061/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1662_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1662_box_0 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-663952023/5000000000 : ℝ)*x 0 + (2702565219/5000000000 : ℝ)*x 1 + (5405128757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663952023/5000000000 : ℝ)^4967 ≤ (7860541044331/100000000000000 : ℝ)^3943 := by
    have hnat : (663952023 : ℕ)^4967*100000000000000^3943 ≤ 7860541044331^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663952023 5000000000 7860541044331 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702565219/5000000000 : ℝ)^4967 ≤ (11517434623543/25000000000000 : ℝ)^3943 := by
    have hnat : (2702565219 : ℕ)^4967*25000000000000^3943 ≤ 11517434623543^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702565219 5000000000 11517434623543 25000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405128757/10000000000 : ℝ)^4967 ≤ (1842788817821/4000000000000 : ℝ)^3943 := by
    have hnat : (5405128757 : ℕ)^4967*4000000000000^3943 ≤ 1842788817821^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405128757 10000000000 1842788817821 4000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-663952023/5000000000 : ℝ), (2702565219/5000000000 : ℝ), (5405128757/10000000000 : ℝ)] ![(7860541044331/100000000000000 : ℝ), (11517434623543/25000000000000 : ℝ), (1842788817821/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-663952023/5000000000 : ℝ)|^4967 ≤ (7860541044331/100000000000000 : ℝ)^3943
        have hw : |(-663952023/5000000000 : ℝ)|=(663952023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702565219/5000000000 : ℝ)|^4967 ≤ (11517434623543/25000000000000 : ℝ)^3943
        have hw : |(2702565219/5000000000 : ℝ)|=(2702565219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405128757/10000000000 : ℝ)|^4967 ≤ (1842788817821/4000000000000 : ℝ)^3943
        have hw : |(5405128757/10000000000 : ℝ)|=(5405128757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_1 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656358837/1250000000 : ℝ)*x 0 + (-1544762471/10000000000 : ℝ)*x 1 + (2702564871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656358837/1250000000 : ℝ)^4967 ≤ (22209828098559/50000000000000 : ℝ)^3943 := by
    have hnat : (656358837 : ℕ)^4967*50000000000000^3943 ≤ 22209828098559^3943*1250000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656358837 1250000000 22209828098559 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1544762471/10000000000 : ℝ)^4967 ≤ (9510612770421/100000000000000 : ℝ)^3943 := by
    have hnat : (1544762471 : ℕ)^4967*100000000000000^3943 ≤ 9510612770421^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1544762471 10000000000 9510612770421 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702564871/5000000000 : ℝ)^4967 ≤ (11517432755331/25000000000000 : ℝ)^3943 := by
    have hnat : (2702564871 : ℕ)^4967*25000000000000^3943 ≤ 11517432755331^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702564871 5000000000 11517432755331 25000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656358837/1250000000 : ℝ), (-1544762471/10000000000 : ℝ), (2702564871/5000000000 : ℝ)] ![(22209828098559/50000000000000 : ℝ), (9510612770421/100000000000000 : ℝ), (11517432755331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656358837/1250000000 : ℝ)|^4967 ≤ (22209828098559/50000000000000 : ℝ)^3943
        have hw : |(656358837/1250000000 : ℝ)|=(656358837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1544762471/10000000000 : ℝ)|^4967 ≤ (9510612770421/100000000000000 : ℝ)^3943
        have hw : |(-1544762471/10000000000 : ℝ)|=(1544762471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702564871/5000000000 : ℝ)|^4967 ≤ (11517432755331/25000000000000 : ℝ)^3943
        have hw : |(2702564871/5000000000 : ℝ)|=(2702564871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_2 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050174183/2000000000 : ℝ)*x 0 + (5405129039/10000000000 : ℝ)*x 1 + (-772381571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050174183/2000000000 : ℝ)^4967 ≤ (44419658530873/100000000000000 : ℝ)^3943 := by
    have hnat : (1050174183 : ℕ)^4967*100000000000000^3943 ≤ 44419658530873^3943*2000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050174183 2000000000 44419658530873 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405129039/10000000000 : ℝ)^4967 ≤ (46069723473317/100000000000000 : ℝ)^3943 := by
    have hnat : (5405129039 : ℕ)^4967*100000000000000^3943 ≤ 46069723473317^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405129039 10000000000 46069723473317 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (772381571/5000000000 : ℝ)^4967 ≤ (4755308987207/50000000000000 : ℝ)^3943 := by
    have hnat : (772381571 : ℕ)^4967*50000000000000^3943 ≤ 4755308987207^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772381571 5000000000 4755308987207 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050174183/2000000000 : ℝ), (5405129039/10000000000 : ℝ), (-772381571/5000000000 : ℝ)] ![(44419658530873/100000000000000 : ℝ), (46069723473317/100000000000000 : ℝ), (4755308987207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050174183/2000000000 : ℝ)|^4967 ≤ (44419658530873/100000000000000 : ℝ)^3943
        have hw : |(1050174183/2000000000 : ℝ)|=(1050174183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405129039/10000000000 : ℝ)|^4967 ≤ (46069723473317/100000000000000 : ℝ)^3943
        have hw : |(5405129039/10000000000 : ℝ)|=(5405129039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-772381571/5000000000 : ℝ)|^4967 ≤ (4755308987207/50000000000000 : ℝ)^3943
        have hw : |(-772381571/5000000000 : ℝ)|=(772381571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_3 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (555959207/1250000000 : ℝ)*x 0 + (2022727889/5000000000 : ℝ)*x 1 + (4045453959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (555959207/1250000000 : ℝ)^4967 ≤ (18018671887611/50000000000000 : ℝ)^3943 := by
    have hnat : (555959207 : ℕ)^4967*50000000000000^3943 ≤ 18018671887611^3943*1250000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555959207 1250000000 18018671887611 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2022727889/5000000000 : ℝ)^4967 ≤ (7995334290639/25000000000000 : ℝ)^3943 := by
    have hnat : (2022727889 : ℕ)^4967*25000000000000^3943 ≤ 7995334290639^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022727889 5000000000 7995334290639 25000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4045453959/10000000000 : ℝ)^4967 ≤ (31981319047937/100000000000000 : ℝ)^3943 := by
    have hnat : (4045453959 : ℕ)^4967*100000000000000^3943 ≤ 31981319047937^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4045453959 10000000000 31981319047937 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(555959207/1250000000 : ℝ), (2022727889/5000000000 : ℝ), (4045453959/10000000000 : ℝ)] ![(18018671887611/50000000000000 : ℝ), (7995334290639/25000000000000 : ℝ), (31981319047937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(555959207/1250000000 : ℝ)|^4967 ≤ (18018671887611/50000000000000 : ℝ)^3943
        have hw : |(555959207/1250000000 : ℝ)|=(555959207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2022727889/5000000000 : ℝ)|^4967 ≤ (7995334290639/25000000000000 : ℝ)^3943
        have hw : |(2022727889/5000000000 : ℝ)|=(2022727889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4045453959/10000000000 : ℝ)|^4967 ≤ (31981319047937/100000000000000 : ℝ)^3943
        have hw : |(4045453959/10000000000 : ℝ)|=(4045453959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_4 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1845970393/10000000000 : ℝ)*x 0 + (5216003243/10000000000 : ℝ)*x 1 + (5216002947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1845970393/10000000000 : ℝ)^4967 ≤ (119031732353/1000000000000 : ℝ)^3943 := by
    have hnat : (1845970393 : ℕ)^4967*1000000000000^3943 ≤ 119031732353^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845970393 10000000000 119031732353 1000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216003243/10000000000 : ℝ)^4967 ≤ (68825648351/156250000000 : ℝ)^3943 := by
    have hnat : (5216003243 : ℕ)^4967*156250000000^3943 ≤ 68825648351^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216003243 10000000000 68825648351 156250000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216002947/10000000000 : ℝ)^4967 ≤ (44048411795793/100000000000000 : ℝ)^3943 := by
    have hnat : (5216002947 : ℕ)^4967*100000000000000^3943 ≤ 44048411795793^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216002947 10000000000 44048411795793 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1845970393/10000000000 : ℝ), (5216003243/10000000000 : ℝ), (5216002947/10000000000 : ℝ)] ![(119031732353/1000000000000 : ℝ), (68825648351/156250000000 : ℝ), (44048411795793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1845970393/10000000000 : ℝ)|^4967 ≤ (119031732353/1000000000000 : ℝ)^3943
        have hw : |(-1845970393/10000000000 : ℝ)|=(1845970393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216003243/10000000000 : ℝ)|^4967 ≤ (68825648351/156250000000 : ℝ)^3943
        have hw : |(5216003243/10000000000 : ℝ)|=(5216003243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216002947/10000000000 : ℝ)|^4967 ≤ (44048411795793/100000000000000 : ℝ)^3943
        have hw : |(5216002947/10000000000 : ℝ)|=(5216002947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_5 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380475723/10000000000 : ℝ)*x 0 + (-813095329/5000000000 : ℝ)*x 1 + (1043200659/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380475723/10000000000 : ℝ)^4967 ≤ (366441451543/800000000000 : ℝ)^3943 := by
    have hnat : (5380475723 : ℕ)^4967*800000000000^3943 ≤ 366441451543^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380475723 10000000000 366441451543 800000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (813095329/5000000000 : ℝ)^4967 ≤ (10146403057383/100000000000000 : ℝ)^3943 := by
    have hnat : (813095329 : ℕ)^4967*100000000000000^3943 ≤ 10146403057383^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813095329 5000000000 10146403057383 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043200659/2000000000 : ℝ)^4967 ≤ (5506051937227/12500000000000 : ℝ)^3943 := by
    have hnat : (1043200659 : ℕ)^4967*12500000000000^3943 ≤ 5506051937227^3943*2000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043200659 2000000000 5506051937227 12500000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380475723/10000000000 : ℝ), (-813095329/5000000000 : ℝ), (1043200659/2000000000 : ℝ)] ![(366441451543/800000000000 : ℝ), (10146403057383/100000000000000 : ℝ), (5506051937227/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380475723/10000000000 : ℝ)|^4967 ≤ (366441451543/800000000000 : ℝ)^3943
        have hw : |(5380475723/10000000000 : ℝ)|=(5380475723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-813095329/5000000000 : ℝ)|^4967 ≤ (10146403057383/100000000000000 : ℝ)^3943
        have hw : |(-813095329/5000000000 : ℝ)|=(813095329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043200659/2000000000 : ℝ)|^4967 ≤ (5506051937227/12500000000000 : ℝ)^3943
        have hw : |(1043200659/2000000000 : ℝ)|=(1043200659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_6 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380476151/10000000000 : ℝ)*x 0 + (521600281/1000000000 : ℝ)*x 1 + (-1626190729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380476151/10000000000 : ℝ)^4967 ≤ (22902593016397/50000000000000 : ℝ)^3943 := by
    have hnat : (5380476151 : ℕ)^4967*50000000000000^3943 ≤ 22902593016397^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380476151 10000000000 22902593016397 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521600281/1000000000 : ℝ)^4967 ≤ (11012102584597/25000000000000 : ℝ)^3943 := by
    have hnat : (521600281 : ℕ)^4967*25000000000000^3943 ≤ 11012102584597^3943*1000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521600281 1000000000 11012102584597 25000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1626190729/10000000000 : ℝ)^4967 ≤ (158537556491/1562500000000 : ℝ)^3943 := by
    have hnat : (1626190729 : ℕ)^4967*1562500000000^3943 ≤ 158537556491^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1626190729 10000000000 158537556491 1562500000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380476151/10000000000 : ℝ), (521600281/1000000000 : ℝ), (-1626190729/10000000000 : ℝ)] ![(22902593016397/50000000000000 : ℝ), (11012102584597/25000000000000 : ℝ), (158537556491/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380476151/10000000000 : ℝ)|^4967 ≤ (22902593016397/50000000000000 : ℝ)^3943
        have hw : |(5380476151/10000000000 : ℝ)|=(5380476151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521600281/1000000000 : ℝ)|^4967 ≤ (11012102584597/25000000000000 : ℝ)^3943
        have hw : |(521600281/1000000000 : ℝ)|=(521600281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1626190729/10000000000 : ℝ)|^4967 ≤ (158537556491/1562500000000 : ℝ)^3943
        have hw : |(-1626190729/10000000000 : ℝ)|=(1626190729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_7 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (97222769/250000000 : ℝ)*x 0 + (4324516203/10000000000 : ℝ)*x 1 + (864903239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97222769/250000000 : ℝ)^4967 ≤ (1521514185507/5000000000000 : ℝ)^3943 := by
    have hnat : (97222769 : ℕ)^4967*5000000000000^3943 ≤ 1521514185507^3943*250000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97222769 250000000 1521514185507 5000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4324516203/10000000000 : ℝ)^4967 ≤ (4348107272797/12500000000000 : ℝ)^3943 := by
    have hnat : (4324516203 : ℕ)^4967*12500000000000^3943 ≤ 4348107272797^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324516203 10000000000 4348107272797 12500000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864903239/2000000000 : ℝ)^4967 ≤ (6956971620263/20000000000000 : ℝ)^3943 := by
    have hnat : (864903239 : ℕ)^4967*20000000000000^3943 ≤ 6956971620263^3943*2000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864903239 2000000000 6956971620263 20000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(97222769/250000000 : ℝ), (4324516203/10000000000 : ℝ), (864903239/2000000000 : ℝ)] ![(1521514185507/5000000000000 : ℝ), (4348107272797/12500000000000 : ℝ), (6956971620263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(97222769/250000000 : ℝ)|^4967 ≤ (1521514185507/5000000000000 : ℝ)^3943
        have hw : |(97222769/250000000 : ℝ)|=(97222769/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4324516203/10000000000 : ℝ)|^4967 ≤ (4348107272797/12500000000000 : ℝ)^3943
        have hw : |(4324516203/10000000000 : ℝ)|=(4324516203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(864903239/2000000000 : ℝ)|^4967 ≤ (6956971620263/20000000000000 : ℝ)^3943
        have hw : |(864903239/2000000000 : ℝ)|=(864903239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_8 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1735371109/10000000000 : ℝ)*x 0 + (5079710673/10000000000 : ℝ)*x 1 + (5434436999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1735371109/10000000000 : ℝ)^4967 ≤ (1376486679949/12500000000000 : ℝ)^3943 := by
    have hnat : (1735371109 : ℕ)^4967*12500000000000^3943 ≤ 1376486679949^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735371109 10000000000 1376486679949 12500000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5079710673/10000000000 : ℝ)^4967 ≤ (8520697322071/20000000000000 : ℝ)^3943 := by
    have hnat : (5079710673 : ℕ)^4967*20000000000000^3943 ≤ 8520697322071^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079710673 10000000000 8520697322071 20000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434436999/10000000000 : ℝ)^4967 ≤ (46384619930897/100000000000000 : ℝ)^3943 := by
    have hnat : (5434436999 : ℕ)^4967*100000000000000^3943 ≤ 46384619930897^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434436999 10000000000 46384619930897 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1735371109/10000000000 : ℝ), (5079710673/10000000000 : ℝ), (5434436999/10000000000 : ℝ)] ![(1376486679949/12500000000000 : ℝ), (8520697322071/20000000000000 : ℝ), (46384619930897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1735371109/10000000000 : ℝ)|^4967 ≤ (1376486679949/12500000000000 : ℝ)^3943
        have hw : |(-1735371109/10000000000 : ℝ)|=(1735371109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5079710673/10000000000 : ℝ)|^4967 ≤ (8520697322071/20000000000000 : ℝ)^3943
        have hw : |(5079710673/10000000000 : ℝ)|=(5079710673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434436999/10000000000 : ℝ)|^4967 ≤ (46384619930897/100000000000000 : ℝ)^3943
        have hw : |(5434436999/10000000000 : ℝ)|=(5434436999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_9 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209231571/400000000 : ℝ)*x 0 + (-191465579/1250000000 : ℝ)*x 1 + (2717218763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209231571/400000000 : ℝ)^4967 ≤ (22102883274733/50000000000000 : ℝ)^3943 := by
    have hnat : (209231571 : ℕ)^4967*50000000000000^3943 ≤ 22102883274733^3943*400000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209231571 400000000 22102883274733 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191465579/1250000000 : ℝ)^4967 ≤ (235240196033/2500000000000 : ℝ)^3943 := by
    have hnat : (191465579 : ℕ)^4967*2500000000000^3943 ≤ 235240196033^3943*1250000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191465579 1250000000 235240196033 2500000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717218763/5000000000 : ℝ)^4967 ≤ (4638462559717/10000000000000 : ℝ)^3943 := by
    have hnat : (2717218763 : ℕ)^4967*10000000000000^3943 ≤ 4638462559717^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717218763 5000000000 4638462559717 10000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209231571/400000000 : ℝ), (-191465579/1250000000 : ℝ), (2717218763/5000000000 : ℝ)] ![(22102883274733/50000000000000 : ℝ), (235240196033/2500000000000 : ℝ), (4638462559717/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209231571/400000000 : ℝ)|^4967 ≤ (22102883274733/50000000000000 : ℝ)^3943
        have hw : |(209231571/400000000 : ℝ)|=(209231571/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-191465579/1250000000 : ℝ)|^4967 ≤ (235240196033/2500000000000 : ℝ)^3943
        have hw : |(-191465579/1250000000 : ℝ)|=(191465579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717218763/5000000000 : ℝ)|^4967 ≤ (4638462559717/10000000000000 : ℝ)^3943
        have hw : |(2717218763/5000000000 : ℝ)|=(2717218763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_10 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230791337/10000000000 : ℝ)*x 0 + (169826113/312500000 : ℝ)*x 1 + (-1531724449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230791337/10000000000 : ℝ)^4967 ≤ (22102894250573/50000000000000 : ℝ)^3943 := by
    have hnat : (5230791337 : ℕ)^4967*50000000000000^3943 ≤ 22102894250573^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230791337 10000000000 22102894250573 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169826113/312500000 : ℝ)^4967 ≤ (9276921012193/20000000000000 : ℝ)^3943 := by
    have hnat : (169826113 : ℕ)^4967*20000000000000^3943 ≤ 9276921012193^3943*312500000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169826113 312500000 9276921012193 20000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1531724449/10000000000 : ℝ)^4967 ≤ (940960642517/10000000000000 : ℝ)^3943 := by
    have hnat : (1531724449 : ℕ)^4967*10000000000000^3943 ≤ 940960642517^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531724449 10000000000 940960642517 10000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230791337/10000000000 : ℝ), (169826113/312500000 : ℝ), (-1531724449/10000000000 : ℝ)] ![(22102894250573/50000000000000 : ℝ), (9276921012193/20000000000000 : ℝ), (940960642517/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230791337/10000000000 : ℝ)|^4967 ≤ (22102894250573/50000000000000 : ℝ)^3943
        have hw : |(5230791337/10000000000 : ℝ)|=(5230791337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169826113/312500000 : ℝ)|^4967 ≤ (9276921012193/20000000000000 : ℝ)^3943
        have hw : |(169826113/312500000 : ℝ)|=(169826113/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1531724449/10000000000 : ℝ)|^4967 ≤ (940960642517/10000000000000 : ℝ)^3943
        have hw : |(-1531724449/10000000000 : ℝ)|=(1531724449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_11 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4531889929/10000000000 : ℝ)*x 0 + (1000532951/2500000000 : ℝ)*x 1 + (400213079/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4531889929/10000000000 : ℝ)^4967 ≤ (4612377674619/12500000000000 : ℝ)^3943 := by
    have hnat : (4531889929 : ℕ)^4967*12500000000000^3943 ≤ 4612377674619^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531889929 10000000000 4612377674619 12500000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000532951/2500000000 : ℝ)^4967 ≤ (31550494331623/100000000000000 : ℝ)^3943 := by
    have hnat : (1000532951 : ℕ)^4967*100000000000000^3943 ≤ 31550494331623^3943*2500000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000532951 2500000000 31550494331623 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400213079/1000000000 : ℝ)^4967 ≤ (394381053273/1250000000000 : ℝ)^3943 := by
    have hnat : (400213079 : ℕ)^4967*1250000000000^3943 ≤ 394381053273^3943*1000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400213079 1000000000 394381053273 1250000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4531889929/10000000000 : ℝ), (1000532951/2500000000 : ℝ), (400213079/1000000000 : ℝ)] ![(4612377674619/12500000000000 : ℝ), (31550494331623/100000000000000 : ℝ), (394381053273/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4531889929/10000000000 : ℝ)|^4967 ≤ (4612377674619/12500000000000 : ℝ)^3943
        have hw : |(4531889929/10000000000 : ℝ)|=(4531889929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000532951/2500000000 : ℝ)|^4967 ≤ (31550494331623/100000000000000 : ℝ)^3943
        have hw : |(1000532951/2500000000 : ℝ)|=(1000532951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(400213079/1000000000 : ℝ)|^4967 ≤ (394381053273/1250000000000 : ℝ)^3943
        have hw : |(400213079/1000000000 : ℝ)|=(400213079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_12 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-179574749/1250000000 : ℝ)*x 0 + (2768150269/5000000000 : ℝ)*x 1 + (1039242747/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179574749/1250000000 : ℝ)^4967 ≤ (4339748936263/50000000000000 : ℝ)^3943 := by
    have hnat : (179574749 : ℕ)^4967*50000000000000^3943 ≤ 4339748936263^3943*1250000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179574749 1250000000 4339748936263 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2768150269/5000000000 : ℝ)^4967 ≤ (2967656503573/6250000000000 : ℝ)^3943 := by
    have hnat : (2768150269 : ℕ)^4967*6250000000000^3943 ≤ 2967656503573^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768150269 5000000000 2967656503573 6250000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039242747/2000000000 : ℝ)^4967 ≤ (43837998051957/100000000000000 : ℝ)^3943 := by
    have hnat : (1039242747 : ℕ)^4967*100000000000000^3943 ≤ 43837998051957^3943*2000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039242747 2000000000 43837998051957 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-179574749/1250000000 : ℝ), (2768150269/5000000000 : ℝ), (1039242747/2000000000 : ℝ)] ![(4339748936263/50000000000000 : ℝ), (2967656503573/6250000000000 : ℝ), (43837998051957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-179574749/1250000000 : ℝ)|^4967 ≤ (4339748936263/50000000000000 : ℝ)^3943
        have hw : |(-179574749/1250000000 : ℝ)|=(179574749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2768150269/5000000000 : ℝ)|^4967 ≤ (2967656503573/6250000000000 : ℝ)^3943
        have hw : |(2768150269/5000000000 : ℝ)|=(2768150269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039242747/2000000000 : ℝ)|^4967 ≤ (43837998051957/100000000000000 : ℝ)^3943
        have hw : |(1039242747/2000000000 : ℝ)|=(1039242747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_13 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348512043/2500000000 : ℝ)*x 0 + (-408608257/2500000000 : ℝ)*x 1 + (5196212971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348512043/2500000000 : ℝ)^4967 ≤ (11487695385901/25000000000000 : ℝ)^3943 := by
    have hnat : (1348512043 : ℕ)^4967*25000000000000^3943 ≤ 11487695385901^3943*2500000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348512043 2500000000 11487695385901 25000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408608257/2500000000 : ℝ)^4967 ≤ (638201781497/6250000000000 : ℝ)^3943 := by
    have hnat : (408608257 : ℕ)^4967*6250000000000^3943 ≤ 638201781497^3943*2500000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408608257 2500000000 638201781497 6250000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196212971/10000000000 : ℝ)^4967 ≤ (43837989932547/100000000000000 : ℝ)^3943 := by
    have hnat : (5196212971 : ℕ)^4967*100000000000000^3943 ≤ 43837989932547^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196212971 10000000000 43837989932547 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348512043/2500000000 : ℝ), (-408608257/2500000000 : ℝ), (5196212971/10000000000 : ℝ)] ![(11487695385901/25000000000000 : ℝ), (638201781497/6250000000000 : ℝ), (43837989932547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348512043/2500000000 : ℝ)|^4967 ≤ (11487695385901/25000000000000 : ℝ)^3943
        have hw : |(1348512043/2500000000 : ℝ)|=(1348512043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408608257/2500000000 : ℝ)|^4967 ≤ (638201781497/6250000000000 : ℝ)^3943
        have hw : |(-408608257/2500000000 : ℝ)|=(408608257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196212971/10000000000 : ℝ)|^4967 ≤ (43837989932547/100000000000000 : ℝ)^3943
        have hw : |(5196212971/10000000000 : ℝ)|=(5196212971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_14 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697024071/5000000000 : ℝ)*x 0 + (5196212583/10000000000 : ℝ)*x 1 + (-817216797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697024071/5000000000 : ℝ)^4967 ≤ (4595078122167/10000000000000 : ℝ)^3943 := by
    have hnat : (2697024071 : ℕ)^4967*10000000000000^3943 ≤ 4595078122167^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697024071 5000000000 4595078122167 10000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196212583/10000000000 : ℝ)^4967 ≤ (21918992904539/50000000000000 : ℝ)^3943 := by
    have hnat : (5196212583 : ℕ)^4967*50000000000000^3943 ≤ 21918992904539^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196212583 10000000000 21918992904539 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (817216797/5000000000 : ℝ)^4967 ≤ (10211232958409/100000000000000 : ℝ)^3943 := by
    have hnat : (817216797 : ℕ)^4967*100000000000000^3943 ≤ 10211232958409^3943*5000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817216797 5000000000 10211232958409 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697024071/5000000000 : ℝ), (5196212583/10000000000 : ℝ), (-817216797/5000000000 : ℝ)] ![(4595078122167/10000000000000 : ℝ), (21918992904539/50000000000000 : ℝ), (10211232958409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697024071/5000000000 : ℝ)|^4967 ≤ (4595078122167/10000000000000 : ℝ)^3943
        have hw : |(2697024071/5000000000 : ℝ)|=(2697024071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196212583/10000000000 : ℝ)|^4967 ≤ (21918992904539/50000000000000 : ℝ)^3943
        have hw : |(5196212583/10000000000 : ℝ)|=(5196212583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-817216797/5000000000 : ℝ)|^4967 ≤ (10211232958409/100000000000000 : ℝ)^3943
        have hw : |(-817216797/5000000000 : ℝ)|=(817216797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1662_box_15 (p : ℝ) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (765762529/2000000000 : ℝ)*x 0 + (544208003/1250000000 : ℝ)*x 1 + (4353663353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (765762529/2000000000 : ℝ)^4967 ≤ (29839088994813/100000000000000 : ℝ)^3943 := by
    have hnat : (765762529 : ℕ)^4967*100000000000000^3943 ≤ 29839088994813^3943*2000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765762529 2000000000 29839088994813 100000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544208003/1250000000 : ℝ)^4967 ≤ (17540229451189/50000000000000 : ℝ)^3943 := by
    have hnat : (544208003 : ℕ)^4967*50000000000000^3943 ≤ 17540229451189^3943*1250000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544208003 1250000000 17540229451189 50000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4353663353/10000000000 : ℝ)^4967 ≤ (7016090418309/20000000000000 : ℝ)^3943 := by
    have hnat : (4353663353 : ℕ)^4967*20000000000000^3943 ≤ 7016090418309^3943*10000000000^4967 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353663353 10000000000 7016090418309 20000000000000 4967 3943 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4967/1024 : ℝ)) 4967 3943 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(765762529/2000000000 : ℝ), (544208003/1250000000 : ℝ), (4353663353/10000000000 : ℝ)] ![(29839088994813/100000000000000 : ℝ), (17540229451189/50000000000000 : ℝ), (7016090418309/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(765762529/2000000000 : ℝ)|^4967 ≤ (29839088994813/100000000000000 : ℝ)^3943
        have hw : |(765762529/2000000000 : ℝ)|=(765762529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544208003/1250000000 : ℝ)|^4967 ≤ (17540229451189/50000000000000 : ℝ)^3943
        have hw : |(544208003/1250000000 : ℝ)|=(544208003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4353663353/10000000000 : ℝ)|^4967 ≤ (7016090418309/20000000000000 : ℝ)^3943
        have hw : |(4353663353/10000000000 : ℝ)|=(4353663353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1662_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181320169/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4061/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10731/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65119/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11751/20000 : ℝ) ∧ (20353/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88339/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4061/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10731/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4061/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10731/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4061/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10731/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4061/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10731/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4061/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10731/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4061/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10731/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10731/100000 : ℝ) ^ (4963/1024 : ℝ) ≤ (2003657667105249/100000000000000000000 : ℝ) := by
    have hpowers : (10731/100000 : ℝ)^4963 ≤ (2003657667105249/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10731 : ℕ)^4963*100000000000000000000^1024 ≤ 2003657667105249^1024*100000^4963 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10731 100000 2003657667105249 100000000000000000000 4963 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10731/100000 : ℝ)) (X := (2003657667105249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4061/25000 : ℝ) ^ (4963/1024 : ℝ) ≤ (14944510789763581/100000000000000000000 : ℝ) := by
    have hpowers : (4061/25000 : ℝ)^4963 ≤ (14944510789763581/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4061 : ℕ)^4963*100000000000000000000^1024 ≤ 14944510789763581^1024*25000^4963 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4061 25000 14944510789763581 100000000000000000000 4963 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4061/25000 : ℝ)) (X := (14944510789763581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002003657667105249/50000000000000000000 : ℝ) ≤ (10000082680347533/10000000000000000 : ℝ) ^ (4963/1024 : ℝ) := by
    have hpowers : (50002003657667105249/50000000000000000000 : ℝ)^1024 ≤ (10000082680347533/10000000000000000 : ℝ)^4963 := by
      have hnat : (50002003657667105249 : ℕ)^1024*10000000000000000^4963 ≤ 10000082680347533^4963*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002003657667105249 50000000000000000000 10000082680347533 10000000000000000 1024 4963 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000082680347533/10000000000000000 : ℝ)) (X := (50002003657667105249/50000000000000000000 : ℝ)) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10001694816845686883/10000000000000000000 : ℝ) ≤ (10000349662651341/10000000000000000 : ℝ) ^ (4963/1024 : ℝ) := by
    have hpowers : (10001694816845686883/10000000000000000000 : ℝ)^1024 ≤ (10000349662651341/10000000000000000 : ℝ)^4963 := by
      have hnat : (10001694816845686883 : ℕ)^1024*10000000000000000^4963 ≤ 10000349662651341^4963*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001694816845686883 10000000000000000000 10000349662651341 10000000000000000 1024 4963 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000349662651341/10000000000000000 : ℝ)) (X := (10001694816845686883/10000000000000000000 : ℝ)) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014944510789763581/50000000000000000000 : ℝ) ≤ (10000616644955149/10000000000000000 : ℝ) ^ (4963/1024 : ℝ) := by
    have hpowers : (50014944510789763581/50000000000000000000 : ℝ)^1024 ≤ (10000616644955149/10000000000000000 : ℝ)^4963 := by
      have hnat : (50014944510789763581 : ℕ)^1024*10000000000000000^4963 ≤ 10000616644955149^4963*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014944510789763581 50000000000000000000 10000616644955149 10000000000000000 1024 4963 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000616644955149/10000000000000000 : ℝ)) (X := (50014944510789763581/50000000000000000000 : ℝ)) (by norm_num) 4963 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2003657667105249/100000000000000000000 : ℝ) ≤ ((55124725842551622133/55130000000000000000 : ℝ)+2*(4171598497/8614062500000 : ℝ)*(10731/100000 : ℝ))^(4963/1024 : ℝ) := by
    rw [show (55124725842551622133/55130000000000000000 : ℝ)+2*(4171598497/8614062500000 : ℝ)*(10731/100000 : ℝ)=(10000082680347533/10000000000000000 : ℝ) by norm_num, show 1+2*(2003657667105249/100000000000000000000 : ℝ)=(50002003657667105249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14944510789763581/100000000000000000000 : ℝ)+(2003657667105249/100000000000000000000 : ℝ) ≤ ((55124725842551622133/55130000000000000000 : ℝ)+(4171598497/8614062500000 : ℝ)*((4061/25000 : ℝ)+(10731/100000 : ℝ)))^(4963/1024 : ℝ) := by
    rw [show (55124725842551622133/55130000000000000000 : ℝ)+(4171598497/8614062500000 : ℝ)*((4061/25000 : ℝ)+(10731/100000 : ℝ))=(10000349662651341/10000000000000000 : ℝ) by norm_num, show 1+(14944510789763581/100000000000000000000 : ℝ)+(2003657667105249/100000000000000000000 : ℝ)=(10001694816845686883/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14944510789763581/100000000000000000000 : ℝ) ≤ ((55124725842551622133/55130000000000000000 : ℝ)+2*(4171598497/8614062500000 : ℝ)*(4061/25000 : ℝ))^(4963/1024 : ℝ) := by
    rw [show (55124725842551622133/55130000000000000000 : ℝ)+2*(4171598497/8614062500000 : ℝ)*(4061/25000 : ℝ)=(10000616644955149/10000000000000000 : ℝ) by norm_num, show 1+2*(14944510789763581/100000000000000000000 : ℝ)=(50014944510789763581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55124725842551622133/55130000000000000000 : ℝ)*(X 1 0+X 2 0)+(4171598497/8614062500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4963/1024 : ℝ)) (lo := (10731/100000 : ℝ)) (hi := (4061/25000 : ℝ)) (c := (55124725842551622133/55130000000000000000 : ℝ)) (alpha := (4171598497/8614062500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55124725842551622133/55130000000000000000 : ℝ)*(X 0 1+X 2 1)+(4171598497/8614062500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4963/1024 : ℝ)) (lo := (10731/100000 : ℝ)) (hi := (4061/25000 : ℝ)) (c := (55124725842551622133/55130000000000000000 : ℝ)) (alpha := (4171598497/8614062500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55124725842551622133/55130000000000000000 : ℝ)*(X 0 2+X 1 2)+(4171598497/8614062500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4963/1024 : ℝ)) (lo := (10731/100000 : ℝ)) (hi := (4061/25000 : ℝ)) (c := (55124725842551622133/55130000000000000000 : ℝ)) (alpha := (4171598497/8614062500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-663952023/5000000000 : ℝ)*X 0 0+(2702565219/5000000000 : ℝ)*X 0 1+(5405128757/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((656358837/1250000000 : ℝ)*X 1 0+(-1544762471/10000000000 : ℝ)*X 1 1+(2702564871/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1050174183/2000000000 : ℝ)*X 2 0+(5405129039/10000000000 : ℝ)*X 2 1+(-772381571/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((555959207/1250000000 : ℝ)*X 0 0+(2022727889/5000000000 : ℝ)*X 0 1+(4045453959/10000000000 : ℝ)*X 0 2+(555959207/1250000000 : ℝ)*X 1 0+(2022727889/5000000000 : ℝ)*X 1 1+(4045453959/10000000000 : ℝ)*X 1 2+(555959207/1250000000 : ℝ)*X 2 0+(2022727889/5000000000 : ℝ)*X 2 1+(4045453959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1845970393/10000000000 : ℝ)*X 0 0+(5216003243/10000000000 : ℝ)*X 0 1+(5216002947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5380475723/10000000000 : ℝ)*X 1 0+(-813095329/5000000000 : ℝ)*X 1 1+(1043200659/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5380476151/10000000000 : ℝ)*X 2 0+(521600281/1000000000 : ℝ)*X 2 1+(-1626190729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((97222769/250000000 : ℝ)*X 0 0+(4324516203/10000000000 : ℝ)*X 0 1+(864903239/2000000000 : ℝ)*X 0 2+(97222769/250000000 : ℝ)*X 1 0+(4324516203/10000000000 : ℝ)*X 1 1+(864903239/2000000000 : ℝ)*X 1 2+(97222769/250000000 : ℝ)*X 2 0+(4324516203/10000000000 : ℝ)*X 2 1+(864903239/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1735371109/10000000000 : ℝ)*X 0 0+(5079710673/10000000000 : ℝ)*X 0 1+(5434436999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((209231571/400000000 : ℝ)*X 1 0+(-191465579/1250000000 : ℝ)*X 1 1+(2717218763/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230791337/10000000000 : ℝ)*X 2 0+(169826113/312500000 : ℝ)*X 2 1+(-1531724449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4531889929/10000000000 : ℝ)*X 0 0+(1000532951/2500000000 : ℝ)*X 0 1+(400213079/1000000000 : ℝ)*X 0 2+(4531889929/10000000000 : ℝ)*X 1 0+(1000532951/2500000000 : ℝ)*X 1 1+(400213079/1000000000 : ℝ)*X 1 2+(4531889929/10000000000 : ℝ)*X 2 0+(1000532951/2500000000 : ℝ)*X 2 1+(400213079/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-179574749/1250000000 : ℝ)*X 0 0+(2768150269/5000000000 : ℝ)*X 0 1+(1039242747/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1348512043/2500000000 : ℝ)*X 1 0+(-408608257/2500000000 : ℝ)*X 1 1+(5196212971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2697024071/5000000000 : ℝ)*X 2 0+(5196212583/10000000000 : ℝ)*X 2 1+(-817216797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((765762529/2000000000 : ℝ)*X 0 0+(544208003/1250000000 : ℝ)*X 0 1+(4353663353/10000000000 : ℝ)*X 0 2+(765762529/2000000000 : ℝ)*X 1 0+(544208003/1250000000 : ℝ)*X 1 1+(4353663353/10000000000 : ℝ)*X 1 2+(765762529/2000000000 : ℝ)*X 2 0+(544208003/1250000000 : ℝ)*X 2 1+(4353663353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1662_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65119/100000 : ℝ) ≤ (-1794938303150056979140680860848713/2756500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1688731/100000000000000 : ℝ)*(lower2) + (15309949/50000000000000 : ℝ)*(upper4) + (1885041/6250000000000 : ℝ)*(upper5) + (1781684755928087/100000000000000 : ℝ)*(major0) + (1781684755928087/100000000000000 : ℝ)*(major1) + (1781684755928087/100000000000000 : ℝ)*(major2) + (2577542321/50000000000000 : ℝ)*(sp2) + (194868573/25000000000000 : ℝ)*(sp3) + (2602453632397793/100000000000000 : ℝ)*(sp4) + (130122396197979/5000000000000 : ℝ)*(sp5) + (16265323779861/625000000000 : ℝ)*(sp6) + (982617296470743/100000000000000 : ℝ)*(sp7) + (3327464609/100000000000000 : ℝ)*(sp8) + (4517951411/50000000000000 : ℝ)*(sp13) + (245654518986259/25000000000000 : ℝ)*(f.failure) + (1301228479931201/50000000000000 : ℝ)*(f.sum) + (21938048128583/13782500000000000000000000000 : ℝ)*base65 + (5316308063517850429/5513000000000000000000000000000000 : ℝ)*base68 + (21881268602200149571/5513000000000000000000000000000000 : ℝ)*base69 + (11863223774152850429/5513000000000000000000000000000000 : ℝ)*base72 + (6068572200111/27565000000000000000000000000 : ℝ)*base73 + (21210028325500149571/5513000000000000000000000000000000 : ℝ)*base75 + (4818168933789149571/5513000000000000000000000000000000 : ℝ)*base77 + (5480846854416149571/5513000000000000000000000000000000 : ℝ)*base79 + (85013261331711/27565000000000000000000000000 : ℝ)*base81 + (15557771/2500000000000000000000 : ℝ)*base89 + (15557771/2500000000000000000000 : ℝ)*base91 + (15557771/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (11751/20000 : ℝ) ≤ (101228031571732191104644548126537/172281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138839137/50000000000000 : ℝ)*(upper3) + (24807989/100000000000000 : ℝ)*(upper4) + (68891089/100000000000000 : ℝ)*(lower5) + (117111665599029/6250000000000 : ℝ)*(major0) + (117111665599029/6250000000000 : ℝ)*(major1) + (117111665599029/6250000000000 : ℝ)*(major2) + (336820913606863/12500000000000 : ℝ)*(sp0) + (2105127441119/78125000000 : ℝ)*(sp1) + (269454608979439/10000000000000 : ℝ)*(sp2) + (3229327645513/312500000000 : ℝ)*(sp3) + (693193639/10000000000000 : ℝ)*(sp8) + (11116158973/100000000000000 : ℝ)*(sp9) + (3518874613/12500000000000 : ℝ)*(sp10) + (1775153249/6250000000000 : ℝ)*(sp11) + (64588328063509/6250000000000 : ℝ)*(f.failure) + (1347287120395647/50000000000000 : ℝ)*(f.sum) + (24406640341891/13782500000000000000000000000 : ℝ)*base65 + (16351844124533857/344562500000000000000000000000000 : ℝ)*base67 + (2056612979805783857/344562500000000000000000000000000 : ℝ)*base69 + (1598626481931471357/344562500000000000000000000000000 : ℝ)*base71 + (4325800251061/3445625000000000000000000000 : ℝ)*base74 + (2532827883812033857/344562500000000000000000000000000 : ℝ)*base75 + (181689623610283857/344562500000000000000000000000000 : ℝ)*base77 + (1203174754157283857/344562500000000000000000000000000 : ℝ)*base79 + (45206360447463/6891250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5386979/625000000000000000000 : ℝ)*base90 + (5386979/625000000000000000000 : ℝ)*base92 + (5386979/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (20353/25000 : ℝ) ≤ (30326930642869459997219760525657/37250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (584083/25000000000000 : ℝ)*(lower2) + (266671737/100000000000000 : ℝ)*(lower3) + (10306323/3125000000000 : ℝ)*(upper4) + (163212827/100000000000000 : ℝ)*(lower5) + (982478973843091/50000000000000 : ℝ)*(major0) + (982478973843091/50000000000000 : ℝ)*(major1) + (982478973843091/50000000000000 : ℝ)*(major2) + (14168160449/10000000000000 : ℝ)*(sp1) + (8805127377/50000000000000 : ℝ)*(sp2) + (53810434407/100000000000000 : ℝ)*(sp3) + (704770628413363/25000000000000 : ℝ)*(sp8) + (1409470416024481/50000000000000 : ℝ)*(sp9) + (2819064903398697/100000000000000 : ℝ)*(sp10) + (108364137831549/10000000000000 : ℝ)*(sp11) + (1083695188749897/100000000000000 : ℝ)*(f.failure) + (704770628413363/25000000000000 : ℝ)*(f.sum) + (377955084329/372500000000000000000000000 : ℝ)*base65 + (256308772097174781/74500000000000000000000000000000 : ℝ)*base68 + (724502841942674781/74500000000000000000000000000000 : ℝ)*base70 + (211496946852174781/74500000000000000000000000000000 : ℝ)*base72 + (37289001853/46562500000000000000000000 : ℝ)*base73 + (242414760720674781/74500000000000000000000000000000 : ℝ)*base76 + (225351667577325219/74500000000000000000000000000000 : ℝ)*base77 + (107973836033825219/74500000000000000000000000000000 : ℝ)*base79 + (479638071569/93125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (22772593/10000000000000000000000 : ℝ)*base89 + (22772593/10000000000000000000000 : ℝ)*base91 + (22772593/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-88339/100000 : ℝ) ≤ (-608748918245396058116625614161131/689125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (275512277/100000000000000 : ℝ)*(upper3) + (63852049/100000000000000 : ℝ)*(lower4) + (68162221/100000000000000 : ℝ)*(upper5) + (502419428576823/25000000000000 : ℝ)*(major0) + (502419428576823/25000000000000 : ℝ)*(major1) + (502419428576823/25000000000000 : ℝ)*(major2) + (1144051373/10000000000000 : ℝ)*(sp4) + (52834096589/20000000000000 : ℝ)*(sp5) + (76181667559/25000000000000 : ℝ)*(sp6) + (51641384609/50000000000000 : ℝ)*(sp7) + (183776929590989/6250000000000 : ℝ)*(sp12) + (183761133967913/6250000000000 : ℝ)*(sp13) + (1470068793649659/50000000000000 : ℝ)*(sp14) + (1108255332486259/100000000000000 : ℝ)*(sp15) + (554179307627739/50000000000000 : ℝ)*(f.failure) + (1470221156984777/50000000000000 : ℝ)*(f.sum) + (124075775337031/27565000000000000000000000000 : ℝ)*base65 + (1425207315147023459/1378250000000000000000000000000000 : ℝ)*base67 + (7972016493948273459/1378250000000000000000000000000000 : ℝ)*base69 + (13139077592181523459/1378250000000000000000000000000000 : ℝ)*base71 + (6602038295851/6891250000000000000000000000 : ℝ)*base74 + (16162692732196023459/1378250000000000000000000000000000 : ℝ)*base75 + (3286817370368273459/1378250000000000000000000000000000 : ℝ)*base77 + (9003071347628023459/1378250000000000000000000000000000 : ℝ)*base79 + (99237186375371/27565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (24567891/5000000000000000000000 : ℝ)*base89 + (24567891/5000000000000000000000 : ℝ)*base91 + (24567891/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1662_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181320169/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4061/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10731/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65119/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11751/20000 : ℝ) else (20353/25000 : ℝ) ≤ X j i ∧ X j i ≤ (88339/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1662_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1662_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181320169/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16307/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5337/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65119/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11751/20000 : ℝ) else (20353/25000 : ℝ) ≤ X j i ∧ X j i ≤ (88339/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1662_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1662_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1662_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4963/1024 : ℝ) ≤ p) (hpb : p ≤ (4967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181320169/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16307/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5337/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65119/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11751/20000 : ℝ) else (20353/25000 : ℝ) ≤ X j i ∧ X j i ≤ (88339/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1662_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
