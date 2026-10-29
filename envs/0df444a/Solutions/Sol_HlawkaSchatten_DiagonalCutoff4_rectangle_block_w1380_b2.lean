-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1380_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:23:27.215388+00:00
-- url     : https://prove2.me/submissions/04854d49-939b-43bf-8323-bf17955ef040

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
theorem support_rectangle_w1380_s6_0 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2011590201/10000000000 : ℝ)*x 0 + (338172123/625000000 : ℝ)*x 1 + (65571197/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2011590201/10000000000 : ℝ)^1085 ≤ (12259379237439/100000000000000 : ℝ)^829 := by
    have hnat : (2011590201 : ℕ)^1085*100000000000000^829 ≤ 12259379237439^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011590201 10000000000 12259379237439 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338172123/625000000 : ℝ)^1085 ≤ (22379802571559/50000000000000 : ℝ)^829 := by
    have hnat : (338172123 : ℕ)^1085*50000000000000^829 ≤ 22379802571559^829*625000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338172123 625000000 22379802571559 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65571197/125000000 : ℝ)^1085 ≤ (21490507802587/50000000000000 : ℝ)^829 := by
    have hnat : (65571197 : ℕ)^1085*50000000000000^829 ≤ 21490507802587^829*125000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65571197 125000000 21490507802587 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2011590201/10000000000 : ℝ), (338172123/625000000 : ℝ), (65571197/125000000 : ℝ)] ![(12259379237439/100000000000000 : ℝ), (22379802571559/50000000000000 : ℝ), (21490507802587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2011590201/10000000000 : ℝ)|^1085 ≤ (12259379237439/100000000000000 : ℝ)^829
        have hw : |(-2011590201/10000000000 : ℝ)|=(2011590201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338172123/625000000 : ℝ)|^1085 ≤ (22379802571559/50000000000000 : ℝ)^829
        have hw : |(338172123/625000000 : ℝ)|=(338172123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65571197/125000000 : ℝ)|^1085 ≤ (21490507802587/50000000000000 : ℝ)^829
        have hw : |(65571197/125000000 : ℝ)|=(65571197/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s6_1 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348311227/10000000000 : ℝ)*x 0 + (-1047829779/5000000000 : ℝ)*x 1 + (65571197/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348311227/10000000000 : ℝ)^1085 ≤ (44084752424231/100000000000000 : ℝ)^829 := by
    have hnat : (5348311227 : ℕ)^1085*100000000000000^829 ≤ 44084752424231^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348311227 10000000000 44084752424231 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047829779/5000000000 : ℝ)^1085 ≤ (2586846390763/20000000000000 : ℝ)^829 := by
    have hnat : (1047829779 : ℕ)^1085*20000000000000^829 ≤ 2586846390763^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047829779 5000000000 2586846390763 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65571197/125000000 : ℝ)^1085 ≤ (21490507802587/50000000000000 : ℝ)^829 := by
    have hnat : (65571197 : ℕ)^1085*50000000000000^829 ≤ 21490507802587^829*125000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65571197 125000000 21490507802587 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348311227/10000000000 : ℝ), (-1047829779/5000000000 : ℝ), (65571197/125000000 : ℝ)] ![(44084752424231/100000000000000 : ℝ), (2586846390763/20000000000000 : ℝ), (21490507802587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348311227/10000000000 : ℝ)|^1085 ≤ (44084752424231/100000000000000 : ℝ)^829
        have hw : |(5348311227/10000000000 : ℝ)|=(5348311227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1047829779/5000000000 : ℝ)|^1085 ≤ (2586846390763/20000000000000 : ℝ)^829
        have hw : |(-1047829779/5000000000 : ℝ)|=(1047829779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65571197/125000000 : ℝ)|^1085 ≤ (21490507802587/50000000000000 : ℝ)^829
        have hw : |(65571197/125000000 : ℝ)|=(65571197/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s6_2 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337077807/2500000000 : ℝ)*x 0 + (65571197/125000000 : ℝ)*x 1 + (-2095659557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337077807/2500000000 : ℝ)^1085 ≤ (44084752435019/100000000000000 : ℝ)^829 := by
    have hnat : (1337077807 : ℕ)^1085*100000000000000^829 ≤ 44084752435019^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337077807 2500000000 44084752435019 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65571197/125000000 : ℝ)^1085 ≤ (21490507802587/50000000000000 : ℝ)^829 := by
    have hnat : (65571197 : ℕ)^1085*50000000000000^829 ≤ 21490507802587^829*125000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65571197 125000000 21490507802587 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2095659557/10000000000 : ℝ)^1085 ≤ (12934231945737/100000000000000 : ℝ)^829 := by
    have hnat : (2095659557 : ℕ)^1085*100000000000000^829 ≤ 12934231945737^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095659557 10000000000 12934231945737 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337077807/2500000000 : ℝ), (65571197/125000000 : ℝ), (-2095659557/10000000000 : ℝ)] ![(44084752435019/100000000000000 : ℝ), (21490507802587/50000000000000 : ℝ), (12934231945737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337077807/2500000000 : ℝ)|^1085 ≤ (44084752435019/100000000000000 : ℝ)^829
        have hw : |(1337077807/2500000000 : ℝ)|=(1337077807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65571197/125000000 : ℝ)|^1085 ≤ (21490507802587/50000000000000 : ℝ)^829
        have hw : |(65571197/125000000 : ℝ)|=(65571197/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2095659557/10000000000 : ℝ)|^1085 ≤ (12934231945737/100000000000000 : ℝ)^829
        have hw : |(-2095659557/10000000000 : ℝ)|=(2095659557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s6_3 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1079194899/2500000000 : ℝ)*x 0 + (2072357051/5000000000 : ℝ)*x 1 + (140480931/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079194899/2500000000 : ℝ)^1085 ≤ (33303902943963/100000000000000 : ℝ)^829 := by
    have hnat : (1079194899 : ℕ)^1085*100000000000000^829 ≤ 33303902943963^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079194899 2500000000 33303902943963 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072357051/5000000000 : ℝ)^1085 ≤ (31577277952261/100000000000000 : ℝ)^829 := by
    have hnat : (2072357051 : ℕ)^1085*100000000000000^829 ≤ 31577277952261^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072357051 5000000000 31577277952261 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140480931/312500000 : ℝ)^1085 ≤ (17559409543167/50000000000000 : ℝ)^829 := by
    have hnat : (140480931 : ℕ)^1085*50000000000000^829 ≤ 17559409543167^829*312500000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140480931 312500000 17559409543167 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079194899/2500000000 : ℝ), (2072357051/5000000000 : ℝ), (140480931/312500000 : ℝ)] ![(33303902943963/100000000000000 : ℝ), (31577277952261/100000000000000 : ℝ), (17559409543167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079194899/2500000000 : ℝ)|^1085 ≤ (33303902943963/100000000000000 : ℝ)^829
        have hw : |(1079194899/2500000000 : ℝ)|=(1079194899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2072357051/5000000000 : ℝ)|^1085 ≤ (31577277952261/100000000000000 : ℝ)^829
        have hw : |(2072357051/5000000000 : ℝ)|=(2072357051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140480931/312500000 : ℝ)|^1085 ≤ (17559409543167/50000000000000 : ℝ)^829
        have hw : |(140480931/312500000 : ℝ)|=(140480931/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s6_4 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2011601991/10000000000 : ℝ)*x 0 + (524628857/1000000000 : ℝ)*x 1 + (338134881/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2011601991/10000000000 : ℝ)^1085 ≤ (3064868319671/25000000000000 : ℝ)^829 := by
    have hnat : (2011601991 : ℕ)^1085*25000000000000^829 ≤ 3064868319671^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011601991 10000000000 3064868319671 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524628857/1000000000 : ℝ)^1085 ≤ (42987372893093/100000000000000 : ℝ)^829 := by
    have hnat : (524628857 : ℕ)^1085*100000000000000^829 ≤ 42987372893093^829*1000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524628857 1000000000 42987372893093 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338134881/625000000 : ℝ)^1085 ≤ (22376576906533/50000000000000 : ℝ)^829 := by
    have hnat : (338134881 : ℕ)^1085*50000000000000^829 ≤ 22376576906533^829*625000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338134881 625000000 22376576906533 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2011601991/10000000000 : ℝ), (524628857/1000000000 : ℝ), (338134881/625000000 : ℝ)] ![(3064868319671/25000000000000 : ℝ), (42987372893093/100000000000000 : ℝ), (22376576906533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2011601991/10000000000 : ℝ)|^1085 ≤ (3064868319671/25000000000000 : ℝ)^829
        have hw : |(-2011601991/10000000000 : ℝ)|=(2011601991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524628857/1000000000 : ℝ)|^1085 ≤ (42987372893093/100000000000000 : ℝ)^829
        have hw : |(524628857/1000000000 : ℝ)|=(524628857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338134881/625000000 : ℝ)|^1085 ≤ (22376576906533/50000000000000 : ℝ)^829
        have hw : |(338134881/625000000 : ℝ)|=(338134881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s6_5 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1061123139/2000000000 : ℝ)*x 0 + (-1931197239/10000000000 : ℝ)*x 1 + (1082031617/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061123139/2000000000 : ℝ)^1085 ≤ (21812357723031/50000000000000 : ℝ)^829 := by
    have hnat : (1061123139 : ℕ)^1085*50000000000000^829 ≤ 21812357723031^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061123139 2000000000 21812357723031 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1931197239/10000000000 : ℝ)^1085 ≤ (11622130847481/100000000000000 : ℝ)^829 := by
    have hnat : (1931197239 : ℕ)^1085*100000000000000^829 ≤ 11622130847481^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931197239 10000000000 11622130847481 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082031617/2000000000 : ℝ)^1085 ≤ (22376576846987/50000000000000 : ℝ)^829 := by
    have hnat : (1082031617 : ℕ)^1085*50000000000000^829 ≤ 22376576846987^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082031617 2000000000 22376576846987 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061123139/2000000000 : ℝ), (-1931197239/10000000000 : ℝ), (1082031617/2000000000 : ℝ)] ![(21812357723031/50000000000000 : ℝ), (11622130847481/100000000000000 : ℝ), (22376576846987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061123139/2000000000 : ℝ)|^1085 ≤ (21812357723031/50000000000000 : ℝ)^829
        have hw : |(1061123139/2000000000 : ℝ)|=(1061123139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1931197239/10000000000 : ℝ)|^1085 ≤ (11622130847481/100000000000000 : ℝ)^829
        have hw : |(-1931197239/10000000000 : ℝ)|=(1931197239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082031617/2000000000 : ℝ)|^1085 ≤ (22376576846987/50000000000000 : ℝ)^829
        have hw : |(1082031617/2000000000 : ℝ)|=(1082031617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s6_6 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530561571/1000000000 : ℝ)*x 0 + (676269759/1250000000 : ℝ)*x 1 + (-482799309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530561571/1000000000 : ℝ)^1085 ≤ (10906178901871/25000000000000 : ℝ)^829 := by
    have hnat : (530561571 : ℕ)^1085*25000000000000^829 ≤ 10906178901871^829*1000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530561571 1000000000 10906178901871 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676269759/1250000000 : ℝ)^1085 ≤ (4475315355323/10000000000000 : ℝ)^829 := by
    have hnat : (676269759 : ℕ)^1085*10000000000000^829 ≤ 4475315355323^829*1250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676269759 1250000000 4475315355323 10000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482799309/2500000000 : ℝ)^1085 ≤ (2905532705963/25000000000000 : ℝ)^829 := by
    have hnat : (482799309 : ℕ)^1085*25000000000000^829 ≤ 2905532705963^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482799309 2500000000 2905532705963 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530561571/1000000000 : ℝ), (676269759/1250000000 : ℝ), (-482799309/2500000000 : ℝ)] ![(10906178901871/25000000000000 : ℝ), (4475315355323/10000000000000 : ℝ), (2905532705963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530561571/1000000000 : ℝ)|^1085 ≤ (10906178901871/25000000000000 : ℝ)^829
        have hw : |(530561571/1000000000 : ℝ)|=(530561571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676269759/1250000000 : ℝ)|^1085 ≤ (4475315355323/10000000000000 : ℝ)^829
        have hw : |(676269759/1250000000 : ℝ)|=(676269759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-482799309/2500000000 : ℝ)|^1085 ≤ (2905532705963/25000000000000 : ℝ)^829
        have hw : |(-482799309/2500000000 : ℝ)|=(482799309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s6_7 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4316804661/10000000000 : ℝ)*x 0 + (112353257/250000000 : ℝ)*x 1 + (2072990053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316804661/10000000000 : ℝ)^1085 ≤ (2081509752253/6250000000000 : ℝ)^829 := by
    have hnat : (4316804661 : ℕ)^1085*6250000000000^829 ≤ 2081509752253^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316804661 10000000000 2081509752253 6250000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112353257/250000000 : ℝ)^1085 ≤ (17552970797347/50000000000000 : ℝ)^829 := by
    have hnat : (112353257 : ℕ)^1085*50000000000000^829 ≤ 17552970797347^829*250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112353257 250000000 17552970797347 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072990053/5000000000 : ℝ)^1085 ≤ (6317980471211/20000000000000 : ℝ)^829 := by
    have hnat : (2072990053 : ℕ)^1085*20000000000000^829 ≤ 6317980471211^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072990053 5000000000 6317980471211 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316804661/10000000000 : ℝ), (112353257/250000000 : ℝ), (2072990053/5000000000 : ℝ)] ![(2081509752253/6250000000000 : ℝ), (17552970797347/50000000000000 : ℝ), (6317980471211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316804661/10000000000 : ℝ)|^1085 ≤ (2081509752253/6250000000000 : ℝ)^829
        have hw : |(4316804661/10000000000 : ℝ)|=(4316804661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112353257/250000000 : ℝ)|^1085 ≤ (17552970797347/50000000000000 : ℝ)^829
        have hw : |(112353257/250000000 : ℝ)|=(112353257/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2072990053/5000000000 : ℝ)|^1085 ≤ (6317980471211/20000000000000 : ℝ)^829
        have hw : |(2072990053/5000000000 : ℝ)|=(2072990053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1380_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2247/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1473/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (921/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1123/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (921/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1123/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (921/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1123/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (921/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1123/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (921/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1123/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (921/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1123/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1123/10000 : ℝ) ^ (4339/1024 : ℝ) ≤ (9466069524468987/100000000000000000000 : ℝ) := by
    have hpowers : (1123/10000 : ℝ)^4339 ≤ (9466069524468987/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1123 : ℕ)^4339*100000000000000000000^1024 ≤ 9466069524468987^1024*10000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1123 10000 9466069524468987 100000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1123/10000 : ℝ)) (X := (9466069524468987/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (921/6250 : ℝ) ^ (4339/1024 : ℝ) ≤ (748360823113787/2500000000000000000 : ℝ) := by
    have hpowers : (921/6250 : ℝ)^4339 ≤ (748360823113787/2500000000000000000 : ℝ)^1024 := by
      have hnat : (921 : ℕ)^4339*2500000000000000000^1024 ≤ 748360823113787^1024*6250^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        921 6250 748360823113787 2500000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (921/6250 : ℝ)) (X := (748360823113787/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009466069524468987/50000000000000000000 : ℝ) ≤ (10000446764427129/10000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (50009466069524468987/50000000000000000000 : ℝ)^1024 ≤ (10000446764427129/10000000000000000 : ℝ)^4339 := by
      have hnat : (50009466069524468987 : ℕ)^1024*10000000000000000^4339 ≤ 10000446764427129^4339*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009466069524468987 50000000000000000000 10000446764427129 10000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000446764427129/10000000000000000 : ℝ)) (X := (50009466069524468987/50000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039400502449020467/100000000000000000000 : ℝ) ≤ (5000464854153221/5000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (100039400502449020467/100000000000000000000 : ℝ)^1024 ≤ (5000464854153221/5000000000000000 : ℝ)^4339 := by
      have hnat : (100039400502449020467 : ℕ)^1024*5000000000000000^4339 ≤ 5000464854153221^4339*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039400502449020467 100000000000000000000 5000464854153221 5000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000464854153221/5000000000000000 : ℝ)) (X := (100039400502449020467/100000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250748360823113787/1250000000000000000 : ℝ) ≤ (2000282530437151/2000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (1250748360823113787/1250000000000000000 : ℝ)^1024 ≤ (2000282530437151/2000000000000000 : ℝ)^4339 := by
      have hnat : (1250748360823113787 : ℕ)^1024*2000000000000000^4339 ≤ 2000282530437151^4339*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250748360823113787 1250000000000000000 2000282530437151 2000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000282530437151/2000000000000000 : ℝ)) (X := (1250748360823113787/1250000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9466069524468987/100000000000000000000 : ℝ) ≤ ((17525359718276072147/17530000000000000000 : ℝ)+2*(482943879313/350600000000000 : ℝ)*(1123/10000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (17525359718276072147/17530000000000000000 : ℝ)+2*(482943879313/350600000000000 : ℝ)*(1123/10000 : ℝ)=(10000446764427129/10000000000000000 : ℝ) by norm_num, show 1+2*(9466069524468987/100000000000000000000 : ℝ)=(50009466069524468987/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(748360823113787/2500000000000000000 : ℝ)+(9466069524468987/100000000000000000000 : ℝ) ≤ ((17525359718276072147/17530000000000000000 : ℝ)+(482943879313/350600000000000 : ℝ)*((921/6250 : ℝ)+(1123/10000 : ℝ)))^(4339/1024 : ℝ) := by
    rw [show (17525359718276072147/17530000000000000000 : ℝ)+(482943879313/350600000000000 : ℝ)*((921/6250 : ℝ)+(1123/10000 : ℝ))=(5000464854153221/5000000000000000 : ℝ) by norm_num, show 1+(748360823113787/2500000000000000000 : ℝ)+(9466069524468987/100000000000000000000 : ℝ)=(100039400502449020467/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(748360823113787/2500000000000000000 : ℝ) ≤ ((17525359718276072147/17530000000000000000 : ℝ)+2*(482943879313/350600000000000 : ℝ)*(921/6250 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (17525359718276072147/17530000000000000000 : ℝ)+2*(482943879313/350600000000000 : ℝ)*(921/6250 : ℝ)=(2000282530437151/2000000000000000 : ℝ) by norm_num, show 1+2*(748360823113787/2500000000000000000 : ℝ)=(1250748360823113787/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17525359718276072147/17530000000000000000 : ℝ)*(X 1 0+X 2 0)+(482943879313/350600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (17525359718276072147/17530000000000000000 : ℝ)) (alpha := (482943879313/350600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17525359718276072147/17530000000000000000 : ℝ)*(X 0 1+X 2 1)+(482943879313/350600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (17525359718276072147/17530000000000000000 : ℝ)) (alpha := (482943879313/350600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17525359718276072147/17530000000000000000 : ℝ)*(X 0 2+X 1 2)+(482943879313/350600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (17525359718276072147/17530000000000000000 : ℝ)) (alpha := (482943879313/350600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2011590201/10000000000 : ℝ)*X 0 0+(338172123/625000000 : ℝ)*X 0 1+(65571197/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348311227/10000000000 : ℝ)*X 1 0+(-1047829779/5000000000 : ℝ)*X 1 1+(65571197/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337077807/2500000000 : ℝ)*X 2 0+(65571197/125000000 : ℝ)*X 2 1+(-2095659557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079194899/2500000000 : ℝ)*X 0 0+(2072357051/5000000000 : ℝ)*X 0 1+(140480931/312500000 : ℝ)*X 0 2+(1079194899/2500000000 : ℝ)*X 1 0+(2072357051/5000000000 : ℝ)*X 1 1+(140480931/312500000 : ℝ)*X 1 2+(1079194899/2500000000 : ℝ)*X 2 0+(2072357051/5000000000 : ℝ)*X 2 1+(140480931/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2011601991/10000000000 : ℝ)*X 0 0+(524628857/1000000000 : ℝ)*X 0 1+(338134881/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061123139/2000000000 : ℝ)*X 1 0+(-1931197239/10000000000 : ℝ)*X 1 1+(1082031617/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530561571/1000000000 : ℝ)*X 2 0+(676269759/1250000000 : ℝ)*X 2 1+(-482799309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4316804661/10000000000 : ℝ)*X 0 0+(112353257/250000000 : ℝ)*X 0 1+(2072990053/5000000000 : ℝ)*X 0 2+(4316804661/10000000000 : ℝ)*X 1 0+(112353257/250000000 : ℝ)*X 1 1+(2072990053/5000000000 : ℝ)*X 1 2+(4316804661/10000000000 : ℝ)*X 2 0+(112353257/250000000 : ℝ)*X 2 1+(2072990053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1181536430100120540257859921/109562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (999027147/50000000000000 : ℝ)*(base19) + (1863147909/100000000000000 : ℝ)*(base23) + (72757989/100000000000000 : ℝ)*(lower2) + (269896977/100000000000000 : ℝ)*(upper3) + (171808911/100000000000000 : ℝ)*(upper5) + (556889447924073/12500000000000 : ℝ)*(major0) + (556889447924073/12500000000000 : ℝ)*(major1) + (556889447924073/12500000000000 : ℝ)*(major2) + (6058511887943557/100000000000000 : ℝ)*(sp0) + (6058551239102721/100000000000000 : ℝ)*(sp1) + (3029275687004553/50000000000000 : ℝ)*(sp2) + (22813252235561/800000000000 : ℝ)*(sp3) + (41349213459/100000000000000 : ℝ)*(sp4) + (10520355981/50000000000000 : ℝ)*(sp7) + (2851677570157087/100000000000000 : ℝ)*(f.failure) + (1211710647431403/20000000000000 : ℝ)*(f.sum) + (4166176200507/1095625000000000000000000000 : ℝ)*base65 + (2688755692275044731/219125000000000000000000000000000 : ℝ)*base67 + (1383096215610044731/219125000000000000000000000000000 : ℝ)*base69 + (1578282095756419731/219125000000000000000000000000000 : ℝ)*base71 + (6170547901379/2191250000000000000000000000 : ℝ)*base73 + (3741115553144044731/219125000000000000000000000000000 : ℝ)*base75 + (2703819082349794731/219125000000000000000000000000000 : ℝ)*base77 + (2534065986304794731/219125000000000000000000000000000 : ℝ)*base79 + (11964809365473/4382500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (5035959/5000000000000000000000 : ℝ)*base90 + (5035959/5000000000000000000000 : ℝ)*base92 + (5035959/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7387954307996546947870689/3506000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90977901/25000000000000 : ℝ)*(base19) + (209677737/50000000000000 : ℝ)*(base23) + (16934403/50000000000000 : ℝ)*(upper3) + (48263/250000000000 : ℝ)*(lower4) + (11584157/20000000000000 : ℝ)*(upper5) + (35898959452929/800000000000 : ℝ)*(major0) + (35898959452929/800000000000 : ℝ)*(major1) + (35898959452929/800000000000 : ℝ)*(major2) + (7688582217/100000000000000 : ℝ)*(sp1) + (3956430793/50000000000000 : ℝ)*(sp2) + (1525604129498171/25000000000000 : ℝ)*(sp4) + (6102408465498863/100000000000000 : ℝ)*(sp5) + (762801023221953/12500000000000 : ℝ)*(sp6) + (1436161637499251/50000000000000 : ℝ)*(sp7) + (1436161637499251/50000000000000 : ℝ)*(f.failure) + (1525604129498171/25000000000000 : ℝ)*(f.sum) + (6202697682443/3506000000000000000000000000 : ℝ)*base66 + (38590015715241437/14024000000000000000000000000000 : ℝ)*base68 + (131472488421705437/14024000000000000000000000000000 : ℝ)*base70 + (220182029529465437/14024000000000000000000000000000 : ℝ)*base72 + (9430776357623/3506000000000000000000000000 : ℝ)*base73 + (88217852521630563/14024000000000000000000000000000 : ℝ)*base75 + (91330016839961437/14024000000000000000000000000000 : ℝ)*base78 + (199847649997033437/14024000000000000000000000000000 : ℝ)*base80 + (17505917457851/3506000000000000000000000000 : ℝ)*base82 + (30156693/2500000000000000000000 : ℝ)*base89 + (30156693/2500000000000000000000 : ℝ)*base91 + (30156693/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1380_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1380_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1380_s7_0 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1005798503/5000000000 : ℝ)*x 0 + (1352677451/2500000000 : ℝ)*x 1 + (5245735287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005798503/5000000000 : ℝ)^1085 ≤ (490377340661/4000000000000 : ℝ)^829 := by
    have hnat : (1005798503 : ℕ)^1085*4000000000000^829 ≤ 490377340661^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005798503 5000000000 490377340661 4000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352677451/2500000000 : ℝ)^1085 ≤ (44759126985013/100000000000000 : ℝ)^829 := by
    have hnat : (1352677451 : ℕ)^1085*100000000000000^829 ≤ 44759126985013^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352677451 2500000000 44759126985013 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245735287/10000000000 : ℝ)^1085 ≤ (5372679935673/12500000000000 : ℝ)^829 := by
    have hnat : (5245735287 : ℕ)^1085*12500000000000^829 ≤ 5372679935673^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245735287 10000000000 5372679935673 12500000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1005798503/5000000000 : ℝ), (1352677451/2500000000 : ℝ), (5245735287/10000000000 : ℝ)] ![(490377340661/4000000000000 : ℝ), (44759126985013/100000000000000 : ℝ), (5372679935673/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1005798503/5000000000 : ℝ)|^1085 ≤ (490377340661/4000000000000 : ℝ)^829
        have hw : |(-1005798503/5000000000 : ℝ)|=(1005798503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352677451/2500000000 : ℝ)|^1085 ≤ (44759126985013/100000000000000 : ℝ)^829
        have hw : |(1352677451/2500000000 : ℝ)|=(1352677451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245735287/10000000000 : ℝ)|^1085 ≤ (5372679935673/12500000000000 : ℝ)^829
        have hw : |(5245735287/10000000000 : ℝ)|=(5245735287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s7_1 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668537407/1250000000 : ℝ)*x 0 + (-104781149/500000000 : ℝ)*x 1 + (1311433839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668537407/1250000000 : ℝ)^1085 ≤ (22042311639671/50000000000000 : ℝ)^829 := by
    have hnat : (668537407 : ℕ)^1085*50000000000000^829 ≤ 22042311639671^829*1250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668537407 1250000000 22042311639671 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104781149/500000000 : ℝ)^1085 ≤ (6466968241733/50000000000000 : ℝ)^829 := by
    have hnat : (104781149 : ℕ)^1085*50000000000000^829 ≤ 6466968241733^829*500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104781149 500000000 6466968241733 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311433839/2500000000 : ℝ)^1085 ≤ (2686340014083/6250000000000 : ℝ)^829 := by
    have hnat : (1311433839 : ℕ)^1085*6250000000000^829 ≤ 2686340014083^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311433839 2500000000 2686340014083 6250000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668537407/1250000000 : ℝ), (-104781149/500000000 : ℝ), (1311433839/2500000000 : ℝ)] ![(22042311639671/50000000000000 : ℝ), (6466968241733/50000000000000 : ℝ), (2686340014083/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668537407/1250000000 : ℝ)|^1085 ≤ (22042311639671/50000000000000 : ℝ)^829
        have hw : |(668537407/1250000000 : ℝ)|=(668537407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104781149/500000000 : ℝ)|^1085 ≤ (6466968241733/50000000000000 : ℝ)^829
        have hw : |(-104781149/500000000 : ℝ)|=(104781149/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311433839/2500000000 : ℝ)|^1085 ≤ (2686340014083/6250000000000 : ℝ)^829
        have hw : |(1311433839/2500000000 : ℝ)|=(1311433839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s7_2 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348299349/10000000000 : ℝ)*x 0 + (5245735341/10000000000 : ℝ)*x 1 + (-1047811437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348299349/10000000000 : ℝ)^1085 ≤ (44084624282639/100000000000000 : ℝ)^829 := by
    have hnat : (5348299349 : ℕ)^1085*100000000000000^829 ≤ 44084624282639^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348299349 10000000000 44084624282639 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245735341/10000000000 : ℝ)^1085 ≤ (42981440064471/100000000000000 : ℝ)^829 := by
    have hnat : (5245735341 : ℕ)^1085*100000000000000^829 ≤ 42981440064471^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245735341 10000000000 42981440064471 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047811437/5000000000 : ℝ)^1085 ≤ (646696781361/5000000000000 : ℝ)^829 := by
    have hnat : (1047811437 : ℕ)^1085*5000000000000^829 ≤ 646696781361^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047811437 5000000000 646696781361 5000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348299349/10000000000 : ℝ), (5245735341/10000000000 : ℝ), (-1047811437/5000000000 : ℝ)] ![(44084624282639/100000000000000 : ℝ), (42981440064471/100000000000000 : ℝ), (646696781361/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348299349/10000000000 : ℝ)|^1085 ≤ (44084624282639/100000000000000 : ℝ)^829
        have hw : |(5348299349/10000000000 : ℝ)|=(5348299349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245735341/10000000000 : ℝ)|^1085 ≤ (42981440064471/100000000000000 : ℝ)^829
        have hw : |(5245735341/10000000000 : ℝ)|=(5245735341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047811437/5000000000 : ℝ)|^1085 ≤ (646696781361/5000000000000 : ℝ)^829
        have hw : |(-1047811437/5000000000 : ℝ)|=(1047811437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s7_3 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (863356579/2000000000 : ℝ)*x 0 + (165792101/400000000 : ℝ)*x 1 + (4495300301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863356579/2000000000 : ℝ)^1085 ≤ (33303936255359/100000000000000 : ℝ)^829 := by
    have hnat : (863356579 : ℕ)^1085*100000000000000^829 ≤ 33303936255359^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863356579 2000000000 33303936255359 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165792101/400000000 : ℝ)^1085 ≤ (31578159654603/100000000000000 : ℝ)^829 := by
    have hnat : (165792101 : ℕ)^1085*100000000000000^829 ≤ 31578159654603^829*400000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165792101 400000000 31578159654603 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495300301/10000000000 : ℝ)^1085 ≤ (4389738009557/12500000000000 : ℝ)^829 := by
    have hnat : (4495300301 : ℕ)^1085*12500000000000^829 ≤ 4389738009557^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495300301 10000000000 4389738009557 12500000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863356579/2000000000 : ℝ), (165792101/400000000 : ℝ), (4495300301/10000000000 : ℝ)] ![(33303936255359/100000000000000 : ℝ), (31578159654603/100000000000000 : ℝ), (4389738009557/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863356579/2000000000 : ℝ)|^1085 ≤ (33303936255359/100000000000000 : ℝ)^829
        have hw : |(863356579/2000000000 : ℝ)|=(863356579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(165792101/400000000 : ℝ)|^1085 ≤ (31578159654603/100000000000000 : ℝ)^829
        have hw : |(165792101/400000000 : ℝ)|=(165792101/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495300301/10000000000 : ℝ)|^1085 ≤ (4389738009557/12500000000000 : ℝ)^829
        have hw : |(4495300301/10000000000 : ℝ)|=(4495300301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s7_4 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2011608763/10000000000 : ℝ)*x 0 + (5246327421/10000000000 : ℝ)*x 1 + (5410114623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2011608763/10000000000 : ℝ)^1085 ≤ (12259527294649/100000000000000 : ℝ)^829 := by
    have hnat : (2011608763 : ℕ)^1085*100000000000000^829 ≤ 12259527294649^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011608763 10000000000 12259527294649 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246327421/10000000000 : ℝ)^1085 ≤ (5373473692317/12500000000000 : ℝ)^829 := by
    have hnat : (5246327421 : ℕ)^1085*12500000000000^829 ≤ 5373473692317^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246327421 10000000000 5373473692317 12500000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410114623/10000000000 : ℝ)^1085 ≤ (4475268315233/10000000000000 : ℝ)^829 := by
    have hnat : (5410114623 : ℕ)^1085*10000000000000^829 ≤ 4475268315233^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410114623 10000000000 4475268315233 10000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2011608763/10000000000 : ℝ), (5246327421/10000000000 : ℝ), (5410114623/10000000000 : ℝ)] ![(12259527294649/100000000000000 : ℝ), (5373473692317/12500000000000 : ℝ), (4475268315233/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2011608763/10000000000 : ℝ)|^1085 ≤ (12259527294649/100000000000000 : ℝ)^829
        have hw : |(-2011608763/10000000000 : ℝ)|=(2011608763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246327421/10000000000 : ℝ)|^1085 ≤ (5373473692317/12500000000000 : ℝ)^829
        have hw : |(5246327421/10000000000 : ℝ)|=(5246327421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410114623/10000000000 : ℝ)|^1085 ≤ (4475268315233/10000000000000 : ℝ)^829
        have hw : |(5410114623/10000000000 : ℝ)|=(5410114623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s7_5 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (172672313/400000000 : ℝ)*x 0 + (2247021109/5000000000 : ℝ)*x 1 + (259129199/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172672313/400000000 : ℝ)^1085 ≤ (33304187984349/100000000000000 : ℝ)^829 := by
    have hnat : (172672313 : ℕ)^1085*100000000000000^829 ≤ 33304187984349^829*400000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172672313 400000000 33304187984349 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247021109/5000000000 : ℝ)^1085 ≤ (877626031841/2500000000000 : ℝ)^829 := by
    have hnat : (2247021109 : ℕ)^1085*2500000000000^829 ≤ 877626031841^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247021109 5000000000 877626031841 2500000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259129199/625000000 : ℝ)^1085 ≤ (6318154145739/20000000000000 : ℝ)^829 := by
    have hnat : (259129199 : ℕ)^1085*20000000000000^829 ≤ 6318154145739^829*625000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259129199 625000000 6318154145739 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172672313/400000000 : ℝ), (2247021109/5000000000 : ℝ), (259129199/625000000 : ℝ)] ![(33304187984349/100000000000000 : ℝ), (877626031841/2500000000000 : ℝ), (6318154145739/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172672313/400000000 : ℝ)|^1085 ≤ (33304187984349/100000000000000 : ℝ)^829
        have hw : |(172672313/400000000 : ℝ)|=(172672313/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247021109/5000000000 : ℝ)|^1085 ≤ (877626031841/2500000000000 : ℝ)^829
        have hw : |(2247021109/5000000000 : ℝ)|=(2247021109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259129199/625000000 : ℝ)|^1085 ≤ (6318154145739/20000000000000 : ℝ)^829
        have hw : |(259129199/625000000 : ℝ)|=(259129199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1380_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2809/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1473/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2247/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2247/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2247/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2247/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2247/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2247/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2247/20000 : ℝ) ^ (4339/1024 : ℝ) ≤ (9483941090533337/100000000000000000000 : ℝ) := by
    have hpowers : (2247/20000 : ℝ)^4339 ≤ (9483941090533337/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2247 : ℕ)^4339*100000000000000000000^1024 ≤ 9483941090533337^1024*20000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2247 20000 9483941090533337 100000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2247/20000 : ℝ)) (X := (9483941090533337/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1473/10000 : ℝ) ^ (4339/1024 : ℝ) ≤ (29882821465983393/100000000000000000000 : ℝ) := by
    have hpowers : (1473/10000 : ℝ)^4339 ≤ (29882821465983393/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1473 : ℕ)^4339*100000000000000000000^1024 ≤ 29882821465983393^1024*10000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1473 10000 29882821465983393 100000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1473/10000 : ℝ)) (X := (29882821465983393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009483941090533337/50000000000000000000 : ℝ) ≤ (10000447607839647/10000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (50009483941090533337/50000000000000000000 : ℝ)^1024 ≤ (10000447607839647/10000000000000000 : ℝ)^4339 := by
      have hnat : (50009483941090533337 : ℕ)^1024*10000000000000000^4339 ≤ 10000447607839647^4339*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009483941090533337 50000000000000000000 10000447607839647 10000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000447607839647/10000000000000000 : ℝ)) (X := (50009483941090533337/50000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003936676255651673/10000000000000000000 : ℝ) ≤ (10000928912287593/10000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (10003936676255651673/10000000000000000000 : ℝ)^1024 ≤ (10000928912287593/10000000000000000 : ℝ)^4339 := by
      have hnat : (10003936676255651673 : ℕ)^1024*10000000000000000^4339 ≤ 10000928912287593^4339*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003936676255651673 10000000000000000000 10000928912287593 10000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000928912287593/10000000000000000 : ℝ)) (X := (10003936676255651673/10000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029882821465983393/50000000000000000000 : ℝ) ≤ (10001410216735539/10000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (50029882821465983393/50000000000000000000 : ℝ)^1024 ≤ (10001410216735539/10000000000000000 : ℝ)^4339 := by
      have hnat : (50029882821465983393 : ℕ)^1024*10000000000000000^4339 ≤ 10001410216735539^4339*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029882821465983393 50000000000000000000 10001410216735539 10000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001410216735539/10000000000000000 : ℝ)) (X := (50029882821465983393/50000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9483941090533337/100000000000000000000 : ℝ) ≤ ((2329383298563614643/2330000000000000000 : ℝ)+2*(80217407991/58250000000000 : ℝ)*(2247/20000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (2329383298563614643/2330000000000000000 : ℝ)+2*(80217407991/58250000000000 : ℝ)*(2247/20000 : ℝ)=(10000447607839647/10000000000000000 : ℝ) by norm_num, show 1+2*(9483941090533337/100000000000000000000 : ℝ)=(50009483941090533337/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29882821465983393/100000000000000000000 : ℝ)+(9483941090533337/100000000000000000000 : ℝ) ≤ ((2329383298563614643/2330000000000000000 : ℝ)+(80217407991/58250000000000 : ℝ)*((1473/10000 : ℝ)+(2247/20000 : ℝ)))^(4339/1024 : ℝ) := by
    rw [show (2329383298563614643/2330000000000000000 : ℝ)+(80217407991/58250000000000 : ℝ)*((1473/10000 : ℝ)+(2247/20000 : ℝ))=(10000928912287593/10000000000000000 : ℝ) by norm_num, show 1+(29882821465983393/100000000000000000000 : ℝ)+(9483941090533337/100000000000000000000 : ℝ)=(10003936676255651673/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29882821465983393/100000000000000000000 : ℝ) ≤ ((2329383298563614643/2330000000000000000 : ℝ)+2*(80217407991/58250000000000 : ℝ)*(1473/10000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (2329383298563614643/2330000000000000000 : ℝ)+2*(80217407991/58250000000000 : ℝ)*(1473/10000 : ℝ)=(10001410216735539/10000000000000000 : ℝ) by norm_num, show 1+2*(29882821465983393/100000000000000000000 : ℝ)=(50029882821465983393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2329383298563614643/2330000000000000000 : ℝ)*(X 1 0+X 2 0)+(80217407991/58250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (2329383298563614643/2330000000000000000 : ℝ)) (alpha := (80217407991/58250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2329383298563614643/2330000000000000000 : ℝ)*(X 0 1+X 2 1)+(80217407991/58250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (2329383298563614643/2330000000000000000 : ℝ)) (alpha := (80217407991/58250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2329383298563614643/2330000000000000000 : ℝ)*(X 0 2+X 1 2)+(80217407991/58250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (2329383298563614643/2330000000000000000 : ℝ)) (alpha := (80217407991/58250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1005798503/5000000000 : ℝ)*X 0 0+(1352677451/2500000000 : ℝ)*X 0 1+(5245735287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668537407/1250000000 : ℝ)*X 1 0+(-104781149/500000000 : ℝ)*X 1 1+(1311433839/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348299349/10000000000 : ℝ)*X 2 0+(5245735341/10000000000 : ℝ)*X 2 1+(-1047811437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863356579/2000000000 : ℝ)*X 0 0+(165792101/400000000 : ℝ)*X 0 1+(4495300301/10000000000 : ℝ)*X 0 2+(863356579/2000000000 : ℝ)*X 1 0+(165792101/400000000 : ℝ)*X 1 1+(4495300301/10000000000 : ℝ)*X 1 2+(863356579/2000000000 : ℝ)*X 2 0+(165792101/400000000 : ℝ)*X 2 1+(4495300301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2011608763/10000000000 : ℝ)*X 0 0+(5246327421/10000000000 : ℝ)*X 0 1+(5410114623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((172672313/400000000 : ℝ)*X 0 0+(2247021109/5000000000 : ℝ)*X 0 1+(259129199/625000000 : ℝ)*X 0 2+(172672313/400000000 : ℝ)*X 1 0+(2247021109/5000000000 : ℝ)*X 1 1+(259129199/625000000 : ℝ)*X 1 2+(172672313/400000000 : ℝ)*X 2 0+(2247021109/5000000000 : ℝ)*X 2 1+(259129199/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52317191763082196478447/5825000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215814679/12500000000000 : ℝ)*(base19) + (218450703/12500000000000 : ℝ)*(base23) + (22547187/50000000000000 : ℝ)*(lower2) + (248713413/100000000000000 : ℝ)*(upper3) + (168142431/50000000000000 : ℝ)*(upper5) + (1114341084151467/25000000000000 : ℝ)*(major0) + (1114341084151467/25000000000000 : ℝ)*(major1) + (1114341084151467/25000000000000 : ℝ)*(major2) + (6061574048689597/100000000000000 : ℝ)*(sp0) + (757701208922389/12500000000000 : ℝ)*(sp1) + (151540241257273/2500000000000 : ℝ)*(sp2) + (1426550638167947/50000000000000 : ℝ)*(sp3) + (18674603473/50000000000000 : ℝ)*(sp4) + (7849798109/50000000000000 : ℝ)*(sp5) + (178319810995757/6250000000000 : ℝ)*(f.failure) + (189425356184267/3125000000000 : ℝ)*(f.sum) + (1481464411711/364062500000000000000000000 : ℝ)*base65 + (143724405737011281/58250000000000000000000000000000 : ℝ)*base67 + (20625393156738719/58250000000000000000000000000000 : ℝ)*base70 + (63837995214011281/58250000000000000000000000000000 : ℝ)*base71 + (7287328515837/2912500000000000000000000000 : ℝ)*base74 + (486497428100488719/58250000000000000000000000000000 : ℝ)*base76 + (303066643948011281/58250000000000000000000000000000 : ℝ)*base77 + (1063869652407488719/58250000000000000000000000000000 : ℝ)*base80 + (798237449213/2912500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1960149/312500000000000000000 : ℝ)*base90 + (1960149/312500000000000000000 : ℝ)*base92 + (1960149/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1380_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1380_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1380_box_0 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-923645383/5000000000 : ℝ)*x 0 + (5388344927/10000000000 : ℝ)*x 1 + (1077669/2000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (923645383/5000000000 : ℝ)^1085 ≤ (10965718692763/100000000000000 : ℝ)^829 := by
    have hnat : (923645383 : ℕ)^1085*100000000000000^829 ≤ 10965718692763^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923645383 5000000000 10965718692763 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388344927/10000000000 : ℝ)^1085 ≤ (11129285062453/25000000000000 : ℝ)^829 := by
    have hnat : (5388344927 : ℕ)^1085*25000000000000^829 ≤ 11129285062453^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388344927 10000000000 11129285062453 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077669/2000000 : ℝ)^1085 ≤ (22258570519581/50000000000000 : ℝ)^829 := by
    have hnat : (1077669 : ℕ)^1085*50000000000000^829 ≤ 22258570519581^829*2000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077669 2000000 22258570519581 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-923645383/5000000000 : ℝ), (5388344927/10000000000 : ℝ), (1077669/2000000 : ℝ)] ![(10965718692763/100000000000000 : ℝ), (11129285062453/25000000000000 : ℝ), (22258570519581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-923645383/5000000000 : ℝ)|^1085 ≤ (10965718692763/100000000000000 : ℝ)^829
        have hw : |(-923645383/5000000000 : ℝ)|=(923645383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388344927/10000000000 : ℝ)|^1085 ≤ (11129285062453/25000000000000 : ℝ)^829
        have hw : |(5388344927/10000000000 : ℝ)|=(5388344927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077669/2000000 : ℝ)|^1085 ≤ (22258570519581/50000000000000 : ℝ)^829
        have hw : |(1077669/2000000 : ℝ)|=(1077669/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_1 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642813741/5000000000 : ℝ)*x 0 + (-1988196641/10000000000 : ℝ)*x 1 + (5388345097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642813741/5000000000 : ℝ)^1085 ≤ (43409737912897/100000000000000 : ℝ)^829 := by
    have hnat : (2642813741 : ℕ)^1085*100000000000000^829 ≤ 43409737912897^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642813741 5000000000 43409737912897 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988196641/10000000000 : ℝ)^1085 ≤ (6036559990501/50000000000000 : ℝ)^829 := by
    have hnat : (1988196641 : ℕ)^1085*50000000000000^829 ≤ 6036559990501^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988196641 10000000000 6036559990501 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388345097/10000000000 : ℝ)^1085 ≤ (1780685683521/4000000000000 : ℝ)^829 := by
    have hnat : (5388345097 : ℕ)^1085*4000000000000^829 ≤ 1780685683521^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388345097 10000000000 1780685683521 4000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642813741/5000000000 : ℝ), (-1988196641/10000000000 : ℝ), (5388345097/10000000000 : ℝ)] ![(43409737912897/100000000000000 : ℝ), (6036559990501/50000000000000 : ℝ), (1780685683521/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642813741/5000000000 : ℝ)|^1085 ≤ (43409737912897/100000000000000 : ℝ)^829
        have hw : |(2642813741/5000000000 : ℝ)|=(2642813741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1988196641/10000000000 : ℝ)|^1085 ≤ (6036559990501/50000000000000 : ℝ)^829
        have hw : |(-1988196641/10000000000 : ℝ)|=(1988196641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388345097/10000000000 : ℝ)|^1085 ≤ (1780685683521/4000000000000 : ℝ)^829
        have hw : |(5388345097/10000000000 : ℝ)|=(5388345097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_2 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (528562723/1000000000 : ℝ)*x 0 + (5388345319/10000000000 : ℝ)*x 1 + (-49704917/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528562723/1000000000 : ℝ)^1085 ≤ (43409735204163/100000000000000 : ℝ)^829 := by
    have hnat : (528562723 : ℕ)^1085*100000000000000^829 ≤ 43409735204163^829*1000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528562723 1000000000 43409735204163 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388345319/10000000000 : ℝ)^1085 ≤ (11129286122129/25000000000000 : ℝ)^829 := by
    have hnat : (5388345319 : ℕ)^1085*25000000000000^829 ≤ 11129286122129^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388345319 10000000000 11129286122129 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49704917/250000000 : ℝ)^1085 ≤ (6036560145479/50000000000000 : ℝ)^829 := by
    have hnat : (49704917 : ℕ)^1085*50000000000000^829 ≤ 6036560145479^829*250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49704917 250000000 6036560145479 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528562723/1000000000 : ℝ), (5388345319/10000000000 : ℝ), (-49704917/250000000 : ℝ)] ![(43409735204163/100000000000000 : ℝ), (11129286122129/25000000000000 : ℝ), (6036560145479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528562723/1000000000 : ℝ)|^1085 ≤ (43409735204163/100000000000000 : ℝ)^829
        have hw : |(528562723/1000000000 : ℝ)|=(528562723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388345319/10000000000 : ℝ)|^1085 ≤ (11129286122129/25000000000000 : ℝ)^829
        have hw : |(5388345319/10000000000 : ℝ)|=(5388345319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49704917/250000000 : ℝ)|^1085 ≤ (6036560145479/50000000000000 : ℝ)^829
        have hw : |(-49704917/250000000 : ℝ)|=(49704917/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_3 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (139503533/312500000 : ℝ)*x 0 + (1061731051/2500000000 : ℝ)*x 1 + (2123462333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139503533/312500000 : ℝ)^1085 ≤ (6959874002441/20000000000000 : ℝ)^829 := by
    have hnat : (139503533 : ℕ)^1085*20000000000000^829 ≤ 6959874002441^829*312500000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139503533 312500000 6959874002441 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061731051/2500000000 : ℝ)^1085 ≤ (8150078165703/25000000000000 : ℝ)^829 := by
    have hnat : (1061731051 : ℕ)^1085*25000000000000^829 ≤ 8150078165703^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061731051 2500000000 8150078165703 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123462333/5000000000 : ℝ)^1085 ≤ (32600317304377/100000000000000 : ℝ)^829 := by
    have hnat : (2123462333 : ℕ)^1085*100000000000000^829 ≤ 32600317304377^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123462333 5000000000 32600317304377 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(139503533/312500000 : ℝ), (1061731051/2500000000 : ℝ), (2123462333/5000000000 : ℝ)] ![(6959874002441/20000000000000 : ℝ), (8150078165703/25000000000000 : ℝ), (32600317304377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(139503533/312500000 : ℝ)|^1085 ≤ (6959874002441/20000000000000 : ℝ)^829
        have hw : |(139503533/312500000 : ℝ)|=(139503533/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061731051/2500000000 : ℝ)|^1085 ≤ (8150078165703/25000000000000 : ℝ)^829
        have hw : |(1061731051/2500000000 : ℝ)|=(1061731051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123462333/5000000000 : ℝ)|^1085 ≤ (32600317304377/100000000000000 : ℝ)^829
        have hw : |(2123462333/5000000000 : ℝ)|=(2123462333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_4 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-272330193/1250000000 : ℝ)*x 0 + (2632851497/5000000000 : ℝ)*x 1 + (2632851527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272330193/1250000000 : ℝ)^1085 ≤ (6804304214719/50000000000000 : ℝ)^829 := by
    have hnat : (272330193 : ℕ)^1085*50000000000000^829 ≤ 6804304214719^829*1250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272330193 1250000000 6804304214719 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632851497/5000000000 : ℝ)^1085 ≤ (10798923864509/25000000000000 : ℝ)^829 := by
    have hnat : (2632851497 : ℕ)^1085*25000000000000^829 ≤ 10798923864509^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632851497 5000000000 10798923864509 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632851527/5000000000 : ℝ)^1085 ≤ (43195696102221/100000000000000 : ℝ)^829 := by
    have hnat : (2632851527 : ℕ)^1085*100000000000000^829 ≤ 43195696102221^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632851527 5000000000 43195696102221 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272330193/1250000000 : ℝ), (2632851497/5000000000 : ℝ), (2632851527/5000000000 : ℝ)] ![(6804304214719/50000000000000 : ℝ), (10798923864509/25000000000000 : ℝ), (43195696102221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272330193/1250000000 : ℝ)|^1085 ≤ (6804304214719/50000000000000 : ℝ)^829
        have hw : |(-272330193/1250000000 : ℝ)|=(272330193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632851497/5000000000 : ℝ)|^1085 ≤ (10798923864509/25000000000000 : ℝ)^829
        have hw : |(2632851497/5000000000 : ℝ)|=(2632851497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632851527/5000000000 : ℝ)|^1085 ≤ (43195696102221/100000000000000 : ℝ)^829
        have hw : |(2632851527/5000000000 : ℝ)|=(2632851527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_5 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (537163127/1000000000 : ℝ)*x 0 + (-1018834023/5000000000 : ℝ)*x 1 + (5265703221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537163127/1000000000 : ℝ)^1085 ≤ (8867300345919/20000000000000 : ℝ)^829 := by
    have hnat : (537163127 : ℕ)^1085*20000000000000^829 ≤ 8867300345919^829*1000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537163127 1000000000 8867300345919 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018834023/5000000000 : ℝ)^1085 ≤ (6233900180869/50000000000000 : ℝ)^829 := by
    have hnat : (1018834023 : ℕ)^1085*50000000000000^829 ≤ 6233900180869^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018834023 5000000000 6233900180869 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265703221/10000000000 : ℝ)^1085 ≤ (43195697895203/100000000000000 : ℝ)^829 := by
    have hnat : (5265703221 : ℕ)^1085*100000000000000^829 ≤ 43195697895203^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265703221 10000000000 43195697895203 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537163127/1000000000 : ℝ), (-1018834023/5000000000 : ℝ), (5265703221/10000000000 : ℝ)] ![(8867300345919/20000000000000 : ℝ), (6233900180869/50000000000000 : ℝ), (43195697895203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537163127/1000000000 : ℝ)|^1085 ≤ (8867300345919/20000000000000 : ℝ)^829
        have hw : |(537163127/1000000000 : ℝ)|=(537163127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1018834023/5000000000 : ℝ)|^1085 ≤ (6233900180869/50000000000000 : ℝ)^829
        have hw : |(-1018834023/5000000000 : ℝ)|=(1018834023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265703221/10000000000 : ℝ)|^1085 ≤ (43195697895203/100000000000000 : ℝ)^829
        have hw : |(5265703221/10000000000 : ℝ)|=(5265703221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_6 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1074326373/2000000000 : ℝ)*x 0 + (5265702759/10000000000 : ℝ)*x 1 + (-2037667863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074326373/2000000000 : ℝ)^1085 ≤ (22168254078587/50000000000000 : ℝ)^829 := by
    have hnat : (1074326373 : ℕ)^1085*50000000000000^829 ≤ 22168254078587^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074326373 2000000000 22168254078587 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265702759/10000000000 : ℝ)^1085 ≤ (43195692934979/100000000000000 : ℝ)^829 := by
    have hnat : (5265702759 : ℕ)^1085*100000000000000^829 ≤ 43195692934979^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265702759 10000000000 43195692934979 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2037667863/10000000000 : ℝ)^1085 ≤ (12467798896249/100000000000000 : ℝ)^829 := by
    have hnat : (2037667863 : ℕ)^1085*100000000000000^829 ≤ 12467798896249^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037667863 10000000000 12467798896249 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074326373/2000000000 : ℝ), (5265702759/10000000000 : ℝ), (-2037667863/10000000000 : ℝ)] ![(22168254078587/50000000000000 : ℝ), (43195692934979/100000000000000 : ℝ), (12467798896249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074326373/2000000000 : ℝ)|^1085 ≤ (22168254078587/50000000000000 : ℝ)^829
        have hw : |(1074326373/2000000000 : ℝ)|=(1074326373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265702759/10000000000 : ℝ)|^1085 ≤ (43195692934979/100000000000000 : ℝ)^829
        have hw : |(5265702759/10000000000 : ℝ)|=(5265702759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2037667863/10000000000 : ℝ)|^1085 ≤ (12467798896249/100000000000000 : ℝ)^829
        have hw : |(-2037667863/10000000000 : ℝ)|=(2037667863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_7 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (416847059/1000000000 : ℝ)*x 0 + (4394693351/10000000000 : ℝ)*x 1 + (34333541/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416847059/1000000000 : ℝ)^1085 ≤ (7953593079179/25000000000000 : ℝ)^829 := by
    have hnat : (416847059 : ℕ)^1085*25000000000000^829 ≤ 7953593079179^829*1000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416847059 1000000000 7953593079179 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4394693351/10000000000 : ℝ)^1085 ≤ (34092814355807/100000000000000 : ℝ)^829 := by
    have hnat : (4394693351 : ℕ)^1085*100000000000000^829 ≤ 34092814355807^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394693351 10000000000 34092814355807 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34333541/78125000 : ℝ)^1085 ≤ (8523203327503/25000000000000 : ℝ)^829 := by
    have hnat : (34333541 : ℕ)^1085*25000000000000^829 ≤ 8523203327503^829*78125000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34333541 78125000 8523203327503 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(416847059/1000000000 : ℝ), (4394693351/10000000000 : ℝ), (34333541/78125000 : ℝ)] ![(7953593079179/25000000000000 : ℝ), (34092814355807/100000000000000 : ℝ), (8523203327503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(416847059/1000000000 : ℝ)|^1085 ≤ (7953593079179/25000000000000 : ℝ)^829
        have hw : |(416847059/1000000000 : ℝ)|=(416847059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4394693351/10000000000 : ℝ)|^1085 ≤ (34092814355807/100000000000000 : ℝ)^829
        have hw : |(4394693351/10000000000 : ℝ)|=(4394693351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34333541/78125000 : ℝ)|^1085 ≤ (8523203327503/25000000000000 : ℝ)^829
        have hw : |(34333541/78125000 : ℝ)|=(34333541/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_8 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-421792681/2000000000 : ℝ)*x 0 + (5181097011/10000000000 : ℝ)*x 1 + (270117343/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421792681/2000000000 : ℝ)^1085 ≤ (407556357941/3125000000000 : ℝ)^829 := by
    have hnat : (421792681 : ℕ)^1085*3125000000000^829 ≤ 407556357941^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421792681 2000000000 407556357941 3125000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181097011/10000000000 : ℝ)^1085 ≤ (42289592368343/100000000000000 : ℝ)^829 := by
    have hnat : (5181097011 : ℕ)^1085*100000000000000^829 ≤ 42289592368343^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181097011 10000000000 42289592368343 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270117343/500000000 : ℝ)^1085 ≤ (2233430208319/5000000000000 : ℝ)^829 := by
    have hnat : (270117343 : ℕ)^1085*5000000000000^829 ≤ 2233430208319^829*500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270117343 500000000 2233430208319 5000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421792681/2000000000 : ℝ), (5181097011/10000000000 : ℝ), (270117343/500000000 : ℝ)] ![(407556357941/3125000000000 : ℝ), (42289592368343/100000000000000 : ℝ), (2233430208319/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421792681/2000000000 : ℝ)|^1085 ≤ (407556357941/3125000000000 : ℝ)^829
        have hw : |(-421792681/2000000000 : ℝ)|=(421792681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181097011/10000000000 : ℝ)|^1085 ≤ (42289592368343/100000000000000 : ℝ)^829
        have hw : |(5181097011/10000000000 : ℝ)|=(5181097011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270117343/500000000 : ℝ)|^1085 ≤ (2233430208319/5000000000000 : ℝ)^829
        have hw : |(270117343/500000000 : ℝ)|=(270117343/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_9 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2637901311/5000000000 : ℝ)*x 0 + (-495604859/2500000000 : ℝ)*x 1 + (337646729/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637901311/5000000000 : ℝ)^1085 ≤ (8660832272133/20000000000000 : ℝ)^829 := by
    have hnat : (2637901311 : ℕ)^1085*20000000000000^829 ≤ 8660832272133^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637901311 5000000000 8660832272133 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495604859/2500000000 : ℝ)^1085 ≤ (3006806436277/25000000000000 : ℝ)^829 := by
    have hnat : (495604859 : ℕ)^1085*25000000000000^829 ≤ 3006806436277^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495604859 2500000000 3006806436277 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337646729/625000000 : ℝ)^1085 ≤ (2233430643351/5000000000000 : ℝ)^829 := by
    have hnat : (337646729 : ℕ)^1085*5000000000000^829 ≤ 2233430643351^829*625000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337646729 625000000 2233430643351 5000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637901311/5000000000 : ℝ), (-495604859/2500000000 : ℝ), (337646729/625000000 : ℝ)] ![(8660832272133/20000000000000 : ℝ), (3006806436277/25000000000000 : ℝ), (2233430643351/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637901311/5000000000 : ℝ)|^1085 ≤ (8660832272133/20000000000000 : ℝ)^829
        have hw : |(2637901311/5000000000 : ℝ)|=(2637901311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-495604859/2500000000 : ℝ)|^1085 ≤ (3006806436277/25000000000000 : ℝ)^829
        have hw : |(-495604859/2500000000 : ℝ)|=(495604859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337646729/625000000 : ℝ)|^1085 ≤ (2233430643351/5000000000000 : ℝ)^829
        have hw : |(337646729/625000000 : ℝ)|=(337646729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_10 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5275803281/10000000000 : ℝ)*x 0 + (1350586819/2500000000 : ℝ)*x 1 + (-991209537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275803281/10000000000 : ℝ)^1085 ≤ (43304168440151/100000000000000 : ℝ)^829 := by
    have hnat : (5275803281 : ℕ)^1085*100000000000000^829 ≤ 43304168440151^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275803281 10000000000 43304168440151 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350586819/2500000000 : ℝ)^1085 ≤ (11167152167051/25000000000000 : ℝ)^829 := by
    have hnat : (1350586819 : ℕ)^1085*25000000000000^829 ≤ 11167152167051^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350586819 2500000000 11167152167051 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (991209537/5000000000 : ℝ)^1085 ≤ (2405444574133/20000000000000 : ℝ)^829 := by
    have hnat : (991209537 : ℕ)^1085*20000000000000^829 ≤ 2405444574133^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991209537 5000000000 2405444574133 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275803281/10000000000 : ℝ), (1350586819/2500000000 : ℝ), (-991209537/5000000000 : ℝ)] ![(43304168440151/100000000000000 : ℝ), (11167152167051/25000000000000 : ℝ), (2405444574133/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275803281/10000000000 : ℝ)|^1085 ≤ (43304168440151/100000000000000 : ℝ)^829
        have hw : |(5275803281/10000000000 : ℝ)|=(5275803281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350586819/2500000000 : ℝ)|^1085 ≤ (11167152167051/25000000000000 : ℝ)^829
        have hw : |(1350586819/2500000000 : ℝ)|=(1350586819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-991209537/5000000000 : ℝ)|^1085 ≤ (2405444574133/20000000000000 : ℝ)^829
        have hw : |(-991209537/5000000000 : ℝ)|=(991209537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_11 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2248654641/5000000000 : ℝ)*x 0 + (211501959/500000000 : ℝ)*x 1 + (4230038833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2248654641/5000000000 : ℝ)^1085 ≤ (17569223231091/50000000000000 : ℝ)^829 := by
    have hnat : (2248654641 : ℕ)^1085*50000000000000^829 ≤ 17569223231091^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248654641 5000000000 17569223231091 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211501959/500000000 : ℝ)^1085 ≤ (6486155700911/20000000000000 : ℝ)^829 := by
    have hnat : (211501959 : ℕ)^1085*20000000000000^829 ≤ 6486155700911^829*500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211501959 500000000 6486155700911 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230038833/10000000000 : ℝ)^1085 ≤ (8107693755661/25000000000000 : ℝ)^829 := by
    have hnat : (4230038833 : ℕ)^1085*25000000000000^829 ≤ 8107693755661^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230038833 10000000000 8107693755661 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2248654641/5000000000 : ℝ), (211501959/500000000 : ℝ), (4230038833/10000000000 : ℝ)] ![(17569223231091/50000000000000 : ℝ), (6486155700911/20000000000000 : ℝ), (8107693755661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2248654641/5000000000 : ℝ)|^1085 ≤ (17569223231091/50000000000000 : ℝ)^829
        have hw : |(2248654641/5000000000 : ℝ)|=(2248654641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211501959/500000000 : ℝ)|^1085 ≤ (6486155700911/20000000000000 : ℝ)^829
        have hw : |(211501959/500000000 : ℝ)|=(211501959/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230038833/10000000000 : ℝ)|^1085 ≤ (8107693755661/25000000000000 : ℝ)^829
        have hw : |(4230038833/10000000000 : ℝ)|=(4230038833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_12 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-479308839/2500000000 : ℝ)*x 0 + (5470828969/10000000000 : ℝ)*x 1 + (656825543/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (479308839/2500000000 : ℝ)^1085 ≤ (11512282771339/100000000000000 : ℝ)^829 := by
    have hnat : (479308839 : ℕ)^1085*100000000000000^829 ≤ 11512282771339^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479308839 2500000000 11512282771339 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470828969/10000000000 : ℝ)^1085 ≤ (11352785670669/25000000000000 : ℝ)^829 := by
    have hnat : (5470828969 : ℕ)^1085*25000000000000^829 ≤ 11352785670669^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470828969 10000000000 11352785670669 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656825543/1250000000 : ℝ)^1085 ≤ (43076574535907/100000000000000 : ℝ)^829 := by
    have hnat : (656825543 : ℕ)^1085*100000000000000^829 ≤ 43076574535907^829*1250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656825543 1250000000 43076574535907 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-479308839/2500000000 : ℝ), (5470828969/10000000000 : ℝ), (656825543/1250000000 : ℝ)] ![(11512282771339/100000000000000 : ℝ), (11352785670669/25000000000000 : ℝ), (43076574535907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-479308839/2500000000 : ℝ)|^1085 ≤ (11512282771339/100000000000000 : ℝ)^829
        have hw : |(-479308839/2500000000 : ℝ)|=(479308839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470828969/10000000000 : ℝ)|^1085 ≤ (11352785670669/25000000000000 : ℝ)^829
        have hw : |(5470828969/10000000000 : ℝ)|=(5470828969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656825543/1250000000 : ℝ)|^1085 ≤ (43076574535907/100000000000000 : ℝ)^829
        have hw : |(656825543/1250000000 : ℝ)|=(656825543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_13 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5379412057/10000000000 : ℝ)*x 0 + (-51051061/250000000 : ℝ)*x 1 + (1313651297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379412057/10000000000 : ℝ)^1085 ≤ (11105143416553/25000000000000 : ℝ)^829 := by
    have hnat : (5379412057 : ℕ)^1085*25000000000000^829 ≤ 11105143416553^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379412057 10000000000 11105143416553 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51051061/250000000 : ℝ)^1085 ≤ (3125710680871/25000000000000 : ℝ)^829 := by
    have hnat : (51051061 : ℕ)^1085*25000000000000^829 ≤ 3125710680871^829*250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51051061 250000000 3125710680871 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313651297/2500000000 : ℝ)^1085 ≤ (2153829179577/5000000000000 : ℝ)^829 := by
    have hnat : (1313651297 : ℕ)^1085*5000000000000^829 ≤ 2153829179577^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313651297 2500000000 2153829179577 5000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379412057/10000000000 : ℝ), (-51051061/250000000 : ℝ), (1313651297/2500000000 : ℝ)] ![(11105143416553/25000000000000 : ℝ), (3125710680871/25000000000000 : ℝ), (2153829179577/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379412057/10000000000 : ℝ)|^1085 ≤ (11105143416553/25000000000000 : ℝ)^829
        have hw : |(5379412057/10000000000 : ℝ)|=(5379412057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51051061/250000000 : ℝ)|^1085 ≤ (3125710680871/25000000000000 : ℝ)^829
        have hw : |(-51051061/250000000 : ℝ)|=(51051061/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313651297/2500000000 : ℝ)|^1085 ≤ (2153829179577/5000000000000 : ℝ)^829
        have hw : |(1313651297/2500000000 : ℝ)|=(1313651297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_14 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2689706129/5000000000 : ℝ)*x 0 + (5254604641/10000000000 : ℝ)*x 1 + (-2042042903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689706129/5000000000 : ℝ)^1085 ≤ (11105143959629/25000000000000 : ℝ)^829 := by
    have hnat : (2689706129 : ℕ)^1085*25000000000000^829 ≤ 11105143959629^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689706129 5000000000 11105143959629 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254604641/10000000000 : ℝ)^1085 ≤ (21538288861273/50000000000000 : ℝ)^829 := by
    have hnat : (5254604641 : ℕ)^1085*50000000000000^829 ≤ 21538288861273^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254604641 10000000000 21538288861273 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2042042903/10000000000 : ℝ)^1085 ≤ (12502846433709/100000000000000 : ℝ)^829 := by
    have hnat : (2042042903 : ℕ)^1085*100000000000000^829 ≤ 12502846433709^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042042903 10000000000 12502846433709 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689706129/5000000000 : ℝ), (5254604641/10000000000 : ℝ), (-2042042903/10000000000 : ℝ)] ![(11105143959629/25000000000000 : ℝ), (21538288861273/50000000000000 : ℝ), (12502846433709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689706129/5000000000 : ℝ)|^1085 ≤ (11105143959629/25000000000000 : ℝ)^829
        have hw : |(2689706129/5000000000 : ℝ)|=(2689706129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254604641/10000000000 : ℝ)|^1085 ≤ (21538288861273/50000000000000 : ℝ)^829
        have hw : |(5254604641/10000000000 : ℝ)|=(5254604641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2042042903/10000000000 : ℝ)|^1085 ≤ (12502846433709/100000000000000 : ℝ)^829
        have hw : |(-2042042903/10000000000 : ℝ)|=(2042042903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_box_15 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4141269519/10000000000 : ℝ)*x 0 + (4408054193/10000000000 : ℝ)*x 1 + (2204026811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4141269519/10000000000 : ℝ)^1085 ≤ (6308587022091/20000000000000 : ℝ)^829 := by
    have hnat : (4141269519 : ℕ)^1085*20000000000000^829 ≤ 6308587022091^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141269519 10000000000 6308587022091 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4408054193/10000000000 : ℝ)^1085 ≤ (34228535336329/100000000000000 : ℝ)^829 := by
    have hnat : (4408054193 : ℕ)^1085*100000000000000^829 ≤ 34228535336329^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408054193 10000000000 34228535336329 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204026811/5000000000 : ℝ)^1085 ≤ (34228529533327/100000000000000 : ℝ)^829 := by
    have hnat : (2204026811 : ℕ)^1085*100000000000000^829 ≤ 34228529533327^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204026811 5000000000 34228529533327 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4141269519/10000000000 : ℝ), (4408054193/10000000000 : ℝ), (2204026811/5000000000 : ℝ)] ![(6308587022091/20000000000000 : ℝ), (34228535336329/100000000000000 : ℝ), (34228529533327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4141269519/10000000000 : ℝ)|^1085 ≤ (6308587022091/20000000000000 : ℝ)^829
        have hw : |(4141269519/10000000000 : ℝ)|=(4141269519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4408054193/10000000000 : ℝ)|^1085 ≤ (34228535336329/100000000000000 : ℝ)^829
        have hw : |(4408054193/10000000000 : ℝ)|=(4408054193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2204026811/5000000000 : ℝ)|^1085 ≤ (34228529533327/100000000000000 : ℝ)^829
        have hw : |(2204026811/5000000000 : ℝ)|=(2204026811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1380_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7859/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7377/12500 : ℝ) ∧ (40087/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84499/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2809/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2809/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2809/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2809/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2809/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2809/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2809/25000 : ℝ) ^ (4339/1024 : ℝ) ≤ (296484952965913/3125000000000000000 : ℝ) := by
    have hpowers : (2809/25000 : ℝ)^4339 ≤ (296484952965913/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2809 : ℕ)^4339*3125000000000000000^1024 ≤ 296484952965913^1024*25000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2809 25000 296484952965913 3125000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2809/25000 : ℝ)) (X := (296484952965913/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1473/10000 : ℝ) ^ (4339/1024 : ℝ) ≤ (29882821465983393/100000000000000000000 : ℝ) := by
    have hpowers : (1473/10000 : ℝ)^4339 ≤ (29882821465983393/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1473 : ℕ)^4339*100000000000000000000^1024 ≤ 29882821465983393^1024*10000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1473 10000 29882821465983393 100000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1473/10000 : ℝ)) (X := (29882821465983393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562796484952965913/1562500000000000000 : ℝ) ≤ (2500111944167001/2500000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (1562796484952965913/1562500000000000000 : ℝ)^1024 ≤ (2500111944167001/2500000000000000 : ℝ)^4339 := by
      have hnat : (1562796484952965913 : ℕ)^1024*2500000000000000^4339 ≤ 2500111944167001^4339*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562796484952965913 1562500000000000000 2500111944167001 2500000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500111944167001/2500000000000000 : ℝ)) (X := (1562796484952965913/1562500000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039370339960892609/100000000000000000000 : ℝ) ≤ (5000464498344311/5000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (100039370339960892609/100000000000000000000 : ℝ)^1024 ≤ (5000464498344311/5000000000000000 : ℝ)^4339 := by
      have hnat : (100039370339960892609 : ℕ)^1024*5000000000000000^4339 ≤ 5000464498344311^4339*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039370339960892609 100000000000000000000 5000464498344311 5000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000464498344311/5000000000000000 : ℝ)) (X := (100039370339960892609/100000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029882821465983393/50000000000000000000 : ℝ) ≤ (250035255417731/250000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (50029882821465983393/50000000000000000000 : ℝ)^1024 ≤ (250035255417731/250000000000000 : ℝ)^4339 := by
      have hnat : (50029882821465983393 : ℕ)^1024*250000000000000^4339 ≤ 250035255417731^4339*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029882821465983393 50000000000000000000 250035255417731 250000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250035255417731/250000000000000 : ℝ)) (X := (50029882821465983393/50000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(296484952965913/3125000000000000000 : ℝ) ≤ ((873268763884366957/873500000000000000 : ℝ)+2*(240610010309/174700000000000 : ℝ)*(2809/25000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (873268763884366957/873500000000000000 : ℝ)+2*(240610010309/174700000000000 : ℝ)*(2809/25000 : ℝ)=(2500111944167001/2500000000000000 : ℝ) by norm_num, show 1+2*(296484952965913/3125000000000000000 : ℝ)=(1562796484952965913/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29882821465983393/100000000000000000000 : ℝ)+(296484952965913/3125000000000000000 : ℝ) ≤ ((873268763884366957/873500000000000000 : ℝ)+(240610010309/174700000000000 : ℝ)*((1473/10000 : ℝ)+(2809/25000 : ℝ)))^(4339/1024 : ℝ) := by
    rw [show (873268763884366957/873500000000000000 : ℝ)+(240610010309/174700000000000 : ℝ)*((1473/10000 : ℝ)+(2809/25000 : ℝ))=(5000464498344311/5000000000000000 : ℝ) by norm_num, show 1+(29882821465983393/100000000000000000000 : ℝ)+(296484952965913/3125000000000000000 : ℝ)=(100039370339960892609/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29882821465983393/100000000000000000000 : ℝ) ≤ ((873268763884366957/873500000000000000 : ℝ)+2*(240610010309/174700000000000 : ℝ)*(1473/10000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (873268763884366957/873500000000000000 : ℝ)+2*(240610010309/174700000000000 : ℝ)*(1473/10000 : ℝ)=(250035255417731/250000000000000 : ℝ) by norm_num, show 1+2*(29882821465983393/100000000000000000000 : ℝ)=(50029882821465983393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (873268763884366957/873500000000000000 : ℝ)*(X 1 0+X 2 0)+(240610010309/174700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (873268763884366957/873500000000000000 : ℝ)) (alpha := (240610010309/174700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (873268763884366957/873500000000000000 : ℝ)*(X 0 1+X 2 1)+(240610010309/174700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (873268763884366957/873500000000000000 : ℝ)) (alpha := (240610010309/174700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (873268763884366957/873500000000000000 : ℝ)*(X 0 2+X 1 2)+(240610010309/174700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (873268763884366957/873500000000000000 : ℝ)) (alpha := (240610010309/174700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-923645383/5000000000 : ℝ)*X 0 0+(5388344927/10000000000 : ℝ)*X 0 1+(1077669/2000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642813741/5000000000 : ℝ)*X 1 0+(-1988196641/10000000000 : ℝ)*X 1 1+(5388345097/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((528562723/1000000000 : ℝ)*X 2 0+(5388345319/10000000000 : ℝ)*X 2 1+(-49704917/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((139503533/312500000 : ℝ)*X 0 0+(1061731051/2500000000 : ℝ)*X 0 1+(2123462333/5000000000 : ℝ)*X 0 2+(139503533/312500000 : ℝ)*X 1 0+(1061731051/2500000000 : ℝ)*X 1 1+(2123462333/5000000000 : ℝ)*X 1 2+(139503533/312500000 : ℝ)*X 2 0+(1061731051/2500000000 : ℝ)*X 2 1+(2123462333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-272330193/1250000000 : ℝ)*X 0 0+(2632851497/5000000000 : ℝ)*X 0 1+(2632851527/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((537163127/1000000000 : ℝ)*X 1 0+(-1018834023/5000000000 : ℝ)*X 1 1+(5265703221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1074326373/2000000000 : ℝ)*X 2 0+(5265702759/10000000000 : ℝ)*X 2 1+(-2037667863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((416847059/1000000000 : ℝ)*X 0 0+(4394693351/10000000000 : ℝ)*X 0 1+(34333541/78125000 : ℝ)*X 0 2+(416847059/1000000000 : ℝ)*X 1 0+(4394693351/10000000000 : ℝ)*X 1 1+(34333541/78125000 : ℝ)*X 1 2+(416847059/1000000000 : ℝ)*X 2 0+(4394693351/10000000000 : ℝ)*X 2 1+(34333541/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-421792681/2000000000 : ℝ)*X 0 0+(5181097011/10000000000 : ℝ)*X 0 1+(270117343/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637901311/5000000000 : ℝ)*X 1 0+(-495604859/2500000000 : ℝ)*X 1 1+(337646729/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275803281/10000000000 : ℝ)*X 2 0+(1350586819/2500000000 : ℝ)*X 2 1+(-991209537/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2248654641/5000000000 : ℝ)*X 0 0+(211501959/500000000 : ℝ)*X 0 1+(4230038833/10000000000 : ℝ)*X 0 2+(2248654641/5000000000 : ℝ)*X 1 0+(211501959/500000000 : ℝ)*X 1 1+(4230038833/10000000000 : ℝ)*X 1 2+(2248654641/5000000000 : ℝ)*X 2 0+(211501959/500000000 : ℝ)*X 2 1+(4230038833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-479308839/2500000000 : ℝ)*X 0 0+(5470828969/10000000000 : ℝ)*X 0 1+(656825543/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5379412057/10000000000 : ℝ)*X 1 0+(-51051061/250000000 : ℝ)*X 1 1+(1313651297/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2689706129/5000000000 : ℝ)*X 2 0+(5254604641/10000000000 : ℝ)*X 2 1+(-2042042903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4141269519/10000000000 : ℝ)*X 0 0+(4408054193/10000000000 : ℝ)*X 0 1+(2204026811/5000000000 : ℝ)*X 0 2+(4141269519/10000000000 : ℝ)*X 1 0+(4408054193/10000000000 : ℝ)*X 1 1+(2204026811/5000000000 : ℝ)*X 1 2+(4141269519/10000000000 : ℝ)*X 2 0+(4408054193/10000000000 : ℝ)*X 2 1+(2204026811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7859/12500 : ℝ) ≤ (-27458363020447048561428547293909/43675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5178493/25000000000000 : ℝ)*(upper0) + (3313609/100000000000000 : ℝ)*(lower2) + (159560627/100000000000000 : ℝ)*(upper4) + (78802097/100000000000000 : ℝ)*(upper5) + (2962870850023179/100000000000000 : ℝ)*(major0) + (2962870850023179/100000000000000 : ℝ)*(major1) + (2962870850023179/100000000000000 : ℝ)*(major2) + (141911351/1562500000000 : ℝ)*(sp2) + (9383287/250000000000 : ℝ)*(sp3) + (40501875774753/1000000000000 : ℝ)*(sp4) + (253137032965059/6250000000000 : ℝ)*(sp5) + (50627293063931/1250000000000 : ℝ)*(sp6) + (1896502002401039/100000000000000 : ℝ)*(sp7) + (4949965643/100000000000000 : ℝ)*(sp8) + (1896505755715839/100000000000000 : ℝ)*(f.failure) + (253137032965059/6250000000000 : ℝ)*(f.sum) + (49235471520507/4367500000000000000000000000 : ℝ)*base66 + (913300957602551303/87350000000000000000000000000000 : ℝ)*base67 + (915293717701051303/87350000000000000000000000000000 : ℝ)*base69 + (449993192181751303/87350000000000000000000000000000 : ℝ)*base71 + (347648309887/68242187500000000000000000 : ℝ)*base73 + (160821896132348697/87350000000000000000000000000000 : ℝ)*base76 + (1414073368662248697/87350000000000000000000000000000 : ℝ)*base78 + (1903847244249501303/87350000000000000000000000000000 : ℝ)*base79 + (1941100657991/8735000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (21843177/5000000000000000000000 : ℝ)*base89 + (21843177/5000000000000000000000 : ℝ)*base91 + (21843177/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (7377/12500 : ℝ) ≤ (6444027252108937850947070320719/10918750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2731283/5000000000000 : ℝ)*(lower1) + (1326961/5000000000000 : ℝ)*(upper2) + (875497/2000000000000 : ℝ)*(lower4) + (758206725753039/25000000000000 : ℝ)*(major0) + (758206725753039/25000000000000 : ℝ)*(major1) + (758206725753039/25000000000000 : ℝ)*(major2) + (256543202015937/6250000000000 : ℝ)*(sp0) + (410469190211399/10000000000000 : ℝ)*(sp1) + (2052344025355321/50000000000000 : ℝ)*(sp2) + (776512814627/40000000000 : ℝ)*(sp3) + (5272074117/100000000000000 : ℝ)*(sp5) + (4561738733/50000000000000 : ℝ)*(sp6) + (965251813/50000000000000 : ℝ)*(sp7) + (1485483279/25000000000000 : ℝ)*(sp12) + (970641983535563/50000000000000 : ℝ)*(f.failure) + (1026174293547027/25000000000000 : ℝ)*(f.sum) + (3394397637973/1091875000000000000000000000 : ℝ)*base65 + (135536839325287677/21837500000000000000000000000000 : ℝ)*base68 + (20775195990112677/21837500000000000000000000000000 : ℝ)*base70 + (391272596164562323/21837500000000000000000000000000 : ℝ)*base71 + (4060565107493/4367500000000000000000000000 : ℝ)*base74 + (127065945956124823/21837500000000000000000000000000 : ℝ)*base75 + (91456783748687677/21837500000000000000000000000000 : ℝ)*base78 + (114744274706387677/21837500000000000000000000000000 : ℝ)*base80 + (7493598196673/4367500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6654909/2500000000000000000000 : ℝ)*base89 + (6654909/2500000000000000000000 : ℝ)*base91 + (6654909/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40087/50000 : ℝ) ≤ (7003396462526810138460172707/8735000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216706979/100000000000000 : ℝ)*(upper0) + (187989469/100000000000000 : ℝ)*(upper3) + (200477971/50000000000000 : ℝ)*(upper4) + (1671619152439523/50000000000000 : ℝ)*(major0) + (1671619152439523/50000000000000 : ℝ)*(major1) + (1671619152439523/50000000000000 : ℝ)*(major2) + (2431122503/100000000000000 : ℝ)*(sp0) + (127694107137/100000000000000 : ℝ)*(sp1) + (232656326623/100000000000000 : ℝ)*(sp2) + (42795772133/50000000000000 : ℝ)*(sp3) + (4519773373074511/100000000000000 : ℝ)*(sp8) + (4519648110089877/100000000000000 : ℝ)*(sp9) + (4519543147870391/100000000000000 : ℝ)*(sp10) + (213988979343857/10000000000000 : ℝ)*(sp11) + (534993846245709/25000000000000 : ℝ)*(f.failure) + (2259887902098507/50000000000000 : ℝ)*(f.sum) + (10046152270291/8735000000000000000000000000 : ℝ)*base66 + (74960425534973489/43675000000000000000000000000000 : ℝ)*base68 + (189810148739526511/43675000000000000000000000000000 : ℝ)*base69 + (122049692367623489/43675000000000000000000000000000 : ℝ)*base72 + (238208233160911/8735000000000000000000000000 : ℝ)*base74 + (66942146932551511/43675000000000000000000000000000 : ℝ)*base75 + (18081517486101511/43675000000000000000000000000000 : ℝ)*base77 + (687242598109898489/43675000000000000000000000000000 : ℝ)*base80 + (4596613360547/4367500000000000000000000000 : ℝ)*base81 + (1820587/1250000000000000000000 : ℝ)*base89 + (1820587/1250000000000000000000 : ℝ)*base91 + (1820587/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84499/100000 : ℝ) ≤ (-9225969480421136909279618234541/10918750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38345239/100000000000000 : ℝ)*(lower0) + (13225909/50000000000000 : ℝ)*(lower1) + (63443111/25000000000000 : ℝ)*(upper3) + (35091737/100000000000000 : ℝ)*(lower4) + (845032799376271/25000000000000 : ℝ)*(major0) + (845032799376271/25000000000000 : ℝ)*(major1) + (845032799376271/25000000000000 : ℝ)*(major2) + (6506947211/100000000000000 : ℝ)*(sp0) + (82290814401/50000000000000 : ℝ)*(sp6) + (781349379/50000000000000 : ℝ)*(sp8) + (231241483549263/5000000000000 : ℝ)*(sp12) + (4624837740631229/100000000000000 : ℝ)*(sp13) + (4624673159002427/100000000000000 : ℝ)*(sp14) + (1081795089227887/50000000000000 : ℝ)*(sp15) + (1081795089227887/50000000000000 : ℝ)*(f.failure) + (4624837740631229/100000000000000 : ℝ)*(f.sum) + (22419590978203/4367500000000000000000000000 : ℝ)*base65 + (148675968483734847/21837500000000000000000000000000 : ℝ)*base67 + (109662955650977653/21837500000000000000000000000000 : ℝ)*base70 + (108393151096309847/21837500000000000000000000000000 : ℝ)*base71 + (10626440871393/4367500000000000000000000000 : ℝ)*base73 + (72086115348527653/21837500000000000000000000000000 : ℝ)*base76 + (38355968199797347/21837500000000000000000000000000 : ℝ)*base77 + (164969570348109847/21837500000000000000000000000000 : ℝ)*base79 + (78350116818021/8735000000000000000000000000 : ℝ)*base81 + (20871559/2500000000000000000000 : ℝ)*base90 + (20871559/2500000000000000000000 : ℝ)*base92 + (20871559/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1380_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7859/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7377/12500 : ℝ) else (40087/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84499/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1380_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1380_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7859/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7377/12500 : ℝ) else (40087/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84499/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1380_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1380_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1380_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7859/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7377/12500 : ℝ) else (40087/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84499/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1380_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
