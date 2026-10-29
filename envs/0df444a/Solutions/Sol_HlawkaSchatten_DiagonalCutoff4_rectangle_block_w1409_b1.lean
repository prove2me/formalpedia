-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1409_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:40.310576+00:00
-- url     : https://prove2.me/submissions/a5aeee57-3928-4a9a-9270-c432ff5e2804

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
theorem support_rectangle_w1409_s3_0 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1986284449/10000000000 : ℝ)*x 0 + (5419355863/10000000000 : ℝ)*x 1 + (5237119313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986284449/10000000000 : ℝ)^4369 ≤ (302755398351/2500000000000 : ℝ)^3345 := by
    have hnat : (1986284449 : ℕ)^4369*2500000000000^3345 ≤ 302755398351^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986284449 10000000000 302755398351 2500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419355863/10000000000 : ℝ)^4369 ≤ (44926383079297/100000000000000 : ℝ)^3345 := by
    have hnat : (5419355863 : ℕ)^4369*100000000000000^3345 ≤ 44926383079297^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419355863 10000000000 44926383079297 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237119313/10000000000 : ℝ)^4369 ≤ (42963400979661/100000000000000 : ℝ)^3345 := by
    have hnat : (5237119313 : ℕ)^4369*100000000000000^3345 ≤ 42963400979661^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237119313 10000000000 42963400979661 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1986284449/10000000000 : ℝ), (5419355863/10000000000 : ℝ), (5237119313/10000000000 : ℝ)] ![(302755398351/2500000000000 : ℝ), (44926383079297/100000000000000 : ℝ), (42963400979661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1986284449/10000000000 : ℝ)|^4369 ≤ (302755398351/2500000000000 : ℝ)^3345
        have hw : |(-1986284449/10000000000 : ℝ)|=(1986284449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419355863/10000000000 : ℝ)|^4369 ≤ (44926383079297/100000000000000 : ℝ)^3345
        have hw : |(5419355863/10000000000 : ℝ)|=(5419355863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237119313/10000000000 : ℝ)|^4369 ≤ (42963400979661/100000000000000 : ℝ)^3345
        have hw : |(5237119313/10000000000 : ℝ)|=(5237119313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s3_1 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337585613/2500000000 : ℝ)*x 0 + (-2079279341/10000000000 : ℝ)*x 1 + (1309279809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337585613/2500000000 : ℝ)^4369 ≤ (5522572680669/12500000000000 : ℝ)^3345 := by
    have hnat : (1337585613 : ℕ)^4369*12500000000000^3345 ≤ 5522572680669^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337585613 2500000000 5522572680669 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079279341/10000000000 : ℝ)^4369 ≤ (6428009192707/50000000000000 : ℝ)^3345 := by
    have hnat : (2079279341 : ℕ)^4369*50000000000000^3345 ≤ 6428009192707^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079279341 10000000000 6428009192707 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309279809/2500000000 : ℝ)^4369 ≤ (21481700077303/50000000000000 : ℝ)^3345 := by
    have hnat : (1309279809 : ℕ)^4369*50000000000000^3345 ≤ 21481700077303^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309279809 2500000000 21481700077303 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337585613/2500000000 : ℝ), (-2079279341/10000000000 : ℝ), (1309279809/2500000000 : ℝ)] ![(5522572680669/12500000000000 : ℝ), (6428009192707/50000000000000 : ℝ), (21481700077303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337585613/2500000000 : ℝ)|^4369 ≤ (5522572680669/12500000000000 : ℝ)^3345
        have hw : |(1337585613/2500000000 : ℝ)|=(1337585613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079279341/10000000000 : ℝ)|^4369 ≤ (6428009192707/50000000000000 : ℝ)^3345
        have hw : |(-2079279341/10000000000 : ℝ)|=(2079279341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309279809/2500000000 : ℝ)|^4369 ≤ (21481700077303/50000000000000 : ℝ)^3345
        have hw : |(1309279809/2500000000 : ℝ)|=(1309279809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s3_2 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350342413/10000000000 : ℝ)*x 0 + (5237119333/10000000000 : ℝ)*x 1 + (-64977477/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350342413/10000000000 : ℝ)^4369 ≤ (22090290512361/50000000000000 : ℝ)^3345 := by
    have hnat : (5350342413 : ℕ)^4369*50000000000000^3345 ≤ 22090290512361^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350342413 10000000000 22090290512361 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237119333/10000000000 : ℝ)^4369 ≤ (42963401193961/100000000000000 : ℝ)^3345 := by
    have hnat : (5237119333 : ℕ)^4369*100000000000000^3345 ≤ 42963401193961^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237119333 10000000000 42963401193961 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64977477/312500000 : ℝ)^4369 ≤ (6428008881793/50000000000000 : ℝ)^3345 := by
    have hnat : (64977477 : ℕ)^4369*50000000000000^3345 ≤ 6428008881793^3345*312500000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64977477 312500000 6428008881793 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350342413/10000000000 : ℝ), (5237119333/10000000000 : ℝ), (-64977477/312500000 : ℝ)] ![(22090290512361/50000000000000 : ℝ), (42963401193961/100000000000000 : ℝ), (6428008881793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350342413/10000000000 : ℝ)|^4369 ≤ (22090290512361/50000000000000 : ℝ)^3345
        have hw : |(5350342413/10000000000 : ℝ)|=(5350342413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237119333/10000000000 : ℝ)|^4369 ≤ (42963401193961/100000000000000 : ℝ)^3345
        have hw : |(5237119333/10000000000 : ℝ)|=(5237119333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64977477/312500000 : ℝ)|^4369 ≤ (6428008881793/50000000000000 : ℝ)^3345
        have hw : |(-64977477/312500000 : ℝ)|=(64977477/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s3_3 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4308675079/10000000000 : ℝ)*x 0 + (4117029237/10000000000 : ℝ)*x 1 + (1127095193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308675079/10000000000 : ℝ)^4369 ≤ (33297062826207/100000000000000 : ℝ)^3345 := by
    have hnat : (4308675079 : ℕ)^4369*100000000000000^3345 ≤ 33297062826207^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308675079 10000000000 33297062826207 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4117029237/10000000000 : ℝ)^4369 ≤ (6275193044251/20000000000000 : ℝ)^3345 := by
    have hnat : (4117029237 : ℕ)^4369*20000000000000^3345 ≤ 6275193044251^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4117029237 10000000000 6275193044251 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127095193/2500000000 : ℝ)^4369 ≤ (17663485970627/50000000000000 : ℝ)^3345 := by
    have hnat : (1127095193 : ℕ)^4369*50000000000000^3345 ≤ 17663485970627^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127095193 2500000000 17663485970627 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308675079/10000000000 : ℝ), (4117029237/10000000000 : ℝ), (1127095193/2500000000 : ℝ)] ![(33297062826207/100000000000000 : ℝ), (6275193044251/20000000000000 : ℝ), (17663485970627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308675079/10000000000 : ℝ)|^4369 ≤ (33297062826207/100000000000000 : ℝ)^3345
        have hw : |(4308675079/10000000000 : ℝ)|=(4308675079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4117029237/10000000000 : ℝ)|^4369 ≤ (6275193044251/20000000000000 : ℝ)^3345
        have hw : |(4117029237/10000000000 : ℝ)|=(4117029237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127095193/2500000000 : ℝ)|^4369 ≤ (17663485970627/50000000000000 : ℝ)^3345
        have hw : |(1127095193/2500000000 : ℝ)|=(1127095193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s3_4 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1986300423/10000000000 : ℝ)*x 0 + (5237853153/10000000000 : ℝ)*x 1 + (5418617887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986300423/10000000000 : ℝ)^4369 ≤ (6055171570457/50000000000000 : ℝ)^3345 := by
    have hnat : (1986300423 : ℕ)^4369*50000000000000^3345 ≤ 6055171570457^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986300423 10000000000 6055171570457 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237853153/10000000000 : ℝ)^4369 ≤ (42971264242667/100000000000000 : ℝ)^3345 := by
    have hnat : (5237853153 : ℕ)^4369*100000000000000^3345 ≤ 42971264242667^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237853153 10000000000 42971264242667 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418617887/10000000000 : ℝ)^4369 ≤ (4491839259883/10000000000000 : ℝ)^3345 := by
    have hnat : (5418617887 : ℕ)^4369*10000000000000^3345 ≤ 4491839259883^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418617887 10000000000 4491839259883 10000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1986300423/10000000000 : ℝ), (5237853153/10000000000 : ℝ), (5418617887/10000000000 : ℝ)] ![(6055171570457/50000000000000 : ℝ), (42971264242667/100000000000000 : ℝ), (4491839259883/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1986300423/10000000000 : ℝ)|^4369 ≤ (6055171570457/50000000000000 : ℝ)^3345
        have hw : |(-1986300423/10000000000 : ℝ)|=(1986300423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237853153/10000000000 : ℝ)|^4369 ≤ (42971264242667/100000000000000 : ℝ)^3345
        have hw : |(5237853153/10000000000 : ℝ)|=(5237853153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418617887/10000000000 : ℝ)|^4369 ≤ (4491839259883/10000000000000 : ℝ)^3345
        have hw : |(5418617887/10000000000 : ℝ)|=(5418617887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s3_5 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303060763/10000000000 : ℝ)*x 0 + (-1897780747/10000000000 : ℝ)*x 1 + (1354654467/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303060763/10000000000 : ℝ)^4369 ≤ (10917830322281/25000000000000 : ℝ)^3345 := by
    have hnat : (5303060763 : ℕ)^4369*25000000000000^3345 ≤ 10917830322281^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303060763 10000000000 10917830322281 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1897780747/10000000000 : ℝ)^4369 ≤ (356571447207/3125000000000 : ℝ)^3345 := by
    have hnat : (1897780747 : ℕ)^4369*3125000000000^3345 ≤ 356571447207^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897780747 10000000000 356571447207 3125000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354654467/2500000000 : ℝ)^4369 ≤ (44918392393111/100000000000000 : ℝ)^3345 := by
    have hnat : (1354654467 : ℕ)^4369*100000000000000^3345 ≤ 44918392393111^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354654467 2500000000 44918392393111 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303060763/10000000000 : ℝ), (-1897780747/10000000000 : ℝ), (1354654467/2500000000 : ℝ)] ![(10917830322281/25000000000000 : ℝ), (356571447207/3125000000000 : ℝ), (44918392393111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303060763/10000000000 : ℝ)|^4369 ≤ (10917830322281/25000000000000 : ℝ)^3345
        have hw : |(5303060763/10000000000 : ℝ)|=(5303060763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1897780747/10000000000 : ℝ)|^4369 ≤ (356571447207/3125000000000 : ℝ)^3345
        have hw : |(-1897780747/10000000000 : ℝ)|=(1897780747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354654467/2500000000 : ℝ)|^4369 ≤ (44918392393111/100000000000000 : ℝ)^3345
        have hw : |(1354654467/2500000000 : ℝ)|=(1354654467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s3_6 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303060677/10000000000 : ℝ)*x 0 + (1354654487/2500000000 : ℝ)*x 1 + (-1897780753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303060677/10000000000 : ℝ)^4369 ≤ (21835660182049/50000000000000 : ℝ)^3345 := by
    have hnat : (5303060677 : ℕ)^4369*50000000000000^3345 ≤ 21835660182049^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303060677 10000000000 21835660182049 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354654487/2500000000 : ℝ)^4369 ≤ (22459196629649/50000000000000 : ℝ)^3345 := by
    have hnat : (1354654487 : ℕ)^4369*50000000000000^3345 ≤ 22459196629649^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354654487 2500000000 22459196629649 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1897780753/10000000000 : ℝ)^4369 ≤ (5705143178871/50000000000000 : ℝ)^3345 := by
    have hnat : (1897780753 : ℕ)^4369*50000000000000^3345 ≤ 5705143178871^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897780753 10000000000 5705143178871 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303060677/10000000000 : ℝ), (1354654487/2500000000 : ℝ), (-1897780753/10000000000 : ℝ)] ![(21835660182049/50000000000000 : ℝ), (22459196629649/50000000000000 : ℝ), (5705143178871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303060677/10000000000 : ℝ)|^4369 ≤ (21835660182049/50000000000000 : ℝ)^3345
        have hw : |(5303060677/10000000000 : ℝ)|=(5303060677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354654487/2500000000 : ℝ)|^4369 ≤ (22459196629649/50000000000000 : ℝ)^3345
        have hw : |(1354654487/2500000000 : ℝ)|=(1354654487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1897780753/10000000000 : ℝ)|^4369 ≤ (5705143178871/50000000000000 : ℝ)^3345
        have hw : |(-1897780753/10000000000 : ℝ)|=(1897780753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s3_7 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4308709591/10000000000 : ℝ)*x 0 + (140837657/312500000 : ℝ)*x 1 + (2059307113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308709591/10000000000 : ℝ)^4369 ≤ (8324352794643/25000000000000 : ℝ)^3345 := by
    have hnat : (4308709591 : ℕ)^4369*25000000000000^3345 ≤ 8324352794643^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308709591 10000000000 8324352794643 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140837657/312500000 : ℝ)^4369 ≤ (8827711405297/25000000000000 : ℝ)^3345 := by
    have hnat : (140837657 : ℕ)^4369*25000000000000^3345 ≤ 8827711405297^3345*312500000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140837657 312500000 8827711405297 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2059307113/5000000000 : ℝ)^4369 ≤ (7847935795831/25000000000000 : ℝ)^3345 := by
    have hnat : (2059307113 : ℕ)^4369*25000000000000^3345 ≤ 7847935795831^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059307113 5000000000 7847935795831 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308709591/10000000000 : ℝ), (140837657/312500000 : ℝ), (2059307113/5000000000 : ℝ)] ![(8324352794643/25000000000000 : ℝ), (8827711405297/25000000000000 : ℝ), (7847935795831/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308709591/10000000000 : ℝ)|^4369 ≤ (8324352794643/25000000000000 : ℝ)^3345
        have hw : |(4308709591/10000000000 : ℝ)|=(4308709591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140837657/312500000 : ℝ)|^4369 ≤ (8827711405297/25000000000000 : ℝ)^3345
        have hw : |(140837657/312500000 : ℝ)|=(140837657/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2059307113/5000000000 : ℝ)|^4369 ≤ (7847935795831/25000000000000 : ℝ)^3345
        have hw : |(2059307113/5000000000 : ℝ)|=(2059307113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1409_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15863/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5129/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11099/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7479/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15863/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5129/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15863/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5129/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15863/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5129/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15863/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5129/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15863/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5129/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15863/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5129/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5129/50000 : ℝ) ^ (273/64 : ℝ) ≤ (6047338893649169/100000000000000000000 : ℝ) := by
    have hpowers : (5129/50000 : ℝ)^273 ≤ (6047338893649169/100000000000000000000 : ℝ)^64 := by
      have hnat : (5129 : ℕ)^273*100000000000000000000^64 ≤ 6047338893649169^64*50000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5129 50000 6047338893649169 100000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5129/50000 : ℝ)) (X := (6047338893649169/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hpowhi : (15863/100000 : ℝ) ^ (273/64 : ℝ) ≤ (19413938656204387/50000000000000000000 : ℝ) := by
    have hpowers : (15863/100000 : ℝ)^273 ≤ (19413938656204387/50000000000000000000 : ℝ)^64 := by
      have hnat : (15863 : ℕ)^273*50000000000000000000^64 ≤ 19413938656204387^64*100000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15863 100000 19413938656204387 50000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15863/100000 : ℝ)) (X := (19413938656204387/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006047338893649169/50000000000000000000 : ℝ) ≤ (2000056705021591/2000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (50006047338893649169/50000000000000000000 : ℝ)^64 ≤ (2000056705021591/2000000000000000 : ℝ)^273 := by
      have hnat : (50006047338893649169 : ℕ)^64*2000000000000000^273 ≤ 2000056705021591^273*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006047338893649169 50000000000000000000 2000056705021591 2000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056705021591/2000000000000000 : ℝ)) (X := (50006047338893649169/50000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044875216206057943/100000000000000000000 : ℝ) ≤ (5000525919528753/5000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (100044875216206057943/100000000000000000000 : ℝ)^64 ≤ (5000525919528753/5000000000000000 : ℝ)^273 := by
      have hnat : (100044875216206057943 : ℕ)^64*5000000000000000^273 ≤ 5000525919528753^273*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044875216206057943 100000000000000000000 5000525919528753 5000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000525919528753/5000000000000000 : ℝ)) (X := (100044875216206057943/100000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019413938656204387/25000000000000000000 : ℝ) ≤ (10001820153007057/10000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (25019413938656204387/25000000000000000000 : ℝ)^64 ≤ (10001820153007057/10000000000000000 : ℝ)^273 := by
      have hnat : (25019413938656204387 : ℕ)^64*10000000000000000^273 ≤ 10001820153007057^273*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019413938656204387 25000000000000000000 10001820153007057 10000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001820153007057/10000000000000000 : ℝ)) (X := (25019413938656204387/25000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6047338893649169/100000000000000000000 : ℝ) ≤ ((56035826429241099459/56050000000000000000 : ℝ)+2*(768313949551/560500000000000 : ℝ)*(5129/50000 : ℝ))^(273/64 : ℝ) := by
    rw [show (56035826429241099459/56050000000000000000 : ℝ)+2*(768313949551/560500000000000 : ℝ)*(5129/50000 : ℝ)=(2000056705021591/2000000000000000 : ℝ) by norm_num, show 1+2*(6047338893649169/100000000000000000000 : ℝ)=(50006047338893649169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19413938656204387/50000000000000000000 : ℝ)+(6047338893649169/100000000000000000000 : ℝ) ≤ ((56035826429241099459/56050000000000000000 : ℝ)+(768313949551/560500000000000 : ℝ)*((15863/100000 : ℝ)+(5129/50000 : ℝ)))^(273/64 : ℝ) := by
    rw [show (56035826429241099459/56050000000000000000 : ℝ)+(768313949551/560500000000000 : ℝ)*((15863/100000 : ℝ)+(5129/50000 : ℝ))=(5000525919528753/5000000000000000 : ℝ) by norm_num, show 1+(19413938656204387/50000000000000000000 : ℝ)+(6047338893649169/100000000000000000000 : ℝ)=(100044875216206057943/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19413938656204387/50000000000000000000 : ℝ) ≤ ((56035826429241099459/56050000000000000000 : ℝ)+2*(768313949551/560500000000000 : ℝ)*(15863/100000 : ℝ))^(273/64 : ℝ) := by
    rw [show (56035826429241099459/56050000000000000000 : ℝ)+2*(768313949551/560500000000000 : ℝ)*(15863/100000 : ℝ)=(10001820153007057/10000000000000000 : ℝ) by norm_num, show 1+2*(19413938656204387/50000000000000000000 : ℝ)=(25019413938656204387/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56035826429241099459/56050000000000000000 : ℝ)*(X 1 0+X 2 0)+(768313949551/560500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (5129/50000 : ℝ)) (hi := (15863/100000 : ℝ)) (c := (56035826429241099459/56050000000000000000 : ℝ)) (alpha := (768313949551/560500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56035826429241099459/56050000000000000000 : ℝ)*(X 0 1+X 2 1)+(768313949551/560500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (5129/50000 : ℝ)) (hi := (15863/100000 : ℝ)) (c := (56035826429241099459/56050000000000000000 : ℝ)) (alpha := (768313949551/560500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56035826429241099459/56050000000000000000 : ℝ)*(X 0 2+X 1 2)+(768313949551/560500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (5129/50000 : ℝ)) (hi := (15863/100000 : ℝ)) (c := (56035826429241099459/56050000000000000000 : ℝ)) (alpha := (768313949551/560500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1986284449/10000000000 : ℝ)*X 0 0+(5419355863/10000000000 : ℝ)*X 0 1+(5237119313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337585613/2500000000 : ℝ)*X 1 0+(-2079279341/10000000000 : ℝ)*X 1 1+(1309279809/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350342413/10000000000 : ℝ)*X 2 0+(5237119333/10000000000 : ℝ)*X 2 1+(-64977477/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308675079/10000000000 : ℝ)*X 0 0+(4117029237/10000000000 : ℝ)*X 0 1+(1127095193/2500000000 : ℝ)*X 0 2+(4308675079/10000000000 : ℝ)*X 1 0+(4117029237/10000000000 : ℝ)*X 1 1+(1127095193/2500000000 : ℝ)*X 1 2+(4308675079/10000000000 : ℝ)*X 2 0+(4117029237/10000000000 : ℝ)*X 2 1+(1127095193/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1986300423/10000000000 : ℝ)*X 0 0+(5237853153/10000000000 : ℝ)*X 0 1+(5418617887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303060763/10000000000 : ℝ)*X 1 0+(-1897780747/10000000000 : ℝ)*X 1 1+(1354654467/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303060677/10000000000 : ℝ)*X 2 0+(1354654487/2500000000 : ℝ)*X 2 1+(-1897780753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308709591/10000000000 : ℝ)*X 0 0+(140837657/312500000 : ℝ)*X 0 1+(2059307113/5000000000 : ℝ)*X 0 2+(4308709591/10000000000 : ℝ)*X 1 0+(140837657/312500000 : ℝ)*X 1 1+(2059307113/5000000000 : ℝ)*X 1 2+(4308709591/10000000000 : ℝ)*X 2 0+(140837657/312500000 : ℝ)*X 2 1+(2059307113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6736404169306676074863383883/700625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (179629623/10000000000000 : ℝ)*(base19) + (434767403/25000000000000 : ℝ)*(base23) + (4608597/50000000000000 : ℝ)*(lower2) + (480687/250000000000 : ℝ)*(upper3) + (2033939/781250000000 : ℝ)*(upper5) + (1005339683695793/25000000000000 : ℝ)*(major0) + (1005339683695793/25000000000000 : ℝ)*(major1) + (1005339683695793/25000000000000 : ℝ)*(major2) + (171481407711979/3125000000000 : ℝ)*(sp0) + (5487437467086133/100000000000000 : ℝ)*(sp1) + (21949750097251/400000000000 : ℝ)*(sp2) + (255526307473633/10000000000000 : ℝ)*(sp3) + (17108299517/50000000000000 : ℝ)*(sp4) + (14810952649/100000000000000 : ℝ)*(sp7) + (127763894284449/5000000000000 : ℝ)*(f.failure) + (2743719631691181/50000000000000 : ℝ)*(f.sum) + (71447959981397/28025000000000000000000000000 : ℝ)*base65 + (1447538413907824013/1401250000000000000000000000000000 : ℝ)*base68 + (2637019188512824013/1401250000000000000000000000000000 : ℝ)*base70 + (14687668983724074013/1401250000000000000000000000000000 : ℝ)*base72 + (122585416870947/28025000000000000000000000000 : ℝ)*base73 + (17306172355370324013/1401250000000000000000000000000000 : ℝ)*base76 + (7501004730866574013/1401250000000000000000000000000000 : ℝ)*base78 + (11960121553362824013/1401250000000000000000000000000000 : ℝ)*base80 + (41690552108961/14012500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (372427/100000000000000000000 : ℝ)*base89 + (372427/100000000000000000000 : ℝ)*base91 + (372427/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101248084702607849434321203/10947265625000000000000000000000 : ℝ) := by norm_num
    linear_combination (1277775229/100000000000000 : ℝ)*(base19) + (1311338369/100000000000000 : ℝ)*(base23) + (75995509/50000000000000 : ℝ)*(upper3) + (59925517/100000000000000 : ℝ)*(lower4) + (84733999/50000000000000 : ℝ)*(upper5) + (253378235958563/6250000000000 : ℝ)*(major0) + (253378235958563/6250000000000 : ℝ)*(major1) + (253378235958563/6250000000000 : ℝ)*(major2) + (4660043329/20000000000000 : ℝ)*(sp1) + (76414423/312500000000 : ℝ)*(sp2) + (1106410266505411/20000000000000 : ℝ)*(sp4) + (5532026754535181/100000000000000 : ℝ)*(sp5) + (2766012784286663/50000000000000 : ℝ)*(sp6) + (2576051909856623/100000000000000 : ℝ)*(sp7) + (2576051909856623/100000000000000 : ℝ)*(f.failure) + (1106410266505411/20000000000000 : ℝ)*(f.sum) + (784610048847/437890625000000000000000000 : ℝ)*base65 + (676568106592329917/350312500000000000000000000000000 : ℝ)*base67 + (2756890754987329917/350312500000000000000000000000000 : ℝ)*base69 + (1423623711358267417/350312500000000000000000000000000 : ℝ)*base71 + (3245611412081/875781250000000000000000000 : ℝ)*base74 + (2349244519767642417/350312500000000000000000000000000 : ℝ)*base75 + (75800925022670083/350312500000000000000000000000000 : ℝ)*base78 + (1798669659694517417/350312500000000000000000000000000 : ℝ)*base79 + (1749649393037/1751562500000000000000000000 : ℝ)*base82 + (10034971/2000000000000000000000 : ℝ)*base90 + (10034971/2000000000000000000000 : ℝ)*base92 + (10034971/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1409_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15863/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5129/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7479/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1409_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1409_s4_0 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-993646369/5000000000 : ℝ)*x 0 + (1352710101/2500000000 : ℝ)*x 1 + (5244971119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (993646369/5000000000 : ℝ)^4369 ≤ (189347592601/1562500000000 : ℝ)^3345 := by
    have hnat : (993646369 : ℕ)^4369*1562500000000^3345 ≤ 189347592601^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993646369 5000000000 189347592601 1562500000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352710101/2500000000 : ℝ)^4369 ≤ (11208550421513/25000000000000 : ℝ)^3345 := by
    have hnat : (1352710101 : ℕ)^4369*25000000000000^3345 ≤ 11208550421513^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352710101 2500000000 11208550421513 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244971119/10000000000 : ℝ)^4369 ≤ (2690472022997/6250000000000 : ℝ)^3345 := by
    have hnat : (5244971119 : ℕ)^4369*6250000000000^3345 ≤ 2690472022997^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244971119 10000000000 2690472022997 6250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-993646369/5000000000 : ℝ), (1352710101/2500000000 : ℝ), (5244971119/10000000000 : ℝ)] ![(189347592601/1562500000000 : ℝ), (11208550421513/25000000000000 : ℝ), (2690472022997/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-993646369/5000000000 : ℝ)|^4369 ≤ (189347592601/1562500000000 : ℝ)^3345
        have hw : |(-993646369/5000000000 : ℝ)|=(993646369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352710101/2500000000 : ℝ)|^4369 ≤ (11208550421513/25000000000000 : ℝ)^3345
        have hw : |(1352710101/2500000000 : ℝ)|=(1352710101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244971119/10000000000 : ℝ)|^4369 ≤ (2690472022997/6250000000000 : ℝ)^3345
        have hw : |(5244971119/10000000000 : ℝ)|=(5244971119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s4_1 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348149641/10000000000 : ℝ)*x 0 + (-517945653/2500000000 : ℝ)*x 1 + (5244971533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348149641/10000000000 : ℝ)^4369 ≤ (8831386522379/20000000000000 : ℝ)^3345 := by
    have hnat : (5348149641 : ℕ)^4369*20000000000000^3345 ≤ 8831386522379^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348149641 10000000000 8831386522379 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517945653/2500000000 : ℝ)^4369 ≤ (12795510574329/100000000000000 : ℝ)^3345 := by
    have hnat : (517945653 : ℕ)^4369*100000000000000^3345 ≤ 12795510574329^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517945653 2500000000 12795510574329 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244971533/10000000000 : ℝ)^4369 ≤ (43047556805997/100000000000000 : ℝ)^3345 := by
    have hnat : (5244971533 : ℕ)^4369*100000000000000^3345 ≤ 43047556805997^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244971533 10000000000 43047556805997 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348149641/10000000000 : ℝ), (-517945653/2500000000 : ℝ), (5244971533/10000000000 : ℝ)] ![(8831386522379/20000000000000 : ℝ), (12795510574329/100000000000000 : ℝ), (43047556805997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348149641/10000000000 : ℝ)|^4369 ≤ (8831386522379/20000000000000 : ℝ)^3345
        have hw : |(5348149641/10000000000 : ℝ)|=(5348149641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-517945653/2500000000 : ℝ)|^4369 ≤ (12795510574329/100000000000000 : ℝ)^3345
        have hw : |(-517945653/2500000000 : ℝ)|=(517945653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244971533/10000000000 : ℝ)|^4369 ≤ (43047556805997/100000000000000 : ℝ)^3345
        have hw : |(5244971533/10000000000 : ℝ)|=(5244971533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s4_2 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674074811/5000000000 : ℝ)*x 0 + (5244970757/10000000000 : ℝ)*x 1 + (-2071783669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674074811/5000000000 : ℝ)^4369 ≤ (44156932406999/100000000000000 : ℝ)^3345 := by
    have hnat : (2674074811 : ℕ)^4369*100000000000000^3345 ≤ 44156932406999^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674074811 5000000000 44156932406999 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244970757/10000000000 : ℝ)^4369 ≤ (2690471780459/6250000000000 : ℝ)^3345 := by
    have hnat : (5244970757 : ℕ)^4369*6250000000000^3345 ≤ 2690471780459^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244970757 10000000000 2690471780459 6250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2071783669/10000000000 : ℝ)^4369 ≤ (12795519100899/100000000000000 : ℝ)^3345 := by
    have hnat : (2071783669 : ℕ)^4369*100000000000000^3345 ≤ 12795519100899^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071783669 10000000000 12795519100899 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674074811/5000000000 : ℝ), (5244970757/10000000000 : ℝ), (-2071783669/10000000000 : ℝ)] ![(44156932406999/100000000000000 : ℝ), (2690471780459/6250000000000 : ℝ), (12795519100899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674074811/5000000000 : ℝ)|^4369 ≤ (44156932406999/100000000000000 : ℝ)^3345
        have hw : |(2674074811/5000000000 : ℝ)|=(2674074811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244970757/10000000000 : ℝ)|^4369 ≤ (2690471780459/6250000000000 : ℝ)^3345
        have hw : |(5244970757/10000000000 : ℝ)|=(5244970757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2071783669/10000000000 : ℝ)|^4369 ≤ (12795519100899/100000000000000 : ℝ)^3345
        have hw : |(-2071783669/10000000000 : ℝ)|=(2071783669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s4_3 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4309290087/10000000000 : ℝ)*x 0 + (206726481/500000000 : ℝ)*x 1 + (2245365987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309290087/10000000000 : ℝ)^4369 ≤ (16651635317677/50000000000000 : ℝ)^3345 := by
    have hnat : (4309290087 : ℕ)^4369*50000000000000^3345 ≤ 16651635317677^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309290087 10000000000 16651635317677 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206726481/500000000 : ℝ)^4369 ≤ (1971892364763/6250000000000 : ℝ)^3345 := by
    have hnat : (206726481 : ℕ)^4369*6250000000000^3345 ≤ 1971892364763^3345*500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206726481 500000000 1971892364763 6250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245365987/5000000000 : ℝ)^4369 ≤ (35146451520051/100000000000000 : ℝ)^3345 := by
    have hnat : (2245365987 : ℕ)^4369*100000000000000^3345 ≤ 35146451520051^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245365987 5000000000 35146451520051 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309290087/10000000000 : ℝ), (206726481/500000000 : ℝ), (2245365987/5000000000 : ℝ)] ![(16651635317677/50000000000000 : ℝ), (1971892364763/6250000000000 : ℝ), (35146451520051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309290087/10000000000 : ℝ)|^4369 ≤ (16651635317677/50000000000000 : ℝ)^3345
        have hw : |(4309290087/10000000000 : ℝ)|=(4309290087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(206726481/500000000 : ℝ)|^4369 ≤ (1971892364763/6250000000000 : ℝ)^3345
        have hw : |(206726481/500000000 : ℝ)|=(206726481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245365987/5000000000 : ℝ)|^4369 ≤ (35146451520051/100000000000000 : ℝ)^3345
        have hw : |(2245365987/5000000000 : ℝ)|=(2245365987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s4_4 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1987305087/10000000000 : ℝ)*x 0 + (327848701/625000000 : ℝ)*x 1 + (5410228967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1987305087/10000000000 : ℝ)^4369 ≤ (12118344281373/100000000000000 : ℝ)^3345 := by
    have hnat : (1987305087 : ℕ)^4369*100000000000000^3345 ≤ 12118344281373^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987305087 10000000000 12118344281373 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327848701/625000000 : ℝ)^4369 ≤ (10763517807731/25000000000000 : ℝ)^3345 := by
    have hnat : (327848701 : ℕ)^4369*25000000000000^3345 ≤ 10763517807731^3345*625000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327848701 625000000 10763517807731 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410228967/10000000000 : ℝ)^4369 ≤ (21888468983/48828125000 : ℝ)^3345 := by
    have hnat : (5410228967 : ℕ)^4369*48828125000^3345 ≤ 21888468983^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410228967 10000000000 21888468983 48828125000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1987305087/10000000000 : ℝ), (327848701/625000000 : ℝ), (5410228967/10000000000 : ℝ)] ![(12118344281373/100000000000000 : ℝ), (10763517807731/25000000000000 : ℝ), (21888468983/48828125000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1987305087/10000000000 : ℝ)|^4369 ≤ (12118344281373/100000000000000 : ℝ)^3345
        have hw : |(-1987305087/10000000000 : ℝ)|=(1987305087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327848701/625000000 : ℝ)|^4369 ≤ (10763517807731/25000000000000 : ℝ)^3345
        have hw : |(327848701/625000000 : ℝ)|=(327848701/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410228967/10000000000 : ℝ)|^4369 ≤ (21888468983/48828125000 : ℝ)^3345
        have hw : |(5410228967/10000000000 : ℝ)|=(5410228967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s4_5 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305114587/10000000000 : ℝ)*x 0 + (-381304869/2000000000 : ℝ)*x 1 + (1082045857/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305114587/10000000000 : ℝ)^4369 ≤ (43693413776609/100000000000000 : ℝ)^3345 := by
    have hnat : (5305114587 : ℕ)^4369*100000000000000^3345 ≤ 43693413776609^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305114587 10000000000 43693413776609 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (381304869/2000000000 : ℝ)^4369 ≤ (5739499143887/50000000000000 : ℝ)^3345 := by
    have hnat : (381304869 : ℕ)^4369*50000000000000^3345 ≤ 5739499143887^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381304869 2000000000 5739499143887 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082045857/2000000000 : ℝ)^4369 ≤ (11206896979661/25000000000000 : ℝ)^3345 := by
    have hnat : (1082045857 : ℕ)^4369*25000000000000^3345 ≤ 11206896979661^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082045857 2000000000 11206896979661 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305114587/10000000000 : ℝ), (-381304869/2000000000 : ℝ), (1082045857/2000000000 : ℝ)] ![(43693413776609/100000000000000 : ℝ), (5739499143887/50000000000000 : ℝ), (11206896979661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305114587/10000000000 : ℝ)|^4369 ≤ (43693413776609/100000000000000 : ℝ)^3345
        have hw : |(5305114587/10000000000 : ℝ)|=(5305114587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-381304869/2000000000 : ℝ)|^4369 ≤ (5739499143887/50000000000000 : ℝ)^3345
        have hw : |(-381304869/2000000000 : ℝ)|=(381304869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082045857/2000000000 : ℝ)|^4369 ≤ (11206896979661/25000000000000 : ℝ)^3345
        have hw : |(1082045857/2000000000 : ℝ)|=(1082045857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s4_6 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061022913/2000000000 : ℝ)*x 0 + (1352557273/2500000000 : ℝ)*x 1 + (-1906524641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061022913/2000000000 : ℝ)^4369 ≤ (43693413539947/100000000000000 : ℝ)^3345 := by
    have hnat : (1061022913 : ℕ)^4369*100000000000000^3345 ≤ 43693413539947^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061022913 2000000000 43693413539947 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352557273/2500000000 : ℝ)^4369 ≤ (44827585829959/100000000000000 : ℝ)^3345 := by
    have hnat : (1352557273 : ℕ)^4369*100000000000000^3345 ≤ 44827585829959^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352557273 2500000000 44827585829959 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1906524641/10000000000 : ℝ)^4369 ≤ (573950030777/5000000000000 : ℝ)^3345 := by
    have hnat : (1906524641 : ℕ)^4369*5000000000000^3345 ≤ 573950030777^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906524641 10000000000 573950030777 5000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061022913/2000000000 : ℝ), (1352557273/2500000000 : ℝ), (-1906524641/10000000000 : ℝ)] ![(43693413539947/100000000000000 : ℝ), (44827585829959/100000000000000 : ℝ), (573950030777/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061022913/2000000000 : ℝ)|^4369 ≤ (43693413539947/100000000000000 : ℝ)^3345
        have hw : |(1061022913/2000000000 : ℝ)|=(1061022913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352557273/2500000000 : ℝ)|^4369 ≤ (44827585829959/100000000000000 : ℝ)^3345
        have hw : |(1352557273/2500000000 : ℝ)|=(1352557273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1906524641/10000000000 : ℝ)|^4369 ≤ (573950030777/5000000000000 : ℝ)^3345
        have hw : |(-1906524641/10000000000 : ℝ)|=(1906524641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s4_7 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33666539/78125000 : ℝ)*x 0 + (561178207/1250000000 : ℝ)*x 1 + (1033960509/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33666539/78125000 : ℝ)^4369 ≤ (16651771108523/50000000000000 : ℝ)^3345 := by
    have hnat : (33666539 : ℕ)^4369*50000000000000^3345 ≤ 16651771108523^3345*78125000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33666539 78125000 16651771108523 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561178207/1250000000 : ℝ)^4369 ≤ (8783274622367/25000000000000 : ℝ)^3345 := by
    have hnat : (561178207 : ℕ)^4369*25000000000000^3345 ≤ 8783274622367^3345*1250000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561178207 1250000000 8783274622367 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033960509/2500000000 : ℝ)^4369 ≤ (394541990977/1250000000000 : ℝ)^3345 := by
    have hnat : (1033960509 : ℕ)^4369*1250000000000^3345 ≤ 394541990977^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033960509 2500000000 394541990977 1250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33666539/78125000 : ℝ), (561178207/1250000000 : ℝ), (1033960509/2500000000 : ℝ)] ![(16651771108523/50000000000000 : ℝ), (8783274622367/25000000000000 : ℝ), (394541990977/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33666539/78125000 : ℝ)|^4369 ≤ (16651771108523/50000000000000 : ℝ)^3345
        have hw : |(33666539/78125000 : ℝ)|=(33666539/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561178207/1250000000 : ℝ)|^4369 ≤ (8783274622367/25000000000000 : ℝ)^3345
        have hw : |(561178207/1250000000 : ℝ)|=(561178207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1033960509/2500000000 : ℝ)|^4369 ≤ (394541990977/1250000000000 : ℝ)^3345
        have hw : |(1033960509/2500000000 : ℝ)|=(1033960509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1409_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7479/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11267/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (739/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7479/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11099/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7479/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11099/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7479/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11099/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7479/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11099/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7479/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11099/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7479/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11099/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (11099/100000 : ℝ) ^ (273/64 : ℝ) ≤ (8463284272670797/100000000000000000000 : ℝ) := by
    have hpowers : (11099/100000 : ℝ)^273 ≤ (8463284272670797/100000000000000000000 : ℝ)^64 := by
      have hnat : (11099 : ℕ)^273*100000000000000000000^64 ≤ 8463284272670797^64*100000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11099 100000 8463284272670797 100000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11099/100000 : ℝ)) (X := (8463284272670797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hpowhi : (7479/50000 : ℝ) ^ (273/64 : ℝ) ≤ (7555442509823307/25000000000000000000 : ℝ) := by
    have hpowers : (7479/50000 : ℝ)^273 ≤ (7555442509823307/25000000000000000000 : ℝ)^64 := by
      have hnat : (7479 : ℕ)^273*25000000000000000000^64 ≤ 7555442509823307^64*50000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7479 50000 7555442509823307 25000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7479/50000 : ℝ)) (X := (7555442509823307/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008463284272670797/50000000000000000000 : ℝ) ≤ (5000198393810349/5000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (50008463284272670797/50000000000000000000 : ℝ)^64 ≤ (5000198393810349/5000000000000000 : ℝ)^273 := by
      have hnat : (50008463284272670797 : ℕ)^64*5000000000000000^273 ≤ 5000198393810349^273*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008463284272670797 50000000000000000000 5000198393810349 5000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000198393810349/5000000000000000 : ℝ)) (X := (50008463284272670797/50000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001547402172478561/4000000000000000000 : ℝ) ≤ (5000453384054237/5000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (4001547402172478561/4000000000000000000 : ℝ)^64 ≤ (5000453384054237/5000000000000000 : ℝ)^273 := by
      have hnat : (4001547402172478561 : ℕ)^64*5000000000000000^273 ≤ 5000453384054237^273*4000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001547402172478561 4000000000000000000 5000453384054237 5000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000453384054237/5000000000000000 : ℝ)) (X := (4001547402172478561/4000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507555442509823307/12500000000000000000 : ℝ) ≤ (8001133398877/8000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (12507555442509823307/12500000000000000000 : ℝ)^64 ≤ (8001133398877/8000000000000 : ℝ)^273 := by
      have hnat : (12507555442509823307 : ℕ)^64*8000000000000^273 ≤ 8001133398877^273*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507555442509823307 12500000000000000000 8001133398877 8000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (8001133398877/8000000000000 : ℝ)) (X := (12507555442509823307/12500000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8463284272670797/100000000000000000000 : ℝ) ≤ ((19290105328280310967/19295000000000000000 : ℝ)+2*(15936890243/12059375000000 : ℝ)*(11099/100000 : ℝ))^(273/64 : ℝ) := by
    rw [show (19290105328280310967/19295000000000000000 : ℝ)+2*(15936890243/12059375000000 : ℝ)*(11099/100000 : ℝ)=(5000198393810349/5000000000000000 : ℝ) by norm_num, show 1+2*(8463284272670797/100000000000000000000 : ℝ)=(50008463284272670797/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7555442509823307/25000000000000000000 : ℝ)+(8463284272670797/100000000000000000000 : ℝ) ≤ ((19290105328280310967/19295000000000000000 : ℝ)+(15936890243/12059375000000 : ℝ)*((7479/50000 : ℝ)+(11099/100000 : ℝ)))^(273/64 : ℝ) := by
    rw [show (19290105328280310967/19295000000000000000 : ℝ)+(15936890243/12059375000000 : ℝ)*((7479/50000 : ℝ)+(11099/100000 : ℝ))=(5000453384054237/5000000000000000 : ℝ) by norm_num, show 1+(7555442509823307/25000000000000000000 : ℝ)+(8463284272670797/100000000000000000000 : ℝ)=(4001547402172478561/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7555442509823307/25000000000000000000 : ℝ) ≤ ((19290105328280310967/19295000000000000000 : ℝ)+2*(15936890243/12059375000000 : ℝ)*(7479/50000 : ℝ))^(273/64 : ℝ) := by
    rw [show (19290105328280310967/19295000000000000000 : ℝ)+2*(15936890243/12059375000000 : ℝ)*(7479/50000 : ℝ)=(8001133398877/8000000000000 : ℝ) by norm_num, show 1+2*(7555442509823307/25000000000000000000 : ℝ)=(12507555442509823307/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19290105328280310967/19295000000000000000 : ℝ)*(X 1 0+X 2 0)+(15936890243/12059375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (11099/100000 : ℝ)) (hi := (7479/50000 : ℝ)) (c := (19290105328280310967/19295000000000000000 : ℝ)) (alpha := (15936890243/12059375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19290105328280310967/19295000000000000000 : ℝ)*(X 0 1+X 2 1)+(15936890243/12059375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (11099/100000 : ℝ)) (hi := (7479/50000 : ℝ)) (c := (19290105328280310967/19295000000000000000 : ℝ)) (alpha := (15936890243/12059375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19290105328280310967/19295000000000000000 : ℝ)*(X 0 2+X 1 2)+(15936890243/12059375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (11099/100000 : ℝ)) (hi := (7479/50000 : ℝ)) (c := (19290105328280310967/19295000000000000000 : ℝ)) (alpha := (15936890243/12059375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-993646369/5000000000 : ℝ)*X 0 0+(1352710101/2500000000 : ℝ)*X 0 1+(5244971119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348149641/10000000000 : ℝ)*X 1 0+(-517945653/2500000000 : ℝ)*X 1 1+(5244971533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674074811/5000000000 : ℝ)*X 2 0+(5244970757/10000000000 : ℝ)*X 2 1+(-2071783669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4309290087/10000000000 : ℝ)*X 0 0+(206726481/500000000 : ℝ)*X 0 1+(2245365987/5000000000 : ℝ)*X 0 2+(4309290087/10000000000 : ℝ)*X 1 0+(206726481/500000000 : ℝ)*X 1 1+(2245365987/5000000000 : ℝ)*X 1 2+(4309290087/10000000000 : ℝ)*X 2 0+(206726481/500000000 : ℝ)*X 2 1+(2245365987/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1987305087/10000000000 : ℝ)*X 0 0+(327848701/625000000 : ℝ)*X 0 1+(5410228967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305114587/10000000000 : ℝ)*X 1 0+(-381304869/2000000000 : ℝ)*X 1 1+(1082045857/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061022913/2000000000 : ℝ)*X 2 0+(1352557273/2500000000 : ℝ)*X 2 1+(-1906524641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33666539/78125000 : ℝ)*X 0 0+(561178207/1250000000 : ℝ)*X 0 1+(1033960509/2500000000 : ℝ)*X 0 2+(33666539/78125000 : ℝ)*X 1 0+(561178207/1250000000 : ℝ)*X 1 1+(1033960509/2500000000 : ℝ)*X 1 2+(33666539/78125000 : ℝ)*X 2 0+(561178207/1250000000 : ℝ)*X 2 1+(1033960509/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91575100506168698246553/9647500000000000000000000000 : ℝ) := by norm_num
    linear_combination (75906873/100000000000000 : ℝ)*(base21) + (116982431/50000000000000 : ℝ)*(base29) + (164069617/100000000000000 : ℝ)*(upper2) + (107913553/100000000000000 : ℝ)*(upper3) + (50641111/100000000000000 : ℝ)*(upper4) + (2209061556349653/50000000000000 : ℝ)*(major0) + (4418123346664167/100000000000000 : ℝ)*(major1) + (4418123346664167/100000000000000 : ℝ)*(major2) + (3014426289080227/50000000000000 : ℝ)*(sp0) + (753606688829019/12500000000000 : ℝ)*(sp1) + (188400672941329/3125000000000 : ℝ)*(sp2) + (1403696316163877/50000000000000 : ℝ)*(sp3) + (1166436561/100000000000000 : ℝ)*(sp4) + (249223459/781250000000 : ℝ)*(sp6) + (1403696316163877/50000000000000 : ℝ)*(f.failure) + (1205770748919403/20000000000000 : ℝ)*(f.sum) + (63404339511413/19295000000000000000000000000 : ℝ)*base66 + (9963444821418380511/1929500000000000000000000000000000 : ℝ)*base68 + (4445629285090119489/1929500000000000000000000000000000 : ℝ)*base69 + (3582048447344844451/964750000000000000000000000000000 : ℝ)*base71 + (475422875261/141875000000000000000000000 : ℝ)*base74 + (8150647958405180511/1929500000000000000000000000000000 : ℝ)*base76 + (2917771243949155549/964750000000000000000000000000000 : ℝ)*base78 + (3774601808428819489/1929500000000000000000000000000000 : ℝ)*base79 + (1058028580163/283750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3956471/1000000000000000000000 : ℝ)*base89 + (13956471/1000000000000000000000 : ℝ)*base91 + (13956471/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (95455096294769378011985007/9647500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1330446307/100000000000000 : ℝ)*(base19) + (1414868647/100000000000000 : ℝ)*(base23) + (10504069/10000000000000 : ℝ)*(upper2) + (170062419/100000000000000 : ℝ)*(upper3) + (290322241/100000000000000 : ℝ)*(upper5) + (89016822402793/2000000000000 : ℝ)*(major0) + (89016822402793/2000000000000 : ℝ)*(major1) + (89016822402793/2000000000000 : ℝ)*(major2) + (9586830399/25000000000000 : ℝ)*(sp1) + (27451091861/100000000000000 : ℝ)*(sp2) + (1214699907604149/20000000000000 : ℝ)*(sp4) + (6073459860252841/100000000000000 : ℝ)*(sp5) + (1518367668015059/25000000000000 : ℝ)*(sp6) + (707045593112277/25000000000000 : ℝ)*(sp7) + (707045593112277/25000000000000 : ℝ)*(f.failure) + (1214699907604149/20000000000000 : ℝ)*(f.sum) + (17307049777941/3859000000000000000000000000 : ℝ)*base65 + (44987922049389169/38590000000000000000000000000000 : ℝ)*base68 + (372591630234960831/38590000000000000000000000000000 : ℝ)*base69 + (159549455920720831/38590000000000000000000000000000 : ℝ)*base71 + (10142397835229/3859000000000000000000000000 : ℝ)*base74 + (632963958177540831/38590000000000000000000000000000 : ℝ)*base75 + (113275215263110831/38590000000000000000000000000000 : ℝ)*base77 + (830987381772900831/38590000000000000000000000000000 : ℝ)*base79 + (25725082866703/3859000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1070329/500000000000000000000 : ℝ)*base90 + (1070329/500000000000000000000 : ℝ)*base92 + (1070329/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1409_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7479/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (739/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1409_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1409_s5_0 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1987447173/10000000000 : ℝ)*x 0 + (5409468313/10000000000 : ℝ)*x 1 + (5246241507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1987447173/10000000000 : ℝ)^4369 ≤ (6059737976863/50000000000000 : ℝ)^3345 := by
    have hnat : (1987447173 : ℕ)^4369*50000000000000^3345 ≤ 6059737976863^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987447173 10000000000 6059737976863 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409468313/10000000000 : ℝ)^4369 ≤ (44819352703501/100000000000000 : ℝ)^3345 := by
    have hnat : (5409468313 : ℕ)^4369*100000000000000^3345 ≤ 44819352703501^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409468313 10000000000 44819352703501 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246241507/10000000000 : ℝ)^4369 ≤ (43061171322393/100000000000000 : ℝ)^3345 := by
    have hnat : (5246241507 : ℕ)^4369*100000000000000^3345 ≤ 43061171322393^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246241507 10000000000 43061171322393 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1987447173/10000000000 : ℝ), (5409468313/10000000000 : ℝ), (5246241507/10000000000 : ℝ)] ![(6059737976863/50000000000000 : ℝ), (44819352703501/100000000000000 : ℝ), (43061171322393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1987447173/10000000000 : ℝ)|^4369 ≤ (6059737976863/50000000000000 : ℝ)^3345
        have hw : |(-1987447173/10000000000 : ℝ)|=(1987447173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409468313/10000000000 : ℝ)|^4369 ≤ (44819352703501/100000000000000 : ℝ)^3345
        have hw : |(5409468313/10000000000 : ℝ)|=(5409468313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246241507/10000000000 : ℝ)|^4369 ≤ (43061171322393/100000000000000 : ℝ)^3345
        have hw : |(5246241507/10000000000 : ℝ)|=(5246241507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s5_1 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336949269/2500000000 : ℝ)*x 0 + (-129410417/625000000 : ℝ)*x 1 + (327890067/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336949269/2500000000 : ℝ)^4369 ≤ (5519141322141/12500000000000 : ℝ)^3345 := by
    have hnat : (1336949269 : ℕ)^4369*12500000000000^3345 ≤ 5519141322141^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336949269 2500000000 5519141322141 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129410417/625000000 : ℝ)^4369 ≤ (12785702754421/100000000000000 : ℝ)^3345 := by
    have hnat : (129410417 : ℕ)^4369*100000000000000^3345 ≤ 12785702754421^3345*625000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129410417 625000000 12785702754421 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327890067/625000000 : ℝ)^4369 ≤ (8612233331777/20000000000000 : ℝ)^3345 := by
    have hnat : (327890067 : ℕ)^4369*20000000000000^3345 ≤ 8612233331777^3345*625000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327890067 625000000 8612233331777 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336949269/2500000000 : ℝ), (-129410417/625000000 : ℝ), (327890067/625000000 : ℝ)] ![(5519141322141/12500000000000 : ℝ), (12785702754421/100000000000000 : ℝ), (8612233331777/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336949269/2500000000 : ℝ)|^4369 ≤ (5519141322141/12500000000000 : ℝ)^3345
        have hw : |(1336949269/2500000000 : ℝ)|=(1336949269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129410417/625000000 : ℝ)|^4369 ≤ (12785702754421/100000000000000 : ℝ)^3345
        have hw : |(-129410417/625000000 : ℝ)|=(129410417/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327890067/625000000 : ℝ)|^4369 ≤ (8612233331777/20000000000000 : ℝ)^3345
        have hw : |(327890067/625000000 : ℝ)|=(327890067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s5_2 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534779673/1000000000 : ℝ)*x 0 + (5246241209/10000000000 : ℝ)*x 1 + (-258820869/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534779673/1000000000 : ℝ)^4369 ≤ (5519140855741/12500000000000 : ℝ)^3345 := by
    have hnat : (534779673 : ℕ)^4369*12500000000000^3345 ≤ 5519140855741^3345*1000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534779673 1000000000 5519140855741 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246241209/10000000000 : ℝ)^4369 ≤ (21530584063811/50000000000000 : ℝ)^3345 := by
    have hnat : (5246241209 : ℕ)^4369*50000000000000^3345 ≤ 21530584063811^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246241209 10000000000 21530584063811 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258820869/1250000000 : ℝ)^4369 ≤ (12785705012709/100000000000000 : ℝ)^3345 := by
    have hnat : (258820869 : ℕ)^4369*100000000000000^3345 ≤ 12785705012709^3345*1250000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258820869 1250000000 12785705012709 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534779673/1000000000 : ℝ), (5246241209/10000000000 : ℝ), (-258820869/1250000000 : ℝ)] ![(5519140855741/12500000000000 : ℝ), (21530584063811/50000000000000 : ℝ), (12785705012709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534779673/1000000000 : ℝ)|^4369 ≤ (5519140855741/12500000000000 : ℝ)^3345
        have hw : |(534779673/1000000000 : ℝ)|=(534779673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246241209/10000000000 : ℝ)|^4369 ≤ (21530584063811/50000000000000 : ℝ)^3345
        have hw : |(5246241209/10000000000 : ℝ)|=(5246241209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258820869/1250000000 : ℝ)|^4369 ≤ (12785705012709/100000000000000 : ℝ)^3345
        have hw : |(-258820869/1250000000 : ℝ)|=(258820869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s5_3 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2154692123/5000000000 : ℝ)*x 0 + (4137355523/10000000000 : ℝ)*x 1 + (4487883123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154692123/5000000000 : ℝ)^4369 ≤ (8326055271937/25000000000000 : ℝ)^3345 := by
    have hnat : (2154692123 : ℕ)^4369*25000000000000^3345 ≤ 8326055271937^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154692123 5000000000 8326055271937 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4137355523/10000000000 : ℝ)^4369 ≤ (7894611615799/25000000000000 : ℝ)^3345 := by
    have hnat : (4137355523 : ℕ)^4369*25000000000000^3345 ≤ 7894611615799^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137355523 10000000000 7894611615799 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487883123/10000000000 : ℝ)^4369 ≤ (35117332428097/100000000000000 : ℝ)^3345 := by
    have hnat : (4487883123 : ℕ)^4369*100000000000000^3345 ≤ 35117332428097^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487883123 10000000000 35117332428097 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154692123/5000000000 : ℝ), (4137355523/10000000000 : ℝ), (4487883123/10000000000 : ℝ)] ![(8326055271937/25000000000000 : ℝ), (7894611615799/25000000000000 : ℝ), (35117332428097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154692123/5000000000 : ℝ)|^4369 ≤ (8326055271937/25000000000000 : ℝ)^3345
        have hw : |(2154692123/5000000000 : ℝ)|=(2154692123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4137355523/10000000000 : ℝ)|^4369 ≤ (7894611615799/25000000000000 : ℝ)^3345
        have hw : |(4137355523/10000000000 : ℝ)|=(4137355523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487883123/10000000000 : ℝ)|^4369 ≤ (35117332428097/100000000000000 : ℝ)^3345
        have hw : |(4487883123/10000000000 : ℝ)|=(4487883123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s5_4 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1987459393/10000000000 : ℝ)*x 0 + (5246830541/10000000000 : ℝ)*x 1 + (1352218941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1987459393/10000000000 : ℝ)^4369 ≤ (2423914656703/20000000000000 : ℝ)^3345 := by
    have hnat : (1987459393 : ℕ)^4369*20000000000000^3345 ≤ 2423914656703^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987459393 10000000000 2423914656703 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246830541/10000000000 : ℝ)^4369 ≤ (10766871573163/25000000000000 : ℝ)^3345 := by
    have hnat : (5246830541 : ℕ)^4369*25000000000000^3345 ≤ 10766871573163^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246830541 10000000000 10766871573163 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352218941/2500000000 : ℝ)^4369 ≤ (11203235100593/25000000000000 : ℝ)^3345 := by
    have hnat : (1352218941 : ℕ)^4369*25000000000000^3345 ≤ 11203235100593^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352218941 2500000000 11203235100593 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1987459393/10000000000 : ℝ), (5246830541/10000000000 : ℝ), (1352218941/2500000000 : ℝ)] ![(2423914656703/20000000000000 : ℝ), (10766871573163/25000000000000 : ℝ), (11203235100593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1987459393/10000000000 : ℝ)|^4369 ≤ (2423914656703/20000000000000 : ℝ)^3345
        have hw : |(-1987459393/10000000000 : ℝ)|=(1987459393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246830541/10000000000 : ℝ)|^4369 ≤ (10766871573163/25000000000000 : ℝ)^3345
        have hw : |(5246830541/10000000000 : ℝ)|=(5246830541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352218941/2500000000 : ℝ)|^4369 ≤ (11203235100593/25000000000000 : ℝ)^3345
        have hw : |(1352218941/2500000000 : ℝ)|=(1352218941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s5_5 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66318083/125000000 : ℝ)*x 0 + (-953966273/5000000000 : ℝ)*x 1 + (1081775153/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66318083/125000000 : ℝ)^4369 ≤ (43696985836241/100000000000000 : ℝ)^3345 := by
    have hnat : (66318083 : ℕ)^4369*100000000000000^3345 ≤ 43696985836241^3345*125000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66318083 125000000 43696985836241 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (953966273/5000000000 : ℝ)^4369 ≤ (28725184339/250000000000 : ℝ)^3345 := by
    have hnat : (953966273 : ℕ)^4369*250000000000^3345 ≤ 28725184339^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953966273 5000000000 28725184339 250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081775153/2000000000 : ℝ)^4369 ≤ (44812940413193/100000000000000 : ℝ)^3345 := by
    have hnat : (1081775153 : ℕ)^4369*100000000000000^3345 ≤ 44812940413193^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081775153 2000000000 44812940413193 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66318083/125000000 : ℝ), (-953966273/5000000000 : ℝ), (1081775153/2000000000 : ℝ)] ![(43696985836241/100000000000000 : ℝ), (28725184339/250000000000 : ℝ), (44812940413193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66318083/125000000 : ℝ)|^4369 ≤ (43696985836241/100000000000000 : ℝ)^3345
        have hw : |(66318083/125000000 : ℝ)|=(66318083/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-953966273/5000000000 : ℝ)|^4369 ≤ (28725184339/250000000000 : ℝ)^3345
        have hw : |(-953966273/5000000000 : ℝ)|=(953966273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081775153/2000000000 : ℝ)|^4369 ≤ (44812940413193/100000000000000 : ℝ)^3345
        have hw : |(1081775153/2000000000 : ℝ)|=(1081775153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s5_6 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305446637/10000000000 : ℝ)*x 0 + (676109471/1250000000 : ℝ)*x 1 + (-953966273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305446637/10000000000 : ℝ)^4369 ≤ (682765403187/1562500000000 : ℝ)^3345 := by
    have hnat : (5305446637 : ℕ)^4369*1562500000000^3345 ≤ 682765403187^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305446637 10000000000 682765403187 1562500000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676109471/1250000000 : ℝ)^4369 ≤ (44812940445657/100000000000000 : ℝ)^3345 := by
    have hnat : (676109471 : ℕ)^4369*100000000000000^3345 ≤ 44812940445657^3345*1250000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676109471 1250000000 44812940445657 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953966273/5000000000 : ℝ)^4369 ≤ (28725184339/250000000000 : ℝ)^3345 := by
    have hnat : (953966273 : ℕ)^4369*250000000000^3345 ≤ 28725184339^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953966273 5000000000 28725184339 250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305446637/10000000000 : ℝ), (676109471/1250000000 : ℝ), (-953966273/5000000000 : ℝ)] ![(682765403187/1562500000000 : ℝ), (44812940445657/100000000000000 : ℝ), (28725184339/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305446637/10000000000 : ℝ)|^4369 ≤ (682765403187/1562500000000 : ℝ)^3345
        have hw : |(5305446637/10000000000 : ℝ)|=(5305446637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676109471/1250000000 : ℝ)|^4369 ≤ (44812940445657/100000000000000 : ℝ)^3345
        have hw : |(676109471/1250000000 : ℝ)|=(676109471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-953966273/5000000000 : ℝ)|^4369 ≤ (28725184339/250000000000 : ℝ)^3345
        have hw : |(-953966273/5000000000 : ℝ)|=(953966273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s5_7 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134669063/312500000 : ℝ)*x 0 + (560827201/1250000000 : ℝ)*x 1 + (4138626731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134669063/312500000 : ℝ)^4369 ≤ (33304481214369/100000000000000 : ℝ)^3345 := by
    have hnat : (134669063 : ℕ)^4369*100000000000000^3345 ≤ 33304481214369^3345*312500000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134669063 312500000 33304481214369 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560827201/1250000000 : ℝ)^4369 ≤ (35104398976151/100000000000000 : ℝ)^3345 := by
    have hnat : (560827201 : ℕ)^4369*100000000000000^3345 ≤ 35104398976151^3345*1250000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560827201 1250000000 35104398976151 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4138626731/10000000000 : ℝ)^4369 ≤ (15795559898613/50000000000000 : ℝ)^3345 := by
    have hnat : (4138626731 : ℕ)^4369*50000000000000^3345 ≤ 15795559898613^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138626731 10000000000 15795559898613 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134669063/312500000 : ℝ), (560827201/1250000000 : ℝ), (4138626731/10000000000 : ℝ)] ![(33304481214369/100000000000000 : ℝ), (35104398976151/100000000000000 : ℝ), (15795559898613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134669063/312500000 : ℝ)|^4369 ≤ (33304481214369/100000000000000 : ℝ)^3345
        have hw : |(134669063/312500000 : ℝ)|=(134669063/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560827201/1250000000 : ℝ)|^4369 ≤ (35104398976151/100000000000000 : ℝ)^3345
        have hw : |(560827201/1250000000 : ℝ)|=(560827201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4138626731/10000000000 : ℝ)|^4369 ≤ (15795559898613/50000000000000 : ℝ)^3345
        have hw : |(4138626731/10000000000 : ℝ)|=(4138626731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1409_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (739/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5647/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14751/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (739/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (739/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (739/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (739/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (739/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (739/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11267/100000 : ℝ) ^ (273/64 : ℝ) ≤ (9023390561570339/100000000000000000000 : ℝ) := by
    have hpowers : (11267/100000 : ℝ)^273 ≤ (9023390561570339/100000000000000000000 : ℝ)^64 := by
      have hnat : (11267 : ℕ)^273*100000000000000000000^64 ≤ 9023390561570339^64*100000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11267 100000 9023390561570339 100000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11267/100000 : ℝ)) (X := (9023390561570339/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hpowhi : (739/5000 : ℝ) ^ (273/64 : ℝ) ≤ (28717227438980587/100000000000000000000 : ℝ) := by
    have hpowers : (739/5000 : ℝ)^273 ≤ (28717227438980587/100000000000000000000 : ℝ)^64 := by
      have hnat : (739 : ℕ)^273*100000000000000000000^64 ≤ 28717227438980587^64*5000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        739 5000 28717227438980587 100000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (739/5000 : ℝ)) (X := (28717227438980587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009023390561570339/50000000000000000000 : ℝ) ≤ (10000423045499331/10000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (50009023390561570339/50000000000000000000 : ℝ)^64 ≤ (10000423045499331/10000000000000000 : ℝ)^273 := by
      have hnat : (50009023390561570339 : ℕ)^64*10000000000000000^273 ≤ 10000423045499331^273*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009023390561570339 50000000000000000000 10000423045499331 10000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000423045499331/10000000000000000 : ℝ)) (X := (50009023390561570339/50000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018870309000275463/50000000000000000000 : ℝ) ≤ (2500221158487987/2500000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (50018870309000275463/50000000000000000000 : ℝ)^64 ≤ (2500221158487987/2500000000000000 : ℝ)^273 := by
      have hnat : (50018870309000275463 : ℕ)^64*2500000000000000^273 ≤ 2500221158487987^273*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018870309000275463 50000000000000000000 2500221158487987 2500000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500221158487987/2500000000000000 : ℝ)) (X := (50018870309000275463/50000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028717227438980587/50000000000000000000 : ℝ) ≤ (2000269244480913/2000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (50028717227438980587/50000000000000000000 : ℝ)^64 ≤ (2000269244480913/2000000000000000 : ℝ)^273 := by
      have hnat : (50028717227438980587 : ℕ)^64*2000000000000000^273 ≤ 2000269244480913^273*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028717227438980587 50000000000000000000 2000269244480913 2000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000269244480913/2000000000000000 : ℝ)) (X := (50028717227438980587/50000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9023390561570339/100000000000000000000 : ℝ) ≤ ((468281129661971711/468400000000000000 : ℝ)+2*(153862817539/117100000000000 : ℝ)*(11267/100000 : ℝ))^(273/64 : ℝ) := by
    rw [show (468281129661971711/468400000000000000 : ℝ)+2*(153862817539/117100000000000 : ℝ)*(11267/100000 : ℝ)=(10000423045499331/10000000000000000 : ℝ) by norm_num, show 1+2*(9023390561570339/100000000000000000000 : ℝ)=(50009023390561570339/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28717227438980587/100000000000000000000 : ℝ)+(9023390561570339/100000000000000000000 : ℝ) ≤ ((468281129661971711/468400000000000000 : ℝ)+(153862817539/117100000000000 : ℝ)*((739/5000 : ℝ)+(11267/100000 : ℝ)))^(273/64 : ℝ) := by
    rw [show (468281129661971711/468400000000000000 : ℝ)+(153862817539/117100000000000 : ℝ)*((739/5000 : ℝ)+(11267/100000 : ℝ))=(2500221158487987/2500000000000000 : ℝ) by norm_num, show 1+(28717227438980587/100000000000000000000 : ℝ)+(9023390561570339/100000000000000000000 : ℝ)=(50018870309000275463/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28717227438980587/100000000000000000000 : ℝ) ≤ ((468281129661971711/468400000000000000 : ℝ)+2*(153862817539/117100000000000 : ℝ)*(739/5000 : ℝ))^(273/64 : ℝ) := by
    rw [show (468281129661971711/468400000000000000 : ℝ)+2*(153862817539/117100000000000 : ℝ)*(739/5000 : ℝ)=(2000269244480913/2000000000000000 : ℝ) by norm_num, show 1+2*(28717227438980587/100000000000000000000 : ℝ)=(50028717227438980587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (468281129661971711/468400000000000000 : ℝ)*(X 1 0+X 2 0)+(153862817539/117100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (739/5000 : ℝ)) (c := (468281129661971711/468400000000000000 : ℝ)) (alpha := (153862817539/117100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (468281129661971711/468400000000000000 : ℝ)*(X 0 1+X 2 1)+(153862817539/117100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (739/5000 : ℝ)) (c := (468281129661971711/468400000000000000 : ℝ)) (alpha := (153862817539/117100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (468281129661971711/468400000000000000 : ℝ)*(X 0 2+X 1 2)+(153862817539/117100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (739/5000 : ℝ)) (c := (468281129661971711/468400000000000000 : ℝ)) (alpha := (153862817539/117100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1987447173/10000000000 : ℝ)*X 0 0+(5409468313/10000000000 : ℝ)*X 0 1+(5246241507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336949269/2500000000 : ℝ)*X 1 0+(-129410417/625000000 : ℝ)*X 1 1+(327890067/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534779673/1000000000 : ℝ)*X 2 0+(5246241209/10000000000 : ℝ)*X 2 1+(-258820869/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154692123/5000000000 : ℝ)*X 0 0+(4137355523/10000000000 : ℝ)*X 0 1+(4487883123/10000000000 : ℝ)*X 0 2+(2154692123/5000000000 : ℝ)*X 1 0+(4137355523/10000000000 : ℝ)*X 1 1+(4487883123/10000000000 : ℝ)*X 1 2+(2154692123/5000000000 : ℝ)*X 2 0+(4137355523/10000000000 : ℝ)*X 2 1+(4487883123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1987459393/10000000000 : ℝ)*X 0 0+(5246830541/10000000000 : ℝ)*X 0 1+(1352218941/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66318083/125000000 : ℝ)*X 1 0+(-953966273/5000000000 : ℝ)*X 1 1+(1081775153/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305446637/10000000000 : ℝ)*X 2 0+(676109471/1250000000 : ℝ)*X 2 1+(-953966273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((134669063/312500000 : ℝ)*X 0 0+(560827201/1250000000 : ℝ)*X 0 1+(4138626731/10000000000 : ℝ)*X 0 2+(134669063/312500000 : ℝ)*X 1 0+(560827201/1250000000 : ℝ)*X 1 1+(4138626731/10000000000 : ℝ)*X 1 2+(134669063/312500000 : ℝ)*X 2 0+(560827201/1250000000 : ℝ)*X 2 1+(4138626731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10144554717249765768417/1171000000000000000000000000 : ℝ) := by norm_num
    linear_combination (139208403/12500000000000 : ℝ)*(base19) + (905832101/100000000000000 : ℝ)*(base23) + (22361537/50000000000000 : ℝ)*(lower2) + (72776841/50000000000000 : ℝ)*(lower4) + (135689581/50000000000000 : ℝ)*(lower5) + (448967599920829/10000000000000 : ℝ)*(major0) + (448967599920829/10000000000000 : ℝ)*(major1) + (448967599920829/10000000000000 : ℝ)*(major2) + (6126476460502747/100000000000000 : ℝ)*(sp0) + (1225298302488177/20000000000000 : ℝ)*(sp1) + (6126491720276009/100000000000000 : ℝ)*(sp2) + (1426424949386033/50000000000000 : ℝ)*(sp3) + (16165605363/100000000000000 : ℝ)*(sp4) + (9184764557/100000000000000 : ℝ)*(sp7) + (178303692721039/6250000000000 : ℝ)*(f.failure) + (6126492626108109/100000000000000 : ℝ)*(f.sum) + (424675468557/146375000000000000000000000 : ℝ)*base66 + (53627587914719581/4684000000000000000000000000000 : ℝ)*base68 + (5848111108328419/4684000000000000000000000000000 : ℝ)*base69 + (20326026937920419/4684000000000000000000000000000 : ℝ)*base71 + (465363200757/292750000000000000000000000 : ℝ)*base73 + (33291729597572419/4684000000000000000000000000000 : ℝ)*base75 + (41511196346119581/4684000000000000000000000000000 : ℝ)*base78 + (11387780320627581/4684000000000000000000000000000 : ℝ)*base80 + (533793648011/234200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (504997/125000000000000000000 : ℝ)*base89 + (504997/125000000000000000000 : ℝ)*base91 + (504997/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73040332280380988627506809/11710000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1070349613/100000000000000 : ℝ)*(base19) + (23083129/2000000000000 : ℝ)*(base23) + (129291477/100000000000000 : ℝ)*(upper3) + (9858241/25000000000000 : ℝ)*(lower4) + (128135027/100000000000000 : ℝ)*(upper5) + (4522377188313773/100000000000000 : ℝ)*(major0) + (4522377188313773/100000000000000 : ℝ)*(major1) + (4522377188313773/100000000000000 : ℝ)*(major2) + (4460751071/20000000000000 : ℝ)*(sp1) + (11964438477/50000000000000 : ℝ)*(sp2) + (6171115883203253/100000000000000 : ℝ)*(sp4) + (1234218501819657/20000000000000 : ℝ)*(sp5) + (6171090800169849/100000000000000 : ℝ)*(sp6) + (2873638285509879/100000000000000 : ℝ)*(sp7) + (2873638285509879/100000000000000 : ℝ)*(f.failure) + (6171115883203253/100000000000000 : ℝ)*(f.sum) + (381363731639/2927500000000000000000000000 : ℝ)*base66 + (162324306269936397/46840000000000000000000000000000 : ℝ)*base68 + (515504301616176397/46840000000000000000000000000000 : ℝ)*base70 + (114388397300696397/46840000000000000000000000000000 : ℝ)*base72 + (16477516004363/5855000000000000000000000000 : ℝ)*base74 + (6955081460296397/46840000000000000000000000000000 : ℝ)*base76 + (133486360224783603/46840000000000000000000000000000 : ℝ)*base77 + (207036203237736397/46840000000000000000000000000000 : ℝ)*base80 + (13278766959119/2927500000000000000000000000 : ℝ)*base82 + (2735683/2000000000000000000000 : ℝ)*base90 + (2735683/2000000000000000000000 : ℝ)*base92 + (2735683/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1409_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (739/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1409_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1409_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15863/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5129/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1409_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1409_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1409_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15863/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5129/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1409_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
