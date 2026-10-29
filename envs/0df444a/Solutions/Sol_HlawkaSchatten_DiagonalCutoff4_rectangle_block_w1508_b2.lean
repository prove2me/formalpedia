-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1508_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:54.496052+00:00
-- url     : https://prove2.me/submissions/bb6c631d-a50e-4633-afd0-07d4d1536727

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
theorem support_rectangle_w1508_s6_0 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1873944337/10000000000 : ℝ)*x 0 + (5433753673/10000000000 : ℝ)*x 1 + (1304357831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1873944337/10000000000 : ℝ)^4513 ≤ (11463447743349/100000000000000 : ℝ)^3489 := by
    have hnat : (1873944337 : ℕ)^4513*100000000000000^3489 ≤ 11463447743349^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873944337 10000000000 11463447743349 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433753673/10000000000 : ℝ)^4513 ≤ (45431116865209/100000000000000 : ℝ)^3489 := by
    have hnat : (5433753673 : ℕ)^4513*100000000000000^3489 ≤ 45431116865209^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433753673 10000000000 45431116865209 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304357831/2500000000 : ℝ)^4513 ≤ (21552717685859/50000000000000 : ℝ)^3489 := by
    have hnat : (1304357831 : ℕ)^4513*50000000000000^3489 ≤ 21552717685859^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304357831 2500000000 21552717685859 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1873944337/10000000000 : ℝ), (5433753673/10000000000 : ℝ), (1304357831/2500000000 : ℝ)] ![(11463447743349/100000000000000 : ℝ), (45431116865209/100000000000000 : ℝ), (21552717685859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1873944337/10000000000 : ℝ)|^4513 ≤ (11463447743349/100000000000000 : ℝ)^3489
        have hw : |(-1873944337/10000000000 : ℝ)|=(1873944337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433753673/10000000000 : ℝ)|^4513 ≤ (45431116865209/100000000000000 : ℝ)^3489
        have hw : |(5433753673/10000000000 : ℝ)|=(5433753673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304357831/2500000000 : ℝ)|^4513 ≤ (21552717685859/50000000000000 : ℝ)^3489
        have hw : |(1304357831/2500000000 : ℝ)|=(1304357831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s6_1 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351811567/10000000000 : ℝ)*x 0 + (-992371593/5000000000 : ℝ)*x 1 + (1304357831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351811567/10000000000 : ℝ)^4513 ≤ (44546898843249/100000000000000 : ℝ)^3489 := by
    have hnat : (5351811567 : ℕ)^4513*100000000000000^3489 ≤ 44546898843249^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351811567 10000000000 44546898843249 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992371593/5000000000 : ℝ)^4513 ≤ (12347665762709/100000000000000 : ℝ)^3489 := by
    have hnat : (992371593 : ℕ)^4513*100000000000000^3489 ≤ 12347665762709^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992371593 5000000000 12347665762709 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304357831/2500000000 : ℝ)^4513 ≤ (21552717685859/50000000000000 : ℝ)^3489 := by
    have hnat : (1304357831 : ℕ)^4513*50000000000000^3489 ≤ 21552717685859^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304357831 2500000000 21552717685859 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351811567/10000000000 : ℝ), (-992371593/5000000000 : ℝ), (1304357831/2500000000 : ℝ)] ![(44546898843249/100000000000000 : ℝ), (12347665762709/100000000000000 : ℝ), (21552717685859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351811567/10000000000 : ℝ)|^4513 ≤ (44546898843249/100000000000000 : ℝ)^3489
        have hw : |(5351811567/10000000000 : ℝ)|=(5351811567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992371593/5000000000 : ℝ)|^4513 ≤ (12347665762709/100000000000000 : ℝ)^3489
        have hw : |(-992371593/5000000000 : ℝ)|=(992371593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304357831/2500000000 : ℝ)|^4513 ≤ (21552717685859/50000000000000 : ℝ)^3489
        have hw : |(1304357831/2500000000 : ℝ)|=(1304357831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s6_2 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351811567/10000000000 : ℝ)*x 0 + (1304357831/2500000000 : ℝ)*x 1 + (-992371593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351811567/10000000000 : ℝ)^4513 ≤ (44546898843249/100000000000000 : ℝ)^3489 := by
    have hnat : (5351811567 : ℕ)^4513*100000000000000^3489 ≤ 44546898843249^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351811567 10000000000 44546898843249 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304357831/2500000000 : ℝ)^4513 ≤ (21552717685859/50000000000000 : ℝ)^3489 := by
    have hnat : (1304357831 : ℕ)^4513*50000000000000^3489 ≤ 21552717685859^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304357831 2500000000 21552717685859 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992371593/5000000000 : ℝ)^4513 ≤ (12347665762709/100000000000000 : ℝ)^3489 := by
    have hnat : (992371593 : ℕ)^4513*100000000000000^3489 ≤ 12347665762709^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992371593 5000000000 12347665762709 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351811567/10000000000 : ℝ), (1304357831/2500000000 : ℝ), (-992371593/5000000000 : ℝ)] ![(44546898843249/100000000000000 : ℝ), (21552717685859/50000000000000 : ℝ), (12347665762709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351811567/10000000000 : ℝ)|^4513 ≤ (44546898843249/100000000000000 : ℝ)^3489
        have hw : |(5351811567/10000000000 : ℝ)|=(5351811567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304357831/2500000000 : ℝ)|^4513 ≤ (21552717685859/50000000000000 : ℝ)^3489
        have hw : |(1304357831/2500000000 : ℝ)|=(1304357831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-992371593/5000000000 : ℝ)|^4513 ≤ (12347665762709/100000000000000 : ℝ)^3489
        have hw : |(-992371593/5000000000 : ℝ)|=(992371593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s6_3 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067909643/2500000000 : ℝ)*x 0 + (126032167/312500000 : ℝ)*x 1 + (1130544099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067909643/2500000000 : ℝ)^4513 ≤ (3327945928549/10000000000000 : ℝ)^3489 := by
    have hnat : (1067909643 : ℕ)^4513*10000000000000^3489 ≤ 3327945928549^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067909643 2500000000 3327945928549 10000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126032167/312500000 : ℝ)^4513 ≤ (30894887824909/100000000000000 : ℝ)^3489 := by
    have hnat : (126032167 : ℕ)^4513*100000000000000^3489 ≤ 30894887824909^3489*312500000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126032167 312500000 30894887824909 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130544099/2500000000 : ℝ)^4513 ≤ (35825652871583/100000000000000 : ℝ)^3489 := by
    have hnat : (1130544099 : ℕ)^4513*100000000000000^3489 ≤ 35825652871583^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130544099 2500000000 35825652871583 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067909643/2500000000 : ℝ), (126032167/312500000 : ℝ), (1130544099/2500000000 : ℝ)] ![(3327945928549/10000000000000 : ℝ), (30894887824909/100000000000000 : ℝ), (35825652871583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067909643/2500000000 : ℝ)|^4513 ≤ (3327945928549/10000000000000 : ℝ)^3489
        have hw : |(1067909643/2500000000 : ℝ)|=(1067909643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126032167/312500000 : ℝ)|^4513 ≤ (30894887824909/100000000000000 : ℝ)^3489
        have hw : |(126032167/312500000 : ℝ)|=(126032167/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130544099/2500000000 : ℝ)|^4513 ≤ (35825652871583/100000000000000 : ℝ)^3489
        have hw : |(1130544099/2500000000 : ℝ)|=(1130544099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s6_4 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-936986721/5000000000 : ℝ)*x 0 + (2609271991/5000000000 : ℝ)*x 1 + (5432632839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936986721/5000000000 : ℝ)^4513 ≤ (1146367804207/10000000000000 : ℝ)^3489 := by
    have hnat : (936986721 : ℕ)^4513*10000000000000^3489 ≤ 1146367804207^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936986721 5000000000 1146367804207 10000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609271991/5000000000 : ℝ)^4513 ≤ (21558663138831/50000000000000 : ℝ)^3489 := by
    have hnat : (2609271991 : ℕ)^4513*50000000000000^3489 ≤ 21558663138831^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609271991 5000000000 21558663138831 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432632839/10000000000 : ℝ)^4513 ≤ (45418995655067/100000000000000 : ℝ)^3489 := by
    have hnat : (5432632839 : ℕ)^4513*100000000000000^3489 ≤ 45418995655067^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432632839 10000000000 45418995655067 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-936986721/5000000000 : ℝ), (2609271991/5000000000 : ℝ), (5432632839/10000000000 : ℝ)] ![(1146367804207/10000000000000 : ℝ), (21558663138831/50000000000000 : ℝ), (45418995655067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-936986721/5000000000 : ℝ)|^4513 ≤ (1146367804207/10000000000000 : ℝ)^3489
        have hw : |(-936986721/5000000000 : ℝ)|=(936986721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609271991/5000000000 : ℝ)|^4513 ≤ (21558663138831/50000000000000 : ℝ)^3489
        have hw : |(2609271991/5000000000 : ℝ)|=(2609271991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432632839/10000000000 : ℝ)|^4513 ≤ (45418995655067/100000000000000 : ℝ)^3489
        have hw : |(5432632839/10000000000 : ℝ)|=(5432632839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s6_5 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059011781/2000000000 : ℝ)*x 0 + (-1769541579/10000000000 : ℝ)*x 1 + (2716316453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059011781/2000000000 : ℝ)^4513 ≤ (43936815445647/100000000000000 : ℝ)^3489 := by
    have hnat : (1059011781 : ℕ)^4513*100000000000000^3489 ≤ 43936815445647^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059011781 2000000000 43936815445647 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1769541579/10000000000 : ℝ)^4513 ≤ (10644188160099/100000000000000 : ℝ)^3489 := by
    have hnat : (1769541579 : ℕ)^4513*100000000000000^3489 ≤ 10644188160099^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769541579 10000000000 10644188160099 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716316453/5000000000 : ℝ)^4513 ≤ (45418996379613/100000000000000 : ℝ)^3489 := by
    have hnat : (2716316453 : ℕ)^4513*100000000000000^3489 ≤ 45418996379613^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716316453 5000000000 45418996379613 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059011781/2000000000 : ℝ), (-1769541579/10000000000 : ℝ), (2716316453/5000000000 : ℝ)] ![(43936815445647/100000000000000 : ℝ), (10644188160099/100000000000000 : ℝ), (45418996379613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059011781/2000000000 : ℝ)|^4513 ≤ (43936815445647/100000000000000 : ℝ)^3489
        have hw : |(1059011781/2000000000 : ℝ)|=(1059011781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1769541579/10000000000 : ℝ)|^4513 ≤ (10644188160099/100000000000000 : ℝ)^3489
        have hw : |(-1769541579/10000000000 : ℝ)|=(1769541579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716316453/5000000000 : ℝ)|^4513 ≤ (45418996379613/100000000000000 : ℝ)^3489
        have hw : |(2716316453/5000000000 : ℝ)|=(2716316453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s6_6 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295058923/10000000000 : ℝ)*x 0 + (5432632859/10000000000 : ℝ)*x 1 + (-88477081/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295058923/10000000000 : ℝ)^4513 ≤ (43936815638841/100000000000000 : ℝ)^3489 := by
    have hnat : (5295058923 : ℕ)^4513*100000000000000^3489 ≤ 43936815638841^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295058923 10000000000 43936815638841 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432632859/10000000000 : ℝ)^4513 ≤ (45418995871349/100000000000000 : ℝ)^3489 := by
    have hnat : (5432632859 : ℕ)^4513*100000000000000^3489 ≤ 45418995871349^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432632859 10000000000 45418995871349 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88477081/500000000 : ℝ)^4513 ≤ (5322094239553/50000000000000 : ℝ)^3489 := by
    have hnat : (88477081 : ℕ)^4513*50000000000000^3489 ≤ 5322094239553^3489*500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88477081 500000000 5322094239553 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295058923/10000000000 : ℝ), (5432632859/10000000000 : ℝ), (-88477081/500000000 : ℝ)] ![(43936815638841/100000000000000 : ℝ), (45418995871349/100000000000000 : ℝ), (5322094239553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295058923/10000000000 : ℝ)|^4513 ≤ (43936815638841/100000000000000 : ℝ)^3489
        have hw : |(5295058923/10000000000 : ℝ)|=(5295058923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432632859/10000000000 : ℝ)|^4513 ≤ (45418995871349/100000000000000 : ℝ)^3489
        have hw : |(5432632859/10000000000 : ℝ)|=(5432632859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88477081/500000000 : ℝ)|^4513 ≤ (5322094239553/50000000000000 : ℝ)^3489
        have hw : |(-88477081/500000000 : ℝ)|=(88477081/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s6_7 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (854340871/2000000000 : ℝ)*x 0 + (2259830253/5000000000 : ℝ)*x 1 + (80711277/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854340871/2000000000 : ℝ)^4513 ≤ (33280122204973/100000000000000 : ℝ)^3489 := by
    have hnat : (854340871 : ℕ)^4513*100000000000000^3489 ≤ 33280122204973^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854340871 2000000000 33280122204973 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259830253/5000000000 : ℝ)^4513 ≤ (35799873806379/100000000000000 : ℝ)^3489 := by
    have hnat : (2259830253 : ℕ)^4513*100000000000000^3489 ≤ 35799873806379^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259830253 5000000000 35799873806379 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80711277/200000000 : ℝ)^4513 ≤ (15460001984673/50000000000000 : ℝ)^3489 := by
    have hnat : (80711277 : ℕ)^4513*50000000000000^3489 ≤ 15460001984673^3489*200000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80711277 200000000 15460001984673 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854340871/2000000000 : ℝ), (2259830253/5000000000 : ℝ), (80711277/200000000 : ℝ)] ![(33280122204973/100000000000000 : ℝ), (35799873806379/100000000000000 : ℝ), (15460001984673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854340871/2000000000 : ℝ)|^4513 ≤ (33280122204973/100000000000000 : ℝ)^3489
        have hw : |(854340871/2000000000 : ℝ)|=(854340871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259830253/5000000000 : ℝ)|^4513 ≤ (35799873806379/100000000000000 : ℝ)^3489
        have hw : |(2259830253/5000000000 : ℝ)|=(2259830253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80711277/200000000 : ℝ)|^4513 ≤ (15460001984673/50000000000000 : ℝ)^3489
        have hw : |(80711277/200000000 : ℝ)|=(80711277/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1508_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (109/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10899/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10899/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10899/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10899/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10899/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10899/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10899/100000 : ℝ) ^ (4511/1024 : ℝ) ≤ (1436696384052841/25000000000000000000 : ℝ) := by
    have hpowers : (10899/100000 : ℝ)^4511 ≤ (1436696384052841/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10899 : ℕ)^4511*25000000000000000000^1024 ≤ 1436696384052841^1024*100000^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10899 100000 1436696384052841 25000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10899/100000 : ℝ)) (X := (1436696384052841/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4511/1024 : ℝ) ≤ (26975324726517969/100000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4511 ≤ (26975324726517969/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4511*100000000000000000000^1024 ≤ 26975324726517969^1024*50000^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 26975324726517969 100000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (26975324726517969/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501436696384052841/12500000000000000000 : ℝ) ≤ (10000260893238427/10000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (12501436696384052841/12500000000000000000 : ℝ)^1024 ≤ (10000260893238427/10000000000000000 : ℝ)^4511 := by
      have hnat : (12501436696384052841 : ℕ)^1024*10000000000000000^4511 ≤ 10000260893238427^4511*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501436696384052841 12500000000000000000 10000260893238427 10000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000260893238427/10000000000000000 : ℝ)) (X := (12501436696384052841/12500000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032722110262729333/100000000000000000000 : ℝ) ≤ (2000148540031097/2000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (100032722110262729333/100000000000000000000 : ℝ)^1024 ≤ (2000148540031097/2000000000000000 : ℝ)^4511 := by
      have hnat : (100032722110262729333 : ℕ)^1024*2000000000000000^4511 ≤ 2000148540031097^4511*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032722110262729333 100000000000000000000 2000148540031097 2000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000148540031097/2000000000000000 : ℝ)) (X := (100032722110262729333/100000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026975324726517969/50000000000000000000 : ℝ) ≤ (10001224507072543/10000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (50026975324726517969/50000000000000000000 : ℝ)^1024 ≤ (10001224507072543/10000000000000000 : ℝ)^4511 := by
      have hnat : (50026975324726517969 : ℕ)^1024*10000000000000000^4511 ≤ 10001224507072543^4511*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026975324726517969 50000000000000000000 10001224507072543 10000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001224507072543/10000000000000000 : ℝ)) (X := (50026975324726517969/50000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1436696384052841/25000000000000000000 : ℝ) ≤ ((45820693246533680657/45830000000000000000 : ℝ)+2*(240903458529/229150000000000 : ℝ)*(10899/100000 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (45820693246533680657/45830000000000000000 : ℝ)+2*(240903458529/229150000000000 : ℝ)*(10899/100000 : ℝ)=(10000260893238427/10000000000000000 : ℝ) by norm_num, show 1+2*(1436696384052841/25000000000000000000 : ℝ)=(12501436696384052841/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26975324726517969/100000000000000000000 : ℝ)+(1436696384052841/25000000000000000000 : ℝ) ≤ ((45820693246533680657/45830000000000000000 : ℝ)+(240903458529/229150000000000 : ℝ)*((7741/50000 : ℝ)+(10899/100000 : ℝ)))^(4511/1024 : ℝ) := by
    rw [show (45820693246533680657/45830000000000000000 : ℝ)+(240903458529/229150000000000 : ℝ)*((7741/50000 : ℝ)+(10899/100000 : ℝ))=(2000148540031097/2000000000000000 : ℝ) by norm_num, show 1+(26975324726517969/100000000000000000000 : ℝ)+(1436696384052841/25000000000000000000 : ℝ)=(100032722110262729333/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26975324726517969/100000000000000000000 : ℝ) ≤ ((45820693246533680657/45830000000000000000 : ℝ)+2*(240903458529/229150000000000 : ℝ)*(7741/50000 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (45820693246533680657/45830000000000000000 : ℝ)+2*(240903458529/229150000000000 : ℝ)*(7741/50000 : ℝ)=(10001224507072543/10000000000000000 : ℝ) by norm_num, show 1+2*(26975324726517969/100000000000000000000 : ℝ)=(50026975324726517969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45820693246533680657/45830000000000000000 : ℝ)*(X 1 0+X 2 0)+(240903458529/229150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (10899/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (45820693246533680657/45830000000000000000 : ℝ)) (alpha := (240903458529/229150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45820693246533680657/45830000000000000000 : ℝ)*(X 0 1+X 2 1)+(240903458529/229150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (10899/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (45820693246533680657/45830000000000000000 : ℝ)) (alpha := (240903458529/229150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45820693246533680657/45830000000000000000 : ℝ)*(X 0 2+X 1 2)+(240903458529/229150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (10899/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (45820693246533680657/45830000000000000000 : ℝ)) (alpha := (240903458529/229150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1873944337/10000000000 : ℝ)*X 0 0+(5433753673/10000000000 : ℝ)*X 0 1+(1304357831/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351811567/10000000000 : ℝ)*X 1 0+(-992371593/5000000000 : ℝ)*X 1 1+(1304357831/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351811567/10000000000 : ℝ)*X 2 0+(1304357831/2500000000 : ℝ)*X 2 1+(-992371593/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1067909643/2500000000 : ℝ)*X 0 0+(126032167/312500000 : ℝ)*X 0 1+(1130544099/2500000000 : ℝ)*X 0 2+(1067909643/2500000000 : ℝ)*X 1 0+(126032167/312500000 : ℝ)*X 1 1+(1130544099/2500000000 : ℝ)*X 1 2+(1067909643/2500000000 : ℝ)*X 2 0+(126032167/312500000 : ℝ)*X 2 1+(1130544099/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-936986721/5000000000 : ℝ)*X 0 0+(2609271991/5000000000 : ℝ)*X 0 1+(5432632839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1059011781/2000000000 : ℝ)*X 1 0+(-1769541579/10000000000 : ℝ)*X 1 1+(2716316453/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295058923/10000000000 : ℝ)*X 2 0+(5432632859/10000000000 : ℝ)*X 2 1+(-88477081/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((854340871/2000000000 : ℝ)*X 0 0+(2259830253/5000000000 : ℝ)*X 0 1+(80711277/200000000 : ℝ)*X 0 2+(854340871/2000000000 : ℝ)*X 1 0+(2259830253/5000000000 : ℝ)*X 1 1+(80711277/200000000 : ℝ)*X 1 2+(854340871/2000000000 : ℝ)*X 2 0+(2259830253/5000000000 : ℝ)*X 2 1+(80711277/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3028249847680719133652543031/286437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (464946211/25000000000000 : ℝ)*(base19) + (1736280449/100000000000000 : ℝ)*(base23) + (2643889/4000000000000 : ℝ)*(lower2) + (263503911/100000000000000 : ℝ)*(upper3) + (173138143/100000000000000 : ℝ)*(upper5) + (833398989586861/25000000000000 : ℝ)*(major0) + (833398989586861/25000000000000 : ℝ)*(major1) + (666719191669489/20000000000000 : ℝ)*(major2) + (924552220108761/20000000000000 : ℝ)*(sp0) + (4622788327494863/100000000000000 : ℝ)*(sp1) + (2311394225499629/50000000000000 : ℝ)*(sp2) + (2044387438875521/100000000000000 : ℝ)*(sp3) + (14543367951/50000000000000 : ℝ)*(sp4) + (13938135863/100000000000000 : ℝ)*(sp7) + (255550172126423/12500000000000 : ℝ)*(f.failure) + (4622790187279707/100000000000000 : ℝ)*(f.sum) + (79224342621039/22915000000000000000000000000 : ℝ)*base66 + (5188085971760952323/1145750000000000000000000000000000 : ℝ)*base68 + (2031133444290985727/916600000000000000000000000000000 : ℝ)*base70 + (429737260426202323/1145750000000000000000000000000000 : ℝ)*base72 + (24409226643921/22915000000000000000000000000 : ℝ)*base73 + (1178199369876614273/916600000000000000000000000000000 : ℝ)*base75 + (139690511001402323/1145750000000000000000000000000000 : ℝ)*base78 + (13986166144369652323/1145750000000000000000000000000000 : ℝ)*base80 + (19112748994809/11457500000000000000000000000 : ℝ)*base82 + (1912057/1250000000000000000000 : ℝ)*base89 + (1912057/1250000000000000000000 : ℝ)*base91 + (10587943/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26932850875487663989821/5728750000000000000000000000 : ℝ) := by norm_num
    linear_combination (758479143/100000000000000 : ℝ)*(base19) + (815507439/100000000000000 : ℝ)*(base23) + (292327693/100000000000000 : ℝ)*(lower1) + (79241583/100000000000000 : ℝ)*(upper3) + (11705669/50000000000000 : ℝ)*(lower4) + (21225787/25000000000000 : ℝ)*(upper5) + (3368320485927939/100000000000000 : ℝ)*(major0) + (3368320485927939/100000000000000 : ℝ)*(major1) + (3368320485927939/100000000000000 : ℝ)*(major2) + (285839697/100000000000000 : ℝ)*(sp1) + (4670943854358271/100000000000000 : ℝ)*(sp4) + (583867851254929/12500000000000 : ℝ)*(sp5) + (291933939928177/6250000000000 : ℝ)*(sp6) + (1032848480392989/50000000000000 : ℝ)*(sp7) + (1032848480392989/50000000000000 : ℝ)*(f.failure) + (4670943854358271/100000000000000 : ℝ)*(f.sum) + (17840407804571/11457500000000000000000000000 : ℝ)*base65 + (1418554929916375923/4583000000000000000000000000000000 : ℝ)*base67 + (62645353649940624077/4583000000000000000000000000000000 : ℝ)*base70 + (13848607131619375923/4583000000000000000000000000000000 : ℝ)*base71 + (3359919316599/2864375000000000000000000000 : ℝ)*base73 + (98875604098073624077/4583000000000000000000000000000000 : ℝ)*base76 + (17870387722628375923/4583000000000000000000000000000000 : ℝ)*base77 + (62393824343061624077/4583000000000000000000000000000000 : ℝ)*base80 + (45972963981219/11457500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (61629651/5000000000000000000000 : ℝ)*base89 + (61629651/5000000000000000000000 : ℝ)*base91 + (61629651/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1508_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (109/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1508_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1508_box_0 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-331919759/2000000000 : ℝ)*x 0 + (5403265113/10000000000 : ℝ)*x 1 + (5403265019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331919759/2000000000 : ℝ)^4513 ≤ (9796677923277/100000000000000 : ℝ)^3489 := by
    have hnat : (331919759 : ℕ)^4513*100000000000000^3489 ≤ 9796677923277^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331919759 2000000000 9796677923277 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403265113/10000000000 : ℝ)^4513 ≤ (9020332308537/20000000000000 : ℝ)^3489 := by
    have hnat : (5403265113 : ℕ)^4513*20000000000000^3489 ≤ 9020332308537^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403265113 10000000000 9020332308537 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403265019/10000000000 : ℝ)^4513 ≤ (45101660527773/100000000000000 : ℝ)^3489 := by
    have hnat : (5403265019 : ℕ)^4513*100000000000000^3489 ≤ 45101660527773^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403265019 10000000000 45101660527773 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-331919759/2000000000 : ℝ), (5403265113/10000000000 : ℝ), (5403265019/10000000000 : ℝ)] ![(9796677923277/100000000000000 : ℝ), (9020332308537/20000000000000 : ℝ), (45101660527773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-331919759/2000000000 : ℝ)|^4513 ≤ (9796677923277/100000000000000 : ℝ)^3489
        have hw : |(-331919759/2000000000 : ℝ)|=(331919759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403265113/10000000000 : ℝ)|^4513 ≤ (9020332308537/20000000000000 : ℝ)^3489
        have hw : |(5403265113/10000000000 : ℝ)|=(5403265113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403265019/10000000000 : ℝ)|^4513 ≤ (45101660527773/100000000000000 : ℝ)^3489
        have hw : |(5403265019/10000000000 : ℝ)|=(5403265019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_1 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527072307/1000000000 : ℝ)*x 0 + (-921712999/5000000000 : ℝ)*x 1 + (5403264943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527072307/1000000000 : ℝ)^4513 ≤ (5459474333941/12500000000000 : ℝ)^3489 := by
    have hnat : (527072307 : ℕ)^4513*12500000000000^3489 ≤ 5459474333941^3489*1000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527072307 1000000000 5459474333941 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921712999/5000000000 : ℝ)^4513 ≤ (11222545601813/100000000000000 : ℝ)^3489 := by
    have hnat : (921712999 : ℕ)^4513*100000000000000^3489 ≤ 11222545601813^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921712999 5000000000 11222545601813 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403264943/10000000000 : ℝ)^4513 ≤ (9020331941441/20000000000000 : ℝ)^3489 := by
    have hnat : (5403264943 : ℕ)^4513*20000000000000^3489 ≤ 9020331941441^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403264943 10000000000 9020331941441 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527072307/1000000000 : ℝ), (-921712999/5000000000 : ℝ), (5403264943/10000000000 : ℝ)] ![(5459474333941/12500000000000 : ℝ), (11222545601813/100000000000000 : ℝ), (9020331941441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527072307/1000000000 : ℝ)|^4513 ≤ (5459474333941/12500000000000 : ℝ)^3489
        have hw : |(527072307/1000000000 : ℝ)|=(527072307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-921712999/5000000000 : ℝ)|^4513 ≤ (11222545601813/100000000000000 : ℝ)^3489
        have hw : |(-921712999/5000000000 : ℝ)|=(921712999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403264943/10000000000 : ℝ)|^4513 ≤ (9020331941441/20000000000000 : ℝ)^3489
        have hw : |(5403264943/10000000000 : ℝ)|=(5403264943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_2 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635361459/5000000000 : ℝ)*x 0 + (675408147/1250000000 : ℝ)*x 1 + (-921712943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635361459/5000000000 : ℝ)^4513 ≤ (43675793042313/100000000000000 : ℝ)^3489 := by
    have hnat : (2635361459 : ℕ)^4513*100000000000000^3489 ≤ 43675793042313^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635361459 5000000000 43675793042313 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675408147/1250000000 : ℝ)^4513 ≤ (11275415555723/25000000000000 : ℝ)^3489 := by
    have hnat : (675408147 : ℕ)^4513*25000000000000^3489 ≤ 11275415555723^3489*1250000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675408147 1250000000 11275415555723 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921712943/5000000000 : ℝ)^4513 ≤ (2244508943971/20000000000000 : ℝ)^3489 := by
    have hnat : (921712943 : ℕ)^4513*20000000000000^3489 ≤ 2244508943971^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921712943 5000000000 2244508943971 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635361459/5000000000 : ℝ), (675408147/1250000000 : ℝ), (-921712943/5000000000 : ℝ)] ![(43675793042313/100000000000000 : ℝ), (11275415555723/25000000000000 : ℝ), (2244508943971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635361459/5000000000 : ℝ)|^4513 ≤ (43675793042313/100000000000000 : ℝ)^3489
        have hw : |(2635361459/5000000000 : ℝ)|=(2635361459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675408147/1250000000 : ℝ)|^4513 ≤ (11275415555723/25000000000000 : ℝ)^3489
        have hw : |(675408147/1250000000 : ℝ)|=(675408147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-921712943/5000000000 : ℝ)|^4513 ≤ (2244508943971/20000000000000 : ℝ)^3489
        have hw : |(-921712943/5000000000 : ℝ)|=(921712943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_3 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (559360683/1250000000 : ℝ)*x 0 + (835404669/2000000000 : ℝ)*x 1 + (4177023217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (559360683/1250000000 : ℝ)^4513 ≤ (35341792322457/100000000000000 : ℝ)^3489 := by
    have hnat : (559360683 : ℕ)^4513*100000000000000^3489 ≤ 35341792322457^3489*1250000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559360683 1250000000 35341792322457 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (835404669/2000000000 : ℝ)^4513 ≤ (6465820894839/20000000000000 : ℝ)^3489 := by
    have hnat : (835404669 : ℕ)^4513*20000000000000^3489 ≤ 6465820894839^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835404669 2000000000 6465820894839 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4177023217/10000000000 : ℝ)^4513 ≤ (32329103192747/100000000000000 : ℝ)^3489 := by
    have hnat : (4177023217 : ℕ)^4513*100000000000000^3489 ≤ 32329103192747^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177023217 10000000000 32329103192747 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(559360683/1250000000 : ℝ), (835404669/2000000000 : ℝ), (4177023217/10000000000 : ℝ)] ![(35341792322457/100000000000000 : ℝ), (6465820894839/20000000000000 : ℝ), (32329103192747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(559360683/1250000000 : ℝ)|^4513 ≤ (35341792322457/100000000000000 : ℝ)^3489
        have hw : |(559360683/1250000000 : ℝ)|=(559360683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(835404669/2000000000 : ℝ)|^4513 ≤ (6465820894839/20000000000000 : ℝ)^3489
        have hw : |(835404669/2000000000 : ℝ)|=(835404669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4177023217/10000000000 : ℝ)|^4513 ≤ (32329103192747/100000000000000 : ℝ)^3489
        have hw : |(4177023217/10000000000 : ℝ)|=(4177023217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_4 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-130858303/625000000 : ℝ)*x 0 + (2621746323/5000000000 : ℝ)*x 1 + (262174639/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130858303/625000000 : ℝ)^4513 ≤ (13231706013543/100000000000000 : ℝ)^3489 := by
    have hnat : (130858303 : ℕ)^4513*100000000000000^3489 ≤ 13231706013543^3489*625000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130858303 625000000 13231706013543 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621746323/5000000000 : ℝ)^4513 ≤ (8676829254149/20000000000000 : ℝ)^3489 := by
    have hnat : (2621746323 : ℕ)^4513*20000000000000^3489 ≤ 8676829254149^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621746323 5000000000 8676829254149 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262174639/500000000 : ℝ)^4513 ≤ (21692073852423/50000000000000 : ℝ)^3489 := by
    have hnat : (262174639 : ℕ)^4513*50000000000000^3489 ≤ 21692073852423^3489*500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262174639 500000000 21692073852423 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130858303/625000000 : ℝ), (2621746323/5000000000 : ℝ), (262174639/500000000 : ℝ)] ![(13231706013543/100000000000000 : ℝ), (8676829254149/20000000000000 : ℝ), (21692073852423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130858303/625000000 : ℝ)|^4513 ≤ (13231706013543/100000000000000 : ℝ)^3489
        have hw : |(-130858303/625000000 : ℝ)|=(130858303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621746323/5000000000 : ℝ)|^4513 ≤ (8676829254149/20000000000000 : ℝ)^3489
        have hw : |(2621746323/5000000000 : ℝ)|=(2621746323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262174639/500000000 : ℝ)|^4513 ≤ (21692073852423/50000000000000 : ℝ)^3489
        have hw : |(262174639/500000000 : ℝ)|=(262174639/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_5 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538199447/1000000000 : ℝ)*x 0 + (-1909267393/10000000000 : ℝ)*x 1 + (2621746329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538199447/1000000000 : ℝ)^4513 ≤ (44872136511519/100000000000000 : ℝ)^3489 := by
    have hnat : (538199447 : ℕ)^4513*100000000000000^3489 ≤ 44872136511519^3489*1000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538199447 1000000000 44872136511519 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1909267393/10000000000 : ℝ)^4513 ≤ (5871858537583/50000000000000 : ℝ)^3489 := by
    have hnat : (1909267393 : ℕ)^4513*50000000000000^3489 ≤ 5871858537583^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909267393 10000000000 5871858537583 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621746329/5000000000 : ℝ)^4513 ≤ (10846036599793/25000000000000 : ℝ)^3489 := by
    have hnat : (2621746329 : ℕ)^4513*25000000000000^3489 ≤ 10846036599793^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621746329 5000000000 10846036599793 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538199447/1000000000 : ℝ), (-1909267393/10000000000 : ℝ), (2621746329/5000000000 : ℝ)] ![(44872136511519/100000000000000 : ℝ), (5871858537583/50000000000000 : ℝ), (10846036599793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538199447/1000000000 : ℝ)|^4513 ≤ (44872136511519/100000000000000 : ℝ)^3489
        have hw : |(538199447/1000000000 : ℝ)|=(538199447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1909267393/10000000000 : ℝ)|^4513 ≤ (5871858537583/50000000000000 : ℝ)^3489
        have hw : |(-1909267393/10000000000 : ℝ)|=(1909267393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621746329/5000000000 : ℝ)|^4513 ≤ (10846036599793/25000000000000 : ℝ)^3489
        have hw : |(2621746329/5000000000 : ℝ)|=(2621746329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_6 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345498573/2500000000 : ℝ)*x 0 + (5243492889/10000000000 : ℝ)*x 1 + (-477316831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345498573/2500000000 : ℝ)^4513 ≤ (44872134591887/100000000000000 : ℝ)^3489 := by
    have hnat : (1345498573 : ℕ)^4513*100000000000000^3489 ≤ 44872134591887^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345498573 2500000000 44872134591887 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243492889/10000000000 : ℝ)^4513 ≤ (4338414887139/10000000000000 : ℝ)^3489 := by
    have hnat : (5243492889 : ℕ)^4513*10000000000000^3489 ≤ 4338414887139^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243492889 10000000000 4338414887139 10000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477316831/2500000000 : ℝ)^4513 ≤ (11743716526191/100000000000000 : ℝ)^3489 := by
    have hnat : (477316831 : ℕ)^4513*100000000000000^3489 ≤ 11743716526191^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477316831 2500000000 11743716526191 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345498573/2500000000 : ℝ), (5243492889/10000000000 : ℝ), (-477316831/2500000000 : ℝ)] ![(44872134591887/100000000000000 : ℝ), (4338414887139/10000000000000 : ℝ), (11743716526191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345498573/2500000000 : ℝ)|^4513 ≤ (44872134591887/100000000000000 : ℝ)^3489
        have hw : |(1345498573/2500000000 : ℝ)|=(1345498573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243492889/10000000000 : ℝ)|^4513 ≤ (4338414887139/10000000000000 : ℝ)^3489
        have hw : |(5243492889/10000000000 : ℝ)|=(5243492889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-477316831/2500000000 : ℝ)|^4513 ≤ (11743716526191/100000000000000 : ℝ)^3489
        have hw : |(-477316831/2500000000 : ℝ)|=(477316831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_7 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4065992179/10000000000 : ℝ)*x 0 + (876267023/2000000000 : ℝ)*x 1 + (2190667549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4065992179/10000000000 : ℝ)^4513 ≤ (6244379972827/20000000000000 : ℝ)^3489 := by
    have hnat : (4065992179 : ℕ)^4513*20000000000000^3489 ≤ 6244379972827^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4065992179 10000000000 6244379972827 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876267023/2000000000 : ℝ)^4513 ≤ (17194525073911/50000000000000 : ℝ)^3489 := by
    have hnat : (876267023 : ℕ)^4513*50000000000000^3489 ≤ 17194525073911^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876267023 2000000000 17194525073911 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190667549/5000000000 : ℝ)^4513 ≤ (8597262493807/25000000000000 : ℝ)^3489 := by
    have hnat : (2190667549 : ℕ)^4513*25000000000000^3489 ≤ 8597262493807^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190667549 5000000000 8597262493807 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4065992179/10000000000 : ℝ), (876267023/2000000000 : ℝ), (2190667549/5000000000 : ℝ)] ![(6244379972827/20000000000000 : ℝ), (17194525073911/50000000000000 : ℝ), (8597262493807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4065992179/10000000000 : ℝ)|^4513 ≤ (6244379972827/20000000000000 : ℝ)^3489
        have hw : |(4065992179/10000000000 : ℝ)|=(4065992179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(876267023/2000000000 : ℝ)|^4513 ≤ (17194525073911/50000000000000 : ℝ)^3489
        have hw : |(876267023/2000000000 : ℝ)|=(876267023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2190667549/5000000000 : ℝ)|^4513 ≤ (8597262493807/25000000000000 : ℝ)^3489
        have hw : |(2190667549/5000000000 : ℝ)|=(2190667549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_8 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2002010957/10000000000 : ℝ)*x 0 + (5131603937/10000000000 : ℝ)*x 1 + (5423730239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2002010957/10000000000 : ℝ)^4513 ≤ (1560850006951/12500000000000 : ℝ)^3489 := by
    have hnat : (2002010957 : ℕ)^4513*12500000000000^3489 ≤ 1560850006951^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002010957 10000000000 1560850006951 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5131603937/10000000000 : ℝ)^4513 ≤ (5273806871/12500000000 : ℝ)^3489 := by
    have hnat : (5131603937 : ℕ)^4513*12500000000^3489 ≤ 5273806871^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131603937 10000000000 5273806871 12500000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423730239/10000000000 : ℝ)^4513 ≤ (4532274495311/10000000000000 : ℝ)^3489 := by
    have hnat : (5423730239 : ℕ)^4513*10000000000000^3489 ≤ 4532274495311^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423730239 10000000000 4532274495311 10000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2002010957/10000000000 : ℝ), (5131603937/10000000000 : ℝ), (5423730239/10000000000 : ℝ)] ![(1560850006951/12500000000000 : ℝ), (5273806871/12500000000 : ℝ), (4532274495311/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2002010957/10000000000 : ℝ)|^4513 ≤ (1560850006951/12500000000000 : ℝ)^3489
        have hw : |(-2002010957/10000000000 : ℝ)|=(2002010957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5131603937/10000000000 : ℝ)|^4513 ≤ (5273806871/12500000000 : ℝ)^3489
        have hw : |(5131603937/10000000000 : ℝ)|=(5131603937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423730239/10000000000 : ℝ)|^4513 ≤ (4532274495311/10000000000000 : ℝ)^3489
        have hw : |(5423730239/10000000000 : ℝ)|=(5423730239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_9 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628232307/5000000000 : ℝ)*x 0 + (-458686263/2500000000 : ℝ)*x 1 + (542372983/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628232307/5000000000 : ℝ)^4513 ≤ (43523025779287/100000000000000 : ℝ)^3489 := by
    have hnat : (2628232307 : ℕ)^4513*100000000000000^3489 ≤ 43523025779287^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628232307 5000000000 43523025779287 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458686263/2500000000 : ℝ)^4513 ≤ (2230846735097/20000000000000 : ℝ)^3489 := by
    have hnat : (458686263 : ℕ)^4513*20000000000000^3489 ≤ 2230846735097^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458686263 2500000000 2230846735097 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542372983/1000000000 : ℝ)^4513 ≤ (2266137026613/5000000000000 : ℝ)^3489 := by
    have hnat : (542372983 : ℕ)^4513*5000000000000^3489 ≤ 2266137026613^3489*1000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542372983 1000000000 2266137026613 5000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628232307/5000000000 : ℝ), (-458686263/2500000000 : ℝ), (542372983/1000000000 : ℝ)] ![(43523025779287/100000000000000 : ℝ), (2230846735097/20000000000000 : ℝ), (2266137026613/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628232307/5000000000 : ℝ)|^4513 ≤ (43523025779287/100000000000000 : ℝ)^3489
        have hw : |(2628232307/5000000000 : ℝ)|=(2628232307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-458686263/2500000000 : ℝ)|^4513 ≤ (2230846735097/20000000000000 : ℝ)^3489
        have hw : |(-458686263/2500000000 : ℝ)|=(458686263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542372983/1000000000 : ℝ)|^4513 ≤ (2266137026613/5000000000000 : ℝ)^3489
        have hw : |(542372983/1000000000 : ℝ)|=(542372983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_10 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256463503/10000000000 : ℝ)*x 0 + (5423730277/10000000000 : ℝ)*x 1 + (-1834745951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256463503/10000000000 : ℝ)^4513 ≤ (43523013880471/100000000000000 : ℝ)^3489 := by
    have hnat : (5256463503 : ℕ)^4513*100000000000000^3489 ≤ 43523013880471^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256463503 10000000000 43523013880471 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423730277/10000000000 : ℝ)^4513 ≤ (45322745363849/100000000000000 : ℝ)^3489 := by
    have hnat : (5423730277 : ℕ)^4513*100000000000000^3489 ≤ 45322745363849^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423730277 10000000000 45322745363849 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1834745951/10000000000 : ℝ)^4513 ≤ (446169629799/4000000000000 : ℝ)^3489 := by
    have hnat : (1834745951 : ℕ)^4513*4000000000000^3489 ≤ 446169629799^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834745951 10000000000 446169629799 4000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256463503/10000000000 : ℝ), (5423730277/10000000000 : ℝ), (-1834745951/10000000000 : ℝ)] ![(43523013880471/100000000000000 : ℝ), (45322745363849/100000000000000 : ℝ), (446169629799/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256463503/10000000000 : ℝ)|^4513 ≤ (43523013880471/100000000000000 : ℝ)^3489
        have hw : |(5256463503/10000000000 : ℝ)|=(5256463503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423730277/10000000000 : ℝ)|^4513 ≤ (45322745363849/100000000000000 : ℝ)^3489
        have hw : |(5423730277/10000000000 : ℝ)|=(5423730277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1834745951/10000000000 : ℝ)|^4513 ≤ (446169629799/4000000000000 : ℝ)^3489
        have hw : |(-1834745951/10000000000 : ℝ)|=(1834745951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_11 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (36208869/80000000 : ℝ)*x 0 + (4150819583/10000000000 : ℝ)*x 1 + (1037705463/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36208869/80000000 : ℝ)^4513 ≤ (35865952884273/100000000000000 : ℝ)^3489 := by
    have hnat : (36208869 : ℕ)^4513*100000000000000^3489 ≤ 35865952884273^3489*80000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36208869 80000000 35865952884273 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4150819583/10000000000 : ℝ)^4513 ≤ (32067012212303/100000000000000 : ℝ)^3489 := by
    have hnat : (4150819583 : ℕ)^4513*100000000000000^3489 ≤ 32067012212303^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150819583 10000000000 32067012212303 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037705463/2500000000 : ℝ)^4513 ≤ (32067034886063/100000000000000 : ℝ)^3489 := by
    have hnat : (1037705463 : ℕ)^4513*100000000000000^3489 ≤ 32067034886063^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037705463 2500000000 32067034886063 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(36208869/80000000 : ℝ), (4150819583/10000000000 : ℝ), (1037705463/2500000000 : ℝ)] ![(35865952884273/100000000000000 : ℝ), (32067012212303/100000000000000 : ℝ), (32067034886063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(36208869/80000000 : ℝ)|^4513 ≤ (35865952884273/100000000000000 : ℝ)^3489
        have hw : |(36208869/80000000 : ℝ)|=(36208869/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4150819583/10000000000 : ℝ)|^4513 ≤ (32067012212303/100000000000000 : ℝ)^3489
        have hw : |(4150819583/10000000000 : ℝ)|=(4150819583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037705463/2500000000 : ℝ)|^4513 ≤ (32067034886063/100000000000000 : ℝ)^3489
        have hw : |(1037705463/2500000000 : ℝ)|=(1037705463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_12 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1751291851/10000000000 : ℝ)*x 0 + (5511543261/10000000000 : ℝ)*x 1 + (2042371/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1751291851/10000000000 : ℝ)^4513 ≤ (10502408754951/100000000000000 : ℝ)^3489 := by
    have hnat : (1751291851 : ℕ)^4513*100000000000000^3489 ≤ 10502408754951^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751291851 10000000000 10502408754951 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5511543261/10000000000 : ℝ)^4513 ≤ (23137077938517/50000000000000 : ℝ)^3489 := by
    have hnat : (5511543261 : ℕ)^4513*50000000000000^3489 ≤ 23137077938517^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511543261 10000000000 23137077938517 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2042371/3906250 : ℝ)^4513 ≤ (5402929419523/12500000000000 : ℝ)^3489 := by
    have hnat : (2042371 : ℕ)^4513*12500000000000^3489 ≤ 5402929419523^3489*3906250^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042371 3906250 5402929419523 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1751291851/10000000000 : ℝ), (5511543261/10000000000 : ℝ), (2042371/3906250 : ℝ)] ![(10502408754951/100000000000000 : ℝ), (23137077938517/50000000000000 : ℝ), (5402929419523/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1751291851/10000000000 : ℝ)|^4513 ≤ (10502408754951/100000000000000 : ℝ)^3489
        have hw : |(-1751291851/10000000000 : ℝ)|=(1751291851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5511543261/10000000000 : ℝ)|^4513 ≤ (23137077938517/50000000000000 : ℝ)^3489
        have hw : |(5511543261/10000000000 : ℝ)|=(5511543261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2042371/3906250 : ℝ)|^4513 ≤ (5402929419523/12500000000000 : ℝ)^3489
        have hw : |(2042371/3906250 : ℝ)|=(2042371/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_13 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392457147/10000000000 : ℝ)*x 0 + (-9576393/50000000 : ℝ)*x 1 + (1045693887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392457147/10000000000 : ℝ)^4513 ≤ (44985002867523/100000000000000 : ℝ)^3489 := by
    have hnat : (5392457147 : ℕ)^4513*100000000000000^3489 ≤ 44985002867523^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392457147 10000000000 44985002867523 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9576393/50000000 : ℝ)^4513 ≤ (11791565245021/100000000000000 : ℝ)^3489 := by
    have hnat : (9576393 : ℕ)^4513*100000000000000^3489 ≤ 11791565245021^3489*50000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9576393 50000000 11791565245021 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045693887/2000000000 : ℝ)^4513 ≤ (43223431880883/100000000000000 : ℝ)^3489 := by
    have hnat : (1045693887 : ℕ)^4513*100000000000000^3489 ≤ 43223431880883^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045693887 2000000000 43223431880883 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392457147/10000000000 : ℝ), (-9576393/50000000 : ℝ), (1045693887/2000000000 : ℝ)] ![(44985002867523/100000000000000 : ℝ), (11791565245021/100000000000000 : ℝ), (43223431880883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392457147/10000000000 : ℝ)|^4513 ≤ (44985002867523/100000000000000 : ℝ)^3489
        have hw : |(5392457147/10000000000 : ℝ)|=(5392457147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9576393/50000000 : ℝ)|^4513 ≤ (11791565245021/100000000000000 : ℝ)^3489
        have hw : |(-9576393/50000000 : ℝ)|=(9576393/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045693887/2000000000 : ℝ)|^4513 ≤ (43223431880883/100000000000000 : ℝ)^3489
        have hw : |(1045693887/2000000000 : ℝ)|=(1045693887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_14 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53924569/100000000 : ℝ)*x 0 + (163389659/312500000 : ℝ)*x 1 + (-9576397/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53924569/100000000 : ℝ)^4513 ≤ (22492500101123/50000000000000 : ℝ)^3489 := by
    have hnat : (53924569 : ℕ)^4513*50000000000000^3489 ≤ 22492500101123^3489*100000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53924569 100000000 22492500101123 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163389659/312500000 : ℝ)^4513 ≤ (43223428170331/100000000000000 : ℝ)^3489 := by
    have hnat : (163389659 : ℕ)^4513*100000000000000^3489 ≤ 43223428170331^3489*312500000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163389659 312500000 43223428170331 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9576397/50000000 : ℝ)^4513 ≤ (11791571615819/100000000000000 : ℝ)^3489 := by
    have hnat : (9576397 : ℕ)^4513*100000000000000^3489 ≤ 11791571615819^3489*50000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9576397 50000000 11791571615819 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53924569/100000000 : ℝ), (163389659/312500000 : ℝ), (-9576397/50000000 : ℝ)] ![(22492500101123/50000000000000 : ℝ), (43223428170331/100000000000000 : ℝ), (11791571615819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53924569/100000000 : ℝ)|^4513 ≤ (22492500101123/50000000000000 : ℝ)^3489
        have hw : |(53924569/100000000 : ℝ)|=(53924569/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163389659/312500000 : ℝ)|^4513 ≤ (43223428170331/100000000000000 : ℝ)^3489
        have hw : |(163389659/312500000 : ℝ)|=(163389659/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9576397/50000000 : ℝ)|^4513 ≤ (11791571615819/100000000000000 : ℝ)^3489
        have hw : |(-9576397/50000000 : ℝ)|=(9576397/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_box_15 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2013341803/5000000000 : ℝ)*x 0 + (880104609/2000000000 : ℝ)*x 1 + (880104809/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2013341803/5000000000 : ℝ)^4513 ≤ (7708005977789/25000000000000 : ℝ)^3489 := by
    have hnat : (2013341803 : ℕ)^4513*25000000000000^3489 ≤ 7708005977789^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013341803 5000000000 7708005977789 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880104609/2000000000 : ℝ)^4513 ≤ (34583982952107/100000000000000 : ℝ)^3489 := by
    have hnat : (880104609 : ℕ)^4513*100000000000000^3489 ≤ 34583982952107^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880104609 2000000000 34583982952107 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880104809/2000000000 : ℝ)^4513 ≤ (6916798623551/20000000000000 : ℝ)^3489 := by
    have hnat : (880104809 : ℕ)^4513*20000000000000^3489 ≤ 6916798623551^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880104809 2000000000 6916798623551 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2013341803/5000000000 : ℝ), (880104609/2000000000 : ℝ), (880104809/2000000000 : ℝ)] ![(7708005977789/25000000000000 : ℝ), (34583982952107/100000000000000 : ℝ), (6916798623551/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2013341803/5000000000 : ℝ)|^4513 ≤ (7708005977789/25000000000000 : ℝ)^3489
        have hw : |(2013341803/5000000000 : ℝ)|=(2013341803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(880104609/2000000000 : ℝ)|^4513 ≤ (34583982952107/100000000000000 : ℝ)^3489
        have hw : |(880104609/2000000000 : ℝ)|=(880104609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(880104809/2000000000 : ℝ)|^4513 ≤ (6916798623551/20000000000000 : ℝ)^3489
        have hw : |(880104809/2000000000 : ℝ)|=(880104809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1508_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (109/1000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31867/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58609/100000 : ℝ) ∧ (20069/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10747/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (109/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (109/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (109/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (109/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (109/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (109/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (109/1000 : ℝ) ^ (4511/1024 : ℝ) ≤ (1437277173961173/25000000000000000000 : ℝ) := by
    have hpowers : (109/1000 : ℝ)^4511 ≤ (1437277173961173/25000000000000000000 : ℝ)^1024 := by
      have hnat : (109 : ℕ)^4511*25000000000000000000^1024 ≤ 1437277173961173^1024*1000^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109 1000 1437277173961173 25000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (109/1000 : ℝ)) (X := (1437277173961173/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4511/1024 : ℝ) ≤ (5393529993573851/20000000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4511 ≤ (5393529993573851/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4511*20000000000000000000^1024 ≤ 5393529993573851^1024*100000^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 5393529993573851 20000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (5393529993573851/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501437277173961173/12500000000000000000 : ℝ) ≤ (2500065249675203/2500000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (12501437277173961173/12500000000000000000 : ℝ)^1024 ≤ (2500065249675203/2500000000000000 : ℝ)^4511 := by
      have hnat : (12501437277173961173 : ℕ)^1024*2500000000000000^4511 ≤ 2500065249675203^4511*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501437277173961173 12500000000000000000 2500065249675203 2500000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500065249675203/2500000000000000 : ℝ)) (X := (12501437277173961173/12500000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032716758663713947/100000000000000000000 : ℝ) ≤ (2500185644676137/2500000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (100032716758663713947/100000000000000000000 : ℝ)^1024 ≤ (2500185644676137/2500000000000000 : ℝ)^4511 := by
      have hnat : (100032716758663713947 : ℕ)^1024*2500000000000000^4511 ≤ 2500185644676137^4511*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032716758663713947 100000000000000000000 2500185644676137 2500000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500185644676137/2500000000000000 : ℝ)) (X := (100032716758663713947/100000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005393529993573851/10000000000000000000 : ℝ) ≤ (2500306039677071/2500000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (10005393529993573851/10000000000000000000 : ℝ)^1024 ≤ (2500306039677071/2500000000000000 : ℝ)^4511 := by
      have hnat : (10005393529993573851 : ℕ)^1024*2500000000000000^4511 ≤ 2500306039677071^4511*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005393529993573851 10000000000000000000 2500306039677071 2500000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500306039677071/2500000000000000 : ℝ)) (X := (10005393529993573851/10000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1437277173961173/25000000000000000000 : ℝ) ≤ ((1272241588637971527/1272500000000000000 : ℝ)+2*(6688611163/6362500000000 : ℝ)*(109/1000 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (1272241588637971527/1272500000000000000 : ℝ)+2*(6688611163/6362500000000 : ℝ)*(109/1000 : ℝ)=(2500065249675203/2500000000000000 : ℝ) by norm_num, show 1+2*(1437277173961173/25000000000000000000 : ℝ)=(12501437277173961173/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5393529993573851/20000000000000000000 : ℝ)+(1437277173961173/25000000000000000000 : ℝ) ≤ ((1272241588637971527/1272500000000000000 : ℝ)+(6688611163/6362500000000 : ℝ)*((15481/100000 : ℝ)+(109/1000 : ℝ)))^(4511/1024 : ℝ) := by
    rw [show (1272241588637971527/1272500000000000000 : ℝ)+(6688611163/6362500000000 : ℝ)*((15481/100000 : ℝ)+(109/1000 : ℝ))=(2500185644676137/2500000000000000 : ℝ) by norm_num, show 1+(5393529993573851/20000000000000000000 : ℝ)+(1437277173961173/25000000000000000000 : ℝ)=(100032716758663713947/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5393529993573851/20000000000000000000 : ℝ) ≤ ((1272241588637971527/1272500000000000000 : ℝ)+2*(6688611163/6362500000000 : ℝ)*(15481/100000 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (1272241588637971527/1272500000000000000 : ℝ)+2*(6688611163/6362500000000 : ℝ)*(15481/100000 : ℝ)=(2500306039677071/2500000000000000 : ℝ) by norm_num, show 1+2*(5393529993573851/20000000000000000000 : ℝ)=(10005393529993573851/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1272241588637971527/1272500000000000000 : ℝ)*(X 1 0+X 2 0)+(6688611163/6362500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (109/1000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (1272241588637971527/1272500000000000000 : ℝ)) (alpha := (6688611163/6362500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1272241588637971527/1272500000000000000 : ℝ)*(X 0 1+X 2 1)+(6688611163/6362500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (109/1000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (1272241588637971527/1272500000000000000 : ℝ)) (alpha := (6688611163/6362500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1272241588637971527/1272500000000000000 : ℝ)*(X 0 2+X 1 2)+(6688611163/6362500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (109/1000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (1272241588637971527/1272500000000000000 : ℝ)) (alpha := (6688611163/6362500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-331919759/2000000000 : ℝ)*X 0 0+(5403265113/10000000000 : ℝ)*X 0 1+(5403265019/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((527072307/1000000000 : ℝ)*X 1 0+(-921712999/5000000000 : ℝ)*X 1 1+(5403264943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635361459/5000000000 : ℝ)*X 2 0+(675408147/1250000000 : ℝ)*X 2 1+(-921712943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((559360683/1250000000 : ℝ)*X 0 0+(835404669/2000000000 : ℝ)*X 0 1+(4177023217/10000000000 : ℝ)*X 0 2+(559360683/1250000000 : ℝ)*X 1 0+(835404669/2000000000 : ℝ)*X 1 1+(4177023217/10000000000 : ℝ)*X 1 2+(559360683/1250000000 : ℝ)*X 2 0+(835404669/2000000000 : ℝ)*X 2 1+(4177023217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-130858303/625000000 : ℝ)*X 0 0+(2621746323/5000000000 : ℝ)*X 0 1+(262174639/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((538199447/1000000000 : ℝ)*X 1 0+(-1909267393/10000000000 : ℝ)*X 1 1+(2621746329/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1345498573/2500000000 : ℝ)*X 2 0+(5243492889/10000000000 : ℝ)*X 2 1+(-477316831/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4065992179/10000000000 : ℝ)*X 0 0+(876267023/2000000000 : ℝ)*X 0 1+(2190667549/5000000000 : ℝ)*X 0 2+(4065992179/10000000000 : ℝ)*X 1 0+(876267023/2000000000 : ℝ)*X 1 1+(2190667549/5000000000 : ℝ)*X 1 2+(4065992179/10000000000 : ℝ)*X 2 0+(876267023/2000000000 : ℝ)*X 2 1+(2190667549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2002010957/10000000000 : ℝ)*X 0 0+(5131603937/10000000000 : ℝ)*X 0 1+(5423730239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628232307/5000000000 : ℝ)*X 1 0+(-458686263/2500000000 : ℝ)*X 1 1+(542372983/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256463503/10000000000 : ℝ)*X 2 0+(5423730277/10000000000 : ℝ)*X 2 1+(-1834745951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((36208869/80000000 : ℝ)*X 0 0+(4150819583/10000000000 : ℝ)*X 0 1+(1037705463/2500000000 : ℝ)*X 0 2+(36208869/80000000 : ℝ)*X 1 0+(4150819583/10000000000 : ℝ)*X 1 1+(1037705463/2500000000 : ℝ)*X 1 2+(36208869/80000000 : ℝ)*X 2 0+(4150819583/10000000000 : ℝ)*X 2 1+(1037705463/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1751291851/10000000000 : ℝ)*X 0 0+(5511543261/10000000000 : ℝ)*X 0 1+(2042371/3906250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5392457147/10000000000 : ℝ)*X 1 0+(-9576393/50000000 : ℝ)*X 1 1+(1045693887/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((53924569/100000000 : ℝ)*X 2 0+(163389659/312500000 : ℝ)*X 2 1+(-9576397/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2013341803/5000000000 : ℝ)*X 0 0+(880104609/2000000000 : ℝ)*X 0 1+(880104809/2000000000 : ℝ)*X 0 2+(2013341803/5000000000 : ℝ)*X 1 0+(880104609/2000000000 : ℝ)*X 1 1+(880104809/2000000000 : ℝ)*X 1 2+(2013341803/5000000000 : ℝ)*X 2 0+(880104609/2000000000 : ℝ)*X 2 1+(880104809/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31867/50000 : ℝ) ≤ (-1267164129676821111964077486651/1988281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (983139/12500000000000 : ℝ)*(upper1) + (154003/1562500000000 : ℝ)*(lower4) + (580329/100000000000000 : ℝ)*(upper5) + (277185590379183/12500000000000 : ℝ)*(major0) + (277185590379183/12500000000000 : ℝ)*(major1) + (277185590379183/12500000000000 : ℝ)*(major2) + (870268499/50000000000000 : ℝ)*(sp1) + (105596443/25000000000000 : ℝ)*(sp3) + (3096290424201171/100000000000000 : ℝ)*(sp4) + (1548145040989289/50000000000000 : ℝ)*(sp5) + (1548133538337311/50000000000000 : ℝ)*(sp6) + (1359921079174563/100000000000000 : ℝ)*(sp7) + (349578601/25000000000000 : ℝ)*(sp12) + (12372920477/50000000000000 : ℝ)*(sp14) + (271984300312067/20000000000000 : ℝ)*(f.failure) + (387036477814447/12500000000000 : ℝ)*(f.sum) + (1046510101229/2545000000000000000000000000 : ℝ)*base66 + (13099440589103691/15906250000000000000000000000000 : ℝ)*base67 + (27424946304865059/15906250000000000000000000000000 : ℝ)*base70 + (119818298429333809/15906250000000000000000000000000 : ℝ)*base72 + (6949565715159/2545000000000000000000000000 : ℝ)*base74 + (50515620247427559/15906250000000000000000000000000 : ℝ)*base76 + (82335740502333809/15906250000000000000000000000000 : ℝ)*base78 + (20123514317146309/15906250000000000000000000000000 : ℝ)*base80 + (5629400286703/1272500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10188147/2000000000000000000000 : ℝ)*base90 + (10188147/2000000000000000000000 : ℝ)*base92 + (10188147/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58609/100000 : ℝ) ≤ (9322866102503462825687750204007/15906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (221991/12500000000000 : ℝ)*(upper0) + (460747/2000000000000 : ℝ)*(upper3) + (16309431/100000000000000 : ℝ)*(upper4) + (1146728895171497/50000000000000 : ℝ)*(major0) + (1146728895171497/50000000000000 : ℝ)*(major1) + (1146728895171497/50000000000000 : ℝ)*(major2) + (1580431997449547/50000000000000 : ℝ)*(sp0) + (1580420499719493/50000000000000 : ℝ)*(sp1) + (197553879423133/6250000000000 : ℝ)*(sp2) + (281302055712559/20000000000000 : ℝ)*(sp3) + (2733223729/100000000000000 : ℝ)*(sp6) + (202273691/25000000000000 : ℝ)*(sp8) + (2975569359/12500000000000 : ℝ)*(sp9) + (3385144383/100000000000000 : ℝ)*(sp11) + (703256831853589/50000000000000 : ℝ)*(f.failure) + (1580432401996929/50000000000000 : ℝ)*(f.sum) + (2383122753289/2545000000000000000000000000 : ℝ)*base66 + (473883354740584081/63625000000000000000000000000000 : ℝ)*base68 + (632617241731959081/63625000000000000000000000000000 : ℝ)*base70 + (516011161510709081/63625000000000000000000000000000 : ℝ)*base72 + (582801037423/79531250000000000000000000 : ℝ)*base73 + (511165908179959081/63625000000000000000000000000000 : ℝ)*base76 + (41333155197709081/63625000000000000000000000000000 : ℝ)*base78 + (399876726688040919/63625000000000000000000000000000 : ℝ)*base79 + (4347887821539/2545000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (45625051/5000000000000000000000 : ℝ)*base89 + (45625051/5000000000000000000000 : ℝ)*base91 + (45625051/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20069/25000 : ℝ) ≤ (25538646050870548454514825185691/31812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9404059/20000000000000 : ℝ)*(upper0) + (133304617/25000000000000 : ℝ)*(upper2) + (16899577/20000000000000 : ℝ)*(lower3) + (1243915963783811/50000000000000 : ℝ)*(major0) + (1243915963783811/50000000000000 : ℝ)*(major1) + (1243915963783811/50000000000000 : ℝ)*(major2) + (3946678309/2500000000000 : ℝ)*(sp1) + (50627391407/100000000000000 : ℝ)*(sp2) + (18448023849/20000000000000 : ℝ)*(sp3) + (21004720291/100000000000000 : ℝ)*(sp4) + (3423165401828197/100000000000000 : ℝ)*(sp8) + (53484820928377/1562500000000 : ℝ)*(sp9) + (1711567889578541/50000000000000 : ℝ)*(sp10) + (381406414480761/25000000000000 : ℝ)*(sp11) + (1525717898042289/100000000000000 : ℝ)*(f.failure) + (427898300818561/12500000000000 : ℝ)*(f.sum) + (14757551807147/2545000000000000000000000000 : ℝ)*base66 + (69363320694149397/63625000000000000000000000000000 : ℝ)*base67 + (351476604515350603/63625000000000000000000000000000 : ℝ)*base70 + (274724955696649397/63625000000000000000000000000000 : ℝ)*base71 + (34678016106743/2545000000000000000000000000 : ℝ)*base73 + (174332239441975603/63625000000000000000000000000000 : ℝ)*base76 + (451853716393350603/63625000000000000000000000000000 : ℝ)*base78 + (88351778110725603/63625000000000000000000000000000 : ℝ)*base80 + (1791785100517/2545000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (16148351/10000000000000000000000 : ℝ)*base89 + (16148351/10000000000000000000000 : ℝ)*base91 + (16148351/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-10747/12500 : ℝ) ≤ (-3418794515870207116105210817043/3976562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (7687461/100000000000000 : ℝ)*(lower0) + (2852657/100000000000000 : ℝ)*(lower1) + (427187/12500000000000 : ℝ)*(lower3) + (306937373/100000000000000 : ℝ)*(lower4) + (19740715035009/781250000000 : ℝ)*(major0) + (19740715035009/781250000000 : ℝ)*(major1) + (2526811524481153/100000000000000 : ℝ)*(major2) + (76046626303/100000000000000 : ℝ)*(sp5) + (286014588117/100000000000000 : ℝ)*(sp6) + (19459903569/25000000000000 : ℝ)*(sp7) + (1766328961688159/50000000000000 : ℝ)*(sp12) + (706516375350003/20000000000000 : ℝ)*(sp13) + (1766185954394101/50000000000000 : ℝ)*(sp14) + (1549545157486531/100000000000000 : ℝ)*(sp15) + (1549622997100807/100000000000000 : ℝ)*(f.failure) + (1766328961688159/50000000000000 : ℝ)*(f.sum) + (322044209947/63625000000000000000000000 : ℝ)*base66 + (12120252425794319/7953125000000000000000000000000 : ℝ)*base67 + (579613731259419369/127250000000000000000000000000000 : ℝ)*base70 + (69489214129643181/7953125000000000000000000000000 : ℝ)*base72 + (112704270821/63625000000000000000000000 : ℝ)*base73 + (661031621122830631/127250000000000000000000000000000 : ℝ)*base75 + (28888653131785653/3976562500000000000000000000000 : ℝ)*base78 + (47797451463441/497070312500000000000000000000 : ℝ)*base80 + (878042304867/2545000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (88125513/10000000000000000000000 : ℝ)*base89 + (88125513/10000000000000000000000 : ℝ)*base91 + (11874487/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1508_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (109/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31867/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58609/100000 : ℝ) else (20069/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10747/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1508_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1508_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31867/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58609/100000 : ℝ) else (20069/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10747/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1508_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1508_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31867/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58609/100000 : ℝ) else (20069/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10747/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1508_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
