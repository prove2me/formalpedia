-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1127_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:12:31.937908+00:00
-- url     : https://prove2.me/submissions/54bcae96-f487-4bab-a626-a0be288bf441

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
theorem support_rectangle_w1127_box_0 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-409336897/2000000000 : ℝ)*x 0 + (5376525749/10000000000 : ℝ)*x 1 + (5376525629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409336897/2000000000 : ℝ)^65 ≤ (12192364144817/100000000000000 : ℝ)^49 := by
    have hnat : (409336897 : ℕ)^65*100000000000000^49 ≤ 12192364144817^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409336897 2000000000 12192364144817 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376525749/10000000000 : ℝ)^65 ≤ (43903818566219/100000000000000 : ℝ)^49 := by
    have hnat : (5376525749 : ℕ)^65*100000000000000^49 ≤ 43903818566219^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376525749 10000000000 43903818566219 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376525629/10000000000 : ℝ)^65 ≤ (43903817266351/100000000000000 : ℝ)^49 := by
    have hnat : (5376525629 : ℕ)^65*100000000000000^49 ≤ 43903817266351^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376525629 10000000000 43903817266351 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-409336897/2000000000 : ℝ), (5376525749/10000000000 : ℝ), (5376525629/10000000000 : ℝ)] ![(12192364144817/100000000000000 : ℝ), (43903818566219/100000000000000 : ℝ), (43903817266351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-409336897/2000000000 : ℝ)|^65 ≤ (12192364144817/100000000000000 : ℝ)^49
        have hw : |(-409336897/2000000000 : ℝ)|=(409336897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376525749/10000000000 : ℝ)|^65 ≤ (43903818566219/100000000000000 : ℝ)^49
        have hw : |(5376525749/10000000000 : ℝ)|=(5376525749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376525629/10000000000 : ℝ)|^65 ≤ (43903817266351/100000000000000 : ℝ)^49
        have hw : |(5376525629/10000000000 : ℝ)|=(5376525629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_1 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2647920253/5000000000 : ℝ)*x 0 + (-2156069759/10000000000 : ℝ)*x 1 + (336032861/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647920253/5000000000 : ℝ)^65 ≤ (43031966181367/100000000000000 : ℝ)^49 := by
    have hnat : (2647920253 : ℕ)^65*100000000000000^49 ≤ 43031966181367^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647920253 5000000000 43031966181367 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156069759/10000000000 : ℝ)^65 ≤ (653210746947/5000000000000 : ℝ)^49 := by
    have hnat : (2156069759 : ℕ)^65*5000000000000^49 ≤ 653210746947^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156069759 10000000000 653210746947 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336032861/625000000 : ℝ)^65 ≤ (43903818858689/100000000000000 : ℝ)^49 := by
    have hnat : (336032861 : ℕ)^65*100000000000000^49 ≤ 43903818858689^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336032861 625000000 43903818858689 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647920253/5000000000 : ℝ), (-2156069759/10000000000 : ℝ), (336032861/625000000 : ℝ)] ![(43031966181367/100000000000000 : ℝ), (653210746947/5000000000000 : ℝ), (43903818858689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647920253/5000000000 : ℝ)|^65 ≤ (43031966181367/100000000000000 : ℝ)^49
        have hw : |(2647920253/5000000000 : ℝ)|=(2647920253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2156069759/10000000000 : ℝ)|^65 ≤ (653210746947/5000000000000 : ℝ)^49
        have hw : |(-2156069759/10000000000 : ℝ)|=(2156069759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336032861/625000000 : ℝ)|^65 ≤ (43903818858689/100000000000000 : ℝ)^49
        have hw : |(336032861/625000000 : ℝ)|=(336032861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_2 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5295840689/10000000000 : ℝ)*x 0 + (672065701/1250000000 : ℝ)*x 1 + (-2156069741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295840689/10000000000 : ℝ)^65 ≤ (21515984076951/50000000000000 : ℝ)^49 := by
    have hnat : (5295840689 : ℕ)^65*50000000000000^49 ≤ 21515984076951^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295840689 10000000000 21515984076951 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672065701/1250000000 : ℝ)^65 ≤ (351230536311/800000000000 : ℝ)^49 := by
    have hnat : (672065701 : ℕ)^65*800000000000^49 ≤ 351230536311^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672065701 1250000000 351230536311 800000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156069741/10000000000 : ℝ)^65 ≤ (653210739713/5000000000000 : ℝ)^49 := by
    have hnat : (2156069741 : ℕ)^65*5000000000000^49 ≤ 653210739713^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156069741 10000000000 653210739713 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295840689/10000000000 : ℝ), (672065701/1250000000 : ℝ), (-2156069741/10000000000 : ℝ)] ![(21515984076951/50000000000000 : ℝ), (351230536311/800000000000 : ℝ), (653210739713/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295840689/10000000000 : ℝ)|^65 ≤ (21515984076951/50000000000000 : ℝ)^49
        have hw : |(5295840689/10000000000 : ℝ)|=(5295840689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672065701/1250000000 : ℝ)|^65 ≤ (351230536311/800000000000 : ℝ)^49
        have hw : |(672065701/1250000000 : ℝ)|=(672065701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2156069741/10000000000 : ℝ)|^65 ≤ (653210739713/5000000000000 : ℝ)^49
        have hw : |(-2156069741/10000000000 : ℝ)|=(2156069741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_3 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4474505163/10000000000 : ℝ)*x 0 + (4315055167/10000000000 : ℝ)*x 1 + (4315055517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4474505163/10000000000 : ℝ)^65 ≤ (34411417992583/100000000000000 : ℝ)^49 := by
    have hnat : (4474505163 : ℕ)^65*100000000000000^49 ≤ 34411417992583^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474505163 10000000000 34411417992583 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4315055167/10000000000 : ℝ)^65 ≤ (16397144615349/50000000000000 : ℝ)^49 := by
    have hnat : (4315055167 : ℕ)^65*50000000000000^49 ≤ 16397144615349^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315055167 10000000000 16397144615349 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4315055517/10000000000 : ℝ)^65 ≤ (4099286594907/12500000000000 : ℝ)^49 := by
    have hnat : (4315055517 : ℕ)^65*12500000000000^49 ≤ 4099286594907^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315055517 10000000000 4099286594907 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4474505163/10000000000 : ℝ), (4315055167/10000000000 : ℝ), (4315055517/10000000000 : ℝ)] ![(34411417992583/100000000000000 : ℝ), (16397144615349/50000000000000 : ℝ), (4099286594907/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4474505163/10000000000 : ℝ)|^65 ≤ (34411417992583/100000000000000 : ℝ)^49
        have hw : |(4474505163/10000000000 : ℝ)|=(4474505163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4315055167/10000000000 : ℝ)|^65 ≤ (16397144615349/50000000000000 : ℝ)^49
        have hw : |(4315055167/10000000000 : ℝ)|=(4315055167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4315055517/10000000000 : ℝ)|^65 ≤ (4099286594907/12500000000000 : ℝ)^49
        have hw : |(4315055517/10000000000 : ℝ)|=(4315055517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_4 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2302866369/10000000000 : ℝ)*x 0 + (2640471721/5000000000 : ℝ)*x 1 + (5280944181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2302866369/10000000000 : ℝ)^65 ≤ (3564264839727/25000000000000 : ℝ)^49 := by
    have hnat : (2302866369 : ℕ)^65*25000000000000^49 ≤ 3564264839727^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2302866369 10000000000 3564264839727 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640471721/5000000000 : ℝ)^65 ≤ (21435733166481/50000000000000 : ℝ)^49 := by
    have hnat : (2640471721 : ℕ)^65*50000000000000^49 ≤ 21435733166481^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640471721 5000000000 21435733166481 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280944181/10000000000 : ℝ)^65 ≤ (4287147429123/10000000000000 : ℝ)^49 := by
    have hnat : (5280944181 : ℕ)^65*10000000000000^49 ≤ 4287147429123^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280944181 10000000000 4287147429123 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2302866369/10000000000 : ℝ), (2640471721/5000000000 : ℝ), (5280944181/10000000000 : ℝ)] ![(3564264839727/25000000000000 : ℝ), (21435733166481/50000000000000 : ℝ), (4287147429123/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2302866369/10000000000 : ℝ)|^65 ≤ (3564264839727/25000000000000 : ℝ)^49
        have hw : |(-2302866369/10000000000 : ℝ)|=(2302866369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640471721/5000000000 : ℝ)|^65 ≤ (21435733166481/50000000000000 : ℝ)^49
        have hw : |(2640471721/5000000000 : ℝ)|=(2640471721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280944181/10000000000 : ℝ)|^65 ≤ (4287147429123/10000000000000 : ℝ)^49
        have hw : |(5280944181/10000000000 : ℝ)|=(5280944181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_5 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2681695817/5000000000 : ℝ)*x 0 + (-548405917/2500000000 : ℝ)*x 1 + (660118033/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681695817/5000000000 : ℝ)^65 ≤ (43761603595997/100000000000000 : ℝ)^49 := by
    have hnat : (2681695817 : ℕ)^65*100000000000000^49 ≤ 43761603595997^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681695817 5000000000 43761603595997 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548405917/2500000000 : ℝ)^65 ≤ (1670865150707/12500000000000 : ℝ)^49 := by
    have hnat : (548405917 : ℕ)^65*12500000000000^49 ≤ 1670865150707^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548405917 2500000000 1670865150707 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660118033/1250000000 : ℝ)^65 ≤ (21435737592527/50000000000000 : ℝ)^49 := by
    have hnat : (660118033 : ℕ)^65*50000000000000^49 ≤ 21435737592527^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660118033 1250000000 21435737592527 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681695817/5000000000 : ℝ), (-548405917/2500000000 : ℝ), (660118033/1250000000 : ℝ)] ![(43761603595997/100000000000000 : ℝ), (1670865150707/12500000000000 : ℝ), (21435737592527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681695817/5000000000 : ℝ)|^65 ≤ (43761603595997/100000000000000 : ℝ)^49
        have hw : |(2681695817/5000000000 : ℝ)|=(2681695817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-548405917/2500000000 : ℝ)|^65 ≤ (1670865150707/12500000000000 : ℝ)^49
        have hw : |(-548405917/2500000000 : ℝ)|=(548405917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660118033/1250000000 : ℝ)|^65 ≤ (21435737592527/50000000000000 : ℝ)^49
        have hw : |(660118033/1250000000 : ℝ)|=(660118033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_6 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5363392381/10000000000 : ℝ)*x 0 + (1320235923/2500000000 : ℝ)*x 1 + (-219362343/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363392381/10000000000 : ℝ)^65 ≤ (43761611681213/100000000000000 : ℝ)^49 := by
    have hnat : (5363392381 : ℕ)^65*100000000000000^49 ≤ 43761611681213^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363392381 10000000000 43761611681213 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320235923/2500000000 : ℝ)^65 ≤ (10717867256301/25000000000000 : ℝ)^49 := by
    have hnat : (1320235923 : ℕ)^65*25000000000000^49 ≤ 10717867256301^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320235923 2500000000 10717867256301 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219362343/1000000000 : ℝ)^65 ≤ (13366919281841/100000000000000 : ℝ)^49 := by
    have hnat : (219362343 : ℕ)^65*100000000000000^49 ≤ 13366919281841^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219362343 1000000000 13366919281841 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363392381/10000000000 : ℝ), (1320235923/2500000000 : ℝ), (-219362343/1000000000 : ℝ)] ![(43761611681213/100000000000000 : ℝ), (10717867256301/25000000000000 : ℝ), (13366919281841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363392381/10000000000 : ℝ)|^65 ≤ (43761611681213/100000000000000 : ℝ)^49
        have hw : |(5363392381/10000000000 : ℝ)|=(5363392381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320235923/2500000000 : ℝ)|^65 ≤ (10717867256301/25000000000000 : ℝ)^49
        have hw : |(1320235923/2500000000 : ℝ)|=(1320235923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219362343/1000000000 : ℝ)|^65 ≤ (13366919281841/100000000000000 : ℝ)^49
        have hw : |(-219362343/1000000000 : ℝ)|=(219362343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_7 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (851745053/2000000000 : ℝ)*x 0 + (1105731273/2500000000 : ℝ)*x 1 + (884584713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851745053/2000000000 : ℝ)^65 ≤ (32227608030107/100000000000000 : ℝ)^49 := by
    have hnat : (851745053 : ℕ)^65*100000000000000^49 ≤ 32227608030107^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851745053 2000000000 32227608030107 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105731273/2500000000 : ℝ)^65 ≤ (2117887733609/6250000000000 : ℝ)^49 := by
    have hnat : (1105731273 : ℕ)^65*6250000000000^49 ≤ 2117887733609^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105731273 2500000000 2117887733609 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (884584713/2000000000 : ℝ)^65 ≤ (33886188218533/100000000000000 : ℝ)^49 := by
    have hnat : (884584713 : ℕ)^65*100000000000000^49 ≤ 33886188218533^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884584713 2000000000 33886188218533 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851745053/2000000000 : ℝ), (1105731273/2500000000 : ℝ), (884584713/2000000000 : ℝ)] ![(32227608030107/100000000000000 : ℝ), (2117887733609/6250000000000 : ℝ), (33886188218533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851745053/2000000000 : ℝ)|^65 ≤ (32227608030107/100000000000000 : ℝ)^49
        have hw : |(851745053/2000000000 : ℝ)|=(851745053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105731273/2500000000 : ℝ)|^65 ≤ (2117887733609/6250000000000 : ℝ)^49
        have hw : |(1105731273/2500000000 : ℝ)|=(1105731273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(884584713/2000000000 : ℝ)|^65 ≤ (33886188218533/100000000000000 : ℝ)^49
        have hw : |(884584713/2000000000 : ℝ)|=(884584713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_8 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-44986247/200000000 : ℝ)*x 0 + (2607983757/5000000000 : ℝ)*x 1 + (5386133783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44986247/200000000 : ℝ)^65 ≤ (13818922517337/100000000000000 : ℝ)^49 := by
    have hnat : (44986247 : ℕ)^65*100000000000000^49 ≤ 13818922517337^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44986247 200000000 13818922517337 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607983757/5000000000 : ℝ)^65 ≤ (10543288031537/25000000000000 : ℝ)^49 := by
    have hnat : (2607983757 : ℕ)^65*25000000000000^49 ≤ 10543288031537^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607983757 5000000000 10543288031537 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386133783/10000000000 : ℝ)^65 ≤ (44007925346097/100000000000000 : ℝ)^49 := by
    have hnat : (5386133783 : ℕ)^65*100000000000000^49 ≤ 44007925346097^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386133783 10000000000 44007925346097 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44986247/200000000 : ℝ), (2607983757/5000000000 : ℝ), (5386133783/10000000000 : ℝ)] ![(13818922517337/100000000000000 : ℝ), (10543288031537/25000000000000 : ℝ), (44007925346097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44986247/200000000 : ℝ)|^65 ≤ (13818922517337/100000000000000 : ℝ)^49
        have hw : |(-44986247/200000000 : ℝ)|=(44986247/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607983757/5000000000 : ℝ)|^65 ≤ (10543288031537/25000000000000 : ℝ)^49
        have hw : |(2607983757/5000000000 : ℝ)|=(2607983757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386133783/10000000000 : ℝ)|^65 ≤ (44007925346097/100000000000000 : ℝ)^49
        have hw : |(5386133783/10000000000 : ℝ)|=(5386133783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_9 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5289046847/10000000000 : ℝ)*x 0 + (-2152225087/10000000000 : ℝ)*x 1 + (2693066889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289046847/10000000000 : ℝ)^65 ≤ (42958753499029/100000000000000 : ℝ)^49 := by
    have hnat : (5289046847 : ℕ)^65*100000000000000^49 ≤ 42958753499029^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289046847 10000000000 42958753499029 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2152225087/10000000000 : ℝ)^65 ≤ (203645643637/1562500000000 : ℝ)^49 := by
    have hnat : (2152225087 : ℕ)^65*1562500000000^49 ≤ 203645643637^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152225087 10000000000 203645643637 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693066889/5000000000 : ℝ)^65 ≤ (343811916343/781250000000 : ℝ)^49 := by
    have hnat : (2693066889 : ℕ)^65*781250000000^49 ≤ 343811916343^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693066889 5000000000 343811916343 781250000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289046847/10000000000 : ℝ), (-2152225087/10000000000 : ℝ), (2693066889/5000000000 : ℝ)] ![(42958753499029/100000000000000 : ℝ), (203645643637/1562500000000 : ℝ), (343811916343/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289046847/10000000000 : ℝ)|^65 ≤ (42958753499029/100000000000000 : ℝ)^49
        have hw : |(5289046847/10000000000 : ℝ)|=(5289046847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2152225087/10000000000 : ℝ)|^65 ≤ (203645643637/1562500000000 : ℝ)^49
        have hw : |(-2152225087/10000000000 : ℝ)|=(2152225087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693066889/5000000000 : ℝ)|^65 ≤ (343811916343/781250000000 : ℝ)^49
        have hw : |(2693066889/5000000000 : ℝ)|=(2693066889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_10 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5289047453/10000000000 : ℝ)*x 0 + (5386132937/10000000000 : ℝ)*x 1 + (-2152225409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289047453/10000000000 : ℝ)^65 ≤ (10739690007073/25000000000000 : ℝ)^49 := by
    have hnat : (5289047453 : ℕ)^65*25000000000000^49 ≤ 10739690007073^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289047453 10000000000 10739690007073 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386132937/10000000000 : ℝ)^65 ≤ (44007916176687/100000000000000 : ℝ)^49 := by
    have hnat : (5386132937 : ℕ)^65*100000000000000^49 ≤ 44007916176687^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386132937 10000000000 44007916176687 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152225409/10000000000 : ℝ)^65 ≤ (2606664755887/20000000000000 : ℝ)^49 := by
    have hnat : (2152225409 : ℕ)^65*20000000000000^49 ≤ 2606664755887^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152225409 10000000000 2606664755887 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289047453/10000000000 : ℝ), (5386132937/10000000000 : ℝ), (-2152225409/10000000000 : ℝ)] ![(10739690007073/25000000000000 : ℝ), (44007916176687/100000000000000 : ℝ), (2606664755887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289047453/10000000000 : ℝ)|^65 ≤ (10739690007073/25000000000000 : ℝ)^49
        have hw : |(5289047453/10000000000 : ℝ)|=(5289047453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386132937/10000000000 : ℝ)|^65 ≤ (44007916176687/100000000000000 : ℝ)^49
        have hw : |(5386132937/10000000000 : ℝ)|=(5386132937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2152225409/10000000000 : ℝ)|^65 ≤ (2606664755887/20000000000000 : ℝ)^49
        have hw : |(-2152225409/10000000000 : ℝ)|=(2152225409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_11 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4495923097/10000000000 : ℝ)*x 0 + (4304205601/10000000000 : ℝ)*x 1 + (107605151/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4495923097/10000000000 : ℝ)^65 ≤ (216438056581/625000000000 : ℝ)^49 := by
    have hnat : (4495923097 : ℕ)^65*625000000000^49 ≤ 216438056581^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495923097 10000000000 216438056581 625000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4304205601/10000000000 : ℝ)^65 ≤ (32684953252499/100000000000000 : ℝ)^49 := by
    have hnat : (4304205601 : ℕ)^65*100000000000000^49 ≤ 32684953252499^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304205601 10000000000 32684953252499 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107605151/250000000 : ℝ)^65 ≤ (32684957674681/100000000000000 : ℝ)^49 := by
    have hnat : (107605151 : ℕ)^65*100000000000000^49 ≤ 32684957674681^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107605151 250000000 32684957674681 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4495923097/10000000000 : ℝ), (4304205601/10000000000 : ℝ), (107605151/250000000 : ℝ)] ![(216438056581/625000000000 : ℝ), (32684953252499/100000000000000 : ℝ), (32684957674681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4495923097/10000000000 : ℝ)|^65 ≤ (216438056581/625000000000 : ℝ)^49
        have hw : |(4495923097/10000000000 : ℝ)|=(4495923097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4304205601/10000000000 : ℝ)|^65 ≤ (32684953252499/100000000000000 : ℝ)^49
        have hw : |(4304205601/10000000000 : ℝ)|=(4304205601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107605151/250000000 : ℝ)|^65 ≤ (32684957674681/100000000000000 : ℝ)^49
        have hw : |(107605151/250000000 : ℝ)|=(107605151/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_12 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050283641/5000000000 : ℝ)*x 0 + (5440212887/10000000000 : ℝ)*x 1 + (2636455869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050283641/5000000000 : ℝ)^65 ≤ (394374451377/3125000000000 : ℝ)^49 := by
    have hnat : (1050283641 : ℕ)^65*3125000000000^49 ≤ 394374451377^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050283641 5000000000 394374451377 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440212887/10000000000 : ℝ)^65 ≤ (11148755722549/25000000000000 : ℝ)^49 := by
    have hnat : (5440212887 : ℕ)^65*25000000000000^49 ≤ 11148755722549^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440212887 10000000000 11148755722549 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636455869/5000000000 : ℝ)^65 ≤ (42784994651501/100000000000000 : ℝ)^49 := by
    have hnat : (2636455869 : ℕ)^65*100000000000000^49 ≤ 42784994651501^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636455869 5000000000 42784994651501 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050283641/5000000000 : ℝ), (5440212887/10000000000 : ℝ), (2636455869/5000000000 : ℝ)] ![(394374451377/3125000000000 : ℝ), (11148755722549/25000000000000 : ℝ), (42784994651501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050283641/5000000000 : ℝ)|^65 ≤ (394374451377/3125000000000 : ℝ)^49
        have hw : |(-1050283641/5000000000 : ℝ)|=(1050283641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440212887/10000000000 : ℝ)|^65 ≤ (11148755722549/25000000000000 : ℝ)^49
        have hw : |(5440212887/10000000000 : ℝ)|=(5440212887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636455869/5000000000 : ℝ)|^65 ≤ (42784994651501/100000000000000 : ℝ)^49
        have hw : |(2636455869/5000000000 : ℝ)|=(2636455869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_13 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1073813263/2000000000 : ℝ)*x 0 + (-109836097/500000000 : ℝ)*x 1 + (659113963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073813263/2000000000 : ℝ)^65 ≤ (43823034575959/100000000000000 : ℝ)^49 := by
    have hnat : (1073813263 : ℕ)^65*100000000000000^49 ≤ 43823034575959^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073813263 2000000000 43823034575959 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109836097/500000000 : ℝ)^65 ≤ (1339197111663/10000000000000 : ℝ)^49 := by
    have hnat : (109836097 : ℕ)^65*10000000000000^49 ≤ 1339197111663^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109836097 500000000 1339197111663 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659113963/1250000000 : ℝ)^65 ≤ (21392497142769/50000000000000 : ℝ)^49 := by
    have hnat : (659113963 : ℕ)^65*50000000000000^49 ≤ 21392497142769^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659113963 1250000000 21392497142769 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073813263/2000000000 : ℝ), (-109836097/500000000 : ℝ), (659113963/1250000000 : ℝ)] ![(43823034575959/100000000000000 : ℝ), (1339197111663/10000000000000 : ℝ), (21392497142769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073813263/2000000000 : ℝ)|^65 ≤ (43823034575959/100000000000000 : ℝ)^49
        have hw : |(1073813263/2000000000 : ℝ)|=(1073813263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109836097/500000000 : ℝ)|^65 ≤ (1339197111663/10000000000000 : ℝ)^49
        have hw : |(-109836097/500000000 : ℝ)|=(109836097/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659113963/1250000000 : ℝ)|^65 ≤ (21392497142769/50000000000000 : ℝ)^49
        have hw : |(659113963/1250000000 : ℝ)|=(659113963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_14 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1342266583/2500000000 : ℝ)*x 0 + (5272911763/10000000000 : ℝ)*x 1 + (-1098360919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342266583/2500000000 : ℝ)^65 ≤ (43823034760023/100000000000000 : ℝ)^49 := by
    have hnat : (1342266583 : ℕ)^65*100000000000000^49 ≤ 43823034760023^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342266583 2500000000 43823034760023 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272911763/10000000000 : ℝ)^65 ≤ (42784994920591/100000000000000 : ℝ)^49 := by
    have hnat : (5272911763 : ℕ)^65*100000000000000^49 ≤ 42784994920591^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272911763 10000000000 42784994920591 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098360919/5000000000 : ℝ)^65 ≤ (13391970291757/100000000000000 : ℝ)^49 := by
    have hnat : (1098360919 : ℕ)^65*100000000000000^49 ≤ 13391970291757^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098360919 5000000000 13391970291757 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342266583/2500000000 : ℝ), (5272911763/10000000000 : ℝ), (-1098360919/5000000000 : ℝ)] ![(43823034760023/100000000000000 : ℝ), (42784994920591/100000000000000 : ℝ), (13391970291757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342266583/2500000000 : ℝ)|^65 ≤ (43823034760023/100000000000000 : ℝ)^49
        have hw : |(1342266583/2500000000 : ℝ)|=(1342266583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272911763/10000000000 : ℝ)|^65 ≤ (42784994920591/100000000000000 : ℝ)^49
        have hw : |(5272911763/10000000000 : ℝ)|=(5272911763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1098360919/5000000000 : ℝ)|^65 ≤ (13391970291757/100000000000000 : ℝ)^49
        have hw : |(-1098360919/5000000000 : ℝ)|=(1098360919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_box_15 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2120180843/5000000000 : ℝ)*x 0 + (2215992009/5000000000 : ℝ)*x 1 + (4431983929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120180843/5000000000 : ℝ)^65 ≤ (32043396459239/100000000000000 : ℝ)^49 := by
    have hnat : (2120180843 : ℕ)^65*100000000000000^49 ≤ 32043396459239^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120180843 5000000000 32043396459239 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2215992009/5000000000 : ℝ)^65 ≤ (16989151108337/50000000000000 : ℝ)^49 := by
    have hnat : (2215992009 : ℕ)^65*50000000000000^49 ≤ 16989151108337^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215992009 5000000000 16989151108337 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4431983929/10000000000 : ℝ)^65 ≤ (4247287663943/12500000000000 : ℝ)^49 := by
    have hnat : (4431983929 : ℕ)^65*12500000000000^49 ≤ 4247287663943^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431983929 10000000000 4247287663943 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120180843/5000000000 : ℝ), (2215992009/5000000000 : ℝ), (4431983929/10000000000 : ℝ)] ![(32043396459239/100000000000000 : ℝ), (16989151108337/50000000000000 : ℝ), (4247287663943/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120180843/5000000000 : ℝ)|^65 ≤ (32043396459239/100000000000000 : ℝ)^49
        have hw : |(2120180843/5000000000 : ℝ)|=(2120180843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2215992009/5000000000 : ℝ)|^65 ≤ (16989151108337/50000000000000 : ℝ)^49
        have hw : |(2215992009/5000000000 : ℝ)|=(2215992009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4431983929/10000000000 : ℝ)|^65 ≤ (4247287663943/12500000000000 : ℝ)^49
        have hw : |(4431983929/10000000000 : ℝ)|=(4431983929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1127_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62229/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59287/100000 : ℝ) ∧ (39881/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83091/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5667/50000 : ℝ) ^ (8319/2048 : ℝ) ≤ (3604404467958823/25000000000000000000 : ℝ) := by
    have hpowers : (5667/50000 : ℝ)^8319 ≤ (3604404467958823/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5667 : ℕ)^8319*25000000000000000000^2048 ≤ 3604404467958823^2048*50000^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5667 50000 3604404467958823 25000000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5667/50000 : ℝ)) (X := (3604404467958823/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (351/2500 : ℝ) ^ (8319/2048 : ℝ) ≤ (17201455822485231/50000000000000000000 : ℝ) := by
    have hpowers : (351/2500 : ℝ)^8319 ≤ (17201455822485231/50000000000000000000 : ℝ)^2048 := by
      have hnat : (351 : ℕ)^8319*50000000000000000000^2048 ≤ 17201455822485231^2048*2500^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 2500 17201455822485231 50000000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/2500 : ℝ)) (X := (17201455822485231/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503604404467958823/12500000000000000000 : ℝ) ≤ (10000709798601919/10000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (12503604404467958823/12500000000000000000 : ℝ)^2048 ≤ (10000709798601919/10000000000000000 : ℝ)^8319 := by
      have hnat : (12503604404467958823 : ℕ)^2048*10000000000000000^8319 ≤ 10000709798601919^8319*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503604404467958823 12500000000000000000 10000709798601919 10000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000709798601919/10000000000000000 : ℝ)) (X := (12503604404467958823/12500000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024410264758402877/50000000000000000000 : ℝ) ≤ (10001201659474697/10000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (50024410264758402877/50000000000000000000 : ℝ)^2048 ≤ (10001201659474697/10000000000000000 : ℝ)^8319 := by
      have hnat : (50024410264758402877 : ℕ)^2048*10000000000000000^8319 ≤ 10001201659474697^8319*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024410264758402877 50000000000000000000 10001201659474697 10000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001201659474697/10000000000000000 : ℝ)) (X := (50024410264758402877/50000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017201455822485231/25000000000000000000 : ℝ) ≤ (400067740813899/400000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (25017201455822485231/25000000000000000000 : ℝ)^2048 ≤ (400067740813899/400000000000000 : ℝ)^8319 := by
      have hnat : (25017201455822485231 : ℕ)^2048*400000000000000^8319 ≤ 400067740813899^8319*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017201455822485231 25000000000000000000 400067740813899 400000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400067740813899/400000000000000 : ℝ)) (X := (25017201455822485231/25000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3604404467958823/25000000000000000000 : ℝ) ≤ ((81972033978038367/82000000000000000 : ℝ)+2*(22357312399/12300000000000 : ℝ)*(5667/50000 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (81972033978038367/82000000000000000 : ℝ)+2*(22357312399/12300000000000 : ℝ)*(5667/50000 : ℝ)=(10000709798601919/10000000000000000 : ℝ) by norm_num, show 1+2*(3604404467958823/25000000000000000000 : ℝ)=(12503604404467958823/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17201455822485231/50000000000000000000 : ℝ)+(3604404467958823/25000000000000000000 : ℝ) ≤ ((81972033978038367/82000000000000000 : ℝ)+(22357312399/12300000000000 : ℝ)*((351/2500 : ℝ)+(5667/50000 : ℝ)))^(8319/2048 : ℝ) := by
    rw [show (81972033978038367/82000000000000000 : ℝ)+(22357312399/12300000000000 : ℝ)*((351/2500 : ℝ)+(5667/50000 : ℝ))=(10001201659474697/10000000000000000 : ℝ) by norm_num, show 1+(17201455822485231/50000000000000000000 : ℝ)+(3604404467958823/25000000000000000000 : ℝ)=(50024410264758402877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17201455822485231/50000000000000000000 : ℝ) ≤ ((81972033978038367/82000000000000000 : ℝ)+2*(22357312399/12300000000000 : ℝ)*(351/2500 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (81972033978038367/82000000000000000 : ℝ)+2*(22357312399/12300000000000 : ℝ)*(351/2500 : ℝ)=(400067740813899/400000000000000 : ℝ) by norm_num, show 1+2*(17201455822485231/50000000000000000000 : ℝ)=(25017201455822485231/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (81972033978038367/82000000000000000 : ℝ)*(X 1 0+X 2 0)+(22357312399/12300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (81972033978038367/82000000000000000 : ℝ)) (alpha := (22357312399/12300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (81972033978038367/82000000000000000 : ℝ)*(X 0 1+X 2 1)+(22357312399/12300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (81972033978038367/82000000000000000 : ℝ)) (alpha := (22357312399/12300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (81972033978038367/82000000000000000 : ℝ)*(X 0 2+X 1 2)+(22357312399/12300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (81972033978038367/82000000000000000 : ℝ)) (alpha := (22357312399/12300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-409336897/2000000000 : ℝ)*X 0 0+(5376525749/10000000000 : ℝ)*X 0 1+(5376525629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647920253/5000000000 : ℝ)*X 1 0+(-2156069759/10000000000 : ℝ)*X 1 1+(336032861/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295840689/10000000000 : ℝ)*X 2 0+(672065701/1250000000 : ℝ)*X 2 1+(-2156069741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4474505163/10000000000 : ℝ)*X 0 0+(4315055167/10000000000 : ℝ)*X 0 1+(4315055517/10000000000 : ℝ)*X 0 2+(4474505163/10000000000 : ℝ)*X 1 0+(4315055167/10000000000 : ℝ)*X 1 1+(4315055517/10000000000 : ℝ)*X 1 2+(4474505163/10000000000 : ℝ)*X 2 0+(4315055167/10000000000 : ℝ)*X 2 1+(4315055517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2302866369/10000000000 : ℝ)*X 0 0+(2640471721/5000000000 : ℝ)*X 0 1+(5280944181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681695817/5000000000 : ℝ)*X 1 0+(-548405917/2500000000 : ℝ)*X 1 1+(660118033/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363392381/10000000000 : ℝ)*X 2 0+(1320235923/2500000000 : ℝ)*X 2 1+(-219362343/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((851745053/2000000000 : ℝ)*X 0 0+(1105731273/2500000000 : ℝ)*X 0 1+(884584713/2000000000 : ℝ)*X 0 2+(851745053/2000000000 : ℝ)*X 1 0+(1105731273/2500000000 : ℝ)*X 1 1+(884584713/2000000000 : ℝ)*X 1 2+(851745053/2000000000 : ℝ)*X 2 0+(1105731273/2500000000 : ℝ)*X 2 1+(884584713/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-44986247/200000000 : ℝ)*X 0 0+(2607983757/5000000000 : ℝ)*X 0 1+(5386133783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289046847/10000000000 : ℝ)*X 1 0+(-2152225087/10000000000 : ℝ)*X 1 1+(2693066889/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289047453/10000000000 : ℝ)*X 2 0+(5386132937/10000000000 : ℝ)*X 2 1+(-2152225409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4495923097/10000000000 : ℝ)*X 0 0+(4304205601/10000000000 : ℝ)*X 0 1+(107605151/250000000 : ℝ)*X 0 2+(4495923097/10000000000 : ℝ)*X 1 0+(4304205601/10000000000 : ℝ)*X 1 1+(107605151/250000000 : ℝ)*X 1 2+(4495923097/10000000000 : ℝ)*X 2 0+(4304205601/10000000000 : ℝ)*X 2 1+(107605151/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1050283641/5000000000 : ℝ)*X 0 0+(5440212887/10000000000 : ℝ)*X 0 1+(2636455869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073813263/2000000000 : ℝ)*X 1 0+(-109836097/500000000 : ℝ)*X 1 1+(659113963/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342266583/2500000000 : ℝ)*X 2 0+(5272911763/10000000000 : ℝ)*X 2 1+(-1098360919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2120180843/5000000000 : ℝ)*X 0 0+(2215992009/5000000000 : ℝ)*X 0 1+(4431983929/10000000000 : ℝ)*X 0 2+(2120180843/5000000000 : ℝ)*X 1 0+(2215992009/5000000000 : ℝ)*X 1 1+(4431983929/10000000000 : ℝ)*X 1 2+(2120180843/5000000000 : ℝ)*X 2 0+(2215992009/5000000000 : ℝ)*X 2 1+(4431983929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62229/100000 : ℝ) ≤ (-637826739944450156758721999121/1025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (167826491/100000000000000 : ℝ)*(lower0) + (47194991/100000000000000 : ℝ)*(upper1) + (333859137/100000000000000 : ℝ)*(lower2) + (1895371/6250000000000 : ℝ)*(lower5) + (1953855316232979/50000000000000 : ℝ)*(major0) + (1953855316232979/50000000000000 : ℝ)*(major1) + (1953855316232979/50000000000000 : ℝ)*(major2) + (4903277477/100000000000000 : ℝ)*(sp3) + (521672210709457/10000000000000 : ℝ)*(sp4) + (5216624812574651/100000000000000 : ℝ)*(sp5) + (5216723197109793/100000000000000 : ℝ)*(sp6) + (1309717748775477/50000000000000 : ℝ)*(sp7) + (1090015223/100000000000000 : ℝ)*(sp8) + (49192267571/50000000000000 : ℝ)*(sp13) + (261944040082843/10000000000000 : ℝ)*(f.failure) + (5216723197109793/100000000000000 : ℝ)*(f.sum) + (205216362691/205000000000000000000000000 : ℝ)*base66 + (17826602238054707/4100000000000000000000000000000 : ℝ)*base68 + (26712984914954707/4100000000000000000000000000000 : ℝ)*base70 + (38960835485654707/4100000000000000000000000000000 : ℝ)*base72 + (13277529108219/205000000000000000000000000 : ℝ)*base73 + (29544845067745293/4100000000000000000000000000000 : ℝ)*base75 + (63466025728554707/4100000000000000000000000000000 : ℝ)*base78 + (17523203033454707/4100000000000000000000000000000 : ℝ)*base80 + (411233920469/205000000000000000000000000 : ℝ)*base81 + (2036117/250000000000000000000 : ℝ)*base90 + (2036117/250000000000000000000 : ℝ)*base92 + (2036117/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (59287/100000 : ℝ) ≤ (243086170151668104049499410271/410000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10349229/12500000000000 : ℝ)*(upper0) + (12482267/50000000000000 : ℝ)*(lower1) + (25589611/50000000000000 : ℝ)*(upper4) + (1252839/6250000000000 : ℝ)*(upper5) + (397163024216057/10000000000000 : ℝ)*(major0) + (397163024216057/10000000000000 : ℝ)*(major1) + (397163024216057/10000000000000 : ℝ)*(major2) + (20551601554671/390625000000 : ℝ)*(sp0) + (13153011295883/250000000000 : ℝ)*(sp1) + (2630599047992919/50000000000000 : ℝ)*(sp2) + (332785807416821/12500000000000 : ℝ)*(sp3) + (5479642577/100000000000000 : ℝ)*(sp5) + (461863211/50000000000000 : ℝ)*(sp7) + (5951004969/50000000000000 : ℝ)*(sp10) + (266228738306099/10000000000000 : ℝ)*(f.failure) + (20551601554671/390625000000 : ℝ)*(f.sum) + (45698945461/30750000000000000000000000 : ℝ)*base65 + (23411319218603243/2460000000000000000000000000000 : ℝ)*base68 + (41844983062163243/2460000000000000000000000000000 : ℝ)*base70 + (20359975877483243/2460000000000000000000000000000 : ℝ)*base72 + (128075790437/61500000000000000000000000 : ℝ)*base73 + (72232547385203243/2460000000000000000000000000000 : ℝ)*base76 + (32268910361363243/2460000000000000000000000000000 : ℝ)*base78 + (12386167936163243/2460000000000000000000000000000 : ℝ)*base80 + (203948386823/30750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1218819/250000000000000000000 : ℝ)*base89 + (1218819/250000000000000000000 : ℝ)*base91 + (1218819/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39881/50000 : ℝ) ≤ (39882266904307477302446138193/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2960941/2500000000000 : ℝ)*(upper0) + (21113763/12500000000000 : ℝ)*(lower3) + (144393843/100000000000000 : ℝ)*(lower5) + (2219813507100387/50000000000000 : ℝ)*(major0) + (2219813507100387/50000000000000 : ℝ)*(major1) + (2219813507100387/50000000000000 : ℝ)*(major2) + (11585117561/100000000000000 : ℝ)*(sp0) + (104840729303/20000000000000 : ℝ)*(sp1) + (157296348433/50000000000000 : ℝ)*(sp3) + (5876627592812593/100000000000000 : ℝ)*(sp8) + (1469035954005087/25000000000000 : ℝ)*(sp9) + (5876668019666863/100000000000000 : ℝ)*(sp10) + (1487841619050801/50000000000000 : ℝ)*(sp11) + (28841736709/100000000000000 : ℝ)*(sp12) + (2975997830798469/100000000000000 : ℝ)*(f.failure) + (5876668019666863/100000000000000 : ℝ)*(f.sum) + (24328475567/5000000000000000000000000 : ℝ)*base65 + (1075676931077269/100000000000000000000000000000 : ℝ)*base67 + (1262192337677269/100000000000000000000000000000 : ℝ)*base69 + (72210028922731/100000000000000000000000000000 : ℝ)*base72 + (120195134147/5000000000000000000000000 : ℝ)*base73 + (833507157722731/100000000000000000000000000000 : ℝ)*base76 + (33922911777269/100000000000000000000000000000 : ℝ)*base77 + (3083445355377269/100000000000000000000000000000 : ℝ)*base79 + (26735661287/5000000000000000000000000 : ℝ)*base81 + (5724789/2500000000000000000000 : ℝ)*base89 + (5724789/2500000000000000000000 : ℝ)*base91 + (5724789/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-83091/100000 : ℝ) ≤ (-106456992480823646178876923851/128125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7837107/25000000000000 : ℝ)*(lower0) + (41239/25000000000000 : ℝ)*(lower1) + (39983491/100000000000000 : ℝ)*(lower2) + (2458667/5000000000000 : ℝ)*(upper5) + (279652495051249/6250000000000 : ℝ)*(major0) + (279652495051249/6250000000000 : ℝ)*(major1) + (279652495051249/6250000000000 : ℝ)*(major2) + (524205113/25000000000000 : ℝ)*(sp0) + (52553048503/100000000000000 : ℝ)*(sp5) + (10840792131/100000000000000 : ℝ)*(sp7) + (74715500530827/1250000000000 : ℝ)*(sp12) + (5977189586238109/100000000000000 : ℝ)*(sp13) + (5977242139286611/100000000000000 : ℝ)*(sp14) + (93728843427697/3125000000000 : ℝ)*(sp15) + (599866766095687/20000000000000 : ℝ)*(f.failure) + (5977242139286611/100000000000000 : ℝ)*(f.sum) + (1402083221431/615000000000000000000000000 : ℝ)*base65 + (14636164413368851/1537500000000000000000000000000 : ℝ)*base68 + (3856541009881351/1537500000000000000000000000000 : ℝ)*base70 + (22997854325768851/1537500000000000000000000000000 : ℝ)*base72 + (12748277186179/153750000000000000000000000 : ℝ)*base73 + (1082809749868649/1537500000000000000000000000000 : ℝ)*base75 + (2750299446331351/1537500000000000000000000000000 : ℝ)*base78 + (4594879103056351/1537500000000000000000000000000 : ℝ)*base80 + (722514067621/615000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (446953/500000000000000000000 : ℝ)*base90 + (446953/500000000000000000000 : ℝ)*base92 + (446953/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1127_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59287/100000 : ℝ) else (39881/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83091/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1127_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1127_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59287/100000 : ℝ) else (39881/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83091/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1127_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59287/100000 : ℝ) else (39881/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83091/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1127_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
