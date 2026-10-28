-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1245_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:20:52.980911+00:00
-- url     : https://prove2.me/submissions/3adb3acf-dfa9-4ae1-8dad-d99320971285

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
theorem support_rectangle_w1245_s0_0 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-464908693/2500000000 : ℝ)*x 0 + (301541469/500000000 : ℝ)*x 1 + (958671829/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464908693/2500000000 : ℝ)^4219 ≤ (10846226036549/100000000000000 : ℝ)^3195 := by
    have hnat : (464908693 : ℕ)^4219*100000000000000^3195 ≤ 10846226036549^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464908693 2500000000 10846226036549 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301541469/500000000 : ℝ)^4219 ≤ (25642343658587/50000000000000 : ℝ)^3195 := by
    have hnat : (301541469 : ℕ)^4219*50000000000000^3195 ≤ 25642343658587^3195*500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301541469 500000000 25642343658587 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958671829/2000000000 : ℝ)^4219 ≤ (4733635828781/12500000000000 : ℝ)^3195 := by
    have hnat : (958671829 : ℕ)^4219*12500000000000^3195 ≤ 4733635828781^3195*2000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958671829 2000000000 4733635828781 12500000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464908693/2500000000 : ℝ), (301541469/500000000 : ℝ), (958671829/2000000000 : ℝ)] ![(10846226036549/100000000000000 : ℝ), (25642343658587/50000000000000 : ℝ), (4733635828781/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464908693/2500000000 : ℝ)|^4219 ≤ (10846226036549/100000000000000 : ℝ)^3195
        have hw : |(-464908693/2500000000 : ℝ)|=(464908693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301541469/500000000 : ℝ)|^4219 ≤ (25642343658587/50000000000000 : ℝ)^3195
        have hw : |(301541469/500000000 : ℝ)|=(301541469/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958671829/2000000000 : ℝ)|^4219 ≤ (4733635828781/12500000000000 : ℝ)^3195
        have hw : |(958671829/2000000000 : ℝ)|=(958671829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s0_1 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1377747621/2500000000 : ℝ)*x 0 + (-1283492849/5000000000 : ℝ)*x 1 + (4793359089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377747621/2500000000 : ℝ)^4219 ≤ (11382392928557/25000000000000 : ℝ)^3195 := by
    have hnat : (1377747621 : ℕ)^4219*25000000000000^3195 ≤ 11382392928557^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377747621 2500000000 11382392928557 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283492849/5000000000 : ℝ)^4219 ≤ (16601342223331/100000000000000 : ℝ)^3195 := by
    have hnat : (1283492849 : ℕ)^4219*100000000000000^3195 ≤ 16601342223331^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283492849 5000000000 16601342223331 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4793359089/10000000000 : ℝ)^4219 ≤ (7573817209207/20000000000000 : ℝ)^3195 := by
    have hnat : (4793359089 : ℕ)^4219*20000000000000^3195 ≤ 7573817209207^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793359089 10000000000 7573817209207 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377747621/2500000000 : ℝ), (-1283492849/5000000000 : ℝ), (4793359089/10000000000 : ℝ)] ![(11382392928557/25000000000000 : ℝ), (16601342223331/100000000000000 : ℝ), (7573817209207/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377747621/2500000000 : ℝ)|^4219 ≤ (11382392928557/25000000000000 : ℝ)^3195
        have hw : |(1377747621/2500000000 : ℝ)|=(1377747621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1283492849/5000000000 : ℝ)|^4219 ≤ (16601342223331/100000000000000 : ℝ)^3195
        have hw : |(-1283492849/5000000000 : ℝ)|=(1283492849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4793359089/10000000000 : ℝ)|^4219 ≤ (7573817209207/20000000000000 : ℝ)^3195
        have hw : |(4793359089/10000000000 : ℝ)|=(4793359089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s0_2 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2755495201/5000000000 : ℝ)*x 0 + (2396679587/5000000000 : ℝ)*x 1 + (-1283492849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755495201/5000000000 : ℝ)^4219 ≤ (22764785409827/50000000000000 : ℝ)^3195 := by
    have hnat : (2755495201 : ℕ)^4219*50000000000000^3195 ≤ 22764785409827^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755495201 5000000000 22764785409827 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2396679587/5000000000 : ℝ)^4219 ≤ (37869086932787/100000000000000 : ℝ)^3195 := by
    have hnat : (2396679587 : ℕ)^4219*100000000000000^3195 ≤ 37869086932787^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396679587 5000000000 37869086932787 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1283492849/5000000000 : ℝ)^4219 ≤ (16601342223331/100000000000000 : ℝ)^3195 := by
    have hnat : (1283492849 : ℕ)^4219*100000000000000^3195 ≤ 16601342223331^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283492849 5000000000 16601342223331 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755495201/5000000000 : ℝ), (2396679587/5000000000 : ℝ), (-1283492849/5000000000 : ℝ)] ![(22764785409827/50000000000000 : ℝ), (37869086932787/100000000000000 : ℝ), (16601342223331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755495201/5000000000 : ℝ)|^4219 ≤ (22764785409827/50000000000000 : ℝ)^3195
        have hw : |(2755495201/5000000000 : ℝ)|=(2755495201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2396679587/5000000000 : ℝ)|^4219 ≤ (37869086932787/100000000000000 : ℝ)^3195
        have hw : |(2396679587/5000000000 : ℝ)|=(2396679587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1283492849/5000000000 : ℝ)|^4219 ≤ (16601342223331/100000000000000 : ℝ)^3195
        have hw : |(-1283492849/5000000000 : ℝ)|=(1283492849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s0_3 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (838557203/2000000000 : ℝ)*x 0 + (3116778731/10000000000 : ℝ)*x 1 + (2814264233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838557203/2000000000 : ℝ)^4219 ≤ (7933311847699/25000000000000 : ℝ)^3195 := by
    have hnat : (838557203 : ℕ)^4219*25000000000000^3195 ≤ 7933311847699^3195*2000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838557203 2000000000 7933311847699 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3116778731/10000000000 : ℝ)^4219 ≤ (2681318176819/12500000000000 : ℝ)^3195 := by
    have hnat : (3116778731 : ℕ)^4219*12500000000000^3195 ≤ 2681318176819^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116778731 10000000000 2681318176819 12500000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2814264233/5000000000 : ℝ)^4219 ≤ (46816207179809/100000000000000 : ℝ)^3195 := by
    have hnat : (2814264233 : ℕ)^4219*100000000000000^3195 ≤ 46816207179809^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814264233 5000000000 46816207179809 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838557203/2000000000 : ℝ), (3116778731/10000000000 : ℝ), (2814264233/5000000000 : ℝ)] ![(7933311847699/25000000000000 : ℝ), (2681318176819/12500000000000 : ℝ), (46816207179809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838557203/2000000000 : ℝ)|^4219 ≤ (7933311847699/25000000000000 : ℝ)^3195
        have hw : |(838557203/2000000000 : ℝ)|=(838557203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3116778731/10000000000 : ℝ)|^4219 ≤ (2681318176819/12500000000000 : ℝ)^3195
        have hw : |(3116778731/10000000000 : ℝ)|=(3116778731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2814264233/5000000000 : ℝ)|^4219 ≤ (46816207179809/100000000000000 : ℝ)^3195
        have hw : |(2814264233/5000000000 : ℝ)|=(2814264233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s0_4 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1864483759/10000000000 : ℝ)*x 0 + (2412612373/5000000000 : ℝ)*x 1 + (47982699/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1864483759/10000000000 : ℝ)^4219 ≤ (217671746769/2000000000000 : ℝ)^3195 := by
    have hnat : (1864483759 : ℕ)^4219*2000000000000^3195 ≤ 217671746769^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864483759 10000000000 217671746769 2000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2412612373/5000000000 : ℝ)^4219 ≤ (7640374880559/20000000000000 : ℝ)^3195 := by
    have hnat : (2412612373 : ℕ)^4219*20000000000000^3195 ≤ 7640374880559^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2412612373 5000000000 7640374880559 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47982699/80000000 : ℝ)^4219 ≤ (25457269118743/50000000000000 : ℝ)^3195 := by
    have hnat : (47982699 : ℕ)^4219*50000000000000^3195 ≤ 25457269118743^3195*80000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47982699 80000000 25457269118743 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1864483759/10000000000 : ℝ), (2412612373/5000000000 : ℝ), (47982699/80000000 : ℝ)] ![(217671746769/2000000000000 : ℝ), (7640374880559/20000000000000 : ℝ), (25457269118743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1864483759/10000000000 : ℝ)|^4219 ≤ (217671746769/2000000000000 : ℝ)^3195
        have hw : |(-1864483759/10000000000 : ℝ)|=(1864483759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2412612373/5000000000 : ℝ)|^4219 ≤ (7640374880559/20000000000000 : ℝ)^3195
        have hw : |(2412612373/5000000000 : ℝ)|=(2412612373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(47982699/80000000 : ℝ)|^4219 ≤ (25457269118743/50000000000000 : ℝ)^3195
        have hw : |(47982699/80000000 : ℝ)|=(47982699/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s0_5 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174279631/10000000000 : ℝ)*x 0 + (-68125261/500000000 : ℝ)*x 1 + (5997839683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174279631/10000000000 : ℝ)^4219 ≤ (41892720375879/100000000000000 : ℝ)^3195 := by
    have hnat : (5174279631 : ℕ)^4219*100000000000000^3195 ≤ 41892720375879^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174279631 10000000000 41892720375879 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68125261/500000000 : ℝ)^4219 ≤ (7192715498091/100000000000000 : ℝ)^3195 := by
    have hnat : (68125261 : ℕ)^4219*100000000000000^3195 ≤ 7192715498091^3195*500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68125261 500000000 7192715498091 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5997839683/10000000000 : ℝ)^4219 ≤ (50914564108987/100000000000000 : ℝ)^3195 := by
    have hnat : (5997839683 : ℕ)^4219*100000000000000^3195 ≤ 50914564108987^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5997839683 10000000000 50914564108987 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174279631/10000000000 : ℝ), (-68125261/500000000 : ℝ), (5997839683/10000000000 : ℝ)] ![(41892720375879/100000000000000 : ℝ), (7192715498091/100000000000000 : ℝ), (50914564108987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174279631/10000000000 : ℝ)|^4219 ≤ (41892720375879/100000000000000 : ℝ)^3195
        have hw : |(5174279631/10000000000 : ℝ)|=(5174279631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-68125261/500000000 : ℝ)|^4219 ≤ (7192715498091/100000000000000 : ℝ)^3195
        have hw : |(-68125261/500000000 : ℝ)|=(68125261/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5997839683/10000000000 : ℝ)|^4219 ≤ (50914564108987/100000000000000 : ℝ)^3195
        have hw : |(5997839683/10000000000 : ℝ)|=(5997839683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s0_6 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174280563/10000000000 : ℝ)*x 0 + (5997837823/10000000000 : ℝ)*x 1 + (-1362506783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174280563/10000000000 : ℝ)^4219 ≤ (20946365170049/50000000000000 : ℝ)^3195 := by
    have hnat : (5174280563 : ℕ)^4219*50000000000000^3195 ≤ 20946365170049^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174280563 10000000000 20946365170049 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5997837823/10000000000 : ℝ)^4219 ≤ (50914543259337/100000000000000 : ℝ)^3195 := by
    have hnat : (5997837823 : ℕ)^4219*100000000000000^3195 ≤ 50914543259337^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5997837823 10000000000 50914543259337 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362506783/10000000000 : ℝ)^4219 ≤ (7192726393723/100000000000000 : ℝ)^3195 := by
    have hnat : (1362506783 : ℕ)^4219*100000000000000^3195 ≤ 7192726393723^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362506783 10000000000 7192726393723 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174280563/10000000000 : ℝ), (5997837823/10000000000 : ℝ), (-1362506783/10000000000 : ℝ)] ![(20946365170049/50000000000000 : ℝ), (50914543259337/100000000000000 : ℝ), (7192726393723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174280563/10000000000 : ℝ)|^4219 ≤ (20946365170049/50000000000000 : ℝ)^3195
        have hw : |(5174280563/10000000000 : ℝ)|=(5174280563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5997837823/10000000000 : ℝ)|^4219 ≤ (50914543259337/100000000000000 : ℝ)^3195
        have hw : |(5997837823/10000000000 : ℝ)|=(5997837823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1362506783/10000000000 : ℝ)|^4219 ≤ (7192726393723/100000000000000 : ℝ)^3195
        have hw : |(-1362506783/10000000000 : ℝ)|=(1362506783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s0_7 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525328681/1250000000 : ℝ)*x 0 + (556385473/1000000000 : ℝ)*x 1 + (127349529/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525328681/1250000000 : ℝ)^4219 ≤ (15915831087557/50000000000000 : ℝ)^3195 := by
    have hnat : (525328681 : ℕ)^4219*50000000000000^3195 ≤ 15915831087557^3195*1250000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525328681 1250000000 15915831087557 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (556385473/1000000000 : ℝ)^4219 ≤ (46107175795419/100000000000000 : ℝ)^3195 := by
    have hnat : (556385473 : ℕ)^4219*100000000000000^3195 ≤ 46107175795419^3195*1000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556385473 1000000000 46107175795419 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127349529/400000000 : ℝ)^4219 ≤ (5515290503599/25000000000000 : ℝ)^3195 := by
    have hnat : (127349529 : ℕ)^4219*25000000000000^3195 ≤ 5515290503599^3195*400000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127349529 400000000 5515290503599 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525328681/1250000000 : ℝ), (556385473/1000000000 : ℝ), (127349529/400000000 : ℝ)] ![(15915831087557/50000000000000 : ℝ), (46107175795419/100000000000000 : ℝ), (5515290503599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525328681/1250000000 : ℝ)|^4219 ≤ (15915831087557/50000000000000 : ℝ)^3195
        have hw : |(525328681/1250000000 : ℝ)|=(525328681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(556385473/1000000000 : ℝ)|^4219 ≤ (46107175795419/100000000000000 : ℝ)^3195
        have hw : |(556385473/1000000000 : ℝ)|=(556385473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127349529/400000000 : ℝ)|^4219 ≤ (5515290503599/25000000000000 : ℝ)^3195
        have hw : |(127349529/400000000 : ℝ)|=(127349529/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1245_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (83/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1097/4000 : ℝ)*pair X 0 0 := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8437/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8437 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8437*1^2048 ≤ 0^2048*1^8437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8437 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8437/2048 : ℝ) ≤ (2294218816108326239/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8437 ≤ (2294218816108326239/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8437*100000000000000000000^2048 ≤ 2294218816108326239^2048*5^8437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2294218816108326239 100000000000000000000 8437 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2294218816108326239/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8437 := by
      have hnat : (1 : ℕ)^2048*1^8437 ≤ 1^8437*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102294218816108326239/100000000000000000000 : ℝ) ≤ (10055212582592419/10000000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (102294218816108326239/100000000000000000000 : ℝ)^2048 ≤ (10055212582592419/10000000000000000 : ℝ)^8437 := by
      have hnat : (102294218816108326239 : ℕ)^2048*10000000000000000^8437 ≤ 10055212582592419^8437*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102294218816108326239 100000000000000000000 10055212582592419 10000000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055212582592419/10000000000000000 : ℝ)) (X := (102294218816108326239/100000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52294218816108326239/50000000000000000000 : ℝ) ≤ (5055212582592419/5000000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (52294218816108326239/50000000000000000000 : ℝ)^2048 ≤ (5055212582592419/5000000000000000 : ℝ)^8437 := by
      have hnat : (52294218816108326239 : ℕ)^2048*5000000000000000^8437 ≤ 5055212582592419^8437*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52294218816108326239 50000000000000000000 5055212582592419 5000000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055212582592419/5000000000000000 : ℝ)) (X := (52294218816108326239/50000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55212582592419/4000000000000000 : ℝ)*(0 : ℝ))^(8437/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55212582592419/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2294218816108326239/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55212582592419/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8437/2048 : ℝ) := by
    rw [show (1 : ℝ)+(55212582592419/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055212582592419/10000000000000000 : ℝ) by norm_num, show 1+(2294218816108326239/100000000000000000000 : ℝ)+(0 : ℝ)=(102294218816108326239/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2294218816108326239/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55212582592419/4000000000000000 : ℝ)*(2/5 : ℝ))^(8437/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55212582592419/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055212582592419/5000000000000000 : ℝ) by norm_num, show 1+2*(2294218816108326239/100000000000000000000 : ℝ)=(52294218816108326239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55212582592419/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55212582592419/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55212582592419/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55212582592419/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55212582592419/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55212582592419/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-464908693/2500000000 : ℝ)*X 0 0+(301541469/500000000 : ℝ)*X 0 1+(958671829/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1377747621/2500000000 : ℝ)*X 1 0+(-1283492849/5000000000 : ℝ)*X 1 1+(4793359089/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2755495201/5000000000 : ℝ)*X 2 0+(2396679587/5000000000 : ℝ)*X 2 1+(-1283492849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((838557203/2000000000 : ℝ)*X 0 0+(3116778731/10000000000 : ℝ)*X 0 1+(2814264233/5000000000 : ℝ)*X 0 2+(838557203/2000000000 : ℝ)*X 1 0+(3116778731/10000000000 : ℝ)*X 1 1+(2814264233/5000000000 : ℝ)*X 1 2+(838557203/2000000000 : ℝ)*X 2 0+(3116778731/10000000000 : ℝ)*X 2 1+(2814264233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1864483759/10000000000 : ℝ)*X 0 0+(2412612373/5000000000 : ℝ)*X 0 1+(47982699/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174279631/10000000000 : ℝ)*X 1 0+(-68125261/500000000 : ℝ)*X 1 1+(5997839683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174280563/10000000000 : ℝ)*X 2 0+(5997837823/10000000000 : ℝ)*X 2 1+(-1362506783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((525328681/1250000000 : ℝ)*X 0 0+(556385473/1000000000 : ℝ)*X 0 1+(127349529/400000000 : ℝ)*X 0 2+(525328681/1250000000 : ℝ)*X 1 0+(556385473/1000000000 : ℝ)*X 1 1+(127349529/400000000 : ℝ)*X 1 2+(525328681/1250000000 : ℝ)*X 2 0+(556385473/1000000000 : ℝ)*X 2 1+(127349529/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (97321599150812643053079/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2465907/4000000000000 : ℝ)*(base1) + (594024657/50000000000000 : ℝ)*(base19) + (274421579/25000000000000 : ℝ)*(base23) + (9792363/12500000000000 : ℝ)*(base24) + (53051997/20000000000000 : ℝ)*(upper3) + (120623917846047/20000000000000 : ℝ)*(major0) + (120623917846047/20000000000000 : ℝ)*(major1) + (120623917846047/20000000000000 : ℝ)*(major2) + (808104271881573/100000000000000 : ℝ)*(sp0) + (101013209077617/12500000000000 : ℝ)*(sp1) + (80810568464503/10000000000000 : ℝ)*(sp2) + (398130045684033/100000000000000 : ℝ)*(sp3) + (10353267/390625000000 : ℝ)*(sp4) + (512063961/25000000000000 : ℝ)*(sp7) + (398132155587551/100000000000000 : ℝ)*(f.failure) + (3232427442681/400000000000 : ℝ)*(f.sum) + (130635372002307/40000000000000000000000000000 : ℝ)*base66 + (35139745317693/80000000000000000000000000000 : ℝ)*base67 + (100683117722307/80000000000000000000000000000 : ℝ)*base70 + (87040540837693/80000000000000000000000000000 : ℝ)*base71 + (181965045282307/40000000000000000000000000000 : ℝ)*base74 + (247597184757693/80000000000000000000000000000 : ℝ)*base75 + (30705782042307/80000000000000000000000000000 : ℝ)*base78 + (532209834277693/80000000000000000000000000000 : ℝ)*base79 + (169363782202307/40000000000000000000000000000 : ℝ)*base82 + (6300371/2500000000000000000000 : ℝ)*base89 + (6300371/2500000000000000000000 : ℝ)*base91 + (6300371/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (277958053136746100943549/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76385953/50000000000000 : ℝ)*(base1) + (664565573/50000000000000 : ℝ)*(base19) + (737606343/50000000000000 : ℝ)*(base23) + (311886353/100000000000000 : ℝ)*(upper3) + (1203533/50000000000000 : ℝ)*(upper5) + (318235802569243/50000000000000 : ℝ)*(major0) + (318235802569243/50000000000000 : ℝ)*(major1) + (318235802569243/50000000000000 : ℝ)*(major2) + (2700318331/100000000000000 : ℝ)*(sp1) + (2584688781/100000000000000 : ℝ)*(sp2) + (85279464228063/10000000000000 : ℝ)*(sp4) + (53299403753703/6250000000000 : ℝ)*(sp5) + (852790429607257/100000000000000 : ℝ)*(sp6) + (420148382690969/100000000000000 : ℝ)*(sp7) + (3361188283703/800000000000 : ℝ)*(f.failure) + (213198622377181/25000000000000 : ℝ)*(f.sum) + (30961000168817/100000000000000000000000000000 : ℝ)*base65 + (874542975631183/200000000000000000000000000000 : ℝ)*base68 + (1031710439368817/200000000000000000000000000000 : ℝ)*base69 + (736858733568817/200000000000000000000000000000 : ℝ)*base71 + (460805182831183/100000000000000000000000000000 : ℝ)*base74 + (1253320079231183/200000000000000000000000000000 : ℝ)*base76 + (341741541368817/200000000000000000000000000000 : ℝ)*base77 + (793729339368817/200000000000000000000000000000 : ℝ)*base79 + (68636528768817/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (33163/20000000000000000000 : ℝ)*base89 + (33163/20000000000000000000 : ℝ)*base91 + (33163/20000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1245_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (83/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1097/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1245_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1245_s1_0 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2056826647/10000000000 : ℝ)*x 0 + (354678431/625000000 : ℝ)*x 1 + (156972143/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2056826647/10000000000 : ℝ)^4219 ≤ (619508139433/5000000000000 : ℝ)^3195 := by
    have hnat : (2056826647 : ℕ)^4219*5000000000000^3195 ≤ 619508139433^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056826647 10000000000 619508139433 5000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354678431/625000000 : ℝ)^4219 ≤ (23662851271/50000000000 : ℝ)^3195 := by
    have hnat : (354678431 : ℕ)^4219*50000000000^3195 ≤ 23662851271^3195*625000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354678431 625000000 23662851271 50000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156972143/312500000 : ℝ)^4219 ≤ (10071033663697/25000000000000 : ℝ)^3195 := by
    have hnat : (156972143 : ℕ)^4219*25000000000000^3195 ≤ 10071033663697^3195*312500000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156972143 312500000 10071033663697 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2056826647/10000000000 : ℝ), (354678431/625000000 : ℝ), (156972143/312500000 : ℝ)] ![(619508139433/5000000000000 : ℝ), (23662851271/50000000000 : ℝ), (10071033663697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2056826647/10000000000 : ℝ)|^4219 ≤ (619508139433/5000000000000 : ℝ)^3195
        have hw : |(-2056826647/10000000000 : ℝ)|=(2056826647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(354678431/625000000 : ℝ)|^4219 ≤ (23662851271/50000000000 : ℝ)^3195
        have hw : |(354678431/625000000 : ℝ)|=(354678431/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(156972143/312500000 : ℝ)|^4219 ≤ (10071033663697/25000000000000 : ℝ)^3195
        have hw : |(156972143/312500000 : ℝ)|=(156972143/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s1_1 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5413495863/10000000000 : ℝ)*x 0 + (-2406757359/10000000000 : ℝ)*x 1 + (5023108739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413495863/10000000000 : ℝ)^4219 ≤ (44468987222209/100000000000000 : ℝ)^3195 := by
    have hnat : (5413495863 : ℕ)^4219*100000000000000^3195 ≤ 44468987222209^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413495863 10000000000 44468987222209 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406757359/10000000000 : ℝ)^4219 ≤ (3049375276963/20000000000000 : ℝ)^3195 := by
    have hnat : (2406757359 : ℕ)^4219*20000000000000^3195 ≤ 3049375276963^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406757359 10000000000 3049375276963 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5023108739/10000000000 : ℝ)^4219 ≤ (1611365455239/4000000000000 : ℝ)^3195 := by
    have hnat : (5023108739 : ℕ)^4219*4000000000000^3195 ≤ 1611365455239^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5023108739 10000000000 1611365455239 4000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413495863/10000000000 : ℝ), (-2406757359/10000000000 : ℝ), (5023108739/10000000000 : ℝ)] ![(44468987222209/100000000000000 : ℝ), (3049375276963/20000000000000 : ℝ), (1611365455239/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413495863/10000000000 : ℝ)|^4219 ≤ (44468987222209/100000000000000 : ℝ)^3195
        have hw : |(5413495863/10000000000 : ℝ)|=(5413495863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2406757359/10000000000 : ℝ)|^4219 ≤ (3049375276963/20000000000000 : ℝ)^3195
        have hw : |(-2406757359/10000000000 : ℝ)|=(2406757359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5023108739/10000000000 : ℝ)|^4219 ≤ (1611365455239/4000000000000 : ℝ)^3195
        have hw : |(5023108739/10000000000 : ℝ)|=(5023108739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s1_2 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1353374003/2500000000 : ℝ)*x 0 + (1255777159/2500000000 : ℝ)*x 1 + (-150422331/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353374003/2500000000 : ℝ)^4219 ≤ (11117247209611/25000000000000 : ℝ)^3195 := by
    have hnat : (1353374003 : ℕ)^4219*25000000000000^3195 ≤ 11117247209611^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353374003 2500000000 11117247209611 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1255777159/2500000000 : ℝ)^4219 ≤ (20142067645097/50000000000000 : ℝ)^3195 := by
    have hnat : (1255777159 : ℕ)^4219*50000000000000^3195 ≤ 20142067645097^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255777159 2500000000 20142067645097 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150422331/625000000 : ℝ)^4219 ≤ (7623437928897/50000000000000 : ℝ)^3195 := by
    have hnat : (150422331 : ℕ)^4219*50000000000000^3195 ≤ 7623437928897^3195*625000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150422331 625000000 7623437928897 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353374003/2500000000 : ℝ), (1255777159/2500000000 : ℝ), (-150422331/625000000 : ℝ)] ![(11117247209611/25000000000000 : ℝ), (20142067645097/50000000000000 : ℝ), (7623437928897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353374003/2500000000 : ℝ)|^4219 ≤ (11117247209611/25000000000000 : ℝ)^3195
        have hw : |(1353374003/2500000000 : ℝ)|=(1353374003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1255777159/2500000000 : ℝ)|^4219 ≤ (20142067645097/50000000000000 : ℝ)^3195
        have hw : |(1255777159/2500000000 : ℝ)|=(1255777159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-150422331/625000000 : ℝ)|^4219 ≤ (7623437928897/50000000000000 : ℝ)^3195
        have hw : |(-150422331/625000000 : ℝ)|=(150422331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s1_3 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2154297313/5000000000 : ℝ)*x 0 + (3695985429/10000000000 : ℝ)*x 1 + (5018865147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154297313/5000000000 : ℝ)^4219 ≤ (657915193913/2000000000000 : ℝ)^3195 := by
    have hnat : (2154297313 : ℕ)^4219*2000000000000^3195 ≤ 657915193913^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154297313 5000000000 657915193913 2000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3695985429/10000000000 : ℝ)^4219 ≤ (5373007577761/20000000000000 : ℝ)^3195 := by
    have hnat : (3695985429 : ℕ)^4219*20000000000000^3195 ≤ 5373007577761^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3695985429 10000000000 5373007577761 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5018865147/10000000000 : ℝ)^4219 ≤ (10059800598581/25000000000000 : ℝ)^3195 := by
    have hnat : (5018865147 : ℕ)^4219*25000000000000^3195 ≤ 10059800598581^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018865147 10000000000 10059800598581 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154297313/5000000000 : ℝ), (3695985429/10000000000 : ℝ), (5018865147/10000000000 : ℝ)] ![(657915193913/2000000000000 : ℝ), (5373007577761/20000000000000 : ℝ), (10059800598581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154297313/5000000000 : ℝ)|^4219 ≤ (657915193913/2000000000000 : ℝ)^3195
        have hw : |(2154297313/5000000000 : ℝ)|=(2154297313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3695985429/10000000000 : ℝ)|^4219 ≤ (5373007577761/20000000000000 : ℝ)^3195
        have hw : |(3695985429/10000000000 : ℝ)|=(3695985429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5018865147/10000000000 : ℝ)|^4219 ≤ (10059800598581/25000000000000 : ℝ)^3195
        have hw : |(5018865147/10000000000 : ℝ)|=(5018865147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s1_4 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2057499289/10000000000 : ℝ)*x 0 + (2515829901/5000000000 : ℝ)*x 1 + (1133228257/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057499289/10000000000 : ℝ)^4219 ≤ (6197756831327/50000000000000 : ℝ)^3195 := by
    have hnat : (2057499289 : ℕ)^4219*50000000000000^3195 ≤ 6197756831327^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057499289 10000000000 6197756831327 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2515829901/5000000000 : ℝ)^4219 ≤ (10093679426079/25000000000000 : ℝ)^3195 := by
    have hnat : (2515829901 : ℕ)^4219*25000000000000^3195 ≤ 10093679426079^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2515829901 5000000000 10093679426079 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133228257/2000000000 : ℝ)^4219 ≤ (23614884307101/50000000000000 : ℝ)^3195 := by
    have hnat : (1133228257 : ℕ)^4219*50000000000000^3195 ≤ 23614884307101^3195*2000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133228257 2000000000 23614884307101 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2057499289/10000000000 : ℝ), (2515829901/5000000000 : ℝ), (1133228257/2000000000 : ℝ)] ![(6197756831327/50000000000000 : ℝ), (10093679426079/25000000000000 : ℝ), (23614884307101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2057499289/10000000000 : ℝ)|^4219 ≤ (6197756831327/50000000000000 : ℝ)^3195
        have hw : |(-2057499289/10000000000 : ℝ)|=(2057499289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2515829901/5000000000 : ℝ)|^4219 ≤ (10093679426079/25000000000000 : ℝ)^3195
        have hw : |(2515829901/5000000000 : ℝ)|=(2515829901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133228257/2000000000 : ℝ)|^4219 ≤ (23614884307101/50000000000000 : ℝ)^3195
        have hw : |(1133228257/2000000000 : ℝ)|=(1133228257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s1_5 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (163923837/312500000 : ℝ)*x 0 + (-88186231/500000000 : ℝ)*x 1 + (5666141481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163923837/312500000 : ℝ)^4219 ≤ (42656501621153/100000000000000 : ℝ)^3195 := by
    have hnat : (163923837 : ℕ)^4219*100000000000000^3195 ≤ 42656501621153^3195*312500000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163923837 312500000 42656501621153 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88186231/500000000 : ℝ)^4219 ≤ (126421594851/1250000000000 : ℝ)^3195 := by
    have hnat : (88186231 : ℕ)^4219*1250000000000^3195 ≤ 126421594851^3195*500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88186231 500000000 126421594851 1250000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5666141481/10000000000 : ℝ)^4219 ≤ (11807442692891/25000000000000 : ℝ)^3195 := by
    have hnat : (5666141481 : ℕ)^4219*25000000000000^3195 ≤ 11807442692891^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5666141481 10000000000 11807442692891 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(163923837/312500000 : ℝ), (-88186231/500000000 : ℝ), (5666141481/10000000000 : ℝ)] ![(42656501621153/100000000000000 : ℝ), (126421594851/1250000000000 : ℝ), (11807442692891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(163923837/312500000 : ℝ)|^4219 ≤ (42656501621153/100000000000000 : ℝ)^3195
        have hw : |(163923837/312500000 : ℝ)|=(163923837/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88186231/500000000 : ℝ)|^4219 ≤ (126421594851/1250000000000 : ℝ)^3195
        have hw : |(-88186231/500000000 : ℝ)|=(88186231/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5666141481/10000000000 : ℝ)|^4219 ≤ (11807442692891/25000000000000 : ℝ)^3195
        have hw : |(5666141481/10000000000 : ℝ)|=(5666141481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s1_6 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5245562717/10000000000 : ℝ)*x 0 + (2833070657/5000000000 : ℝ)*x 1 + (-881862479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245562717/10000000000 : ℝ)^4219 ≤ (42656500901693/100000000000000 : ℝ)^3195 := by
    have hnat : (5245562717 : ℕ)^4219*100000000000000^3195 ≤ 42656500901693^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245562717 10000000000 42656500901693 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2833070657/5000000000 : ℝ)^4219 ≤ (47229768933403/100000000000000 : ℝ)^3195 := by
    have hnat : (2833070657 : ℕ)^4219*100000000000000^3195 ≤ 47229768933403^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2833070657 5000000000 47229768933403 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (881862479/5000000000 : ℝ)^4219 ≤ (5056865073733/50000000000000 : ℝ)^3195 := by
    have hnat : (881862479 : ℕ)^4219*50000000000000^3195 ≤ 5056865073733^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881862479 5000000000 5056865073733 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245562717/10000000000 : ℝ), (2833070657/5000000000 : ℝ), (-881862479/5000000000 : ℝ)] ![(42656500901693/100000000000000 : ℝ), (47229768933403/100000000000000 : ℝ), (5056865073733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245562717/10000000000 : ℝ)|^4219 ≤ (42656500901693/100000000000000 : ℝ)^3195
        have hw : |(5245562717/10000000000 : ℝ)|=(5245562717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2833070657/5000000000 : ℝ)|^4219 ≤ (47229768933403/100000000000000 : ℝ)^3195
        have hw : |(2833070657/5000000000 : ℝ)|=(2833070657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-881862479/5000000000 : ℝ)|^4219 ≤ (5056865073733/50000000000000 : ℝ)^3195
        have hw : |(-881862479/5000000000 : ℝ)|=(881862479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s1_7 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4309959853/10000000000 : ℝ)*x 0 + (5001508441/10000000000 : ℝ)*x 1 + (1856836059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309959853/10000000000 : ℝ)^4219 ≤ (32909524494419/100000000000000 : ℝ)^3195 := by
    have hnat : (4309959853 : ℕ)^4219*100000000000000^3195 ≤ 32909524494419^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309959853 10000000000 32909524494419 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5001508441/10000000000 : ℝ)^4219 ≤ (5006943101203/12500000000000 : ℝ)^3195 := by
    have hnat : (5001508441 : ℕ)^4219*12500000000000^3195 ≤ 5006943101203^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001508441 10000000000 5006943101203 12500000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1856836059/5000000000 : ℝ)^4219 ≤ (5406986136989/20000000000000 : ℝ)^3195 := by
    have hnat : (1856836059 : ℕ)^4219*20000000000000^3195 ≤ 5406986136989^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856836059 5000000000 5406986136989 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309959853/10000000000 : ℝ), (5001508441/10000000000 : ℝ), (1856836059/5000000000 : ℝ)] ![(32909524494419/100000000000000 : ℝ), (5006943101203/12500000000000 : ℝ), (5406986136989/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309959853/10000000000 : ℝ)|^4219 ≤ (32909524494419/100000000000000 : ℝ)^3195
        have hw : |(4309959853/10000000000 : ℝ)|=(4309959853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5001508441/10000000000 : ℝ)|^4219 ≤ (5006943101203/12500000000000 : ℝ)^3195
        have hw : |(5001508441/10000000000 : ℝ)|=(5001508441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1856836059/5000000000 : ℝ)|^4219 ≤ (5406986136989/20000000000000 : ℝ)^3195
        have hw : |(1856836059/5000000000 : ℝ)|=(1856836059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1245_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1097/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (83/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (6207/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9993/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1097/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (83/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1097/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (83/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1097/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (83/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1097/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (83/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1097/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (83/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1097/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (83/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (83/10000 : ℝ) ^ (8437/2048 : ℝ) ≤ (267530904401/100000000000000000000 : ℝ) := by
    have hpowers : (83/10000 : ℝ)^8437 ≤ (267530904401/100000000000000000000 : ℝ)^2048 := by
      have hnat : (83 : ℕ)^8437*100000000000000000000^2048 ≤ 267530904401^2048*10000^8437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83 10000 267530904401 100000000000000000000 8437 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83/10000 : ℝ)) (X := (267530904401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1097/4000 : ℝ) ^ (8437/2048 : ℝ) ≤ (484587984646503569/100000000000000000000 : ℝ) := by
    have hpowers : (1097/4000 : ℝ)^8437 ≤ (484587984646503569/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1097 : ℕ)^8437*100000000000000000000^2048 ≤ 484587984646503569^2048*4000^8437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1097 4000 484587984646503569 100000000000000000000 8437 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1097/4000 : ℝ)) (X := (484587984646503569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000267530904401/50000000000000000000 : ℝ) ≤ (10000000012988107/10000000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (50000000267530904401/50000000000000000000 : ℝ)^2048 ≤ (10000000012988107/10000000000000000 : ℝ)^8437 := by
      have hnat : (50000000267530904401 : ℕ)^2048*10000000000000000^8437 ≤ 10000000012988107^8437*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000267530904401 50000000000000000000 10000000012988107 10000000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000012988107/10000000000000000 : ℝ)) (X := (50000000267530904401/50000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10048458825217740797/10000000000000000000 : ℝ) ≤ (625733836800113/625000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (10048458825217740797/10000000000000000000 : ℝ)^2048 ≤ (625733836800113/625000000000000 : ℝ)^8437 := by
      have hnat : (10048458825217740797 : ℕ)^2048*625000000000000^8437 ≤ 625733836800113^8437*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10048458825217740797 10000000000000000000 625733836800113 625000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625733836800113/625000000000000 : ℝ)) (X := (10048458825217740797/10000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50484587984646503569/50000000000000000000 : ℝ) ≤ (10023482764615509/10000000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (50484587984646503569/50000000000000000000 : ℝ)^2048 ≤ (10023482764615509/10000000000000000 : ℝ)^8437 := by
      have hnat : (50484587984646503569 : ℕ)^2048*10000000000000000^8437 ≤ 10023482764615509^8437*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50484587984646503569 50000000000000000000 10023482764615509 10000000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023482764615509/10000000000000000 : ℝ)) (X := (50484587984646503569/50000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(267530904401/100000000000000000000 : ℝ) ≤ ((53186101932313592401/53190000000000000000 : ℝ)+2*(11741375813701/2659500000000000 : ℝ)*(83/10000 : ℝ))^(8437/2048 : ℝ) := by
    rw [show (53186101932313592401/53190000000000000000 : ℝ)+2*(11741375813701/2659500000000000 : ℝ)*(83/10000 : ℝ)=(10000000012988107/10000000000000000 : ℝ) by norm_num, show 1+2*(267530904401/100000000000000000000 : ℝ)=(50000000267530904401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(484587984646503569/100000000000000000000 : ℝ)+(267530904401/100000000000000000000 : ℝ) ≤ ((53186101932313592401/53190000000000000000 : ℝ)+(11741375813701/2659500000000000 : ℝ)*((1097/4000 : ℝ)+(83/10000 : ℝ)))^(8437/2048 : ℝ) := by
    rw [show (53186101932313592401/53190000000000000000 : ℝ)+(11741375813701/2659500000000000 : ℝ)*((1097/4000 : ℝ)+(83/10000 : ℝ))=(625733836800113/625000000000000 : ℝ) by norm_num, show 1+(484587984646503569/100000000000000000000 : ℝ)+(267530904401/100000000000000000000 : ℝ)=(10048458825217740797/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(484587984646503569/100000000000000000000 : ℝ) ≤ ((53186101932313592401/53190000000000000000 : ℝ)+2*(11741375813701/2659500000000000 : ℝ)*(1097/4000 : ℝ))^(8437/2048 : ℝ) := by
    rw [show (53186101932313592401/53190000000000000000 : ℝ)+2*(11741375813701/2659500000000000 : ℝ)*(1097/4000 : ℝ)=(10023482764615509/10000000000000000 : ℝ) by norm_num, show 1+2*(484587984646503569/100000000000000000000 : ℝ)=(50484587984646503569/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (53186101932313592401/53190000000000000000 : ℝ)*(X 1 0+X 2 0)+(11741375813701/2659500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (83/10000 : ℝ)) (hi := (1097/4000 : ℝ)) (c := (53186101932313592401/53190000000000000000 : ℝ)) (alpha := (11741375813701/2659500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (53186101932313592401/53190000000000000000 : ℝ)*(X 0 1+X 2 1)+(11741375813701/2659500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (83/10000 : ℝ)) (hi := (1097/4000 : ℝ)) (c := (53186101932313592401/53190000000000000000 : ℝ)) (alpha := (11741375813701/2659500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (53186101932313592401/53190000000000000000 : ℝ)*(X 0 2+X 1 2)+(11741375813701/2659500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (83/10000 : ℝ)) (hi := (1097/4000 : ℝ)) (c := (53186101932313592401/53190000000000000000 : ℝ)) (alpha := (11741375813701/2659500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2056826647/10000000000 : ℝ)*X 0 0+(354678431/625000000 : ℝ)*X 0 1+(156972143/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5413495863/10000000000 : ℝ)*X 1 0+(-2406757359/10000000000 : ℝ)*X 1 1+(5023108739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1353374003/2500000000 : ℝ)*X 2 0+(1255777159/2500000000 : ℝ)*X 2 1+(-150422331/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154297313/5000000000 : ℝ)*X 0 0+(3695985429/10000000000 : ℝ)*X 0 1+(5018865147/10000000000 : ℝ)*X 0 2+(2154297313/5000000000 : ℝ)*X 1 0+(3695985429/10000000000 : ℝ)*X 1 1+(5018865147/10000000000 : ℝ)*X 1 2+(2154297313/5000000000 : ℝ)*X 2 0+(3695985429/10000000000 : ℝ)*X 2 1+(5018865147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2057499289/10000000000 : ℝ)*X 0 0+(2515829901/5000000000 : ℝ)*X 0 1+(1133228257/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((163923837/312500000 : ℝ)*X 1 0+(-88186231/500000000 : ℝ)*X 1 1+(5666141481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5245562717/10000000000 : ℝ)*X 2 0+(2833070657/5000000000 : ℝ)*X 2 1+(-881862479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309959853/10000000000 : ℝ)*X 0 0+(5001508441/10000000000 : ℝ)*X 0 1+(1856836059/5000000000 : ℝ)*X 0 2+(4309959853/10000000000 : ℝ)*X 1 0+(5001508441/10000000000 : ℝ)*X 1 1+(1856836059/5000000000 : ℝ)*X 1 2+(4309959853/10000000000 : ℝ)*X 2 0+(5001508441/10000000000 : ℝ)*X 2 1+(1856836059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1308925737320723136387324763/443250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6783241/25000000000000 : ℝ)*(base1) + (682585313/100000000000000 : ℝ)*(base19) + (72481637/10000000000000 : ℝ)*(base23) + (71110967/100000000000000 : ℝ)*(upper3) + (21123893/20000000000000 : ℝ)*(upper5) + (1145139224963563/100000000000000 : ℝ)*(major0) + (1145139224963563/100000000000000 : ℝ)*(major1) + (1145139224963563/100000000000000 : ℝ)*(major2) + (767171550484187/50000000000000 : ℝ)*(sp0) + (306869349076643/20000000000000 : ℝ)*(sp1) + (1534346703152157/100000000000000 : ℝ)*(sp2) + (755928788056333/100000000000000 : ℝ)*(sp3) + (2177066559/50000000000000 : ℝ)*(sp4) + (2108335323/100000000000000 : ℝ)*(sp7) + (37796546176231/5000000000000 : ℝ)*(f.failure) + (1534347427968527/100000000000000 : ℝ)*(f.sum) + (1604068268989/16621875000000000000000000000 : ℝ)*base66 + (4949414485122685079/1773000000000000000000000000000000 : ℝ)*base68 + (21750339576189685079/1773000000000000000000000000000000 : ℝ)*base70 + (7636889733708685079/1773000000000000000000000000000000 : ℝ)*base72 + (128635449492269/66487500000000000000000000000 : ℝ)*base73 + (24481936548552685079/1773000000000000000000000000000000 : ℝ)*base76 + (9403787668755685079/1773000000000000000000000000000000 : ℝ)*base78 + (1582058458301314921/1773000000000000000000000000000000 : ℝ)*base79 + (58634115265939/16621875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1136651/125000000000000000000 : ℝ)*base89 + (1136651/125000000000000000000 : ℝ)*base91 + (1136651/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (154094017508341558849456133/29550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8685143/20000000000000 : ℝ)*(base1) + (1003053833/100000000000000 : ℝ)*(base19) + (959964373/100000000000000 : ℝ)*(base23) + (131152899/100000000000000 : ℝ)*(upper3) + (112361789/100000000000000 : ℝ)*(upper5) + (235258620800799/20000000000000 : ℝ)*(major0) + (235258620800799/20000000000000 : ℝ)*(major1) + (235258620800799/20000000000000 : ℝ)*(major2) + (4818451001/100000000000000 : ℝ)*(sp1) + (4101311773/100000000000000 : ℝ)*(sp2) + (197011226428311/12500000000000 : ℝ)*(sp4) + (1576083946495939/100000000000000 : ℝ)*(sp5) + (1576084706724627/100000000000000 : ℝ)*(sp6) + (388248111379289/50000000000000 : ℝ)*(sp7) + (776496266184293/100000000000000 : ℝ)*(f.failure) + (1576089768000773/100000000000000 : ℝ)*(f.sum) + (1036206901303/8865000000000000000000000000 : ℝ)*base65 + (1277078095893121289/118200000000000000000000000000000 : ℝ)*base68 + (286383969675121289/118200000000000000000000000000000 : ℝ)*base70 + (365321096134921289/118200000000000000000000000000000 : ℝ)*base72 + (22684129656751/4432500000000000000000000000 : ℝ)*base74 + (1200422952462721289/118200000000000000000000000000000 : ℝ)*base76 + (941408723622121289/118200000000000000000000000000000 : ℝ)*base78 + (70038305540878711/118200000000000000000000000000000 : ℝ)*base79 + (25000609212583/8865000000000000000000000000 : ℝ)*base81 + (22507553/2500000000000000000000 : ℝ)*base89 + (22507553/2500000000000000000000 : ℝ)*base91 + (22507553/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1245_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1097/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (83/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9993/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1245_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1245_s2_0 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-263090087/1250000000 : ℝ)*x 0 + (2746138897/5000000000 : ℝ)*x 1 + (5175138919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263090087/1250000000 : ℝ)^4219 ≤ (2554510933133/20000000000000 : ℝ)^3195 := by
    have hnat : (263090087 : ℕ)^4219*20000000000000^3195 ≤ 2554510933133^3195*1250000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263090087 1250000000 2554510933133 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746138897/5000000000 : ℝ)^4219 ≤ (9065107572417/20000000000000 : ℝ)^3195 := by
    have hnat : (2746138897 : ℕ)^4219*20000000000000^3195 ≤ 9065107572417^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746138897 5000000000 9065107572417 20000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175138919/10000000000 : ℝ)^4219 ≤ (20950953729381/50000000000000 : ℝ)^3195 := by
    have hnat : (5175138919 : ℕ)^4219*50000000000000^3195 ≤ 20950953729381^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175138919 10000000000 20950953729381 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263090087/1250000000 : ℝ), (2746138897/5000000000 : ℝ), (5175138919/10000000000 : ℝ)] ![(2554510933133/20000000000000 : ℝ), (9065107572417/20000000000000 : ℝ), (20950953729381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263090087/1250000000 : ℝ)|^4219 ≤ (2554510933133/20000000000000 : ℝ)^3195
        have hw : |(-263090087/1250000000 : ℝ)|=(263090087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746138897/5000000000 : ℝ)|^4219 ≤ (9065107572417/20000000000000 : ℝ)^3195
        have hw : |(2746138897/5000000000 : ℝ)|=(2746138897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175138919/10000000000 : ℝ)|^4219 ≤ (20950953729381/50000000000000 : ℝ)^3195
        have hw : |(5175138919/10000000000 : ℝ)|=(5175138919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s2_1 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671195533/1250000000 : ℝ)*x 0 + (-226897919/1000000000 : ℝ)*x 1 + (5175138953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671195533/1250000000 : ℝ)^4219 ≤ (43993072753817/100000000000000 : ℝ)^3195 := by
    have hnat : (671195533 : ℕ)^4219*100000000000000^3195 ≤ 43993072753817^3195*1250000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671195533 1250000000 43993072753817 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226897919/1000000000 : ℝ)^4219 ≤ (7052509703833/50000000000000 : ℝ)^3195 := by
    have hnat : (226897919 : ℕ)^4219*50000000000000^3195 ≤ 7052509703833^3195*1000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226897919 1000000000 7052509703833 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175138953/10000000000 : ℝ)^4219 ≤ (41901907822283/100000000000000 : ℝ)^3195 := by
    have hnat : (5175138953 : ℕ)^4219*100000000000000^3195 ≤ 41901907822283^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175138953 10000000000 41901907822283 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671195533/1250000000 : ℝ), (-226897919/1000000000 : ℝ), (5175138953/10000000000 : ℝ)] ![(43993072753817/100000000000000 : ℝ), (7052509703833/50000000000000 : ℝ), (41901907822283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671195533/1250000000 : ℝ)|^4219 ≤ (43993072753817/100000000000000 : ℝ)^3195
        have hw : |(671195533/1250000000 : ℝ)|=(671195533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226897919/1000000000 : ℝ)|^4219 ≤ (7052509703833/50000000000000 : ℝ)^3195
        have hw : |(-226897919/1000000000 : ℝ)|=(226897919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175138953/10000000000 : ℝ)|^4219 ≤ (41901907822283/100000000000000 : ℝ)^3195
        have hw : |(5175138953/10000000000 : ℝ)|=(5175138953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s2_2 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369564127/10000000000 : ℝ)*x 0 + (5175139057/10000000000 : ℝ)*x 1 + (-567244809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369564127/10000000000 : ℝ)^4219 ≤ (351944570173/800000000000 : ℝ)^3195 := by
    have hnat : (5369564127 : ℕ)^4219*800000000000^3195 ≤ 351944570173^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369564127 10000000000 351944570173 800000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175139057/10000000000 : ℝ)^4219 ≤ (41901908934229/100000000000000 : ℝ)^3195 := by
    have hnat : (5175139057 : ℕ)^4219*100000000000000^3195 ≤ 41901908934229^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175139057 10000000000 41901908934229 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567244809/2500000000 : ℝ)^4219 ≤ (14105019785273/100000000000000 : ℝ)^3195 := by
    have hnat : (567244809 : ℕ)^4219*100000000000000^3195 ≤ 14105019785273^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567244809 2500000000 14105019785273 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369564127/10000000000 : ℝ), (5175139057/10000000000 : ℝ), (-567244809/2500000000 : ℝ)] ![(351944570173/800000000000 : ℝ), (41901908934229/100000000000000 : ℝ), (14105019785273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369564127/10000000000 : ℝ)|^4219 ≤ (351944570173/800000000000 : ℝ)^3195
        have hw : |(5369564127/10000000000 : ℝ)|=(5369564127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175139057/10000000000 : ℝ)|^4219 ≤ (41901908934229/100000000000000 : ℝ)^3195
        have hw : |(5175139057/10000000000 : ℝ)|=(5175139057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-567244809/2500000000 : ℝ)|^4219 ≤ (14105019785273/100000000000000 : ℝ)^3195
        have hw : |(-567244809/2500000000 : ℝ)|=(567244809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s2_3 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (542710427/1250000000 : ℝ)*x 0 + (806275037/2000000000 : ℝ)*x 1 + (2337543167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542710427/1250000000 : ℝ)^4219 ≤ (16614883919883/50000000000000 : ℝ)^3195 := by
    have hnat : (542710427 : ℕ)^4219*50000000000000^3195 ≤ 16614883919883^3195*1250000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542710427 1250000000 16614883919883 50000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806275037/2000000000 : ℝ)^4219 ≤ (30130106440453/100000000000000 : ℝ)^3195 := by
    have hnat : (806275037 : ℕ)^4219*100000000000000^3195 ≤ 30130106440453^3195*2000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806275037 2000000000 30130106440453 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2337543167/5000000000 : ℝ)^4219 ≤ (4580015714037/12500000000000 : ℝ)^3195 := by
    have hnat : (2337543167 : ℕ)^4219*12500000000000^3195 ≤ 4580015714037^3195*5000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337543167 5000000000 4580015714037 12500000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542710427/1250000000 : ℝ), (806275037/2000000000 : ℝ), (2337543167/5000000000 : ℝ)] ![(16614883919883/50000000000000 : ℝ), (30130106440453/100000000000000 : ℝ), (4580015714037/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542710427/1250000000 : ℝ)|^4219 ≤ (16614883919883/50000000000000 : ℝ)^3195
        have hw : |(542710427/1250000000 : ℝ)|=(542710427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(806275037/2000000000 : ℝ)|^4219 ≤ (30130106440453/100000000000000 : ℝ)^3195
        have hw : |(806275037/2000000000 : ℝ)|=(806275037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2337543167/5000000000 : ℝ)|^4219 ≤ (4580015714037/12500000000000 : ℝ)^3195
        have hw : |(2337543167/5000000000 : ℝ)|=(2337543167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s2_4 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2104798493/10000000000 : ℝ)*x 0 + (5177173421/10000000000 : ℝ)*x 1 + (21960897/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104798493/10000000000 : ℝ)^4219 ≤ (798323630951/6250000000000 : ℝ)^3195 := by
    have hnat : (2104798493 : ℕ)^4219*6250000000000^3195 ≤ 798323630951^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104798493 10000000000 798323630951 6250000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177173421/10000000000 : ℝ)^4219 ≤ (10480915324591/25000000000000 : ℝ)^3195 := by
    have hnat : (5177173421 : ℕ)^4219*25000000000000^3195 ≤ 10480915324591^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177173421 10000000000 10480915324591 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21960897/40000000 : ℝ)^4219 ≤ (2831447536941/6250000000000 : ℝ)^3195 := by
    have hnat : (21960897 : ℕ)^4219*6250000000000^3195 ≤ 2831447536941^3195*40000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21960897 40000000 2831447536941 6250000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2104798493/10000000000 : ℝ), (5177173421/10000000000 : ℝ), (21960897/40000000 : ℝ)] ![(798323630951/6250000000000 : ℝ), (10480915324591/25000000000000 : ℝ), (2831447536941/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2104798493/10000000000 : ℝ)|^4219 ≤ (798323630951/6250000000000 : ℝ)^3195
        have hw : |(-2104798493/10000000000 : ℝ)|=(2104798493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177173421/10000000000 : ℝ)|^4219 ≤ (10480915324591/25000000000000 : ℝ)^3195
        have hw : |(5177173421/10000000000 : ℝ)|=(5177173421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21960897/40000000 : ℝ)|^4219 ≤ (2831447536941/6250000000000 : ℝ)^3195
        have hw : |(21960897/40000000 : ℝ)|=(21960897/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s2_5 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288560341/10000000000 : ℝ)*x 0 + (-1953893663/10000000000 : ℝ)*x 1 + (1098044859/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288560341/10000000000 : ℝ)^4219 ≤ (43118823699407/100000000000000 : ℝ)^3195 := by
    have hnat : (5288560341 : ℕ)^4219*100000000000000^3195 ≤ 43118823699407^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288560341 10000000000 43118823699407 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1953893663/10000000000 : ℝ)^4219 ≤ (11578015210217/100000000000000 : ℝ)^3195 := by
    have hnat : (1953893663 : ℕ)^4219*100000000000000^3195 ≤ 11578015210217^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953893663 10000000000 11578015210217 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098044859/2000000000 : ℝ)^4219 ≤ (45303161081387/100000000000000 : ℝ)^3195 := by
    have hnat : (1098044859 : ℕ)^4219*100000000000000^3195 ≤ 45303161081387^3195*2000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098044859 2000000000 45303161081387 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288560341/10000000000 : ℝ), (-1953893663/10000000000 : ℝ), (1098044859/2000000000 : ℝ)] ![(43118823699407/100000000000000 : ℝ), (11578015210217/100000000000000 : ℝ), (45303161081387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288560341/10000000000 : ℝ)|^4219 ≤ (43118823699407/100000000000000 : ℝ)^3195
        have hw : |(5288560341/10000000000 : ℝ)|=(5288560341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1953893663/10000000000 : ℝ)|^4219 ≤ (11578015210217/100000000000000 : ℝ)^3195
        have hw : |(-1953893663/10000000000 : ℝ)|=(1953893663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098044859/2000000000 : ℝ)|^4219 ≤ (45303161081387/100000000000000 : ℝ)^3195
        have hw : |(1098044859/2000000000 : ℝ)|=(1098044859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s2_6 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288560501/10000000000 : ℝ)*x 0 + (5490224381/10000000000 : ℝ)*x 1 + (-1953893321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288560501/10000000000 : ℝ)^4219 ≤ (43118825422021/100000000000000 : ℝ)^3195 := by
    have hnat : (5288560501 : ℕ)^4219*100000000000000^3195 ≤ 43118825422021^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288560501 10000000000 43118825422021 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490224381/10000000000 : ℝ)^4219 ≤ (1415723813077/3125000000000 : ℝ)^3195 := by
    have hnat : (5490224381 : ℕ)^4219*3125000000000^3195 ≤ 1415723813077^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490224381 10000000000 1415723813077 3125000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1953893321/10000000000 : ℝ)^4219 ≤ (90453222923/781250000000 : ℝ)^3195 := by
    have hnat : (1953893321 : ℕ)^4219*781250000000^3195 ≤ 90453222923^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953893321 10000000000 90453222923 781250000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288560501/10000000000 : ℝ), (5490224381/10000000000 : ℝ), (-1953893321/10000000000 : ℝ)] ![(43118825422021/100000000000000 : ℝ), (1415723813077/3125000000000 : ℝ), (90453222923/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288560501/10000000000 : ℝ)|^4219 ≤ (43118825422021/100000000000000 : ℝ)^3195
        have hw : |(5288560501/10000000000 : ℝ)|=(5288560501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490224381/10000000000 : ℝ)|^4219 ≤ (1415723813077/3125000000000 : ℝ)^3195
        have hw : |(5490224381/10000000000 : ℝ)|=(5490224381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1953893321/10000000000 : ℝ)|^4219 ≤ (90453222923/781250000000 : ℝ)^3195
        have hw : |(-1953893321/10000000000 : ℝ)|=(1953893321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1245_s2_7 (p : ℝ) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4341840799/10000000000 : ℝ)*x 0 + (1167739277/2500000000 : ℝ)*x 1 + (4035542717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341840799/10000000000 : ℝ)^4219 ≤ (8307839616517/25000000000000 : ℝ)^3195 := by
    have hnat : (4341840799 : ℕ)^4219*25000000000000^3195 ≤ 8307839616517^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341840799 10000000000 8307839616517 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1167739277/2500000000 : ℝ)^4219 ≤ (36597397654803/100000000000000 : ℝ)^3195 := by
    have hnat : (1167739277 : ℕ)^4219*100000000000000^3195 ≤ 36597397654803^3195*2500000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167739277 2500000000 36597397654803 100000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035542717/10000000000 : ℝ)^4219 ≤ (7542810963377/25000000000000 : ℝ)^3195 := by
    have hnat : (4035542717 : ℕ)^4219*25000000000000^3195 ≤ 7542810963377^3195*10000000000^4219 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035542717 10000000000 7542810963377 25000000000000 4219 3195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4219/1024 : ℝ)) 4219 3195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341840799/10000000000 : ℝ), (1167739277/2500000000 : ℝ), (4035542717/10000000000 : ℝ)] ![(8307839616517/25000000000000 : ℝ), (36597397654803/100000000000000 : ℝ), (7542810963377/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341840799/10000000000 : ℝ)|^4219 ≤ (8307839616517/25000000000000 : ℝ)^3195
        have hw : |(4341840799/10000000000 : ℝ)|=(4341840799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1167739277/2500000000 : ℝ)|^4219 ≤ (36597397654803/100000000000000 : ℝ)^3195
        have hw : |(1167739277/2500000000 : ℝ)|=(1167739277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035542717/10000000000 : ℝ)|^4219 ≤ (7542810963377/25000000000000 : ℝ)^3195
        have hw : |(4035542717/10000000000 : ℝ)|=(4035542717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1245_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9993/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1189/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3243/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9993/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9993/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9993/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9993/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9993/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9993/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6207/100000 : ℝ) ^ (8437/2048 : ℝ) ≤ (133054864808077/12500000000000000000 : ℝ) := by
    have hpowers : (6207/100000 : ℝ)^8437 ≤ (133054864808077/12500000000000000000 : ℝ)^2048 := by
      have hnat : (6207 : ℕ)^8437*12500000000000000000^2048 ≤ 133054864808077^2048*100000^8437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6207 100000 133054864808077 12500000000000000000 8437 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6207/100000 : ℝ)) (X := (133054864808077/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (9993/50000 : ℝ) ^ (8437/2048 : ℝ) ≤ (65799128102223389/50000000000000000000 : ℝ) := by
    have hpowers : (9993/50000 : ℝ)^8437 ≤ (65799128102223389/50000000000000000000 : ℝ)^2048 := by
      have hnat : (9993 : ℕ)^8437*50000000000000000000^2048 ≤ 65799128102223389^2048*50000^8437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9993 50000 65799128102223389 50000000000000000000 8437 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9993/50000 : ℝ)) (X := (65799128102223389/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250133054864808077/6250000000000000000 : ℝ) ≤ (10000051676030187/10000000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (6250133054864808077/6250000000000000000 : ℝ)^2048 ≤ (10000051676030187/10000000000000000 : ℝ)^8437 := by
      have hnat : (6250133054864808077 : ℕ)^2048*10000000000000000^8437 ≤ 10000051676030187^8437*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250133054864808077 6250000000000000000 10000051676030187 10000000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000051676030187/10000000000000000 : ℝ)) (X := (6250133054864808077/6250000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50066331347561455697/50000000000000000000 : ℝ) ≤ (2000643728419861/2000000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (50066331347561455697/50000000000000000000 : ℝ)^2048 ≤ (2000643728419861/2000000000000000 : ℝ)^8437 := by
      have hnat : (50066331347561455697 : ℕ)^2048*2000000000000000^8437 ≤ 2000643728419861^8437*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50066331347561455697 50000000000000000000 2000643728419861 2000000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000643728419861/2000000000000000 : ℝ)) (X := (50066331347561455697/50000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25065799128102223389/25000000000000000000 : ℝ) ≤ (10006385608168423/10000000000000000 : ℝ) ^ (8437/2048 : ℝ) := by
    have hpowers : (25065799128102223389/25000000000000000000 : ℝ)^2048 ≤ (10006385608168423/10000000000000000 : ℝ)^8437 := by
      have hnat : (25065799128102223389 : ℕ)^2048*10000000000000000^8437 ≤ 10006385608168423^8437*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25065799128102223389 25000000000000000000 10006385608168423 10000000000000000 2048 8437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006385608168423/10000000000000000 : ℝ)) (X := (25065799128102223389/25000000000000000000 : ℝ)) (by norm_num) 8437 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(133054864808077/12500000000000000000 : ℝ) ≤ ((45917132442412638607/45930000000000000000 : ℝ)+2*(1583483034559/688950000000000 : ℝ)*(6207/100000 : ℝ))^(8437/2048 : ℝ) := by
    rw [show (45917132442412638607/45930000000000000000 : ℝ)+2*(1583483034559/688950000000000 : ℝ)*(6207/100000 : ℝ)=(10000051676030187/10000000000000000 : ℝ) by norm_num, show 1+2*(133054864808077/12500000000000000000 : ℝ)=(6250133054864808077/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(65799128102223389/50000000000000000000 : ℝ)+(133054864808077/12500000000000000000 : ℝ) ≤ ((45917132442412638607/45930000000000000000 : ℝ)+(1583483034559/688950000000000 : ℝ)*((9993/50000 : ℝ)+(6207/100000 : ℝ)))^(8437/2048 : ℝ) := by
    rw [show (45917132442412638607/45930000000000000000 : ℝ)+(1583483034559/688950000000000 : ℝ)*((9993/50000 : ℝ)+(6207/100000 : ℝ))=(2000643728419861/2000000000000000 : ℝ) by norm_num, show 1+(65799128102223389/50000000000000000000 : ℝ)+(133054864808077/12500000000000000000 : ℝ)=(50066331347561455697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(65799128102223389/50000000000000000000 : ℝ) ≤ ((45917132442412638607/45930000000000000000 : ℝ)+2*(1583483034559/688950000000000 : ℝ)*(9993/50000 : ℝ))^(8437/2048 : ℝ) := by
    rw [show (45917132442412638607/45930000000000000000 : ℝ)+2*(1583483034559/688950000000000 : ℝ)*(9993/50000 : ℝ)=(10006385608168423/10000000000000000 : ℝ) by norm_num, show 1+2*(65799128102223389/50000000000000000000 : ℝ)=(25065799128102223389/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45917132442412638607/45930000000000000000 : ℝ)*(X 1 0+X 2 0)+(1583483034559/688950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (6207/100000 : ℝ)) (hi := (9993/50000 : ℝ)) (c := (45917132442412638607/45930000000000000000 : ℝ)) (alpha := (1583483034559/688950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45917132442412638607/45930000000000000000 : ℝ)*(X 0 1+X 2 1)+(1583483034559/688950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (6207/100000 : ℝ)) (hi := (9993/50000 : ℝ)) (c := (45917132442412638607/45930000000000000000 : ℝ)) (alpha := (1583483034559/688950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45917132442412638607/45930000000000000000 : ℝ)*(X 0 2+X 1 2)+(1583483034559/688950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8437/2048 : ℝ)) (lo := (6207/100000 : ℝ)) (hi := (9993/50000 : ℝ)) (c := (45917132442412638607/45930000000000000000 : ℝ)) (alpha := (1583483034559/688950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-263090087/1250000000 : ℝ)*X 0 0+(2746138897/5000000000 : ℝ)*X 0 1+(5175138919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((671195533/1250000000 : ℝ)*X 1 0+(-226897919/1000000000 : ℝ)*X 1 1+(5175138953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369564127/10000000000 : ℝ)*X 2 0+(5175139057/10000000000 : ℝ)*X 2 1+(-567244809/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((542710427/1250000000 : ℝ)*X 0 0+(806275037/2000000000 : ℝ)*X 0 1+(2337543167/5000000000 : ℝ)*X 0 2+(542710427/1250000000 : ℝ)*X 1 0+(806275037/2000000000 : ℝ)*X 1 1+(2337543167/5000000000 : ℝ)*X 1 2+(542710427/1250000000 : ℝ)*X 2 0+(806275037/2000000000 : ℝ)*X 2 1+(2337543167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2104798493/10000000000 : ℝ)*X 0 0+(5177173421/10000000000 : ℝ)*X 0 1+(21960897/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288560341/10000000000 : ℝ)*X 1 0+(-1953893663/10000000000 : ℝ)*X 1 1+(1098044859/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288560501/10000000000 : ℝ)*X 2 0+(5490224381/10000000000 : ℝ)*X 2 1+(-1953893321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4341840799/10000000000 : ℝ)*X 0 0+(1167739277/2500000000 : ℝ)*X 0 1+(4035542717/10000000000 : ℝ)*X 0 2+(4341840799/10000000000 : ℝ)*X 1 0+(1167739277/2500000000 : ℝ)*X 1 1+(4035542717/10000000000 : ℝ)*X 1 2+(4341840799/10000000000 : ℝ)*X 2 0+(1167739277/2500000000 : ℝ)*X 2 1+(4035542717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1245_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12447167470784221917139/5741250000000000000000000000 : ℝ) := by norm_num
    linear_combination (323757991/100000000000000 : ℝ)*(base19) + (27399093/12500000000000 : ℝ)*(base23) + (6474073/50000000000000 : ℝ)*(lower2) + (15874037/20000000000000 : ℝ)*(upper3) + (6579/62500000000 : ℝ)*(upper5) + (294168440427229/12500000000000 : ℝ)*(major0) + (294168440427229/12500000000000 : ℝ)*(major1) + (294168440427229/12500000000000 : ℝ)*(major2) + (1576598551341891/50000000000000 : ℝ)*(sp0) + (1576599778918681/50000000000000 : ℝ)*(sp1) + (3153199662402609/100000000000000 : ℝ)*(sp2) + (388373300772443/25000000000000 : ℝ)*(sp3) + (2778911571/100000000000000 : ℝ)*(sp4) + (1889883069/100000000000000 : ℝ)*(sp7) + (1553495092972841/100000000000000 : ℝ)*(f.failure) + (3153199881595353/100000000000000 : ℝ)*(f.sum) + (57783140449121/17223750000000000000000000000 : ℝ)*base66 + (15074487687579365009/1722375000000000000000000000000000 : ℝ)*base67 + (1336713232180884991/1722375000000000000000000000000000 : ℝ)*base70 + (2213991369560634991/1722375000000000000000000000000000 : ℝ)*base72 + (56154084597709/17223750000000000000000000000 : ℝ)*base73 + (10311961086411365009/1722375000000000000000000000000000 : ℝ)*base75 + (1866718845026259991/1722375000000000000000000000000000 : ℝ)*base78 + (18654429633016115009/1722375000000000000000000000000000 : ℝ)*base79 + (66374929183139/68895000000000000000000000000 : ℝ)*base82 + (7786539/2500000000000000000000 : ℝ)*base90 + (7786539/2500000000000000000000 : ℝ)*base92 + (7786539/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78251059195928549558843171/22965000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (535563593/50000000000000 : ℝ)*(base19) + (276372519/20000000000000 : ℝ)*(base23) + (30518243/50000000000000 : ℝ)*(upper2) + (32967087/20000000000000 : ℝ)*(upper3) + (64062951/100000000000000 : ℝ)*(upper5) + (23840723274883/1000000000000 : ℝ)*(major0) + (23840723274883/1000000000000 : ℝ)*(major1) + (23840723274883/1000000000000 : ℝ)*(major2) + (1055566571/10000000000000 : ℝ)*(sp1) + (849918671/5000000000000 : ℝ)*(sp2) + (159718367366973/5000000000000 : ℝ)*(sp4) + (798588930136641/25000000000000 : ℝ)*(sp5) + (638869793420689/20000000000000 : ℝ)*(sp6) + (1573777194056961/100000000000000 : ℝ)*(sp7) + (1573777194056961/100000000000000 : ℝ)*(f.failure) + (159718367366973/5000000000000 : ℝ)*(f.sum) + (41376883271081/13779000000000000000000000000 : ℝ)*base66 + (1351743696597103943/137790000000000000000000000000000 : ℝ)*base67 + (849321867498793943/137790000000000000000000000000000 : ℝ)*base69 + (1826507938799653943/137790000000000000000000000000000 : ℝ)*base71 + (10927413925039/3444750000000000000000000000 : ℝ)*base73 + (746658808610893943/137790000000000000000000000000000 : ℝ)*base75 + (1188550639051063943/137790000000000000000000000000000 : ℝ)*base77 + (714566246360353943/137790000000000000000000000000000 : ℝ)*base79 + (2344809477901/1722375000000000000000000000 : ℝ)*base82 + (9204019/2500000000000000000000 : ℝ)*base90 + (9204019/2500000000000000000000 : ℝ)*base92 + (9204019/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1245_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9993/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3243/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1245_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1245_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3243/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1245_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1245_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1245_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8437/2048 : ℝ) ≤ p) (hpb : p ≤ (4219/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37871821/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3243/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1245_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
