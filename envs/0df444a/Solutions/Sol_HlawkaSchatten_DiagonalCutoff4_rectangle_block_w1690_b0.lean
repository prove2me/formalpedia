-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1690_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:38:53.580989+00:00
-- url     : https://prove2.me/submissions/b663fca9-c7ed-4b68-a95a-c27d07300761

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
theorem support_rectangle_w1690_s0_0 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1397610571/10000000000 : ℝ)*x 0 + (358732111/625000000 : ℝ)*x 1 + (4937859483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1397610571/10000000000 : ℝ)^5143 ≤ (8568913053933/100000000000000 : ℝ)^4119 := by
    have hnat : (1397610571 : ℕ)^5143*100000000000000^4119 ≤ 8568913053933^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397610571 10000000000 8568913053933 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (358732111/625000000 : ℝ)^5143 ≤ (9999525044271/20000000000000 : ℝ)^4119 := by
    have hnat : (358732111 : ℕ)^5143*20000000000000^4119 ≤ 9999525044271^4119*625000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358732111 625000000 9999525044271 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4937859483/10000000000 : ℝ)^5143 ≤ (41433461705971/100000000000000 : ℝ)^4119 := by
    have hnat : (4937859483 : ℕ)^5143*100000000000000^4119 ≤ 41433461705971^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4937859483 10000000000 41433461705971 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1397610571/10000000000 : ℝ), (358732111/625000000 : ℝ), (4937859483/10000000000 : ℝ)] ![(8568913053933/100000000000000 : ℝ), (9999525044271/20000000000000 : ℝ), (41433461705971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1397610571/10000000000 : ℝ)|^5143 ≤ (8568913053933/100000000000000 : ℝ)^4119
        have hw : |(-1397610571/10000000000 : ℝ)|=(1397610571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(358732111/625000000 : ℝ)|^5143 ≤ (9999525044271/20000000000000 : ℝ)^4119
        have hw : |(358732111/625000000 : ℝ)|=(358732111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4937859483/10000000000 : ℝ)|^5143 ≤ (41433461705971/100000000000000 : ℝ)^4119
        have hw : |(4937859483/10000000000 : ℝ)|=(4937859483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s0_1 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2709300103/5000000000 : ℝ)*x 0 + (-366958377/2000000000 : ℝ)*x 1 + (987572129/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709300103/5000000000 : ℝ)^5143 ≤ (23264856407881/50000000000000 : ℝ)^4119 := by
    have hnat : (2709300103 : ℕ)^5143*50000000000000^4119 ≤ 23264856407881^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709300103 5000000000 23264856407881 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366958377/2000000000 : ℝ)^5143 ≤ (12036813289069/100000000000000 : ℝ)^4119 := by
    have hnat : (366958377 : ℕ)^5143*100000000000000^4119 ≤ 12036813289069^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366958377 2000000000 12036813289069 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987572129/2000000000 : ℝ)^5143 ≤ (41433473880253/100000000000000 : ℝ)^4119 := by
    have hnat : (987572129 : ℕ)^5143*100000000000000^4119 ≤ 41433473880253^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987572129 2000000000 41433473880253 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709300103/5000000000 : ℝ), (-366958377/2000000000 : ℝ), (987572129/2000000000 : ℝ)] ![(23264856407881/50000000000000 : ℝ), (12036813289069/100000000000000 : ℝ), (41433473880253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709300103/5000000000 : ℝ)|^5143 ≤ (23264856407881/50000000000000 : ℝ)^4119
        have hw : |(2709300103/5000000000 : ℝ)|=(2709300103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366958377/2000000000 : ℝ)|^5143 ≤ (12036813289069/100000000000000 : ℝ)^4119
        have hw : |(-366958377/2000000000 : ℝ)|=(366958377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(987572129/2000000000 : ℝ)|^5143 ≤ (41433473880253/100000000000000 : ℝ)^4119
        have hw : |(987572129/2000000000 : ℝ)|=(987572129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s0_2 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67732531/125000000 : ℝ)*x 0 + (4937859567/10000000000 : ℝ)*x 1 + (-917395143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67732531/125000000 : ℝ)^5143 ≤ (46529737197153/100000000000000 : ℝ)^4119 := by
    have hnat : (67732531 : ℕ)^5143*100000000000000^4119 ≤ 46529737197153^4119*125000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67732531 125000000 46529737197153 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4937859567/10000000000 : ℝ)^5143 ≤ (1035836564651/2500000000000 : ℝ)^4119 := by
    have hnat : (4937859567 : ℕ)^5143*2500000000000^4119 ≤ 1035836564651^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4937859567 10000000000 1035836564651 2500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (917395143/5000000000 : ℝ)^5143 ≤ (3009200047821/25000000000000 : ℝ)^4119 := by
    have hnat : (917395143 : ℕ)^5143*25000000000000^4119 ≤ 3009200047821^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917395143 5000000000 3009200047821 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67732531/125000000 : ℝ), (4937859567/10000000000 : ℝ), (-917395143/5000000000 : ℝ)] ![(46529737197153/100000000000000 : ℝ), (1035836564651/2500000000000 : ℝ), (3009200047821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67732531/125000000 : ℝ)|^5143 ≤ (46529737197153/100000000000000 : ℝ)^4119
        have hw : |(67732531/125000000 : ℝ)|=(67732531/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4937859567/10000000000 : ℝ)|^5143 ≤ (1035836564651/2500000000000 : ℝ)^4119
        have hw : |(4937859567/10000000000 : ℝ)|=(4937859567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-917395143/5000000000 : ℝ)|^5143 ≤ (3009200047821/25000000000000 : ℝ)^4119
        have hw : |(-917395143/5000000000 : ℝ)|=(917395143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s0_3 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2028318563/5000000000 : ℝ)*x 0 + (609494227/2000000000 : ℝ)*x 1 + (5266462629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2028318563/5000000000 : ℝ)^5143 ≤ (16207823318031/50000000000000 : ℝ)^4119 := by
    have hnat : (2028318563 : ℕ)^5143*50000000000000^4119 ≤ 16207823318031^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028318563 5000000000 16207823318031 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (609494227/2000000000 : ℝ)^5143 ≤ (2835012112521/12500000000000 : ℝ)^4119 := by
    have hnat : (609494227 : ℕ)^5143*12500000000000^4119 ≤ 2835012112521^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609494227 2000000000 2835012112521 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266462629/10000000000 : ℝ)^5143 ≤ (22452128227351/50000000000000 : ℝ)^4119 := by
    have hnat : (5266462629 : ℕ)^5143*50000000000000^4119 ≤ 22452128227351^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266462629 10000000000 22452128227351 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2028318563/5000000000 : ℝ), (609494227/2000000000 : ℝ), (5266462629/10000000000 : ℝ)] ![(16207823318031/50000000000000 : ℝ), (2835012112521/12500000000000 : ℝ), (22452128227351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2028318563/5000000000 : ℝ)|^5143 ≤ (16207823318031/50000000000000 : ℝ)^4119
        have hw : |(2028318563/5000000000 : ℝ)|=(2028318563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(609494227/2000000000 : ℝ)|^5143 ≤ (2835012112521/12500000000000 : ℝ)^4119
        have hw : |(609494227/2000000000 : ℝ)|=(609494227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266462629/10000000000 : ℝ)|^5143 ≤ (22452128227351/50000000000000 : ℝ)^4119
        have hw : |(5266462629/10000000000 : ℝ)|=(5266462629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s0_4 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-699810513/5000000000 : ℝ)*x 0 + (2478993669/5000000000 : ℝ)*x 1 + (1143778091/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (699810513/5000000000 : ℝ)^5143 ≤ (8584306514687/100000000000000 : ℝ)^4119 := by
    have hnat : (699810513 : ℕ)^5143*100000000000000^4119 ≤ 8584306514687^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699810513 5000000000 8584306514687 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2478993669/5000000000 : ℝ)^5143 ≤ (41644448119613/100000000000000 : ℝ)^4119 := by
    have hnat : (2478993669 : ℕ)^5143*100000000000000^4119 ≤ 41644448119613^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2478993669 5000000000 41644448119613 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143778091/2000000000 : ℝ)^5143 ≤ (49771245356977/100000000000000 : ℝ)^4119 := by
    have hnat : (1143778091 : ℕ)^5143*100000000000000^4119 ≤ 49771245356977^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143778091 2000000000 49771245356977 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-699810513/5000000000 : ℝ), (2478993669/5000000000 : ℝ), (1143778091/2000000000 : ℝ)] ![(8584306514687/100000000000000 : ℝ), (41644448119613/100000000000000 : ℝ), (49771245356977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-699810513/5000000000 : ℝ)|^5143 ≤ (8584306514687/100000000000000 : ℝ)^4119
        have hw : |(-699810513/5000000000 : ℝ)|=(699810513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2478993669/5000000000 : ℝ)|^5143 ≤ (41644448119613/100000000000000 : ℝ)^4119
        have hw : |(2478993669/5000000000 : ℝ)|=(2478993669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1143778091/2000000000 : ℝ)|^5143 ≤ (49771245356977/100000000000000 : ℝ)^4119
        have hw : |(1143778091/2000000000 : ℝ)|=(1143778091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s0_5 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1040155301/2000000000 : ℝ)*x 0 + (-526880571/5000000000 : ℝ)*x 1 + (5718891011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040155301/2000000000 : ℝ)^5143 ≤ (5525754831683/12500000000000 : ℝ)^4119 := by
    have hnat : (1040155301 : ℕ)^5143*12500000000000^4119 ≤ 5525754831683^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040155301 2000000000 5525754831683 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526880571/5000000000 : ℝ)^5143 ≤ (6022709933279/100000000000000 : ℝ)^4119 := by
    have hnat : (526880571 : ℕ)^5143*100000000000000^4119 ≤ 6022709933279^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526880571 5000000000 6022709933279 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5718891011/10000000000 : ℝ)^5143 ≤ (6221406424847/12500000000000 : ℝ)^4119 := by
    have hnat : (5718891011 : ℕ)^5143*12500000000000^4119 ≤ 6221406424847^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5718891011 10000000000 6221406424847 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040155301/2000000000 : ℝ), (-526880571/5000000000 : ℝ), (5718891011/10000000000 : ℝ)] ![(5525754831683/12500000000000 : ℝ), (6022709933279/100000000000000 : ℝ), (6221406424847/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040155301/2000000000 : ℝ)|^5143 ≤ (5525754831683/12500000000000 : ℝ)^4119
        have hw : |(1040155301/2000000000 : ℝ)|=(1040155301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-526880571/5000000000 : ℝ)|^5143 ≤ (6022709933279/100000000000000 : ℝ)^4119
        have hw : |(-526880571/5000000000 : ℝ)|=(526880571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5718891011/10000000000 : ℝ)|^5143 ≤ (6221406424847/12500000000000 : ℝ)^4119
        have hw : |(5718891011/10000000000 : ℝ)|=(5718891011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s0_6 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2600388303/5000000000 : ℝ)*x 0 + (1429722771/2500000000 : ℝ)*x 1 + (-13172011/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2600388303/5000000000 : ℝ)^5143 ≤ (44206039725377/100000000000000 : ℝ)^4119 := by
    have hnat : (2600388303 : ℕ)^5143*100000000000000^4119 ≤ 44206039725377^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600388303 5000000000 44206039725377 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1429722771/2500000000 : ℝ)^5143 ≤ (24885626096017/50000000000000 : ℝ)^4119 := by
    have hnat : (1429722771 : ℕ)^5143*50000000000000^4119 ≤ 24885626096017^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429722771 2500000000 24885626096017 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13172011/125000000 : ℝ)^5143 ≤ (3011354031781/50000000000000 : ℝ)^4119 := by
    have hnat : (13172011 : ℕ)^5143*50000000000000^4119 ≤ 3011354031781^4119*125000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13172011 125000000 3011354031781 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2600388303/5000000000 : ℝ), (1429722771/2500000000 : ℝ), (-13172011/125000000 : ℝ)] ![(44206039725377/100000000000000 : ℝ), (24885626096017/50000000000000 : ℝ), (3011354031781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2600388303/5000000000 : ℝ)|^5143 ≤ (44206039725377/100000000000000 : ℝ)^4119
        have hw : |(2600388303/5000000000 : ℝ)|=(2600388303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1429722771/2500000000 : ℝ)|^5143 ≤ (24885626096017/50000000000000 : ℝ)^4119
        have hw : |(1429722771/2500000000 : ℝ)|=(1429722771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13172011/125000000 : ℝ)|^5143 ≤ (3011354031781/50000000000000 : ℝ)^4119
        have hw : |(-13172011/125000000 : ℝ)|=(13172011/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s0_7 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4062200101/10000000000 : ℝ)*x 0 + (5210761103/10000000000 : ℝ)*x 1 + (3105094329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4062200101/10000000000 : ℝ)^5143 ≤ (8117789898431/25000000000000 : ℝ)^4119 := by
    have hnat : (4062200101 : ℕ)^5143*25000000000000^4119 ≤ 8117789898431^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4062200101 10000000000 8117789898431 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5210761103/10000000000 : ℝ)^5143 ≤ (44312030461769/100000000000000 : ℝ)^4119 := by
    have hnat : (5210761103 : ℕ)^5143*100000000000000^4119 ≤ 44312030461769^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5210761103 10000000000 44312030461769 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3105094329/10000000000 : ℝ)^5143 ≤ (23216809925687/100000000000000 : ℝ)^4119 := by
    have hnat : (3105094329 : ℕ)^5143*100000000000000^4119 ≤ 23216809925687^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3105094329 10000000000 23216809925687 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4062200101/10000000000 : ℝ), (5210761103/10000000000 : ℝ), (3105094329/10000000000 : ℝ)] ![(8117789898431/25000000000000 : ℝ), (44312030461769/100000000000000 : ℝ), (23216809925687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4062200101/10000000000 : ℝ)|^5143 ≤ (8117789898431/25000000000000 : ℝ)^4119
        have hw : |(4062200101/10000000000 : ℝ)|=(4062200101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5210761103/10000000000 : ℝ)|^5143 ≤ (44312030461769/100000000000000 : ℝ)^4119
        have hw : |(5210761103/10000000000 : ℝ)|=(5210761103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3105094329/10000000000 : ℝ)|^5143 ≤ (23216809925687/100000000000000 : ℝ)^4119
        have hw : |(3105094329/10000000000 : ℝ)|=(3105094329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1690_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (679/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22639/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5135/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5135 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5135*1^1024 ≤ 0^1024*1^5135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5135/1024 : ℝ) ≤ (1010347467684423937/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5135 ≤ (1010347467684423937/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5135*100000000000000000000^1024 ≤ 1010347467684423937^1024*5^5135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1010347467684423937 100000000000000000000 5135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1010347467684423937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5135 := by
      have hnat : (1 : ℕ)^1024*1^5135 ≤ 1^5135*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101010347467684423937/100000000000000000000 : ℝ) ≤ (10020066927826171/10000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (101010347467684423937/100000000000000000000 : ℝ)^1024 ≤ (10020066927826171/10000000000000000 : ℝ)^5135 := by
      have hnat : (101010347467684423937 : ℕ)^1024*10000000000000000^5135 ≤ 10020066927826171^5135*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101010347467684423937 100000000000000000000 10020066927826171 10000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020066927826171/10000000000000000 : ℝ)) (X := (101010347467684423937/100000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51010347467684423937/50000000000000000000 : ℝ) ≤ (5020066927826171/5000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (51010347467684423937/50000000000000000000 : ℝ)^1024 ≤ (5020066927826171/5000000000000000 : ℝ)^5135 := by
      have hnat : (51010347467684423937 : ℕ)^1024*5000000000000000^5135 ≤ 5020066927826171^5135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51010347467684423937 50000000000000000000 5020066927826171 5000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5020066927826171/5000000000000000 : ℝ)) (X := (51010347467684423937/50000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(20066927826171/4000000000000000 : ℝ)*(0 : ℝ))^(5135/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(20066927826171/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1010347467684423937/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(20066927826171/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5135/1024 : ℝ) := by
    rw [show (1 : ℝ)+(20066927826171/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10020066927826171/10000000000000000 : ℝ) by norm_num, show 1+(1010347467684423937/100000000000000000000 : ℝ)+(0 : ℝ)=(101010347467684423937/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1010347467684423937/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(20066927826171/4000000000000000 : ℝ)*(2/5 : ℝ))^(5135/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(20066927826171/4000000000000000 : ℝ)*(2/5 : ℝ)=(5020066927826171/5000000000000000 : ℝ) by norm_num, show 1+2*(1010347467684423937/100000000000000000000 : ℝ)=(51010347467684423937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(20066927826171/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20066927826171/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(20066927826171/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20066927826171/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(20066927826171/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20066927826171/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1397610571/10000000000 : ℝ)*X 0 0+(358732111/625000000 : ℝ)*X 0 1+(4937859483/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2709300103/5000000000 : ℝ)*X 1 0+(-366958377/2000000000 : ℝ)*X 1 1+(987572129/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((67732531/125000000 : ℝ)*X 2 0+(4937859567/10000000000 : ℝ)*X 2 1+(-917395143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2028318563/5000000000 : ℝ)*X 0 0+(609494227/2000000000 : ℝ)*X 0 1+(5266462629/10000000000 : ℝ)*X 0 2+(2028318563/5000000000 : ℝ)*X 1 0+(609494227/2000000000 : ℝ)*X 1 1+(5266462629/10000000000 : ℝ)*X 1 2+(2028318563/5000000000 : ℝ)*X 2 0+(609494227/2000000000 : ℝ)*X 2 1+(5266462629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-699810513/5000000000 : ℝ)*X 0 0+(2478993669/5000000000 : ℝ)*X 0 1+(1143778091/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1040155301/2000000000 : ℝ)*X 1 0+(-526880571/5000000000 : ℝ)*X 1 1+(5718891011/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2600388303/5000000000 : ℝ)*X 2 0+(1429722771/2500000000 : ℝ)*X 2 1+(-13172011/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4062200101/10000000000 : ℝ)*X 0 0+(5210761103/10000000000 : ℝ)*X 0 1+(3105094329/10000000000 : ℝ)*X 0 2+(4062200101/10000000000 : ℝ)*X 1 0+(5210761103/10000000000 : ℝ)*X 1 1+(3105094329/10000000000 : ℝ)*X 1 2+(4062200101/10000000000 : ℝ)*X 2 0+(5210761103/10000000000 : ℝ)*X 2 1+(3105094329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (366724226223132816117147/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (210863011/50000000000000 : ℝ)*(base19) + (745168963/100000000000000 : ℝ)*(base23) + (9269833/5000000000000 : ℝ)*(base24) + (31497/400000000000 : ℝ)*(upper4) + (10057141/12500000000000 : ℝ)*(upper5) + (424443663144181/50000000000000 : ℝ)*(major0) + (424443663144181/50000000000000 : ℝ)*(major1) + (424443663144181/50000000000000 : ℝ)*(major2) + (1247111941958919/100000000000000 : ℝ)*(sp0) + (623558054510289/50000000000000 : ℝ)*(sp1) + (77944725011311/6250000000000 : ℝ)*(sp2) + (450656488022999/100000000000000 : ℝ)*(sp3) + (4588787681/100000000000000 : ℝ)*(sp4) + (1511565707/100000000000000 : ℝ)*(sp7) + (225328999794353/50000000000000 : ℝ)*(f.failure) + (6235582653733/500000000000 : ℝ)*(f.sum) + (525296895560951/100000000000000000000000000000 : ℝ)*base65 + (546110723439049/200000000000000000000000000000 : ℝ)*base68 + (773096536960951/200000000000000000000000000000 : ℝ)*base69 + (1488658008360951/200000000000000000000000000000 : ℝ)*base71 + (235826637439049/100000000000000000000000000000 : ℝ)*base74 + (987438721360951/200000000000000000000000000000 : ℝ)*base75 + (969981725960951/200000000000000000000000000000 : ℝ)*base77 + (1395040062560951/200000000000000000000000000000 : ℝ)*base79 + (127352805639049/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8580633/1000000000000000000000 : ℝ)*base90 + (8580633/1000000000000000000000 : ℝ)*base92 + (8580633/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (748783974795782489377533/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (155485721/10000000000000 : ℝ)*(base19) + (206397349/12500000000000 : ℝ)*(base23) + (20022221/100000000000000 : ℝ)*(upper2) + (296504111/100000000000000 : ℝ)*(upper3) + (60353633/25000000000000 : ℝ)*(upper5) + (894568274645459/100000000000000 : ℝ)*(major0) + (894568274645459/100000000000000 : ℝ)*(major1) + (894568274645459/100000000000000 : ℝ)*(major2) + (2830992599/50000000000000 : ℝ)*(sp1) + (321656601/5000000000000 : ℝ)*(sp2) + (32855679020009/2500000000000 : ℝ)*(sp4) + (1314219943957953/100000000000000 : ℝ)*(sp5) + (1314219076489549/100000000000000 : ℝ)*(sp6) + (474909138895893/100000000000000 : ℝ)*(sp7) + (474909138895893/100000000000000 : ℝ)*(f.failure) + (32855679020009/2500000000000 : ℝ)*(f.sum) + (196923439907489/200000000000000000000000000000 : ℝ)*base65 + (4567989942907489/400000000000000000000000000000 : ℝ)*base67 + (86564767707489/400000000000000000000000000000 : ℝ)*base69 + (1344614508107489/400000000000000000000000000000 : ℝ)*base71 + (587252721907489/200000000000000000000000000000 : ℝ)*base73 + (1507766989492511/400000000000000000000000000000 : ℝ)*base76 + (1400592411707489/400000000000000000000000000000 : ℝ)*base77 + (112199967492511/400000000000000000000000000000 : ℝ)*base80 + (729151384892511/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6892573/2000000000000000000000 : ℝ)*base90 + (6892573/2000000000000000000000 : ℝ)*base92 + (6892573/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1690_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (679/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22639/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1690_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1690_s1_0 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-741072007/5000000000 : ℝ)*x 0 + (5505632561/10000000000 : ℝ)*x 1 + (1023319447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (741072007/5000000000 : ℝ)^5143 ≤ (4610419270287/50000000000000 : ℝ)^4119 := by
    have hnat : (741072007 : ℕ)^5143*50000000000000^4119 ≤ 4610419270287^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741072007 5000000000 4610419270287 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5505632561/10000000000 : ℝ)^5143 ≤ (5933089067549/12500000000000 : ℝ)^4119 := by
    have hnat : (5505632561 : ℕ)^5143*12500000000000^4119 ≤ 5933089067549^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505632561 10000000000 5933089067549 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023319447/2000000000 : ℝ)^5143 ≤ (43314448905671/100000000000000 : ℝ)^4119 := by
    have hnat : (1023319447 : ℕ)^5143*100000000000000^4119 ≤ 43314448905671^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023319447 2000000000 43314448905671 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-741072007/5000000000 : ℝ), (5505632561/10000000000 : ℝ), (1023319447/2000000000 : ℝ)] ![(4610419270287/50000000000000 : ℝ), (5933089067549/12500000000000 : ℝ), (43314448905671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-741072007/5000000000 : ℝ)|^5143 ≤ (4610419270287/50000000000000 : ℝ)^4119
        have hw : |(-741072007/5000000000 : ℝ)|=(741072007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5505632561/10000000000 : ℝ)|^5143 ≤ (5933089067549/12500000000000 : ℝ)^4119
        have hw : |(5505632561/10000000000 : ℝ)|=(5505632561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1023319447/2000000000 : ℝ)|^5143 ≤ (43314448905671/100000000000000 : ℝ)^4119
        have hw : |(1023319447/2000000000 : ℝ)|=(1023319447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s1_1 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678119347/5000000000 : ℝ)*x 0 + (-1685119969/10000000000 : ℝ)*x 1 + (5116596939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678119347/5000000000 : ℝ)^5143 ≤ (11465510998009/25000000000000 : ℝ)^4119 := by
    have hnat : (2678119347 : ℕ)^5143*25000000000000^4119 ≤ 11465510998009^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678119347 5000000000 11465510998009 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1685119969/10000000000 : ℝ)^5143 ≤ (10823510217549/100000000000000 : ℝ)^4119 := by
    have hnat : (1685119969 : ℕ)^5143*100000000000000^4119 ≤ 10823510217549^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685119969 10000000000 10823510217549 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5116596939/10000000000 : ℝ)^5143 ≤ (21657222888471/50000000000000 : ℝ)^4119 := by
    have hnat : (5116596939 : ℕ)^5143*50000000000000^4119 ≤ 21657222888471^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5116596939 10000000000 21657222888471 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678119347/5000000000 : ℝ), (-1685119969/10000000000 : ℝ), (5116596939/10000000000 : ℝ)] ![(11465510998009/25000000000000 : ℝ), (10823510217549/100000000000000 : ℝ), (21657222888471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678119347/5000000000 : ℝ)|^5143 ≤ (11465510998009/25000000000000 : ℝ)^4119
        have hw : |(2678119347/5000000000 : ℝ)|=(2678119347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1685119969/10000000000 : ℝ)|^5143 ≤ (10823510217549/100000000000000 : ℝ)^4119
        have hw : |(-1685119969/10000000000 : ℝ)|=(1685119969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5116596939/10000000000 : ℝ)|^5143 ≤ (21657222888471/50000000000000 : ℝ)^4119
        have hw : |(5116596939/10000000000 : ℝ)|=(5116596939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s1_2 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678118947/5000000000 : ℝ)*x 0 + (5116597637/10000000000 : ℝ)*x 1 + (-1685120117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678118947/5000000000 : ℝ)^5143 ≤ (22931017719619/50000000000000 : ℝ)^4119 := by
    have hnat : (2678118947 : ℕ)^5143*50000000000000^4119 ≤ 22931017719619^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678118947 5000000000 22931017719619 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5116597637/10000000000 : ℝ)^5143 ≤ (5414306644353/12500000000000 : ℝ)^4119 := by
    have hnat : (5116597637 : ℕ)^5143*12500000000000^4119 ≤ 5414306644353^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5116597637 10000000000 5414306644353 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1685120117/10000000000 : ℝ)^5143 ≤ (2705877851119/25000000000000 : ℝ)^4119 := by
    have hnat : (1685120117 : ℕ)^5143*25000000000000^4119 ≤ 2705877851119^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685120117 10000000000 2705877851119 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678118947/5000000000 : ℝ), (5116597637/10000000000 : ℝ), (-1685120117/10000000000 : ℝ)] ![(22931017719619/50000000000000 : ℝ), (5414306644353/12500000000000 : ℝ), (2705877851119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678118947/5000000000 : ℝ)|^5143 ≤ (22931017719619/50000000000000 : ℝ)^4119
        have hw : |(2678118947/5000000000 : ℝ)|=(2678118947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5116597637/10000000000 : ℝ)|^5143 ≤ (5414306644353/12500000000000 : ℝ)^4119
        have hw : |(5116597637/10000000000 : ℝ)|=(5116597637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1685120117/10000000000 : ℝ)|^5143 ≤ (2705877851119/25000000000000 : ℝ)^4119
        have hw : |(-1685120117/10000000000 : ℝ)|=(1685120117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s1_3 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20634757/50000000 : ℝ)*x 0 + (722413187/2000000000 : ℝ)*x 1 + (937730511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20634757/50000000 : ℝ)^5143 ≤ (16559349307567/50000000000000 : ℝ)^4119 := by
    have hnat : (20634757 : ℕ)^5143*50000000000000^4119 ≤ 16559349307567^4119*50000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20634757 50000000 16559349307567 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (722413187/2000000000 : ℝ)^5143 ≤ (28042191222613/100000000000000 : ℝ)^4119 := by
    have hnat : (722413187 : ℕ)^5143*100000000000000^4119 ≤ 28042191222613^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722413187 2000000000 28042191222613 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937730511/2000000000 : ℝ)^5143 ≤ (38839110142969/100000000000000 : ℝ)^4119 := by
    have hnat : (937730511 : ℕ)^5143*100000000000000^4119 ≤ 38839110142969^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937730511 2000000000 38839110142969 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20634757/50000000 : ℝ), (722413187/2000000000 : ℝ), (937730511/2000000000 : ℝ)] ![(16559349307567/50000000000000 : ℝ), (28042191222613/100000000000000 : ℝ), (38839110142969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20634757/50000000 : ℝ)|^5143 ≤ (16559349307567/50000000000000 : ℝ)^4119
        have hw : |(20634757/50000000 : ℝ)|=(20634757/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(722413187/2000000000 : ℝ)|^5143 ≤ (28042191222613/100000000000000 : ℝ)^4119
        have hw : |(722413187/2000000000 : ℝ)|=(722413187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(937730511/2000000000 : ℝ)|^5143 ≤ (38839110142969/100000000000000 : ℝ)^4119
        have hw : |(937730511/2000000000 : ℝ)|=(937730511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s1_4 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-741185251/5000000000 : ℝ)*x 0 + (640165887/1250000000 : ℝ)*x 1 + (550082359/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (741185251/5000000000 : ℝ)^5143 ≤ (9222597914661/100000000000000 : ℝ)^4119 := by
    have hnat : (741185251 : ℕ)^5143*100000000000000^4119 ≤ 9222597914661^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741185251 5000000000 9222597914661 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640165887/1250000000 : ℝ)^5143 ≤ (43364449430241/100000000000000 : ℝ)^4119 := by
    have hnat : (640165887 : ℕ)^5143*100000000000000^4119 ≤ 43364449430241^4119*1250000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640165887 1250000000 43364449430241 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550082359/1000000000 : ℝ)^5143 ≤ (23706476324519/50000000000000 : ℝ)^4119 := by
    have hnat : (550082359 : ℕ)^5143*50000000000000^4119 ≤ 23706476324519^4119*1000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550082359 1000000000 23706476324519 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-741185251/5000000000 : ℝ), (640165887/1250000000 : ℝ), (550082359/1000000000 : ℝ)] ![(9222597914661/100000000000000 : ℝ), (43364449430241/100000000000000 : ℝ), (23706476324519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-741185251/5000000000 : ℝ)|^5143 ≤ (9222597914661/100000000000000 : ℝ)^4119
        have hw : |(-741185251/5000000000 : ℝ)|=(741185251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640165887/1250000000 : ℝ)|^5143 ≤ (43364449430241/100000000000000 : ℝ)^4119
        have hw : |(640165887/1250000000 : ℝ)|=(640165887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550082359/1000000000 : ℝ)|^5143 ≤ (23706476324519/50000000000000 : ℝ)^4119
        have hw : |(550082359/1000000000 : ℝ)|=(550082359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s1_5 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252160891/10000000000 : ℝ)*x 0 + (-1300893887/10000000000 : ℝ)*x 1 + (5500823697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252160891/10000000000 : ℝ)^5143 ≤ (8950409841683/20000000000000 : ℝ)^4119 := by
    have hnat : (5252160891 : ℕ)^5143*20000000000000^4119 ≤ 8950409841683^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252160891 10000000000 8950409841683 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300893887/10000000000 : ℝ)^5143 ≤ (3917498484703/50000000000000 : ℝ)^4119 := by
    have hnat : (1300893887 : ℕ)^5143*50000000000000^4119 ≤ 3917498484703^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300893887 10000000000 3917498484703 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5500823697/10000000000 : ℝ)^5143 ≤ (1896518152023/4000000000000 : ℝ)^4119 := by
    have hnat : (5500823697 : ℕ)^5143*4000000000000^4119 ≤ 1896518152023^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500823697 10000000000 1896518152023 4000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252160891/10000000000 : ℝ), (-1300893887/10000000000 : ℝ), (5500823697/10000000000 : ℝ)] ![(8950409841683/20000000000000 : ℝ), (3917498484703/50000000000000 : ℝ), (1896518152023/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252160891/10000000000 : ℝ)|^5143 ≤ (8950409841683/20000000000000 : ℝ)^4119
        have hw : |(5252160891/10000000000 : ℝ)|=(5252160891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1300893887/10000000000 : ℝ)|^5143 ≤ (3917498484703/50000000000000 : ℝ)^4119
        have hw : |(-1300893887/10000000000 : ℝ)|=(1300893887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5500823697/10000000000 : ℝ)|^5143 ≤ (1896518152023/4000000000000 : ℝ)^4119
        have hw : |(5500823697/10000000000 : ℝ)|=(5500823697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s1_6 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252161069/10000000000 : ℝ)*x 0 + (550082387/1000000000 : ℝ)*x 1 + (-130089339/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252161069/10000000000 : ℝ)^5143 ≤ (5594006387769/12500000000000 : ℝ)^4119 := by
    have hnat : (5252161069 : ℕ)^5143*12500000000000^4119 ≤ 5594006387769^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252161069 10000000000 5594006387769 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550082387/1000000000 : ℝ)^5143 ≤ (9482591132481/20000000000000 : ℝ)^4119 := by
    have hnat : (550082387 : ℕ)^5143*20000000000000^4119 ≤ 9482591132481^4119*1000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550082387 1000000000 9482591132481 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130089339/1000000000 : ℝ)^5143 ≤ (7834993231933/100000000000000 : ℝ)^4119 := by
    have hnat : (130089339 : ℕ)^5143*100000000000000^4119 ≤ 7834993231933^4119*1000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130089339 1000000000 7834993231933 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252161069/10000000000 : ℝ), (550082387/1000000000 : ℝ), (-130089339/1000000000 : ℝ)] ![(5594006387769/12500000000000 : ℝ), (9482591132481/20000000000000 : ℝ), (7834993231933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252161069/10000000000 : ℝ)|^5143 ≤ (5594006387769/12500000000000 : ℝ)^4119
        have hw : |(5252161069/10000000000 : ℝ)|=(5252161069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550082387/1000000000 : ℝ)|^5143 ≤ (9482591132481/20000000000000 : ℝ)^4119
        have hw : |(550082387/1000000000 : ℝ)|=(550082387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130089339/1000000000 : ℝ)|^5143 ≤ (7834993231933/100000000000000 : ℝ)^4119
        have hw : |(-130089339/1000000000 : ℝ)|=(130089339/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s1_7 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4127578197/10000000000 : ℝ)*x 0 + (935112693/2000000000 : ℝ)*x 1 + (113292911/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4127578197/10000000000 : ℝ)^5143 ≤ (33124979252933/100000000000000 : ℝ)^4119 := by
    have hnat : (4127578197 : ℕ)^5143*100000000000000^4119 ≤ 33124979252933^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127578197 10000000000 33124979252933 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935112693/2000000000 : ℝ)^5143 ≤ (2362291069/6103515625 : ℝ)^4119 := by
    have hnat : (935112693 : ℕ)^5143*6103515625^4119 ≤ 2362291069^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935112693 2000000000 2362291069 6103515625 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113292911/312500000 : ℝ)^5143 ≤ (5634248772991/20000000000000 : ℝ)^4119 := by
    have hnat : (113292911 : ℕ)^5143*20000000000000^4119 ≤ 5634248772991^4119*312500000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113292911 312500000 5634248772991 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4127578197/10000000000 : ℝ), (935112693/2000000000 : ℝ), (113292911/312500000 : ℝ)] ![(33124979252933/100000000000000 : ℝ), (2362291069/6103515625 : ℝ), (5634248772991/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4127578197/10000000000 : ℝ)|^5143 ≤ (33124979252933/100000000000000 : ℝ)^4119
        have hw : |(4127578197/10000000000 : ℝ)|=(4127578197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(935112693/2000000000 : ℝ)|^5143 ≤ (2362291069/6103515625 : ℝ)^4119
        have hw : |(935112693/2000000000 : ℝ)|=(935112693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113292911/312500000 : ℝ)|^5143 ≤ (5634248772991/20000000000000 : ℝ)^4119
        have hw : |(113292911/312500000 : ℝ)|=(113292911/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1690_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22639/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (679/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (589/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3541/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22639/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (679/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22639/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (679/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22639/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (679/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22639/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (679/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22639/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (679/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22639/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (679/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (679/12500 : ℝ) ^ (5135/1024 : ℝ) ≤ (9063541740501/20000000000000000000 : ℝ) := by
    have hpowers : (679/12500 : ℝ)^5135 ≤ (9063541740501/20000000000000000000 : ℝ)^1024 := by
      have hnat : (679 : ℕ)^5135*20000000000000000000^1024 ≤ 9063541740501^1024*12500^5135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        679 12500 9063541740501 20000000000000000000 5135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (679/12500 : ℝ)) (X := (9063541740501/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22639/100000 : ℝ) ^ (5135/1024 : ℝ) ≤ (58188326088478793/100000000000000000000 : ℝ) := by
    have hpowers : (22639/100000 : ℝ)^5135 ≤ (58188326088478793/100000000000000000000 : ℝ)^1024 := by
      have hnat : (22639 : ℕ)^5135*100000000000000000000^1024 ≤ 58188326088478793^1024*100000^5135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22639 100000 58188326088478793 100000000000000000000 5135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22639/100000 : ℝ)) (X := (58188326088478793/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000009063541740501/10000000000000000000 : ℝ) ≤ (10000001807412537/10000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (10000009063541740501/10000000000000000000 : ℝ)^1024 ≤ (10000001807412537/10000000000000000 : ℝ)^5135 := by
      have hnat : (10000009063541740501 : ℕ)^1024*10000000000000000^5135 ≤ 10000001807412537^5135*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000009063541740501 10000000000000000000 10000001807412537 10000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001807412537/10000000000000000 : ℝ)) (X := (10000009063541740501/10000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50029116821898590649/50000000000000000000 : ℝ) ≤ (10001161000112577/10000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (50029116821898590649/50000000000000000000 : ℝ)^1024 ≤ (10001161000112577/10000000000000000 : ℝ)^5135 := by
      have hnat : (50029116821898590649 : ℕ)^1024*10000000000000000^5135 ≤ 10001161000112577^5135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029116821898590649 50000000000000000000 10001161000112577 10000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001161000112577/10000000000000000 : ℝ)) (X := (50029116821898590649/50000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50058188326088478793/50000000000000000000 : ℝ) ≤ (10002320192812617/10000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (50058188326088478793/50000000000000000000 : ℝ)^1024 ≤ (10002320192812617/10000000000000000 : ℝ)^5135 := by
      have hnat : (50058188326088478793 : ℕ)^1024*10000000000000000^5135 ≤ 10002320192812617^5135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50058188326088478793 50000000000000000000 10002320192812617 10000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002320192812617/10000000000000000 : ℝ)) (X := (50058188326088478793/50000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9063541740501/20000000000000000000 : ℝ) ≤ ((172057437630654289599/172070000000000000000 : ℝ)+2*(28979817501/43017500000000 : ℝ)*(679/12500 : ℝ))^(5135/1024 : ℝ) := by
    rw [show (172057437630654289599/172070000000000000000 : ℝ)+2*(28979817501/43017500000000 : ℝ)*(679/12500 : ℝ)=(10000001807412537/10000000000000000 : ℝ) by norm_num, show 1+2*(9063541740501/20000000000000000000 : ℝ)=(10000009063541740501/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(58188326088478793/100000000000000000000 : ℝ)+(9063541740501/20000000000000000000 : ℝ) ≤ ((172057437630654289599/172070000000000000000 : ℝ)+(28979817501/43017500000000 : ℝ)*((22639/100000 : ℝ)+(679/12500 : ℝ)))^(5135/1024 : ℝ) := by
    rw [show (172057437630654289599/172070000000000000000 : ℝ)+(28979817501/43017500000000 : ℝ)*((22639/100000 : ℝ)+(679/12500 : ℝ))=(10001161000112577/10000000000000000 : ℝ) by norm_num, show 1+(58188326088478793/100000000000000000000 : ℝ)+(9063541740501/20000000000000000000 : ℝ)=(50029116821898590649/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(58188326088478793/100000000000000000000 : ℝ) ≤ ((172057437630654289599/172070000000000000000 : ℝ)+2*(28979817501/43017500000000 : ℝ)*(22639/100000 : ℝ))^(5135/1024 : ℝ) := by
    rw [show (172057437630654289599/172070000000000000000 : ℝ)+2*(28979817501/43017500000000 : ℝ)*(22639/100000 : ℝ)=(10002320192812617/10000000000000000 : ℝ) by norm_num, show 1+2*(58188326088478793/100000000000000000000 : ℝ)=(50058188326088478793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (172057437630654289599/172070000000000000000 : ℝ)*(X 1 0+X 2 0)+(28979817501/43017500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (679/12500 : ℝ)) (hi := (22639/100000 : ℝ)) (c := (172057437630654289599/172070000000000000000 : ℝ)) (alpha := (28979817501/43017500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (172057437630654289599/172070000000000000000 : ℝ)*(X 0 1+X 2 1)+(28979817501/43017500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (679/12500 : ℝ)) (hi := (22639/100000 : ℝ)) (c := (172057437630654289599/172070000000000000000 : ℝ)) (alpha := (28979817501/43017500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (172057437630654289599/172070000000000000000 : ℝ)*(X 0 2+X 1 2)+(28979817501/43017500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (679/12500 : ℝ)) (hi := (22639/100000 : ℝ)) (c := (172057437630654289599/172070000000000000000 : ℝ)) (alpha := (28979817501/43017500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-741072007/5000000000 : ℝ)*X 0 0+(5505632561/10000000000 : ℝ)*X 0 1+(1023319447/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2678119347/5000000000 : ℝ)*X 1 0+(-1685119969/10000000000 : ℝ)*X 1 1+(5116596939/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678118947/5000000000 : ℝ)*X 2 0+(5116597637/10000000000 : ℝ)*X 2 1+(-1685120117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((20634757/50000000 : ℝ)*X 0 0+(722413187/2000000000 : ℝ)*X 0 1+(937730511/2000000000 : ℝ)*X 0 2+(20634757/50000000 : ℝ)*X 1 0+(722413187/2000000000 : ℝ)*X 1 1+(937730511/2000000000 : ℝ)*X 1 2+(20634757/50000000 : ℝ)*X 2 0+(722413187/2000000000 : ℝ)*X 2 1+(937730511/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-741185251/5000000000 : ℝ)*X 0 0+(640165887/1250000000 : ℝ)*X 0 1+(550082359/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252160891/10000000000 : ℝ)*X 1 0+(-1300893887/10000000000 : ℝ)*X 1 1+(5500823697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252161069/10000000000 : ℝ)*X 2 0+(550082387/1000000000 : ℝ)*X 2 1+(-130089339/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4127578197/10000000000 : ℝ)*X 0 0+(935112693/2000000000 : ℝ)*X 0 1+(113292911/312500000 : ℝ)*X 0 2+(4127578197/10000000000 : ℝ)*X 1 0+(935112693/2000000000 : ℝ)*X 1 1+(113292911/312500000 : ℝ)*X 1 2+(4127578197/10000000000 : ℝ)*X 2 0+(935112693/2000000000 : ℝ)*X 2 1+(113292911/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6584252930300955328275676191/860350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57810303/5000000000000 : ℝ)*(base19) + (29035379/4000000000000 : ℝ)*(base23) + (43971309/20000000000000 : ℝ)*(upper3) + (6213079/25000000000000 : ℝ)*(upper4) + (2225157/5000000000000 : ℝ)*(upper5) + (174967319127801/10000000000000 : ℝ)*(major0) + (174967319127801/10000000000000 : ℝ)*(major1) + (174967319127801/10000000000000 : ℝ)*(major2) + (642617799194493/25000000000000 : ℝ)*(sp0) + (514095406661453/20000000000000 : ℝ)*(sp1) + (51409549272577/2000000000000 : ℝ)*(sp2) + (464432219447067/50000000000000 : ℝ)*(sp3) + (6992735353/100000000000000 : ℝ)*(sp4) + (3499048771/100000000000000 : ℝ)*(sp7) + (116108492242863/12500000000000 : ℝ)*(f.failure) + (102819127580533/4000000000000 : ℝ)*(f.sum) + (10519501168231/17207000000000000000000000000 : ℝ)*base66 + (16909373212639458201/1720700000000000000000000000000000 : ℝ)*base68 + (8436552233566358201/1720700000000000000000000000000000 : ℝ)*base70 + (24053543089467858201/1720700000000000000000000000000000 : ℝ)*base72 + (1174236176703/860350000000000000000000000 : ℝ)*base74 + (12380357306967858201/1720700000000000000000000000000000 : ℝ)*base76 + (12933226803260858201/1720700000000000000000000000000000 : ℝ)*base78 + (13378937776428458201/1720700000000000000000000000000000 : ℝ)*base80 + (2119329108237/2150875000000000000000000000 : ℝ)*base81 + (1156743/250000000000000000000 : ℝ)*base90 + (1156743/250000000000000000000 : ℝ)*base92 + (1156743/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27471989785766110999543497597/2150875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (436832023/25000000000000 : ℝ)*(base19) + (120236001/6250000000000 : ℝ)*(base23) + (323119813/100000000000000 : ℝ)*(upper3) + (2247/125000000000 : ℝ)*(lower4) + (263812683/100000000000000 : ℝ)*(upper5) + (896819788380401/50000000000000 : ℝ)*(major0) + (896819788380401/50000000000000 : ℝ)*(major1) + (896819788380401/50000000000000 : ℝ)*(major2) + (12784876087/100000000000000 : ℝ)*(sp1) + (1063118883/6250000000000 : ℝ)*(sp2) + (527013975813309/20000000000000 : ℝ)*(sp4) + (1317527673431183/50000000000000 : ℝ)*(sp5) + (1317525472694201/50000000000000 : ℝ)*(sp6) + (476104424353001/50000000000000 : ℝ)*(sp7) + (476104424353001/50000000000000 : ℝ)*(f.failure) + (527013975813309/20000000000000 : ℝ)*(f.sum) + (7889243164497/4301750000000000000000000000 : ℝ)*base65 + (11578197171841250801/8603500000000000000000000000000000 : ℝ)*base68 + (10389491187355250801/8603500000000000000000000000000000 : ℝ)*base70 + (5236856379160749199/8603500000000000000000000000000000 : ℝ)*base71 + (3884740971521/17207000000000000000000000000 : ℝ)*base73 + (25987535553212750801/8603500000000000000000000000000000 : ℝ)*base76 + (62246603146340250801/8603500000000000000000000000000000 : ℝ)*base78 + (112869129477287250801/8603500000000000000000000000000000 : ℝ)*base80 + (1200581936749/860350000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7040239/1000000000000000000000 : ℝ)*base89 + (7040239/1000000000000000000000 : ℝ)*base91 + (7040239/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1690_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22639/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (679/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (589/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3541/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1690_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1690_s2_0 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-743735297/5000000000 : ℝ)*x 0 + (5484279409/10000000000 : ℝ)*x 1 + (5134408521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (743735297/5000000000 : ℝ)^5143 ≤ (4631116727559/50000000000000 : ℝ)^4119 := by
    have hnat : (743735297 : ℕ)^5143*50000000000000^4119 ≤ 4631116727559^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743735297 5000000000 4631116727559 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5484279409/10000000000 : ℝ)^5143 ≤ (47234970364743/100000000000000 : ℝ)^4119 := by
    have hnat : (5484279409 : ℕ)^5143*100000000000000^4119 ≤ 47234970364743^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484279409 10000000000 47234970364743 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5134408521/10000000000 : ℝ)^5143 ≤ (43502796157749/100000000000000 : ℝ)^4119 := by
    have hnat : (5134408521 : ℕ)^5143*100000000000000^4119 ≤ 43502796157749^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134408521 10000000000 43502796157749 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-743735297/5000000000 : ℝ), (5484279409/10000000000 : ℝ), (5134408521/10000000000 : ℝ)] ![(4631116727559/50000000000000 : ℝ), (47234970364743/100000000000000 : ℝ), (43502796157749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-743735297/5000000000 : ℝ)|^5143 ≤ (4631116727559/50000000000000 : ℝ)^4119
        have hw : |(-743735297/5000000000 : ℝ)|=(743735297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5484279409/10000000000 : ℝ)|^5143 ≤ (47234970364743/100000000000000 : ℝ)^4119
        have hw : |(5484279409/10000000000 : ℝ)|=(5484279409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5134408521/10000000000 : ℝ)|^5143 ≤ (43502796157749/100000000000000 : ℝ)^4119
        have hw : |(5134408521/10000000000 : ℝ)|=(5134408521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s2_1 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42804109/80000000 : ℝ)*x 0 + (-333849321/2000000000 : ℝ)*x 1 + (5134408477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42804109/80000000 : ℝ)^5143 ≤ (45800845429493/100000000000000 : ℝ)^4119 := by
    have hnat : (42804109 : ℕ)^5143*100000000000000^4119 ≤ 45800845429493^4119*80000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42804109 80000000 45800845429493 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (333849321/2000000000 : ℝ)^5143 ≤ (5348179430383/50000000000000 : ℝ)^4119 := by
    have hnat : (333849321 : ℕ)^5143*50000000000000^4119 ≤ 5348179430383^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333849321 2000000000 5348179430383 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5134408477/10000000000 : ℝ)^5143 ≤ (21751397846133/50000000000000 : ℝ)^4119 := by
    have hnat : (5134408477 : ℕ)^5143*50000000000000^4119 ≤ 21751397846133^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134408477 10000000000 21751397846133 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42804109/80000000 : ℝ), (-333849321/2000000000 : ℝ), (5134408477/10000000000 : ℝ)] ![(45800845429493/100000000000000 : ℝ), (5348179430383/50000000000000 : ℝ), (21751397846133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42804109/80000000 : ℝ)|^5143 ≤ (45800845429493/100000000000000 : ℝ)^4119
        have hw : |(42804109/80000000 : ℝ)|=(42804109/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-333849321/2000000000 : ℝ)|^5143 ≤ (5348179430383/50000000000000 : ℝ)^4119
        have hw : |(-333849321/2000000000 : ℝ)|=(333849321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5134408477/10000000000 : ℝ)|^5143 ≤ (21751397846133/50000000000000 : ℝ)^4119
        have hw : |(5134408477/10000000000 : ℝ)|=(5134408477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s2_2 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675256847/5000000000 : ℝ)*x 0 + (2567204221/5000000000 : ℝ)*x 1 + (-1669246559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675256847/5000000000 : ℝ)^5143 ≤ (715638221359/1562500000000 : ℝ)^4119 := by
    have hnat : (2675256847 : ℕ)^5143*1562500000000^4119 ≤ 715638221359^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675256847 5000000000 715638221359 1562500000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2567204221/5000000000 : ℝ)^5143 ≤ (8700559064399/20000000000000 : ℝ)^4119 := by
    have hnat : (2567204221 : ℕ)^5143*20000000000000^4119 ≤ 8700559064399^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567204221 5000000000 8700559064399 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1669246559/10000000000 : ℝ)^5143 ≤ (2674089623181/25000000000000 : ℝ)^4119 := by
    have hnat : (1669246559 : ℕ)^5143*25000000000000^4119 ≤ 2674089623181^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669246559 10000000000 2674089623181 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675256847/5000000000 : ℝ), (2567204221/5000000000 : ℝ), (-1669246559/10000000000 : ℝ)] ![(715638221359/1562500000000 : ℝ), (8700559064399/20000000000000 : ℝ), (2674089623181/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675256847/5000000000 : ℝ)|^5143 ≤ (715638221359/1562500000000 : ℝ)^4119
        have hw : |(2675256847/5000000000 : ℝ)|=(2675256847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2567204221/5000000000 : ℝ)|^5143 ≤ (8700559064399/20000000000000 : ℝ)^4119
        have hw : |(2567204221/5000000000 : ℝ)|=(2567204221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1669246559/10000000000 : ℝ)|^5143 ≤ (2674089623181/25000000000000 : ℝ)^4119
        have hw : |(-1669246559/10000000000 : ℝ)|=(1669246559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s2_3 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4131048049/10000000000 : ℝ)*x 0 + (916468711/2500000000 : ℝ)*x 1 + (926816217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4131048049/10000000000 : ℝ)^5143 ≤ (6631950437739/20000000000000 : ℝ)^4119 := by
    have hnat : (4131048049 : ℕ)^5143*20000000000000^4119 ≤ 6631950437739^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131048049 10000000000 6631950437739 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916468711/2500000000 : ℝ)^5143 ≤ (357059382883/1250000000000 : ℝ)^4119 := by
    have hnat : (916468711 : ℕ)^5143*1250000000000^4119 ≤ 357059382883^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916468711 2500000000 357059382883 1250000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (926816217/2000000000 : ℝ)^5143 ≤ (9568874290443/25000000000000 : ℝ)^4119 := by
    have hnat : (926816217 : ℕ)^5143*25000000000000^4119 ≤ 9568874290443^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926816217 2000000000 9568874290443 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4131048049/10000000000 : ℝ), (916468711/2500000000 : ℝ), (926816217/2000000000 : ℝ)] ![(6631950437739/20000000000000 : ℝ), (357059382883/1250000000000 : ℝ), (9568874290443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4131048049/10000000000 : ℝ)|^5143 ≤ (6631950437739/20000000000000 : ℝ)^4119
        have hw : |(4131048049/10000000000 : ℝ)|=(4131048049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(916468711/2500000000 : ℝ)|^5143 ≤ (357059382883/1250000000000 : ℝ)^4119
        have hw : |(916468711/2500000000 : ℝ)|=(916468711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(926816217/2000000000 : ℝ)|^5143 ≤ (9568874290443/25000000000000 : ℝ)^4119
        have hw : |(926816217/2000000000 : ℝ)|=(926816217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s2_4 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1487635211/10000000000 : ℝ)*x 0 + (5138237539/10000000000 : ℝ)*x 1 + (1370098231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1487635211/10000000000 : ℝ)^5143 ≤ (9263513345347/100000000000000 : ℝ)^4119 := by
    have hnat : (1487635211 : ℕ)^5143*100000000000000^4119 ≤ 9263513345347^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487635211 10000000000 9263513345347 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138237539/10000000000 : ℝ)^5143 ≤ (21771653867003/50000000000000 : ℝ)^4119 := by
    have hnat : (5138237539 : ℕ)^5143*50000000000000^4119 ≤ 21771653867003^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138237539 10000000000 21771653867003 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370098231/2500000000 : ℝ)^5143 ≤ (5899147363159/12500000000000 : ℝ)^4119 := by
    have hnat : (1370098231 : ℕ)^5143*12500000000000^4119 ≤ 5899147363159^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370098231 2500000000 5899147363159 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1487635211/10000000000 : ℝ), (5138237539/10000000000 : ℝ), (1370098231/2500000000 : ℝ)] ![(9263513345347/100000000000000 : ℝ), (21771653867003/50000000000000 : ℝ), (5899147363159/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1487635211/10000000000 : ℝ)|^5143 ≤ (9263513345347/100000000000000 : ℝ)^4119
        have hw : |(-1487635211/10000000000 : ℝ)|=(1487635211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138237539/10000000000 : ℝ)|^5143 ≤ (21771653867003/50000000000000 : ℝ)^4119
        have hw : |(5138237539/10000000000 : ℝ)|=(5138237539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1370098231/2500000000 : ℝ)|^5143 ≤ (5899147363159/12500000000000 : ℝ)^4119
        have hw : |(1370098231/2500000000 : ℝ)|=(1370098231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s2_5 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657121673/1250000000 : ℝ)*x 0 + (-661631023/5000000000 : ℝ)*x 1 + (85631141/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657121673/1250000000 : ℝ)^5143 ≤ (8960651002699/20000000000000 : ℝ)^4119 := by
    have hnat : (657121673 : ℕ)^5143*20000000000000^4119 ≤ 8960651002699^4119*1250000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657121673 1250000000 8960651002699 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (661631023/5000000000 : ℝ)^5143 ≤ (8003564996359/100000000000000 : ℝ)^4119 := by
    have hnat : (661631023 : ℕ)^5143*100000000000000^4119 ≤ 8003564996359^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661631023 5000000000 8003564996359 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85631141/156250000 : ℝ)^5143 ≤ (47193179980479/100000000000000 : ℝ)^4119 := by
    have hnat : (85631141 : ℕ)^5143*100000000000000^4119 ≤ 47193179980479^4119*156250000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85631141 156250000 47193179980479 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657121673/1250000000 : ℝ), (-661631023/5000000000 : ℝ), (85631141/156250000 : ℝ)] ![(8960651002699/20000000000000 : ℝ), (8003564996359/100000000000000 : ℝ), (47193179980479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657121673/1250000000 : ℝ)|^5143 ≤ (8960651002699/20000000000000 : ℝ)^4119
        have hw : |(657121673/1250000000 : ℝ)|=(657121673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-661631023/5000000000 : ℝ)|^5143 ≤ (8003564996359/100000000000000 : ℝ)^4119
        have hw : |(-661631023/5000000000 : ℝ)|=(661631023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85631141/156250000 : ℝ)|^5143 ≤ (47193179980479/100000000000000 : ℝ)^4119
        have hw : |(85631141/156250000 : ℝ)|=(85631141/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s2_6 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051394673/2000000000 : ℝ)*x 0 + (1370098257/2500000000 : ℝ)*x 1 + (-661631033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051394673/2000000000 : ℝ)^5143 ≤ (44803254811309/100000000000000 : ℝ)^4119 := by
    have hnat : (1051394673 : ℕ)^5143*100000000000000^4119 ≤ 44803254811309^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051394673 2000000000 44803254811309 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1370098257/2500000000 : ℝ)^5143 ≤ (47193180023487/100000000000000 : ℝ)^4119 := by
    have hnat : (1370098257 : ℕ)^5143*100000000000000^4119 ≤ 47193180023487^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370098257 2500000000 47193180023487 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (661631033/5000000000 : ℝ)^5143 ≤ (8003565147399/100000000000000 : ℝ)^4119 := by
    have hnat : (661631033 : ℕ)^5143*100000000000000^4119 ≤ 8003565147399^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661631033 5000000000 8003565147399 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051394673/2000000000 : ℝ), (1370098257/2500000000 : ℝ), (-661631033/5000000000 : ℝ)] ![(44803254811309/100000000000000 : ℝ), (47193180023487/100000000000000 : ℝ), (8003565147399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051394673/2000000000 : ℝ)|^5143 ≤ (44803254811309/100000000000000 : ℝ)^4119
        have hw : |(1051394673/2000000000 : ℝ)|=(1051394673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1370098257/2500000000 : ℝ)|^5143 ≤ (47193180023487/100000000000000 : ℝ)^4119
        have hw : |(1370098257/2500000000 : ℝ)|=(1370098257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-661631033/5000000000 : ℝ)|^5143 ≤ (8003565147399/100000000000000 : ℝ)^4119
        have hw : |(-661631033/5000000000 : ℝ)|=(661631033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s2_7 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2065751919/5000000000 : ℝ)*x 0 + (4623484907/10000000000 : ℝ)*x 1 + (3676630107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065751919/5000000000 : ℝ)^5143 ≤ (33164320393413/100000000000000 : ℝ)^4119 := by
    have hnat : (2065751919 : ℕ)^5143*100000000000000^4119 ≤ 33164320393413^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065751919 5000000000 33164320393413 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4623484907/10000000000 : ℝ)^5143 ≤ (9541562657191/25000000000000 : ℝ)^4119 := by
    have hnat : (4623484907 : ℕ)^5143*25000000000000^4119 ≤ 9541562657191^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4623484907 10000000000 9541562657191 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3676630107/10000000000 : ℝ)^5143 ≤ (7167357241481/25000000000000 : ℝ)^4119 := by
    have hnat : (3676630107 : ℕ)^5143*25000000000000^4119 ≤ 7167357241481^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3676630107 10000000000 7167357241481 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2065751919/5000000000 : ℝ), (4623484907/10000000000 : ℝ), (3676630107/10000000000 : ℝ)] ![(33164320393413/100000000000000 : ℝ), (9541562657191/25000000000000 : ℝ), (7167357241481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2065751919/5000000000 : ℝ)|^5143 ≤ (33164320393413/100000000000000 : ℝ)^4119
        have hw : |(2065751919/5000000000 : ℝ)|=(2065751919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4623484907/10000000000 : ℝ)|^5143 ≤ (9541562657191/25000000000000 : ℝ)^4119
        have hw : |(4623484907/10000000000 : ℝ)|=(4623484907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3676630107/10000000000 : ℝ)|^5143 ≤ (7167357241481/25000000000000 : ℝ)^4119
        have hw : |(3676630107/10000000000 : ℝ)|=(3676630107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1690_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3541/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (589/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (9811/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8629/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3541/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (589/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3541/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (589/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3541/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (589/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3541/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (589/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3541/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (589/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3541/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (589/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (589/6250 : ℝ) ^ (5135/1024 : ℝ) ≤ (359021569477289/50000000000000000000 : ℝ) := by
    have hpowers : (589/6250 : ℝ)^5135 ≤ (359021569477289/50000000000000000000 : ℝ)^1024 := by
      have hnat : (589 : ℕ)^5135*50000000000000000000^1024 ≤ 359021569477289^1024*6250^5135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        589 6250 359021569477289 50000000000000000000 5135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (589/6250 : ℝ)) (X := (359021569477289/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3541/20000 : ℝ) ^ (5135/1024 : ℝ) ≤ (16961546046653187/100000000000000000000 : ℝ) := by
    have hpowers : (3541/20000 : ℝ)^5135 ≤ (16961546046653187/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3541 : ℕ)^5135*100000000000000000000^1024 ≤ 16961546046653187^1024*20000^5135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3541 20000 16961546046653187 100000000000000000000 5135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3541/20000 : ℝ)) (X := (16961546046653187/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000359021569477289/25000000000000000000 : ℝ) ≤ (5000014318830527/5000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (25000359021569477289/25000000000000000000 : ℝ)^1024 ≤ (5000014318830527/5000000000000000 : ℝ)^5135 := by
      have hnat : (25000359021569477289 : ℕ)^1024*5000000000000000^5135 ≤ 5000014318830527^5135*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000359021569477289 25000000000000000000 5000014318830527 5000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000014318830527/5000000000000000 : ℝ)) (X := (25000359021569477289/25000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20003535917837121553/20000000000000000000 : ℝ) ≤ (80002820271587/80000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (20003535917837121553/20000000000000000000 : ℝ)^1024 ≤ (80002820271587/80000000000000 : ℝ)^5135 := by
      have hnat : (20003535917837121553 : ℕ)^1024*80000000000000^5135 ≤ 80002820271587^5135*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20003535917837121553 20000000000000000000 80002820271587 80000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80002820271587/80000000000000 : ℝ)) (X := (20003535917837121553/20000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016961546046653187/50000000000000000000 : ℝ) ≤ (625042276889731/625000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (50016961546046653187/50000000000000000000 : ℝ)^1024 ≤ (625042276889731/625000000000000 : ℝ)^5135 := by
      have hnat : (50016961546046653187 : ℕ)^1024*625000000000000^5135 ≤ 625042276889731^5135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016961546046653187 50000000000000000000 625042276889731 625000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625042276889731/625000000000000 : ℝ)) (X := (50016961546046653187/50000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(359021569477289/50000000000000000000 : ℝ) ≤ ((41402066175623880983/41405000000000000000 : ℝ)+2*(323896287321/828100000000000 : ℝ)*(589/6250 : ℝ))^(5135/1024 : ℝ) := by
    rw [show (41402066175623880983/41405000000000000000 : ℝ)+2*(323896287321/828100000000000 : ℝ)*(589/6250 : ℝ)=(5000014318830527/5000000000000000 : ℝ) by norm_num, show 1+2*(359021569477289/50000000000000000000 : ℝ)=(25000359021569477289/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16961546046653187/100000000000000000000 : ℝ)+(359021569477289/50000000000000000000 : ℝ) ≤ ((41402066175623880983/41405000000000000000 : ℝ)+(323896287321/828100000000000 : ℝ)*((3541/20000 : ℝ)+(589/6250 : ℝ)))^(5135/1024 : ℝ) := by
    rw [show (41402066175623880983/41405000000000000000 : ℝ)+(323896287321/828100000000000 : ℝ)*((3541/20000 : ℝ)+(589/6250 : ℝ))=(80002820271587/80000000000000 : ℝ) by norm_num, show 1+(16961546046653187/100000000000000000000 : ℝ)+(359021569477289/50000000000000000000 : ℝ)=(20003535917837121553/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16961546046653187/100000000000000000000 : ℝ) ≤ ((41402066175623880983/41405000000000000000 : ℝ)+2*(323896287321/828100000000000 : ℝ)*(3541/20000 : ℝ))^(5135/1024 : ℝ) := by
    rw [show (41402066175623880983/41405000000000000000 : ℝ)+2*(323896287321/828100000000000 : ℝ)*(3541/20000 : ℝ)=(625042276889731/625000000000000 : ℝ) by norm_num, show 1+2*(16961546046653187/100000000000000000000 : ℝ)=(50016961546046653187/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41402066175623880983/41405000000000000000 : ℝ)*(X 1 0+X 2 0)+(323896287321/828100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (589/6250 : ℝ)) (hi := (3541/20000 : ℝ)) (c := (41402066175623880983/41405000000000000000 : ℝ)) (alpha := (323896287321/828100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41402066175623880983/41405000000000000000 : ℝ)*(X 0 1+X 2 1)+(323896287321/828100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (589/6250 : ℝ)) (hi := (3541/20000 : ℝ)) (c := (41402066175623880983/41405000000000000000 : ℝ)) (alpha := (323896287321/828100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41402066175623880983/41405000000000000000 : ℝ)*(X 0 2+X 1 2)+(323896287321/828100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (589/6250 : ℝ)) (hi := (3541/20000 : ℝ)) (c := (41402066175623880983/41405000000000000000 : ℝ)) (alpha := (323896287321/828100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-743735297/5000000000 : ℝ)*X 0 0+(5484279409/10000000000 : ℝ)*X 0 1+(5134408521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42804109/80000000 : ℝ)*X 1 0+(-333849321/2000000000 : ℝ)*X 1 1+(5134408477/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675256847/5000000000 : ℝ)*X 2 0+(2567204221/5000000000 : ℝ)*X 2 1+(-1669246559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4131048049/10000000000 : ℝ)*X 0 0+(916468711/2500000000 : ℝ)*X 0 1+(926816217/2000000000 : ℝ)*X 0 2+(4131048049/10000000000 : ℝ)*X 1 0+(916468711/2500000000 : ℝ)*X 1 1+(926816217/2000000000 : ℝ)*X 1 2+(4131048049/10000000000 : ℝ)*X 2 0+(916468711/2500000000 : ℝ)*X 2 1+(926816217/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1487635211/10000000000 : ℝ)*X 0 0+(5138237539/10000000000 : ℝ)*X 0 1+(1370098231/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((657121673/1250000000 : ℝ)*X 1 0+(-661631023/5000000000 : ℝ)*X 1 1+(85631141/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051394673/2000000000 : ℝ)*X 2 0+(1370098257/2500000000 : ℝ)*X 2 1+(-661631033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2065751919/5000000000 : ℝ)*X 0 0+(4623484907/10000000000 : ℝ)*X 0 1+(3676630107/10000000000 : ℝ)*X 0 2+(2065751919/5000000000 : ℝ)*X 1 0+(4623484907/10000000000 : ℝ)*X 1 1+(3676630107/10000000000 : ℝ)*X 1 2+(2065751919/5000000000 : ℝ)*X 2 0+(4623484907/10000000000 : ℝ)*X 2 1+(3676630107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85484941440118562550992109/7962500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1611355889/100000000000000 : ℝ)*(base19) + (1564161861/100000000000000 : ℝ)*(base23) + (11243247/25000000000000 : ℝ)*(lower2) + (60255503/25000000000000 : ℝ)*(upper3) + (212516963/100000000000000 : ℝ)*(upper5) + (194553839724933/10000000000000 : ℝ)*(major0) + (194553839724933/10000000000000 : ℝ)*(major1) + (194553839724933/10000000000000 : ℝ)*(major2) + (357276510850071/12500000000000 : ℝ)*(sp0) + (89319556445123/3125000000000 : ℝ)*(sp1) + (714556463359491/25000000000000 : ℝ)*(sp2) + (258210792143271/25000000000000 : ℝ)*(sp3) + (15330799257/100000000000000 : ℝ)*(sp4) + (5850461/100000000000 : ℝ)*(sp7) + (258212254758521/25000000000000 : ℝ)*(f.failure) + (114329096703993/4000000000000 : ℝ)*(f.sum) + (1832331318333/637000000000000000000000000 : ℝ)*base65 + (26260117092019297/31850000000000000000000000000000 : ℝ)*base68 + (173579164581269297/31850000000000000000000000000000 : ℝ)*base70 + (245133966354269297/31850000000000000000000000000000 : ℝ)*base72 + (175570460153/63700000000000000000000000 : ℝ)*base73 + (149186780801869297/31850000000000000000000000000000 : ℝ)*base76 + (45111221213869297/31850000000000000000000000000000 : ℝ)*base78 + (97245288699930703/31850000000000000000000000000000 : ℝ)*base79 + (132903833623/318500000000000000000000000 : ℝ)*base82 + (1080481/500000000000000000000 : ℝ)*base90 + (1080481/500000000000000000000 : ℝ)*base92 + (1080481/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101479598398222219433289/10351250000000000000000000000 : ℝ) := by norm_num
    linear_combination (132382647/10000000000000 : ℝ)*(base19) + (1456476881/100000000000000 : ℝ)*(base23) + (102619859/50000000000000 : ℝ)*(upper3) + (65548599/100000000000000 : ℝ)*(lower4) + (198693673/100000000000000 : ℝ)*(upper5) + (994694020325489/50000000000000 : ℝ)*(major0) + (994694020325489/50000000000000 : ℝ)*(major1) + (994694020325489/50000000000000 : ℝ)*(major2) + (762866973/6250000000000 : ℝ)*(sp1) + (6623475403/50000000000000 : ℝ)*(sp2) + (2922647800849561/100000000000000 : ℝ)*(sp4) + (730658567787881/25000000000000 : ℝ)*(sp5) + (1461316548710937/50000000000000 : ℝ)*(sp6) + (528063976832727/50000000000000 : ℝ)*(sp7) + (528063976832727/50000000000000 : ℝ)*(f.failure) + (2922647800849561/100000000000000 : ℝ)*(f.sum) + (205442321303867/41405000000000000000000000000 : ℝ)*base66 + (1989685426026475687/2070250000000000000000000000000000 : ℝ)*base67 + (13320046116880225687/2070250000000000000000000000000000 : ℝ)*base69 + (14682018179371274313/2070250000000000000000000000000000 : ℝ)*base72 + (1178626369021/5175625000000000000000000000 : ℝ)*base73 + (5718271305516774313/2070250000000000000000000000000000 : ℝ)*base76 + (326109810529225687/2070250000000000000000000000000000 : ℝ)*base77 + (1545325130209774313/2070250000000000000000000000000000 : ℝ)*base80 + (20456742248619/20702500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (7292753/1000000000000000000000 : ℝ)*base89 + (7292753/1000000000000000000000 : ℝ)*base91 + (7292753/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1690_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3541/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (589/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8629/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1690_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1690_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8629/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1690_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1690_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1690_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8629/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1690_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
