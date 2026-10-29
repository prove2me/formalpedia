-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1535_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:06:11.148427+00:00
-- url     : https://prove2.me/submissions/53eca29d-af22-455d-841d-2bfeaf26fc6e

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
theorem support_rectangle_w1535_s6_0 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1834566827/10000000000 : ℝ)*x 0 + (2715128673/5000000000 : ℝ)*x 1 + (2609357867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1834566827/10000000000 : ℝ)^4567 ≤ (1404719357113/12500000000000 : ℝ)^3543 := by
    have hnat : (1834566827 : ℕ)^4567*12500000000000^3543 ≤ 1404719357113^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834566827 10000000000 1404719357113 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715128673/5000000000 : ℝ)^4567 ≤ (45517462912713/100000000000000 : ℝ)^3543 := by
    have hnat : (2715128673 : ℕ)^4567*100000000000000^3543 ≤ 45517462912713^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715128673 5000000000 45517462912713 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609357867/5000000000 : ℝ)^4567 ≤ (1351399444133/3125000000000 : ℝ)^3543 := by
    have hnat : (2609357867 : ℕ)^4567*3125000000000^3543 ≤ 1351399444133^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609357867 5000000000 1351399444133 3125000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1834566827/10000000000 : ℝ), (2715128673/5000000000 : ℝ), (2609357867/5000000000 : ℝ)] ![(1404719357113/12500000000000 : ℝ), (45517462912713/100000000000000 : ℝ), (1351399444133/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1834566827/10000000000 : ℝ)|^4567 ≤ (1404719357113/12500000000000 : ℝ)^3543
        have hw : |(-1834566827/10000000000 : ℝ)|=(1834566827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715128673/5000000000 : ℝ)|^4567 ≤ (45517462912713/100000000000000 : ℝ)^3543
        have hw : |(2715128673/5000000000 : ℝ)|=(2715128673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609357867/5000000000 : ℝ)|^4567 ≤ (1351399444133/3125000000000 : ℝ)^3543
        have hw : |(2609357867/5000000000 : ℝ)|=(2609357867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s6_1 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350282739/10000000000 : ℝ)*x 0 + (-1942858963/10000000000 : ℝ)*x 1 + (1043743127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350282739/10000000000 : ℝ)^4567 ≤ (1786207892009/4000000000000 : ℝ)^3543 := by
    have hnat : (5350282739 : ℕ)^4567*4000000000000^3543 ≤ 1786207892009^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350282739 10000000000 1786207892009 4000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942858963/10000000000 : ℝ)^4567 ≤ (1512502690287/12500000000000 : ℝ)^3543 := by
    have hnat : (1942858963 : ℕ)^4567*12500000000000^3543 ≤ 1512502690287^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942858963 10000000000 1512502690287 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043743127/2000000000 : ℝ)^4567 ≤ (21622390577397/50000000000000 : ℝ)^3543 := by
    have hnat : (1043743127 : ℕ)^4567*50000000000000^3543 ≤ 21622390577397^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043743127 2000000000 21622390577397 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350282739/10000000000 : ℝ), (-1942858963/10000000000 : ℝ), (1043743127/2000000000 : ℝ)] ![(1786207892009/4000000000000 : ℝ), (1512502690287/12500000000000 : ℝ), (21622390577397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350282739/10000000000 : ℝ)|^4567 ≤ (1786207892009/4000000000000 : ℝ)^3543
        have hw : |(5350282739/10000000000 : ℝ)|=(5350282739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1942858963/10000000000 : ℝ)|^4567 ≤ (1512502690287/12500000000000 : ℝ)^3543
        have hw : |(-1942858963/10000000000 : ℝ)|=(1942858963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043743127/2000000000 : ℝ)|^4567 ≤ (21622390577397/50000000000000 : ℝ)^3543
        have hw : |(1043743127/2000000000 : ℝ)|=(1043743127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s6_2 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350282649/10000000000 : ℝ)*x 0 + (5218715779/10000000000 : ℝ)*x 1 + (-971429447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350282649/10000000000 : ℝ)^4567 ≤ (2790949770747/6250000000000 : ℝ)^3543 := by
    have hnat : (5350282649 : ℕ)^4567*6250000000000^3543 ≤ 2790949770747^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350282649 10000000000 2790949770747 6250000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218715779/10000000000 : ℝ)^4567 ≤ (43244782692921/100000000000000 : ℝ)^3543 := by
    have hnat : (5218715779 : ℕ)^4567*100000000000000^3543 ≤ 43244782692921^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218715779 10000000000 43244782692921 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971429447/5000000000 : ℝ)^4567 ≤ (12100020968367/100000000000000 : ℝ)^3543 := by
    have hnat : (971429447 : ℕ)^4567*100000000000000^3543 ≤ 12100020968367^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971429447 5000000000 12100020968367 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350282649/10000000000 : ℝ), (5218715779/10000000000 : ℝ), (-971429447/5000000000 : ℝ)] ![(2790949770747/6250000000000 : ℝ), (43244782692921/100000000000000 : ℝ), (12100020968367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350282649/10000000000 : ℝ)|^4567 ≤ (2790949770747/6250000000000 : ℝ)^3543
        have hw : |(5350282649/10000000000 : ℝ)|=(5350282649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218715779/10000000000 : ℝ)|^4567 ≤ (43244782692921/100000000000000 : ℝ)^3543
        have hw : |(5218715779/10000000000 : ℝ)|=(5218715779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-971429447/5000000000 : ℝ)|^4567 ≤ (12100020968367/100000000000000 : ℝ)^3543
        have hw : |(-971429447/5000000000 : ℝ)|=(971429447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s6_3 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259179937/10000000000 : ℝ)*x 0 + (2010626749/5000000000 : ℝ)*x 1 + (2254363377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259179937/10000000000 : ℝ)^4567 ≤ (16640392488203/50000000000000 : ℝ)^3543 := by
    have hnat : (4259179937 : ℕ)^4567*50000000000000^3543 ≤ 16640392488203^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259179937 10000000000 16640392488203 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010626749/5000000000 : ℝ)^4567 ≤ (7725983355129/25000000000000 : ℝ)^3543 := by
    have hnat : (2010626749 : ℕ)^4567*25000000000000^3543 ≤ 7725983355129^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010626749 5000000000 7725983355129 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254363377/5000000000 : ℝ)^4567 ≤ (7163056318951/20000000000000 : ℝ)^3543 := by
    have hnat : (2254363377 : ℕ)^4567*20000000000000^3543 ≤ 7163056318951^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254363377 5000000000 7163056318951 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259179937/10000000000 : ℝ), (2010626749/5000000000 : ℝ), (2254363377/5000000000 : ℝ)] ![(16640392488203/50000000000000 : ℝ), (7725983355129/25000000000000 : ℝ), (7163056318951/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259179937/10000000000 : ℝ)|^4567 ≤ (16640392488203/50000000000000 : ℝ)^3543
        have hw : |(4259179937/10000000000 : ℝ)|=(4259179937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010626749/5000000000 : ℝ)|^4567 ≤ (7725983355129/25000000000000 : ℝ)^3543
        have hw : |(2010626749/5000000000 : ℝ)|=(2010626749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254363377/5000000000 : ℝ)|^4567 ≤ (7163056318951/20000000000000 : ℝ)^3543
        have hw : |(2254363377/5000000000 : ℝ)|=(2254363377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s6_4 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-917297479/5000000000 : ℝ)*x 0 + (5219809581/10000000000 : ℝ)*x 1 + (5429155367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (917297479/5000000000 : ℝ)^4567 ≤ (5618988489563/50000000000000 : ℝ)^3543 := by
    have hnat : (917297479 : ℕ)^4567*50000000000000^3543 ≤ 5618988489563^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917297479 5000000000 5618988489563 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219809581/10000000000 : ℝ)^4567 ≤ (43256466430653/100000000000000 : ℝ)^3543 := by
    have hnat : (5219809581 : ℕ)^4567*100000000000000^3543 ≤ 43256466430653^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219809581 10000000000 43256466430653 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429155367/10000000000 : ℝ)^4567 ≤ (45505556578311/100000000000000 : ℝ)^3543 := by
    have hnat : (5429155367 : ℕ)^4567*100000000000000^3543 ≤ 45505556578311^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429155367 10000000000 45505556578311 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-917297479/5000000000 : ℝ), (5219809581/10000000000 : ℝ), (5429155367/10000000000 : ℝ)] ![(5618988489563/50000000000000 : ℝ), (43256466430653/100000000000000 : ℝ), (45505556578311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-917297479/5000000000 : ℝ)|^4567 ≤ (5618988489563/50000000000000 : ℝ)^3543
        have hw : |(-917297479/5000000000 : ℝ)|=(917297479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219809581/10000000000 : ℝ)|^4567 ≤ (43256466430653/100000000000000 : ℝ)^3543
        have hw : |(5219809581/10000000000 : ℝ)|=(5219809581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429155367/10000000000 : ℝ)|^4567 ≤ (45505556578311/100000000000000 : ℝ)^3543
        have hw : |(5429155367/10000000000 : ℝ)|=(5429155367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s6_5 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294565743/10000000000 : ℝ)*x 0 + (-866209647/5000000000 : ℝ)*x 1 + (542915537/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294565743/10000000000 : ℝ)^4567 ≤ (44056665618019/100000000000000 : ℝ)^3543 := by
    have hnat : (5294565743 : ℕ)^4567*100000000000000^3543 ≤ 44056665618019^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294565743 10000000000 44056665618019 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (866209647/5000000000 : ℝ)^4567 ≤ (2609444438717/25000000000000 : ℝ)^3543 := by
    have hnat : (866209647 : ℕ)^4567*25000000000000^3543 ≤ 2609444438717^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866209647 5000000000 2609444438717 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542915537/1000000000 : ℝ)^4567 ≤ (45505556610723/100000000000000 : ℝ)^3543 := by
    have hnat : (542915537 : ℕ)^4567*100000000000000^3543 ≤ 45505556610723^3543*1000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542915537 1000000000 45505556610723 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294565743/10000000000 : ℝ), (-866209647/5000000000 : ℝ), (542915537/1000000000 : ℝ)] ![(44056665618019/100000000000000 : ℝ), (2609444438717/25000000000000 : ℝ), (45505556610723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294565743/10000000000 : ℝ)|^4567 ≤ (44056665618019/100000000000000 : ℝ)^3543
        have hw : |(5294565743/10000000000 : ℝ)|=(5294565743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-866209647/5000000000 : ℝ)|^4567 ≤ (2609444438717/25000000000000 : ℝ)^3543
        have hw : |(-866209647/5000000000 : ℝ)|=(866209647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542915537/1000000000 : ℝ)|^4567 ≤ (45505556610723/100000000000000 : ℝ)^3543
        have hw : |(542915537/1000000000 : ℝ)|=(542915537/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s6_6 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294565757/10000000000 : ℝ)*x 0 + (542915537/1000000000 : ℝ)*x 1 + (-69296771/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294565757/10000000000 : ℝ)^4567 ≤ (8811333153637/20000000000000 : ℝ)^3543 := by
    have hnat : (5294565757 : ℕ)^4567*20000000000000^3543 ≤ 8811333153637^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294565757 10000000000 8811333153637 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542915537/1000000000 : ℝ)^4567 ≤ (45505556610723/100000000000000 : ℝ)^3543 := by
    have hnat : (542915537 : ℕ)^4567*100000000000000^3543 ≤ 45505556610723^3543*1000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542915537 1000000000 45505556610723 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69296771/400000000 : ℝ)^4567 ≤ (2609444401827/25000000000000 : ℝ)^3543 := by
    have hnat : (69296771 : ℕ)^4567*25000000000000^3543 ≤ 2609444401827^3543*400000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69296771 400000000 2609444401827 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294565757/10000000000 : ℝ), (542915537/1000000000 : ℝ), (-69296771/400000000 : ℝ)] ![(8811333153637/20000000000000 : ℝ), (45505556610723/100000000000000 : ℝ), (2609444401827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294565757/10000000000 : ℝ)|^4567 ≤ (8811333153637/20000000000000 : ℝ)^3543
        have hw : |(5294565757/10000000000 : ℝ)|=(5294565757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542915537/1000000000 : ℝ)|^4567 ≤ (45505556610723/100000000000000 : ℝ)^3543
        have hw : |(542915537/1000000000 : ℝ)|=(542915537/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69296771/400000000 : ℝ)|^4567 ≤ (2609444401827/25000000000000 : ℝ)^3543
        have hw : |(-69296771/400000000 : ℝ)|=(69296771/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s6_7 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1064811207/2500000000 : ℝ)*x 0 + (4506205699/10000000000 : ℝ)*x 1 + (4023792897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064811207/2500000000 : ℝ)^4567 ≤ (8320359644407/25000000000000 : ℝ)^3543 := by
    have hnat : (1064811207 : ℕ)^4567*25000000000000^3543 ≤ 8320359644407^3543*2500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064811207 2500000000 8320359644407 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506205699/10000000000 : ℝ)^4567 ≤ (7157893920391/20000000000000 : ℝ)^3543 := by
    have hnat : (4506205699 : ℕ)^4567*20000000000000^3543 ≤ 7157893920391^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506205699 10000000000 7157893920391 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4023792897/10000000000 : ℝ)^4567 ≤ (30929091804201/100000000000000 : ℝ)^3543 := by
    have hnat : (4023792897 : ℕ)^4567*100000000000000^3543 ≤ 30929091804201^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023792897 10000000000 30929091804201 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064811207/2500000000 : ℝ), (4506205699/10000000000 : ℝ), (4023792897/10000000000 : ℝ)] ![(8320359644407/25000000000000 : ℝ), (7157893920391/20000000000000 : ℝ), (30929091804201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064811207/2500000000 : ℝ)|^4567 ≤ (8320359644407/25000000000000 : ℝ)^3543
        have hw : |(1064811207/2500000000 : ℝ)|=(1064811207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506205699/10000000000 : ℝ)|^4567 ≤ (7157893920391/20000000000000 : ℝ)^3543
        have hw : |(4506205699/10000000000 : ℝ)|=(4506205699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4023792897/10000000000 : ℝ)|^4567 ≤ (30929091804201/100000000000000 : ℝ)^3543
        have hw : |(4023792897/10000000000 : ℝ)|=(4023792897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1535_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5501/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11001/100000 : ℝ) ^ (4565/1024 : ℝ) ≤ (5329630507757053/100000000000000000000 : ℝ) := by
    have hpowers : (11001/100000 : ℝ)^4565 ≤ (5329630507757053/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11001 : ℕ)^4565*100000000000000000000^1024 ≤ 5329630507757053^1024*100000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11001 100000 5329630507757053 100000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11001/100000 : ℝ)) (X := (5329630507757053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4565/1024 : ℝ) ≤ (978763657817573/4000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4565 ≤ (978763657817573/4000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4565*4000000000000000000^1024 ≤ 978763657817573^1024*20000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 978763657817573 4000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (978763657817573/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005329630507757053/50000000000000000000 : ℝ) ≤ (2500059773450529/2500000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (50005329630507757053/50000000000000000000 : ℝ)^1024 ≤ (2500059773450529/2500000000000000 : ℝ)^4565 := by
      have hnat : (50005329630507757053 : ℕ)^1024*2500000000000000^4565 ≤ 2500059773450529^4565*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005329630507757053 50000000000000000000 2500059773450529 2500000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500059773450529/2500000000000000 : ℝ)) (X := (50005329630507757053/50000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014899360976598189/50000000000000000000 : ℝ) ≤ (10000668354114989/10000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (50014899360976598189/50000000000000000000 : ℝ)^1024 ≤ (10000668354114989/10000000000000000 : ℝ)^4565 := by
      have hnat : (50014899360976598189 : ℕ)^1024*10000000000000000^4565 ≤ 10000668354114989^4565*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014899360976598189 50000000000000000000 10000668354114989 10000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000668354114989/10000000000000000 : ℝ)) (X := (50014899360976598189/50000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000978763657817573/2000000000000000000 : ℝ) ≤ (5000548807213931/5000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (2000978763657817573/2000000000000000000 : ℝ)^1024 ≤ (5000548807213931/5000000000000000 : ℝ)^4565 := by
      have hnat : (2000978763657817573 : ℕ)^1024*5000000000000000^4565 ≤ 5000548807213931^4565*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000978763657817573 2000000000000000000 5000548807213931 5000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000548807213931/5000000000000000 : ℝ)) (X := (2000978763657817573/2000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5329630507757053/100000000000000000000 : ℝ) ≤ ((1179779671347496221/1180000000000000000 : ℝ)+2*(429260312873/448400000000000 : ℝ)*(11001/100000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (1179779671347496221/1180000000000000000 : ℝ)+2*(429260312873/448400000000000 : ℝ)*(11001/100000 : ℝ)=(2500059773450529/2500000000000000 : ℝ) by norm_num, show 1+2*(5329630507757053/100000000000000000000 : ℝ)=(50005329630507757053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(978763657817573/4000000000000000000 : ℝ)+(5329630507757053/100000000000000000000 : ℝ) ≤ ((1179779671347496221/1180000000000000000 : ℝ)+(429260312873/448400000000000 : ℝ)*((3097/20000 : ℝ)+(11001/100000 : ℝ)))^(4565/1024 : ℝ) := by
    rw [show (1179779671347496221/1180000000000000000 : ℝ)+(429260312873/448400000000000 : ℝ)*((3097/20000 : ℝ)+(11001/100000 : ℝ))=(10000668354114989/10000000000000000 : ℝ) by norm_num, show 1+(978763657817573/4000000000000000000 : ℝ)+(5329630507757053/100000000000000000000 : ℝ)=(50014899360976598189/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(978763657817573/4000000000000000000 : ℝ) ≤ ((1179779671347496221/1180000000000000000 : ℝ)+2*(429260312873/448400000000000 : ℝ)*(3097/20000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (1179779671347496221/1180000000000000000 : ℝ)+2*(429260312873/448400000000000 : ℝ)*(3097/20000 : ℝ)=(5000548807213931/5000000000000000 : ℝ) by norm_num, show 1+2*(978763657817573/4000000000000000000 : ℝ)=(2000978763657817573/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1179779671347496221/1180000000000000000 : ℝ)*(X 1 0+X 2 0)+(429260312873/448400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (11001/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (1179779671347496221/1180000000000000000 : ℝ)) (alpha := (429260312873/448400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1179779671347496221/1180000000000000000 : ℝ)*(X 0 1+X 2 1)+(429260312873/448400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (11001/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (1179779671347496221/1180000000000000000 : ℝ)) (alpha := (429260312873/448400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1179779671347496221/1180000000000000000 : ℝ)*(X 0 2+X 1 2)+(429260312873/448400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (11001/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (1179779671347496221/1180000000000000000 : ℝ)) (alpha := (429260312873/448400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1834566827/10000000000 : ℝ)*X 0 0+(2715128673/5000000000 : ℝ)*X 0 1+(2609357867/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350282739/10000000000 : ℝ)*X 1 0+(-1942858963/10000000000 : ℝ)*X 1 1+(1043743127/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350282649/10000000000 : ℝ)*X 2 0+(5218715779/10000000000 : ℝ)*X 2 1+(-971429447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4259179937/10000000000 : ℝ)*X 0 0+(2010626749/5000000000 : ℝ)*X 0 1+(2254363377/5000000000 : ℝ)*X 0 2+(4259179937/10000000000 : ℝ)*X 1 0+(2010626749/5000000000 : ℝ)*X 1 1+(2254363377/5000000000 : ℝ)*X 1 2+(4259179937/10000000000 : ℝ)*X 2 0+(2010626749/5000000000 : ℝ)*X 2 1+(2254363377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-917297479/5000000000 : ℝ)*X 0 0+(5219809581/10000000000 : ℝ)*X 0 1+(5429155367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294565743/10000000000 : ℝ)*X 1 0+(-866209647/5000000000 : ℝ)*X 1 1+(542915537/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294565757/10000000000 : ℝ)*X 2 0+(542915537/1000000000 : ℝ)*X 2 1+(-69296771/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1064811207/2500000000 : ℝ)*X 0 0+(4506205699/10000000000 : ℝ)*X 0 1+(4023792897/10000000000 : ℝ)*X 0 2+(1064811207/2500000000 : ℝ)*X 1 0+(4506205699/10000000000 : ℝ)*X 1 1+(4023792897/10000000000 : ℝ)*X 1 2+(1064811207/2500000000 : ℝ)*X 2 0+(4506205699/10000000000 : ℝ)*X 2 1+(4023792897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1266158709634216404189249651/280250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (886757287/100000000000000 : ℝ)*(base19) + (783912659/100000000000000 : ℝ)*(base23) + (6239859/50000000000000 : ℝ)*(lower2) + (35233757/50000000000000 : ℝ)*(upper3) + (109405789/100000000000000 : ℝ)*(upper5) + (1694659474257617/50000000000000 : ℝ)*(major0) + (1694659474257617/50000000000000 : ℝ)*(major1) + (1694659474257617/50000000000000 : ℝ)*(major2) + (147725493783971/3125000000000 : ℝ)*(sp0) + (472722948937799/10000000000000 : ℝ)*(sp1) + (2363614796111309/50000000000000 : ℝ)*(sp2) + (1025700608928997/50000000000000 : ℝ)*(sp3) + (2915009641/20000000000000 : ℝ)*(sp4) + (1538109619/25000000000000 : ℝ)*(sp7) + (205140737029647/10000000000000 : ℝ)*(f.failure) + (4727230376135277/100000000000000 : ℝ)*(f.sum) + (4860405021521/11210000000000000000000000000 : ℝ)*base65 + (110825982104074437/19000000000000000000000000000000 : ℝ)*base67 + (60815839322074437/19000000000000000000000000000000 : ℝ)*base69 + (95541197207074437/19000000000000000000000000000000 : ℝ)*base71 + (2057279570781/11210000000000000000000000000 : ℝ)*base73 + (118316475450925563/19000000000000000000000000000000 : ℝ)*base76 + (196483628239074437/19000000000000000000000000000000 : ℝ)*base77 + (96997660409074437/19000000000000000000000000000000 : ℝ)*base79 + (19221526623119/11210000000000000000000000000 : ℝ)*base82 + (245873/200000000000000000000 : ℝ)*base90 + (245873/200000000000000000000 : ℝ)*base92 + (245873/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5024635894912128660382490547/1121000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119806351/12500000000000 : ℝ)*(base19) + (50994673/5000000000000 : ℝ)*(base23) + (65878603/20000000000000 : ℝ)*(lower1) + (110062763/100000000000000 : ℝ)*(upper3) + (2586233/10000000000000 : ℝ)*(lower4) + (163426219/100000000000000 : ℝ)*(upper5) + (3424838740298649/100000000000000 : ℝ)*(major0) + (3424838740298649/100000000000000 : ℝ)*(major1) + (3424838740298649/100000000000000 : ℝ)*(major2) + (667423/20000000000000 : ℝ)*(sp1) + (955354275110489/20000000000000 : ℝ)*(sp4) + (2388385206882261/50000000000000 : ℝ)*(sp5) + (2388385177829493/50000000000000 : ℝ)*(sp6) + (1036452977817757/50000000000000 : ℝ)*(sp7) + (1036452977817757/50000000000000 : ℝ)*(f.failure) + (955354275110489/20000000000000 : ℝ)*(f.sum) + (56016225693863/22420000000000000000000000000 : ℝ)*base66 + (12338473528238189/38000000000000000000000000000000 : ℝ)*base67 + (415127204932238189/38000000000000000000000000000000 : ℝ)*base69 + (43315550967761811/38000000000000000000000000000000 : ℝ)*base72 + (35473806328083/22420000000000000000000000000 : ℝ)*base74 + (362065758632238189/38000000000000000000000000000000 : ℝ)*base75 + (115812695334238189/38000000000000000000000000000000 : ℝ)*base77 + (69425338921761811/38000000000000000000000000000000 : ℝ)*base80 + (174500088108783/22420000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (715363/1000000000000000000000 : ℝ)*base90 + (715363/1000000000000000000000 : ℝ)*base92 + (715363/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1535_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1535_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1535_box_0 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1624965527/10000000000 : ℝ)*x 0 + (1350087521/2500000000 : ℝ)*x 1 + (5400349439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1624965527/10000000000 : ℝ)^4567 ≤ (961085117457/10000000000000 : ℝ)^3543 := by
    have hnat : (1624965527 : ℕ)^4567*10000000000000^3543 ≤ 961085117457^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624965527 10000000000 961085117457 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350087521/2500000000 : ℝ)^4567 ≤ (22597288942387/50000000000000 : ℝ)^3543 := by
    have hnat : (1350087521 : ℕ)^4567*50000000000000^3543 ≤ 22597288942387^3543*2500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350087521 2500000000 22597288942387 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400349439/10000000000 : ℝ)^4567 ≤ (45194570926781/100000000000000 : ℝ)^3543 := by
    have hnat : (5400349439 : ℕ)^4567*100000000000000^3543 ≤ 45194570926781^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400349439 10000000000 45194570926781 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1624965527/10000000000 : ℝ), (1350087521/2500000000 : ℝ), (5400349439/10000000000 : ℝ)] ![(961085117457/10000000000000 : ℝ), (22597288942387/50000000000000 : ℝ), (45194570926781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1624965527/10000000000 : ℝ)|^4567 ≤ (961085117457/10000000000000 : ℝ)^3543
        have hw : |(-1624965527/10000000000 : ℝ)|=(1624965527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350087521/2500000000 : ℝ)|^4567 ≤ (22597288942387/50000000000000 : ℝ)^3543
        have hw : |(1350087521/2500000000 : ℝ)|=(1350087521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400349439/10000000000 : ℝ)|^4567 ≤ (45194570926781/100000000000000 : ℝ)^3543
        have hw : |(5400349439/10000000000 : ℝ)|=(5400349439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_1 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527101109/1000000000 : ℝ)*x 0 + (-902270649/5000000000 : ℝ)*x 1 + (2700175327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527101109/1000000000 : ℝ)^4567 ≤ (2190208953183/5000000000000 : ℝ)^3543 := by
    have hnat : (527101109 : ℕ)^4567*5000000000000^3543 ≤ 2190208953183^3543*1000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527101109 1000000000 2190208953183 5000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902270649/5000000000 : ℝ)^4567 ≤ (2750309221941/25000000000000 : ℝ)^3543 := by
    have hnat : (902270649 : ℕ)^4567*25000000000000^3543 ≤ 2750309221941^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902270649 5000000000 2750309221941 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700175327/5000000000 : ℝ)^4567 ≤ (22597292016849/50000000000000 : ℝ)^3543 := by
    have hnat : (2700175327 : ℕ)^4567*50000000000000^3543 ≤ 22597292016849^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700175327 5000000000 22597292016849 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527101109/1000000000 : ℝ), (-902270649/5000000000 : ℝ), (2700175327/5000000000 : ℝ)] ![(2190208953183/5000000000000 : ℝ), (2750309221941/25000000000000 : ℝ), (22597292016849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527101109/1000000000 : ℝ)|^4567 ≤ (2190208953183/5000000000000 : ℝ)^3543
        have hw : |(527101109/1000000000 : ℝ)|=(527101109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-902270649/5000000000 : ℝ)|^4567 ≤ (2750309221941/25000000000000 : ℝ)^3543
        have hw : |(-902270649/5000000000 : ℝ)|=(902270649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700175327/5000000000 : ℝ)|^4567 ≤ (22597292016849/50000000000000 : ℝ)^3543
        have hw : |(2700175327/5000000000 : ℝ)|=(2700175327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_2 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271011503/10000000000 : ℝ)*x 0 + (540035017/1000000000 : ℝ)*x 1 + (-1804541399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271011503/10000000000 : ℝ)^4567 ≤ (43804183487827/100000000000000 : ℝ)^3543 := by
    have hnat : (5271011503 : ℕ)^4567*100000000000000^3543 ≤ 43804183487827^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271011503 10000000000 43804183487827 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540035017/1000000000 : ℝ)^4567 ≤ (22597289406253/50000000000000 : ℝ)^3543 := by
    have hnat : (540035017 : ℕ)^4567*50000000000000^3543 ≤ 22597289406253^3543*1000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540035017 1000000000 22597289406253 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1804541399/10000000000 : ℝ)^4567 ≤ (11001237681463/100000000000000 : ℝ)^3543 := by
    have hnat : (1804541399 : ℕ)^4567*100000000000000^3543 ≤ 11001237681463^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804541399 10000000000 11001237681463 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271011503/10000000000 : ℝ), (540035017/1000000000 : ℝ), (-1804541399/10000000000 : ℝ)] ![(43804183487827/100000000000000 : ℝ), (22597289406253/50000000000000 : ℝ), (11001237681463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271011503/10000000000 : ℝ)|^4567 ≤ (43804183487827/100000000000000 : ℝ)^3543
        have hw : |(5271011503/10000000000 : ℝ)|=(5271011503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540035017/1000000000 : ℝ)|^4567 ≤ (22597289406253/50000000000000 : ℝ)^3543
        have hw : |(540035017/1000000000 : ℝ)|=(540035017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1804541399/10000000000 : ℝ)|^4567 ≤ (11001237681463/100000000000000 : ℝ)^3543
        have hw : |(-1804541399/10000000000 : ℝ)|=(1804541399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_3 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2230620157/5000000000 : ℝ)*x 0 + (2082493891/5000000000 : ℝ)*x 1 + (832997573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2230620157/5000000000 : ℝ)^4567 ≤ (8832447765317/25000000000000 : ℝ)^3543 := by
    have hnat : (2230620157 : ℕ)^4567*25000000000000^3543 ≤ 8832447765317^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230620157 5000000000 8832447765317 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082493891/5000000000 : ℝ)^4567 ≤ (1616755202299/5000000000000 : ℝ)^3543 := by
    have hnat : (2082493891 : ℕ)^4567*5000000000000^3543 ≤ 1616755202299^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082493891 5000000000 1616755202299 5000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832997573/2000000000 : ℝ)^4567 ≤ (2020944054787/6250000000000 : ℝ)^3543 := by
    have hnat : (832997573 : ℕ)^4567*6250000000000^3543 ≤ 2020944054787^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832997573 2000000000 2020944054787 6250000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2230620157/5000000000 : ℝ), (2082493891/5000000000 : ℝ), (832997573/2000000000 : ℝ)] ![(8832447765317/25000000000000 : ℝ), (1616755202299/5000000000000 : ℝ), (2020944054787/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2230620157/5000000000 : ℝ)|^4567 ≤ (8832447765317/25000000000000 : ℝ)^3543
        have hw : |(2230620157/5000000000 : ℝ)|=(2230620157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2082493891/5000000000 : ℝ)|^4567 ≤ (1616755202299/5000000000000 : ℝ)^3543
        have hw : |(2082493891/5000000000 : ℝ)|=(2082493891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832997573/2000000000 : ℝ)|^4567 ≤ (2020944054787/6250000000000 : ℝ)^3543
        have hw : |(832997573/2000000000 : ℝ)|=(832997573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_4 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049589191/10000000000 : ℝ)*x 0 + (5244296543/10000000000 : ℝ)*x 1 + (5244297191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049589191/10000000000 : ℝ)^4567 ≤ (810222628927/6250000000000 : ℝ)^3543 := by
    have hnat : (2049589191 : ℕ)^4567*6250000000000^3543 ≤ 810222628927^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049589191 10000000000 810222628927 6250000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244296543/10000000000 : ℝ)^4567 ≤ (21759107747233/50000000000000 : ℝ)^3543 := by
    have hnat : (5244296543 : ℕ)^4567*50000000000000^3543 ≤ 21759107747233^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244296543 10000000000 21759107747233 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244297191/10000000000 : ℝ)^4567 ≤ (43518222425831/100000000000000 : ℝ)^3543 := by
    have hnat : (5244297191 : ℕ)^4567*100000000000000^3543 ≤ 43518222425831^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244297191 10000000000 43518222425831 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049589191/10000000000 : ℝ), (5244296543/10000000000 : ℝ), (5244297191/10000000000 : ℝ)] ![(810222628927/6250000000000 : ℝ), (21759107747233/50000000000000 : ℝ), (43518222425831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049589191/10000000000 : ℝ)|^4567 ≤ (810222628927/6250000000000 : ℝ)^3543
        have hw : |(-2049589191/10000000000 : ℝ)|=(2049589191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244296543/10000000000 : ℝ)|^4567 ≤ (21759107747233/50000000000000 : ℝ)^3543
        have hw : |(5244296543/10000000000 : ℝ)|=(5244296543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244297191/10000000000 : ℝ)|^4567 ≤ (43518222425831/100000000000000 : ℝ)^3543
        have hw : |(5244297191/10000000000 : ℝ)|=(5244297191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_5 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379468757/10000000000 : ℝ)*x 0 + (-373849451/2000000000 : ℝ)*x 1 + (5244296943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379468757/10000000000 : ℝ)^4567 ≤ (5621180594219/12500000000000 : ℝ)^3543 := by
    have hnat : (5379468757 : ℕ)^4567*12500000000000^3543 ≤ 5621180594219^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379468757 10000000000 5621180594219 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (373849451/2000000000 : ℝ)^4567 ≤ (2302467092389/20000000000000 : ℝ)^3543 := by
    have hnat : (373849451 : ℕ)^4567*20000000000000^3543 ≤ 2302467092389^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373849451 2000000000 2302467092389 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244296943/10000000000 : ℝ)^4567 ≤ (21759109886543/50000000000000 : ℝ)^3543 := by
    have hnat : (5244296943 : ℕ)^4567*50000000000000^3543 ≤ 21759109886543^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244296943 10000000000 21759109886543 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379468757/10000000000 : ℝ), (-373849451/2000000000 : ℝ), (5244296943/10000000000 : ℝ)] ![(5621180594219/12500000000000 : ℝ), (2302467092389/20000000000000 : ℝ), (21759109886543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379468757/10000000000 : ℝ)|^4567 ≤ (5621180594219/12500000000000 : ℝ)^3543
        have hw : |(5379468757/10000000000 : ℝ)|=(5379468757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-373849451/2000000000 : ℝ)|^4567 ≤ (2302467092389/20000000000000 : ℝ)^3543
        have hw : |(-373849451/2000000000 : ℝ)|=(373849451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244296943/10000000000 : ℝ)|^4567 ≤ (21759109886543/50000000000000 : ℝ)^3543
        have hw : |(5244296943/10000000000 : ℝ)|=(5244296943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_6 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336216777/625000000 : ℝ)*x 0 + (5244296701/10000000000 : ℝ)*x 1 + (-1869248021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336216777/625000000 : ℝ)^4567 ≤ (4496944125171/10000000000000 : ℝ)^3543 := by
    have hnat : (336216777 : ℕ)^4567*10000000000000^3543 ≤ 4496944125171^3543*625000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336216777 625000000 4496944125171 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244296701/10000000000 : ℝ)^4567 ≤ (43518217184521/100000000000000 : ℝ)^3543 := by
    have hnat : (5244296701 : ℕ)^4567*100000000000000^3543 ≤ 43518217184521^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244296701 10000000000 43518217184521 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1869248021/10000000000 : ℝ)^4567 ≤ (1151234154309/10000000000000 : ℝ)^3543 := by
    have hnat : (1869248021 : ℕ)^4567*10000000000000^3543 ≤ 1151234154309^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869248021 10000000000 1151234154309 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336216777/625000000 : ℝ), (5244296701/10000000000 : ℝ), (-1869248021/10000000000 : ℝ)] ![(4496944125171/10000000000000 : ℝ), (43518217184521/100000000000000 : ℝ), (1151234154309/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336216777/625000000 : ℝ)|^4567 ≤ (4496944125171/10000000000000 : ℝ)^3543
        have hw : |(336216777/625000000 : ℝ)|=(336216777/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244296701/10000000000 : ℝ)|^4567 ≤ (43518217184521/100000000000000 : ℝ)^3543
        have hw : |(5244296701/10000000000 : ℝ)|=(5244296701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1869248021/10000000000 : ℝ)|^4567 ≤ (1151234154309/10000000000000 : ℝ)^3543
        have hw : |(-1869248021/10000000000 : ℝ)|=(1869248021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_7 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4054591231/10000000000 : ℝ)*x 0 + (4368181407/10000000000 : ℝ)*x 1 + (4368180497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4054591231/10000000000 : ℝ)^4567 ≤ (31234582415433/100000000000000 : ℝ)^3543 := by
    have hnat : (4054591231 : ℕ)^4567*100000000000000^3543 ≤ 31234582415433^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4054591231 10000000000 31234582415433 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4368181407/10000000000 : ℝ)^4567 ≤ (17191356700619/50000000000000 : ℝ)^3543 := by
    have hnat : (4368181407 : ℕ)^4567*50000000000000^3543 ≤ 17191356700619^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368181407 10000000000 17191356700619 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4368180497/10000000000 : ℝ)^4567 ≤ (34382704168283/100000000000000 : ℝ)^3543 := by
    have hnat : (4368180497 : ℕ)^4567*100000000000000^3543 ≤ 34382704168283^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368180497 10000000000 34382704168283 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4054591231/10000000000 : ℝ), (4368181407/10000000000 : ℝ), (4368180497/10000000000 : ℝ)] ![(31234582415433/100000000000000 : ℝ), (17191356700619/50000000000000 : ℝ), (34382704168283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4054591231/10000000000 : ℝ)|^4567 ≤ (31234582415433/100000000000000 : ℝ)^3543
        have hw : |(4054591231/10000000000 : ℝ)|=(4054591231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4368181407/10000000000 : ℝ)|^4567 ≤ (17191356700619/50000000000000 : ℝ)^3543
        have hw : |(4368181407/10000000000 : ℝ)|=(4368181407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4368180497/10000000000 : ℝ)|^4567 ≤ (34382704168283/100000000000000 : ℝ)^3543
        have hw : |(4368180497/10000000000 : ℝ)|=(4368180497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_8 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1959740657/10000000000 : ℝ)*x 0 + (320920153/625000000 : ℝ)*x 1 + (2710366299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1959740657/10000000000 : ℝ)^4567 ≤ (3058929191033/25000000000000 : ℝ)^3543 := by
    have hnat : (1959740657 : ℕ)^4567*25000000000000^3543 ≤ 3058929191033^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959740657 10000000000 3058929191033 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320920153/625000000 : ℝ)^4567 ≤ (42349707391911/100000000000000 : ℝ)^3543 := by
    have hnat : (320920153 : ℕ)^4567*100000000000000^3543 ≤ 42349707391911^3543*625000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320920153 625000000 42349707391911 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710366299/5000000000 : ℝ)^4567 ≤ (5676821978937/12500000000000 : ℝ)^3543 := by
    have hnat : (2710366299 : ℕ)^4567*12500000000000^3543 ≤ 5676821978937^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710366299 5000000000 5676821978937 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1959740657/10000000000 : ℝ), (320920153/625000000 : ℝ), (2710366299/5000000000 : ℝ)] ![(3058929191033/25000000000000 : ℝ), (42349707391911/100000000000000 : ℝ), (5676821978937/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1959740657/10000000000 : ℝ)|^4567 ≤ (3058929191033/25000000000000 : ℝ)^3543
        have hw : |(-1959740657/10000000000 : ℝ)|=(1959740657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(320920153/625000000 : ℝ)|^4567 ≤ (42349707391911/100000000000000 : ℝ)^3543
        have hw : |(320920153/625000000 : ℝ)|=(320920153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710366299/5000000000 : ℝ)|^4567 ≤ (5676821978937/12500000000000 : ℝ)^3543
        have hw : |(2710366299/5000000000 : ℝ)|=(2710366299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_9 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628420533/5000000000 : ℝ)*x 0 + (-1795849203/10000000000 : ℝ)*x 1 + (2710366333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628420533/5000000000 : ℝ)^4567 ≤ (21826222480097/50000000000000 : ℝ)^3543 := by
    have hnat : (2628420533 : ℕ)^4567*50000000000000^3543 ≤ 21826222480097^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628420533 5000000000 21826222480097 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1795849203/10000000000 : ℝ)^4567 ≤ (1366622307883/12500000000000 : ℝ)^3543 := by
    have hnat : (1795849203 : ℕ)^4567*12500000000000^3543 ≤ 1366622307883^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795849203 10000000000 1366622307883 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710366333/5000000000 : ℝ)^4567 ≤ (45414576565851/100000000000000 : ℝ)^3543 := by
    have hnat : (2710366333 : ℕ)^4567*100000000000000^3543 ≤ 45414576565851^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710366333 5000000000 45414576565851 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628420533/5000000000 : ℝ), (-1795849203/10000000000 : ℝ), (2710366333/5000000000 : ℝ)] ![(21826222480097/50000000000000 : ℝ), (1366622307883/12500000000000 : ℝ), (45414576565851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628420533/5000000000 : ℝ)|^4567 ≤ (21826222480097/50000000000000 : ℝ)^3543
        have hw : |(2628420533/5000000000 : ℝ)|=(2628420533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1795849203/10000000000 : ℝ)|^4567 ≤ (1366622307883/12500000000000 : ℝ)^3543
        have hw : |(-1795849203/10000000000 : ℝ)|=(1795849203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710366333/5000000000 : ℝ)|^4567 ≤ (45414576565851/100000000000000 : ℝ)^3543
        have hw : |(2710366333/5000000000 : ℝ)|=(2710366333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_10 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256841259/10000000000 : ℝ)*x 0 + (5420732539/10000000000 : ℝ)*x 1 + (-897924557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256841259/10000000000 : ℝ)^4567 ≤ (21826223513027/50000000000000 : ℝ)^3543 := by
    have hnat : (5256841259 : ℕ)^4567*50000000000000^3543 ≤ 21826223513027^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256841259 10000000000 21826223513027 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420732539/10000000000 : ℝ)^4567 ≤ (9082915038867/20000000000000 : ℝ)^3543 := by
    have hnat : (5420732539 : ℕ)^4567*20000000000000^3543 ≤ 9082915038867^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420732539 10000000000 9082915038867 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897924557/5000000000 : ℝ)^4567 ≤ (10932977764641/100000000000000 : ℝ)^3543 := by
    have hnat : (897924557 : ℕ)^4567*100000000000000^3543 ≤ 10932977764641^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897924557 5000000000 10932977764641 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256841259/10000000000 : ℝ), (5420732539/10000000000 : ℝ), (-897924557/5000000000 : ℝ)] ![(21826223513027/50000000000000 : ℝ), (9082915038867/20000000000000 : ℝ), (10932977764641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256841259/10000000000 : ℝ)|^4567 ≤ (21826223513027/50000000000000 : ℝ)^3543
        have hw : |(5256841259/10000000000 : ℝ)|=(5256841259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420732539/10000000000 : ℝ)|^4567 ≤ (9082915038867/20000000000000 : ℝ)^3543
        have hw : |(5420732539/10000000000 : ℝ)|=(5420732539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-897924557/5000000000 : ℝ)|^4567 ≤ (10932977764641/100000000000000 : ℝ)^3543
        have hw : |(-897924557/5000000000 : ℝ)|=(897924557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_11 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2256602631/5000000000 : ℝ)*x 0 + (1034603803/2500000000 : ℝ)*x 1 + (2069207557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2256602631/5000000000 : ℝ)^4567 ≤ (1434445815591/4000000000000 : ℝ)^3543 := by
    have hnat : (2256602631 : ℕ)^4567*4000000000000^3543 ≤ 1434445815591^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256602631 5000000000 1434445815591 4000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034603803/2500000000 : ℝ)^4567 ≤ (4008678473203/12500000000000 : ℝ)^3543 := by
    have hnat : (1034603803 : ℕ)^4567*12500000000000^3543 ≤ 4008678473203^3543*2500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034603803 2500000000 4008678473203 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069207557/5000000000 : ℝ)^4567 ≤ (16034713403357/50000000000000 : ℝ)^3543 := by
    have hnat : (2069207557 : ℕ)^4567*50000000000000^3543 ≤ 16034713403357^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069207557 5000000000 16034713403357 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2256602631/5000000000 : ℝ), (1034603803/2500000000 : ℝ), (2069207557/5000000000 : ℝ)] ![(1434445815591/4000000000000 : ℝ), (4008678473203/12500000000000 : ℝ), (16034713403357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2256602631/5000000000 : ℝ)|^4567 ≤ (1434445815591/4000000000000 : ℝ)^3543
        have hw : |(2256602631/5000000000 : ℝ)|=(2256602631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034603803/2500000000 : ℝ)|^4567 ≤ (4008678473203/12500000000000 : ℝ)^3543
        have hw : |(1034603803/2500000000 : ℝ)|=(1034603803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2069207557/5000000000 : ℝ)|^4567 ≤ (16034713403357/50000000000000 : ℝ)^3543
        have hw : |(2069207557/5000000000 : ℝ)|=(2069207557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_12 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-342928571/2000000000 : ℝ)*x 0 + (2753238791/5000000000 : ℝ)*x 1 + (5229256037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342928571/2000000000 : ℝ)^4567 ≤ (2574981394953/25000000000000 : ℝ)^3543 := by
    have hnat : (342928571 : ℕ)^4567*25000000000000^3543 ≤ 2574981394953^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342928571 2000000000 2574981394953 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2753238791/5000000000 : ℝ)^4567 ≤ (1158566842543/2500000000000 : ℝ)^3543 := by
    have hnat : (2753238791 : ℕ)^4567*2500000000000^3543 ≤ 1158566842543^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753238791 5000000000 1158566842543 2500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229256037/10000000000 : ℝ)^4567 ≤ (5419675087977/12500000000000 : ℝ)^3543 := by
    have hnat : (5229256037 : ℕ)^4567*12500000000000^3543 ≤ 5419675087977^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229256037 10000000000 5419675087977 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-342928571/2000000000 : ℝ), (2753238791/5000000000 : ℝ), (5229256037/10000000000 : ℝ)] ![(2574981394953/25000000000000 : ℝ), (1158566842543/2500000000000 : ℝ), (5419675087977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-342928571/2000000000 : ℝ)|^4567 ≤ (2574981394953/25000000000000 : ℝ)^3543
        have hw : |(-342928571/2000000000 : ℝ)|=(342928571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2753238791/5000000000 : ℝ)|^4567 ≤ (1158566842543/2500000000000 : ℝ)^3543
        have hw : |(2753238791/5000000000 : ℝ)|=(2753238791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229256037/10000000000 : ℝ)|^4567 ≤ (5419675087977/12500000000000 : ℝ)^3543
        have hw : |(5229256037/10000000000 : ℝ)|=(5229256037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_13 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347480593/2500000000 : ℝ)*x 0 + (-117206833/625000000 : ℝ)*x 1 + (522925567/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347480593/2500000000 : ℝ)^4567 ≤ (45082119446127/100000000000000 : ℝ)^3543 := by
    have hnat : (1347480593 : ℕ)^4567*100000000000000^3543 ≤ 45082119446127^3543*2500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347480593 2500000000 45082119446127 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117206833/625000000 : ℝ)^4567 ≤ (11560483770633/100000000000000 : ℝ)^3543 := by
    have hnat : (117206833 : ℕ)^4567*100000000000000^3543 ≤ 11560483770633^3543*625000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117206833 625000000 11560483770633 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522925567/1000000000 : ℝ)^4567 ≤ (67745932471/156250000000 : ℝ)^3543 := by
    have hnat : (522925567 : ℕ)^4567*156250000000^3543 ≤ 67745932471^3543*1000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522925567 1000000000 67745932471 156250000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347480593/2500000000 : ℝ), (-117206833/625000000 : ℝ), (522925567/1000000000 : ℝ)] ![(45082119446127/100000000000000 : ℝ), (11560483770633/100000000000000 : ℝ), (67745932471/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347480593/2500000000 : ℝ)|^4567 ≤ (45082119446127/100000000000000 : ℝ)^3543
        have hw : |(1347480593/2500000000 : ℝ)|=(1347480593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117206833/625000000 : ℝ)|^4567 ≤ (11560483770633/100000000000000 : ℝ)^3543
        have hw : |(-117206833/625000000 : ℝ)|=(117206833/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522925567/1000000000 : ℝ)|^4567 ≤ (67745932471/156250000000 : ℝ)^3543
        have hw : |(522925567/1000000000 : ℝ)|=(522925567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_14 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389922041/10000000000 : ℝ)*x 0 + (5229255953/10000000000 : ℝ)*x 1 + (-375061879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389922041/10000000000 : ℝ)^4567 ≤ (4508211587743/10000000000000 : ℝ)^3543 := by
    have hnat : (5389922041 : ℕ)^4567*10000000000000^3543 ≤ 4508211587743^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389922041 10000000000 4508211587743 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229255953/10000000000 : ℝ)^4567 ≤ (10839349951513/25000000000000 : ℝ)^3543 := by
    have hnat : (5229255953 : ℕ)^4567*25000000000000^3543 ≤ 10839349951513^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229255953 10000000000 10839349951513 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375061879/2000000000 : ℝ)^4567 ≤ (1445060537879/12500000000000 : ℝ)^3543 := by
    have hnat : (375061879 : ℕ)^4567*12500000000000^3543 ≤ 1445060537879^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375061879 2000000000 1445060537879 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389922041/10000000000 : ℝ), (5229255953/10000000000 : ℝ), (-375061879/2000000000 : ℝ)] ![(4508211587743/10000000000000 : ℝ), (10839349951513/25000000000000 : ℝ), (1445060537879/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389922041/10000000000 : ℝ)|^4567 ≤ (4508211587743/10000000000000 : ℝ)^3543
        have hw : |(5389922041/10000000000 : ℝ)|=(5389922041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229255953/10000000000 : ℝ)|^4567 ≤ (10839349951513/25000000000000 : ℝ)^3543
        have hw : |(5229255953/10000000000 : ℝ)|=(5229255953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-375061879/2000000000 : ℝ)|^4567 ≤ (1445060537879/12500000000000 : ℝ)^3543
        have hw : |(-375061879/2000000000 : ℝ)|=(375061879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_box_15 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (802906941/2000000000 : ℝ)*x 0 + (4387741669/10000000000 : ℝ)*x 1 + (4387742127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (802906941/2000000000 : ℝ)^4567 ≤ (15418695506231/50000000000000 : ℝ)^3543 := by
    have hnat : (802906941 : ℕ)^4567*50000000000000^3543 ≤ 15418695506231^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802906941 2000000000 15418695506231 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4387741669/10000000000 : ℝ)^4567 ≤ (34581302156019/100000000000000 : ℝ)^3543 := by
    have hnat : (4387741669 : ℕ)^4567*100000000000000^3543 ≤ 34581302156019^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387741669 10000000000 34581302156019 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4387742127/10000000000 : ℝ)^4567 ≤ (34581306808939/100000000000000 : ℝ)^3543 := by
    have hnat : (4387742127 : ℕ)^4567*100000000000000^3543 ≤ 34581306808939^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387742127 10000000000 34581306808939 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(802906941/2000000000 : ℝ), (4387741669/10000000000 : ℝ), (4387742127/10000000000 : ℝ)] ![(15418695506231/50000000000000 : ℝ), (34581302156019/100000000000000 : ℝ), (34581306808939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(802906941/2000000000 : ℝ)|^4567 ≤ (15418695506231/50000000000000 : ℝ)^3543
        have hw : |(802906941/2000000000 : ℝ)|=(802906941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4387741669/10000000000 : ℝ)|^4567 ≤ (34581302156019/100000000000000 : ℝ)^3543
        have hw : |(4387741669/10000000000 : ℝ)|=(4387741669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4387742127/10000000000 : ℝ)|^4567 ≤ (34581306808939/100000000000000 : ℝ)^3543
        have hw : |(4387742127/10000000000 : ℝ)|=(4387742127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1535_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15943/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(3671/6250 : ℝ) ∧ (80563/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21537/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5501/50000 : ℝ) ^ (4565/1024 : ℝ) ≤ (5331790608562001/100000000000000000000 : ℝ) := by
    have hpowers : (5501/50000 : ℝ)^4565 ≤ (5331790608562001/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5501 : ℕ)^4565*100000000000000000000^1024 ≤ 5331790608562001^1024*50000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5501 50000 5331790608562001 100000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5501/50000 : ℝ)) (X := (5331790608562001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4565/1024 : ℝ) ≤ (24462047775979779/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4565 ≤ (24462047775979779/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4565*100000000000000000000^1024 ≤ 24462047775979779^1024*25000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 24462047775979779 100000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (24462047775979779/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005331790608562001/50000000000000000000 : ℝ) ≤ (10000239190702897/10000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (50005331790608562001/50000000000000000000 : ℝ)^1024 ≤ (10000239190702897/10000000000000000 : ℝ)^4565 := by
      have hnat : (50005331790608562001 : ℕ)^1024*10000000000000000^4565 ≤ 10000239190702897^4565*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005331790608562001 50000000000000000000 10000239190702897 10000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000239190702897/10000000000000000 : ℝ)) (X := (50005331790608562001/50000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001489691919227089/5000000000000000000 : ℝ) ≤ (5000334122297157/5000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (5001489691919227089/5000000000000000000 : ℝ)^1024 ≤ (5000334122297157/5000000000000000 : ℝ)^4565 := by
      have hnat : (5001489691919227089 : ℕ)^1024*5000000000000000^4565 ≤ 5000334122297157^4565*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001489691919227089 5000000000000000000 5000334122297157 5000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000334122297157/5000000000000000 : ℝ)) (X := (5001489691919227089/5000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024462047775979779/50000000000000000000 : ℝ) ≤ (10001097298485731/10000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (50024462047775979779/50000000000000000000 : ℝ)^1024 ≤ (10001097298485731/10000000000000000 : ℝ)^4565 := by
      have hnat : (50024462047775979779 : ℕ)^1024*10000000000000000^4565 ≤ 10001097298485731^4565*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024462047775979779 50000000000000000000 10001097298485731 10000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001097298485731/10000000000000000 : ℝ)) (X := (50024462047775979779/50000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5331790608562001/100000000000000000000 : ℝ) ≤ ((22405815575451822343/22410000000000000000 : ℝ)+2*(429053891417/448200000000000 : ℝ)*(5501/50000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (22405815575451822343/22410000000000000000 : ℝ)+2*(429053891417/448200000000000 : ℝ)*(5501/50000 : ℝ)=(10000239190702897/10000000000000000 : ℝ) by norm_num, show 1+2*(5331790608562001/100000000000000000000 : ℝ)=(50005331790608562001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24462047775979779/100000000000000000000 : ℝ)+(5331790608562001/100000000000000000000 : ℝ) ≤ ((22405815575451822343/22410000000000000000 : ℝ)+(429053891417/448200000000000 : ℝ)*((3871/25000 : ℝ)+(5501/50000 : ℝ)))^(4565/1024 : ℝ) := by
    rw [show (22405815575451822343/22410000000000000000 : ℝ)+(429053891417/448200000000000 : ℝ)*((3871/25000 : ℝ)+(5501/50000 : ℝ))=(5000334122297157/5000000000000000 : ℝ) by norm_num, show 1+(24462047775979779/100000000000000000000 : ℝ)+(5331790608562001/100000000000000000000 : ℝ)=(5001489691919227089/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24462047775979779/100000000000000000000 : ℝ) ≤ ((22405815575451822343/22410000000000000000 : ℝ)+2*(429053891417/448200000000000 : ℝ)*(3871/25000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (22405815575451822343/22410000000000000000 : ℝ)+2*(429053891417/448200000000000 : ℝ)*(3871/25000 : ℝ)=(10001097298485731/10000000000000000 : ℝ) by norm_num, show 1+2*(24462047775979779/100000000000000000000 : ℝ)=(50024462047775979779/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22405815575451822343/22410000000000000000 : ℝ)*(X 1 0+X 2 0)+(429053891417/448200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (22405815575451822343/22410000000000000000 : ℝ)) (alpha := (429053891417/448200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22405815575451822343/22410000000000000000 : ℝ)*(X 0 1+X 2 1)+(429053891417/448200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (22405815575451822343/22410000000000000000 : ℝ)) (alpha := (429053891417/448200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22405815575451822343/22410000000000000000 : ℝ)*(X 0 2+X 1 2)+(429053891417/448200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (22405815575451822343/22410000000000000000 : ℝ)) (alpha := (429053891417/448200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1624965527/10000000000 : ℝ)*X 0 0+(1350087521/2500000000 : ℝ)*X 0 1+(5400349439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((527101109/1000000000 : ℝ)*X 1 0+(-902270649/5000000000 : ℝ)*X 1 1+(2700175327/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271011503/10000000000 : ℝ)*X 2 0+(540035017/1000000000 : ℝ)*X 2 1+(-1804541399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2230620157/5000000000 : ℝ)*X 0 0+(2082493891/5000000000 : ℝ)*X 0 1+(832997573/2000000000 : ℝ)*X 0 2+(2230620157/5000000000 : ℝ)*X 1 0+(2082493891/5000000000 : ℝ)*X 1 1+(832997573/2000000000 : ℝ)*X 1 2+(2230620157/5000000000 : ℝ)*X 2 0+(2082493891/5000000000 : ℝ)*X 2 1+(832997573/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2049589191/10000000000 : ℝ)*X 0 0+(5244296543/10000000000 : ℝ)*X 0 1+(5244297191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5379468757/10000000000 : ℝ)*X 1 0+(-373849451/2000000000 : ℝ)*X 1 1+(5244296943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((336216777/625000000 : ℝ)*X 2 0+(5244296701/10000000000 : ℝ)*X 2 1+(-1869248021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4054591231/10000000000 : ℝ)*X 0 0+(4368181407/10000000000 : ℝ)*X 0 1+(4368180497/10000000000 : ℝ)*X 0 2+(4054591231/10000000000 : ℝ)*X 1 0+(4368181407/10000000000 : ℝ)*X 1 1+(4368180497/10000000000 : ℝ)*X 1 2+(4054591231/10000000000 : ℝ)*X 2 0+(4368181407/10000000000 : ℝ)*X 2 1+(4368180497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1959740657/10000000000 : ℝ)*X 0 0+(320920153/625000000 : ℝ)*X 0 1+(2710366299/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628420533/5000000000 : ℝ)*X 1 0+(-1795849203/10000000000 : ℝ)*X 1 1+(2710366333/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256841259/10000000000 : ℝ)*X 2 0+(5420732539/10000000000 : ℝ)*X 2 1+(-897924557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2256602631/5000000000 : ℝ)*X 0 0+(1034603803/2500000000 : ℝ)*X 0 1+(2069207557/5000000000 : ℝ)*X 0 2+(2256602631/5000000000 : ℝ)*X 1 0+(1034603803/2500000000 : ℝ)*X 1 1+(2069207557/5000000000 : ℝ)*X 1 2+(2256602631/5000000000 : ℝ)*X 2 0+(1034603803/2500000000 : ℝ)*X 2 1+(2069207557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-342928571/2000000000 : ℝ)*X 0 0+(2753238791/5000000000 : ℝ)*X 0 1+(5229256037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1347480593/2500000000 : ℝ)*X 1 0+(-117206833/625000000 : ℝ)*X 1 1+(522925567/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5389922041/10000000000 : ℝ)*X 2 0+(5229255953/10000000000 : ℝ)*X 2 1+(-375061879/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((802906941/2000000000 : ℝ)*X 0 0+(4387741669/10000000000 : ℝ)*X 0 1+(4387742127/10000000000 : ℝ)*X 0 2+(802906941/2000000000 : ℝ)*X 1 0+(4387741669/10000000000 : ℝ)*X 1 1+(4387742127/10000000000 : ℝ)*X 1 2+(802906941/2000000000 : ℝ)*X 2 0+(4387741669/10000000000 : ℝ)*X 2 1+(4387742127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15943/25000 : ℝ) ≤ (-19848113109927129467354981365063/31125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48902069/25000000000000 : ℝ)*(lower0) + (68988087/100000000000000 : ℝ)*(upper1) + (274818093/100000000000000 : ℝ)*(lower4) + (564294999593041/25000000000000 : ℝ)*(major0) + (564294999593041/25000000000000 : ℝ)*(major1) + (564294999593041/25000000000000 : ℝ)*(major2) + (28641363/12500000000000 : ℝ)*(sp1) + (16070552901/100000000000000 : ℝ)*(sp2) + (2342304499/100000000000000 : ℝ)*(sp3) + (3169439431759413/100000000000000 : ℝ)*(sp4) + (1584721608619651/50000000000000 : ℝ)*(sp5) + (1584713687908653/50000000000000 : ℝ)*(sp6) + (170771319263043/12500000000000 : ℝ)*(sp7) + (2007305397/50000000000000 : ℝ)*(sp12) + (1366172896408843/100000000000000 : ℝ)*(f.failure) + (1584721723185103/50000000000000 : ℝ)*(f.sum) + (1031918880191/11205000000000000000000000000 : ℝ)*base66 + (3198995878057715063/560250000000000000000000000000000 : ℝ)*base67 + (2645097280479965063/560250000000000000000000000000000 : ℝ)*base69 + (6303789030564965063/560250000000000000000000000000000 : ℝ)*base71 + (33521269769863/5602500000000000000000000000 : ℝ)*base74 + (4251618222334715063/560250000000000000000000000000000 : ℝ)*base75 + (4275632811949715063/560250000000000000000000000000000 : ℝ)*base77 + (776462939690465063/560250000000000000000000000000000 : ℝ)*base79 + (5168809863449/2801250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (914037/2000000000000000000000 : ℝ)*base90 + (914037/2000000000000000000000 : ℝ)*base92 + (914037/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (3671/6250 : ℝ) ≤ (6094139096209462245844028361059/10375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10627331/6250000000000 : ℝ)*(upper0) + (6914661/20000000000000 : ℝ)*(upper2) + (37572621/20000000000000 : ℝ)*(upper3) + (81501609/50000000000000 : ℝ)*(upper4) + (1167499615252917/50000000000000 : ℝ)*(major0) + (1167499615252917/50000000000000 : ℝ)*(major1) + (1167499615252917/50000000000000 : ℝ)*(major2) + (202321587756771/6250000000000 : ℝ)*(sp0) + (647426447753089/20000000000000 : ℝ)*(sp1) + (647426544809521/20000000000000 : ℝ)*(sp2) + (706635854971447/50000000000000 : ℝ)*(sp3) + (1316534289/10000000000000 : ℝ)*(sp5) + (1268006073/10000000000000 : ℝ)*(sp6) + (356719823/20000000000000 : ℝ)*(sp11) + (1413273493542009/100000000000000 : ℝ)*(f.failure) + (202321587756771/6250000000000 : ℝ)*(f.sum) + (23805015683573/3735000000000000000000000000 : ℝ)*base65 + (3196693621543341823/373500000000000000000000000000000 : ℝ)*base68 + (1693531745725341823/373500000000000000000000000000000 : ℝ)*base70 + (1597921610422341823/373500000000000000000000000000000 : ℝ)*base72 + (306296066617/3735000000000000000000000000 : ℝ)*base74 + (206745075031341823/373500000000000000000000000000000 : ℝ)*base76 + (978629708295158177/373500000000000000000000000000000 : ℝ)*base77 + (1443407813509341823/373500000000000000000000000000000 : ℝ)*base80 + (7961052129319/1867500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7783431/2000000000000000000000 : ℝ)*base90 + (7783431/2000000000000000000000 : ℝ)*base92 + (7783431/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80563/100000 : ℝ) ≤ (50151939981710641246467840378689/62250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3178341/6250000000000 : ℝ)*(lower3) + (6843907/12500000000000 : ℝ)*(upper4) + (5382177/20000000000000 : ℝ)*(lower5) + (1263041384509131/50000000000000 : ℝ)*(major0) + (1263041384509131/50000000000000 : ℝ)*(major1) + (1263041384509131/50000000000000 : ℝ)*(major2) + (120513851/10000000000000 : ℝ)*(sp0) + (37820265003/100000000000000 : ℝ)*(sp1) + (14418411531/50000000000000 : ℝ)*(sp2) + (17562366443/100000000000000 : ℝ)*(sp3) + (1748190580608277/50000000000000 : ℝ)*(sp8) + (1748172273045031/50000000000000 : ℝ)*(sp9) + (1748176764766001/50000000000000 : ℝ)*(sp10) + (1528910487504189/100000000000000 : ℝ)*(sp11) + (191116006233829/12500000000000 : ℝ)*(f.failure) + (437047795794383/12500000000000 : ℝ)*(f.sum) + (16730595920711/3735000000000000000000000000 : ℝ)*base66 + (761605172007221311/373500000000000000000000000000000 : ℝ)*base67 + (24283155727721311/373500000000000000000000000000000 : ℝ)*base69 + (2381297773808778689/373500000000000000000000000000000 : ℝ)*base72 + (4097941256081/3735000000000000000000000000 : ℝ)*base74 + (373458515164278689/373500000000000000000000000000000 : ℝ)*base76 + (2233599747954221311/373500000000000000000000000000000 : ℝ)*base77 + (2520157244136221311/373500000000000000000000000000000 : ℝ)*base79 + (1209533479901/233437500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (702811/250000000000000000000 : ℝ)*base90 + (702811/250000000000000000000 : ℝ)*base92 + (702811/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-21537/25000 : ℝ) ≤ (-3351611634061277038152243182123/3890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8137509/100000000000000 : ℝ)*(upper3) + (101710931/100000000000000 : ℝ)*(lower4) + (22412979/50000000000000 : ℝ)*(upper5) + (160357152598383/6250000000000 : ℝ)*(major0) + (160357152598383/6250000000000 : ℝ)*(major1) + (160357152598383/6250000000000 : ℝ)*(major2) + (820811237/20000000000000 : ℝ)*(sp4) + (48764416079/50000000000000 : ℝ)*(sp5) + (20152022329/25000000000000 : ℝ)*(sp6) + (25805452283/100000000000000 : ℝ)*(sp7) + (1803612340830293/50000000000000 : ℝ)*(sp12) + (901782814221153/25000000000000 : ℝ)*(sp13) + (1803574088813727/50000000000000 : ℝ)*(sp14) + (776444786189057/50000000000000 : ℝ)*(sp15) + (1552915377830397/100000000000000 : ℝ)*(f.failure) + (3607228785716771/100000000000000 : ℝ)*(f.sum) + (451119623467/1867500000000000000000000000 : ℝ)*base66 + (27168876232832123/46687500000000000000000000000000 : ℝ)*base67 + (50056039418667877/46687500000000000000000000000000 : ℝ)*base70 + (267702033103269623/46687500000000000000000000000000 : ℝ)*base71 + (19292557707539/3735000000000000000000000000 : ℝ)*base74 + (455611183350144623/46687500000000000000000000000000 : ℝ)*base75 + (418943441513769623/46687500000000000000000000000000 : ℝ)*base77 + (380003650155519623/46687500000000000000000000000000 : ℝ)*base79 + (16183961063909/3735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3434877/2000000000000000000000 : ℝ)*base89 + (3434877/2000000000000000000000 : ℝ)*base91 + (3434877/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1535_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15943/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(3671/6250 : ℝ) else (80563/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21537/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1535_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1535_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15943/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(3671/6250 : ℝ) else (80563/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21537/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1535_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1535_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15943/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(3671/6250 : ℝ) else (80563/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21537/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1535_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
