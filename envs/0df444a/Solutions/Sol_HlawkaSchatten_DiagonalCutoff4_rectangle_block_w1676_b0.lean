-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1676_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:52.347259+00:00
-- url     : https://prove2.me/submissions/5174539e-d80f-44fa-b4ee-58bce6d013b7

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
theorem support_rectangle_w1676_s0_0 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1443003033/10000000000 : ℝ)*x 0 + (5771350281/10000000000 : ℝ)*x 1 + (984146647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1443003033/10000000000 : ℝ)^5031 ≤ (8798642024637/100000000000000 : ℝ)^4007 := by
    have hnat : (1443003033 : ℕ)^5031*100000000000000^4007 ≤ 8798642024637^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1443003033 10000000000 8798642024637 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5771350281/10000000000 : ℝ)^5031 ≤ (25075016186373/50000000000000 : ℝ)^4007 := by
    have hnat : (5771350281 : ℕ)^5031*50000000000000^4007 ≤ 25075016186373^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5771350281 10000000000 25075016186373 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (984146647/2000000000 : ℝ)^5031 ≤ (20525662791253/50000000000000 : ℝ)^4007 := by
    have hnat : (984146647 : ℕ)^5031*50000000000000^4007 ≤ 20525662791253^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984146647 2000000000 20525662791253 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1443003033/10000000000 : ℝ), (5771350281/10000000000 : ℝ), (984146647/2000000000 : ℝ)] ![(8798642024637/100000000000000 : ℝ), (25075016186373/50000000000000 : ℝ), (20525662791253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1443003033/10000000000 : ℝ)|^5031 ≤ (8798642024637/100000000000000 : ℝ)^4007
        have hw : |(-1443003033/10000000000 : ℝ)|=(1443003033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5771350281/10000000000 : ℝ)|^5031 ≤ (25075016186373/50000000000000 : ℝ)^4007
        have hw : |(5771350281/10000000000 : ℝ)|=(5771350281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(984146647/2000000000 : ℝ)|^5031 ≤ (20525662791253/50000000000000 : ℝ)^4007
        have hw : |(984146647/2000000000 : ℝ)|=(984146647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s0_1 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1085808539/2000000000 : ℝ)*x 0 + (-1909185241/10000000000 : ℝ)*x 1 + (1230183503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085808539/2000000000 : ℝ)^5031 ≤ (46444153014339/100000000000000 : ℝ)^4007 := by
    have hnat : (1085808539 : ℕ)^5031*100000000000000^4007 ≤ 46444153014339^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085808539 2000000000 46444153014339 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1909185241/10000000000 : ℝ)^5031 ≤ (12504513251527/100000000000000 : ℝ)^4007 := by
    have hnat : (1909185241 : ℕ)^5031*100000000000000^4007 ≤ 12504513251527^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909185241 10000000000 12504513251527 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1230183503/2500000000 : ℝ)^5031 ≤ (1642053348847/4000000000000 : ℝ)^4007 := by
    have hnat : (1230183503 : ℕ)^5031*4000000000000^4007 ≤ 1642053348847^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230183503 2500000000 1642053348847 4000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085808539/2000000000 : ℝ), (-1909185241/10000000000 : ℝ), (1230183503/2500000000 : ℝ)] ![(46444153014339/100000000000000 : ℝ), (12504513251527/100000000000000 : ℝ), (1642053348847/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085808539/2000000000 : ℝ)|^5031 ≤ (46444153014339/100000000000000 : ℝ)^4007
        have hw : |(1085808539/2000000000 : ℝ)|=(1085808539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1909185241/10000000000 : ℝ)|^5031 ≤ (12504513251527/100000000000000 : ℝ)^4007
        have hw : |(-1909185241/10000000000 : ℝ)|=(1909185241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1230183503/2500000000 : ℝ)|^5031 ≤ (1642053348847/4000000000000 : ℝ)^4007
        have hw : |(1230183503/2500000000 : ℝ)|=(1230183503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s0_2 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5429043929/10000000000 : ℝ)*x 0 + (246036657/500000000 : ℝ)*x 1 + (-95459237/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5429043929/10000000000 : ℝ)^5031 ≤ (23222083134337/50000000000000 : ℝ)^4007 := by
    have hnat : (5429043929 : ℕ)^5031*50000000000000^4007 ≤ 23222083134337^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429043929 10000000000 23222083134337 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246036657/500000000 : ℝ)^5031 ≤ (41051324587431/100000000000000 : ℝ)^4007 := by
    have hnat : (246036657 : ℕ)^5031*100000000000000^4007 ≤ 41051324587431^4007*500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246036657 500000000 41051324587431 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95459237/500000000 : ℝ)^5031 ≤ (6252254565791/50000000000000 : ℝ)^4007 := by
    have hnat : (95459237 : ℕ)^5031*50000000000000^4007 ≤ 6252254565791^4007*500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95459237 500000000 6252254565791 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5429043929/10000000000 : ℝ), (246036657/500000000 : ℝ), (-95459237/500000000 : ℝ)] ![(23222083134337/50000000000000 : ℝ), (41051324587431/100000000000000 : ℝ), (6252254565791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5429043929/10000000000 : ℝ)|^5031 ≤ (23222083134337/50000000000000 : ℝ)^4007
        have hw : |(5429043929/10000000000 : ℝ)|=(5429043929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(246036657/500000000 : ℝ)|^5031 ≤ (41051324587431/100000000000000 : ℝ)^4007
        have hw : |(246036657/500000000 : ℝ)|=(246036657/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-95459237/500000000 : ℝ)|^5031 ≤ (6252254565791/50000000000000 : ℝ)^4007
        have hw : |(-95459237/500000000 : ℝ)|=(95459237/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s0_3 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4068969197/10000000000 : ℝ)*x 0 + (608086857/2000000000 : ℝ)*x 1 + (5316217617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4068969197/10000000000 : ℝ)^5031 ≤ (6467211292071/20000000000000 : ℝ)^4007 := by
    have hnat : (4068969197 : ℕ)^5031*20000000000000^4007 ≤ 6467211292071^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4068969197 10000000000 6467211292071 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608086857/2000000000 : ℝ)^5031 ≤ (5607101128339/25000000000000 : ℝ)^4007 := by
    have hnat : (608086857 : ℕ)^5031*25000000000000^4007 ≤ 5607101128339^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608086857 2000000000 5607101128339 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5316217617/10000000000 : ℝ)^5031 ≤ (45235539009863/100000000000000 : ℝ)^4007 := by
    have hnat : (5316217617 : ℕ)^5031*100000000000000^4007 ≤ 45235539009863^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5316217617 10000000000 45235539009863 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4068969197/10000000000 : ℝ), (608086857/2000000000 : ℝ), (5316217617/10000000000 : ℝ)] ![(6467211292071/20000000000000 : ℝ), (5607101128339/25000000000000 : ℝ), (45235539009863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4068969197/10000000000 : ℝ)|^5031 ≤ (6467211292071/20000000000000 : ℝ)^4007
        have hw : |(4068969197/10000000000 : ℝ)|=(4068969197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(608086857/2000000000 : ℝ)|^5031 ≤ (5607101128339/25000000000000 : ℝ)^4007
        have hw : |(608086857/2000000000 : ℝ)|=(608086857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5316217617/10000000000 : ℝ)|^5031 ≤ (45235539009863/100000000000000 : ℝ)^4007
        have hw : |(5316217617/10000000000 : ℝ)|=(5316217617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s0_4 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1445293013/10000000000 : ℝ)*x 0 + (4942384723/10000000000 : ℝ)*x 1 + (2874466639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1445293013/10000000000 : ℝ)^5031 ≤ (4408088458203/50000000000000 : ℝ)^4007 := by
    have hnat : (1445293013 : ℕ)^5031*50000000000000^4007 ≤ 4408088458203^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445293013 10000000000 4408088458203 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4942384723/10000000000 : ℝ)^5031 ≤ (41278240957521/100000000000000 : ℝ)^4007 := by
    have hnat : (4942384723 : ℕ)^5031*100000000000000^4007 ≤ 41278240957521^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4942384723 10000000000 41278240957521 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2874466639/5000000000 : ℝ)^5031 ≤ (49905582112767/100000000000000 : ℝ)^4007 := by
    have hnat : (2874466639 : ℕ)^5031*100000000000000^4007 ≤ 49905582112767^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2874466639 5000000000 49905582112767 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1445293013/10000000000 : ℝ), (4942384723/10000000000 : ℝ), (2874466639/5000000000 : ℝ)] ![(4408088458203/50000000000000 : ℝ), (41278240957521/100000000000000 : ℝ), (49905582112767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1445293013/10000000000 : ℝ)|^5031 ≤ (4408088458203/50000000000000 : ℝ)^4007
        have hw : |(-1445293013/10000000000 : ℝ)|=(1445293013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4942384723/10000000000 : ℝ)|^5031 ≤ (41278240957521/100000000000000 : ℝ)^4007
        have hw : |(4942384723/10000000000 : ℝ)|=(4942384723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2874466639/5000000000 : ℝ)|^5031 ≤ (49905582112767/100000000000000 : ℝ)^4007
        have hw : |(2874466639/5000000000 : ℝ)|=(2874466639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s0_5 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129940647/250000000 : ℝ)*x 0 + (-1080986557/10000000000 : ℝ)*x 1 + (1149786237/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129940647/250000000 : ℝ)^5031 ≤ (2748262516863/6250000000000 : ℝ)^4007 := by
    have hnat : (129940647 : ℕ)^5031*6250000000000^4007 ≤ 2748262516863^4007*250000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129940647 250000000 2748262516863 6250000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080986557/10000000000 : ℝ)^5031 ≤ (6122240423429/100000000000000 : ℝ)^4007 := by
    have hnat : (1080986557 : ℕ)^5031*100000000000000^4007 ≤ 6122240423429^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080986557 10000000000 6122240423429 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1149786237/2000000000 : ℝ)^5031 ≤ (24952779650313/50000000000000 : ℝ)^4007 := by
    have hnat : (1149786237 : ℕ)^5031*50000000000000^4007 ≤ 24952779650313^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149786237 2000000000 24952779650313 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129940647/250000000 : ℝ), (-1080986557/10000000000 : ℝ), (1149786237/2000000000 : ℝ)] ![(2748262516863/6250000000000 : ℝ), (6122240423429/100000000000000 : ℝ), (24952779650313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129940647/250000000 : ℝ)|^5031 ≤ (2748262516863/6250000000000 : ℝ)^4007
        have hw : |(129940647/250000000 : ℝ)|=(129940647/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1080986557/10000000000 : ℝ)|^5031 ≤ (6122240423429/100000000000000 : ℝ)^4007
        have hw : |(-1080986557/10000000000 : ℝ)|=(1080986557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1149786237/2000000000 : ℝ)|^5031 ≤ (24952779650313/50000000000000 : ℝ)^4007
        have hw : |(1149786237/2000000000 : ℝ)|=(1149786237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s0_6 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197625739/10000000000 : ℝ)*x 0 + (5748930717/10000000000 : ℝ)*x 1 + (-270246871/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197625739/10000000000 : ℝ)^5031 ≤ (43972198772099/100000000000000 : ℝ)^4007 := by
    have hnat : (5197625739 : ℕ)^5031*100000000000000^4007 ≤ 43972198772099^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197625739 10000000000 43972198772099 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5748930717/10000000000 : ℝ)^5031 ≤ (1996222167991/4000000000000 : ℝ)^4007 := by
    have hnat : (5748930717 : ℕ)^5031*4000000000000^4007 ≤ 1996222167991^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5748930717 10000000000 1996222167991 4000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270246871/2500000000 : ℝ)^5031 ≤ (6122247015241/100000000000000 : ℝ)^4007 := by
    have hnat : (270246871 : ℕ)^5031*100000000000000^4007 ≤ 6122247015241^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270246871 2500000000 6122247015241 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197625739/10000000000 : ℝ), (5748930717/10000000000 : ℝ), (-270246871/2500000000 : ℝ)] ![(43972198772099/100000000000000 : ℝ), (1996222167991/4000000000000 : ℝ), (6122247015241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197625739/10000000000 : ℝ)|^5031 ≤ (43972198772099/100000000000000 : ℝ)^4007
        have hw : |(5197625739/10000000000 : ℝ)|=(5197625739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5748930717/10000000000 : ℝ)|^5031 ≤ (1996222167991/4000000000000 : ℝ)^4007
        have hw : |(5748930717/10000000000 : ℝ)|=(5748930717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-270246871/2500000000 : ℝ)|^5031 ≤ (6122247015241/100000000000000 : ℝ)^4007
        have hw : |(-270246871/2500000000 : ℝ)|=(270246871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s0_7 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2037546619/5000000000 : ℝ)*x 0 + (1051657823/2000000000 : ℝ)*x 1 + (3100411819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037546619/5000000000 : ℝ)^5031 ≤ (32397173061961/100000000000000 : ℝ)^4007 := by
    have hnat : (2037546619 : ℕ)^5031*100000000000000^4007 ≤ 32397173061961^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037546619 5000000000 32397173061961 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051657823/2000000000 : ℝ)^5031 ≤ (44617526100017/100000000000000 : ℝ)^4007 := by
    have hnat : (1051657823 : ℕ)^5031*100000000000000^4007 ≤ 44617526100017^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051657823 2000000000 44617526100017 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3100411819/10000000000 : ℝ)^5031 ≤ (22985300828811/100000000000000 : ℝ)^4007 := by
    have hnat : (3100411819 : ℕ)^5031*100000000000000^4007 ≤ 22985300828811^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3100411819 10000000000 22985300828811 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2037546619/5000000000 : ℝ), (1051657823/2000000000 : ℝ), (3100411819/10000000000 : ℝ)] ![(32397173061961/100000000000000 : ℝ), (44617526100017/100000000000000 : ℝ), (22985300828811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2037546619/5000000000 : ℝ)|^5031 ≤ (32397173061961/100000000000000 : ℝ)^4007
        have hw : |(2037546619/5000000000 : ℝ)|=(2037546619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051657823/2000000000 : ℝ)|^5031 ≤ (44617526100017/100000000000000 : ℝ)^4007
        have hw : |(1051657823/2000000000 : ℝ)|=(1051657823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3100411819/10000000000 : ℝ)|^5031 ≤ (22985300828811/100000000000000 : ℝ)^4007
        have hw : |(3100411819/10000000000 : ℝ)|=(3100411819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1676_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (619/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11593/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (5023/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5023 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5023*1^1024 ≤ 0^1024*1^5023 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5023 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5023/1024 : ℝ) ≤ (139606441972816921/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5023 ≤ (139606441972816921/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5023*12500000000000000000^1024 ≤ 139606441972816921^1024*5^5023 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 139606441972816921 12500000000000000000 5023 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (139606441972816921/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5023 := by
      have hnat : (1 : ℕ)^1024*1^5023 ≤ 1^5023*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12639606441972816921/12500000000000000000 : ℝ) ≤ (10022667831943177/10000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (12639606441972816921/12500000000000000000 : ℝ)^1024 ≤ (10022667831943177/10000000000000000 : ℝ)^5023 := by
      have hnat : (12639606441972816921 : ℕ)^1024*10000000000000000^5023 ≤ 10022667831943177^5023*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12639606441972816921 12500000000000000000 10022667831943177 10000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10022667831943177/10000000000000000 : ℝ)) (X := (12639606441972816921/12500000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6389606441972816921/6250000000000000000 : ℝ) ≤ (5022667831943177/5000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (6389606441972816921/6250000000000000000 : ℝ)^1024 ≤ (5022667831943177/5000000000000000 : ℝ)^5023 := by
      have hnat : (6389606441972816921 : ℕ)^1024*5000000000000000^5023 ≤ 5022667831943177^5023*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6389606441972816921 6250000000000000000 5022667831943177 5000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5022667831943177/5000000000000000 : ℝ)) (X := (6389606441972816921/6250000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(22667831943177/4000000000000000 : ℝ)*(0 : ℝ))^(5023/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(22667831943177/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(139606441972816921/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(22667831943177/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5023/1024 : ℝ) := by
    rw [show (1 : ℝ)+(22667831943177/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10022667831943177/10000000000000000 : ℝ) by norm_num, show 1+(139606441972816921/12500000000000000000 : ℝ)+(0 : ℝ)=(12639606441972816921/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(139606441972816921/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(22667831943177/4000000000000000 : ℝ)*(2/5 : ℝ))^(5023/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(22667831943177/4000000000000000 : ℝ)*(2/5 : ℝ)=(5022667831943177/5000000000000000 : ℝ) by norm_num, show 1+2*(139606441972816921/12500000000000000000 : ℝ)=(6389606441972816921/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(22667831943177/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22667831943177/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(22667831943177/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22667831943177/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(22667831943177/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22667831943177/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1443003033/10000000000 : ℝ)*X 0 0+(5771350281/10000000000 : ℝ)*X 0 1+(984146647/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1085808539/2000000000 : ℝ)*X 1 0+(-1909185241/10000000000 : ℝ)*X 1 1+(1230183503/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5429043929/10000000000 : ℝ)*X 2 0+(246036657/500000000 : ℝ)*X 2 1+(-95459237/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4068969197/10000000000 : ℝ)*X 0 0+(608086857/2000000000 : ℝ)*X 0 1+(5316217617/10000000000 : ℝ)*X 0 2+(4068969197/10000000000 : ℝ)*X 1 0+(608086857/2000000000 : ℝ)*X 1 1+(5316217617/10000000000 : ℝ)*X 1 2+(4068969197/10000000000 : ℝ)*X 2 0+(608086857/2000000000 : ℝ)*X 2 1+(5316217617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1445293013/10000000000 : ℝ)*X 0 0+(4942384723/10000000000 : ℝ)*X 0 1+(2874466639/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((129940647/250000000 : ℝ)*X 1 0+(-1080986557/10000000000 : ℝ)*X 1 1+(1149786237/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5197625739/10000000000 : ℝ)*X 2 0+(5748930717/10000000000 : ℝ)*X 2 1+(-270246871/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2037546619/5000000000 : ℝ)*X 0 0+(1051657823/2000000000 : ℝ)*X 0 1+(3100411819/10000000000 : ℝ)*X 0 2+(2037546619/5000000000 : ℝ)*X 1 0+(1051657823/2000000000 : ℝ)*X 1 1+(3100411819/10000000000 : ℝ)*X 1 2+(2037546619/5000000000 : ℝ)*X 2 0+(1051657823/2000000000 : ℝ)*X 2 1+(3100411819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (890368641832200505427181/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82380461/100000000000000 : ℝ)*(base1) + (159138129/20000000000000 : ℝ)*(base19) + (1049589181/100000000000000 : ℝ)*(base23) + (6658159/50000000000000 : ℝ)*(base24) + (194155811/100000000000000 : ℝ)*(upper5) + (807519139871849/100000000000000 : ℝ)*(major0) + (807519139871849/100000000000000 : ℝ)*(major1) + (807519139871849/100000000000000 : ℝ)*(major2) + (1175620324992799/100000000000000 : ℝ)*(sp0) + (117562494029663/10000000000000 : ℝ)*(sp1) + (1175624673081777/100000000000000 : ℝ)*(sp2) + (43941090507291/10000000000000 : ℝ)*(sp3) + (5493374937/100000000000000 : ℝ)*(sp4) + (87994267/6250000000000 : ℝ)*(sp7) + (219706197680821/50000000000000 : ℝ)*(f.failure) + (293906433996819/25000000000000 : ℝ)*(f.sum) + (462432261675727/200000000000000000000000000000 : ℝ)*base66 + (379940610075727/400000000000000000000000000000 : ℝ)*base68 + (949156234324273/400000000000000000000000000000 : ℝ)*base69 + (1508482087524273/400000000000000000000000000000 : ℝ)*base71 + (1166771730075727/200000000000000000000000000000 : ℝ)*base74 + (2715335710724273/400000000000000000000000000000 : ℝ)*base75 + (1145376494324273/400000000000000000000000000000 : ℝ)*base77 + (483069065924273/400000000000000000000000000000 : ℝ)*base79 + (321048578324273/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (29541679/5000000000000000000000 : ℝ)*base89 + (29541679/5000000000000000000000 : ℝ)*base91 + (29541679/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (454139228390522596071231/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (275042319/25000000000000 : ℝ)*(base19) + (1235218279/100000000000000 : ℝ)*(base23) + (78677351/50000000000000 : ℝ)*(base39) + (53235861/100000000000000 : ℝ)*(upper2) + (104563609/50000000000000 : ℝ)*(upper5) + (8516341650711/1000000000000 : ℝ)*(major0) + (8516341650711/1000000000000 : ℝ)*(major1) + (425817003858199/50000000000000 : ℝ)*(major2) + (2513759409/100000000000000 : ℝ)*(sp1) + (63287423/12500000000000 : ℝ)*(sp2) + (619925194176571/50000000000000 : ℝ)*(sp4) + (1239846774424457/100000000000000 : ℝ)*(sp5) + (61992440209509/5000000000000 : ℝ)*(sp6) + (231708816527303/50000000000000 : ℝ)*(sp7) + (231708816527303/50000000000000 : ℝ)*(f.failure) + (1239850545707843/100000000000000 : ℝ)*(f.sum) + (1087259539600573/200000000000000000000000000000 : ℝ)*base65 + (591091662358223/200000000000000000000000000000 : ℝ)*base67 + (25150857511153/4000000000000000000000000000 : ℝ)*base70 + (477349395041777/200000000000000000000000000000 : ℝ)*base72 + (1301749701600573/200000000000000000000000000000 : ℝ)*base73 + (31013461419153/4000000000000000000000000000 : ℝ)*base76 + (4442785712847/4000000000000000000000000000 : ℝ)*base77 + (8936699608847/4000000000000000000000000000 : ℝ)*base79 + (2797171580847/2000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (25959803/5000000000000000000000 : ℝ)*base90 + (25959803/5000000000000000000000 : ℝ)*base92 + (25959803/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1676_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (619/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11593/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1676_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1676_s1_0 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1537512143/10000000000 : ℝ)*x 0 + (552264337/1000000000 : ℝ)*x 1 + (5107796911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1537512143/10000000000 : ℝ)^5031 ≤ (9528132178573/100000000000000 : ℝ)^4007 := by
    have hnat : (1537512143 : ℕ)^5031*100000000000000^4007 ≤ 9528132178573^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537512143 10000000000 9528132178573 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552264337/1000000000 : ℝ)^5031 ≤ (47451718709299/100000000000000 : ℝ)^4007 := by
    have hnat : (552264337 : ℕ)^5031*100000000000000^4007 ≤ 47451718709299^4007*1000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552264337 1000000000 47451718709299 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5107796911/10000000000 : ℝ)^5031 ≤ (8604029817899/20000000000000 : ℝ)^4007 := by
    have hnat : (5107796911 : ℕ)^5031*20000000000000^4007 ≤ 8604029817899^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5107796911 10000000000 8604029817899 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1537512143/10000000000 : ℝ), (552264337/1000000000 : ℝ), (5107796911/10000000000 : ℝ)] ![(9528132178573/100000000000000 : ℝ), (47451718709299/100000000000000 : ℝ), (8604029817899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1537512143/10000000000 : ℝ)|^5031 ≤ (9528132178573/100000000000000 : ℝ)^4007
        have hw : |(-1537512143/10000000000 : ℝ)|=(1537512143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552264337/1000000000 : ℝ)|^5031 ≤ (47451718709299/100000000000000 : ℝ)^4007
        have hw : |(552264337/1000000000 : ℝ)|=(552264337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5107796911/10000000000 : ℝ)|^5031 ≤ (8604029817899/20000000000000 : ℝ)^4007
        have hw : |(5107796911/10000000000 : ℝ)|=(5107796911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s1_1 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335173323/625000000 : ℝ)*x 0 + (-877279247/5000000000 : ℝ)*x 1 + (5107796891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335173323/625000000 : ℝ)^5031 ≤ (2286673439779/5000000000000 : ℝ)^4007 := by
    have hnat : (335173323 : ℕ)^5031*5000000000000^4007 ≤ 2286673439779^4007*625000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335173323 625000000 2286673439779 5000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877279247/5000000000 : ℝ)^5031 ≤ (11246382305233/100000000000000 : ℝ)^4007 := by
    have hnat : (877279247 : ℕ)^5031*100000000000000^4007 ≤ 11246382305233^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877279247 5000000000 11246382305233 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5107796891/10000000000 : ℝ)^5031 ≤ (43020148877999/100000000000000 : ℝ)^4007 := by
    have hnat : (5107796891 : ℕ)^5031*100000000000000^4007 ≤ 43020148877999^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5107796891 10000000000 43020148877999 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335173323/625000000 : ℝ), (-877279247/5000000000 : ℝ), (5107796891/10000000000 : ℝ)] ![(2286673439779/5000000000000 : ℝ), (11246382305233/100000000000000 : ℝ), (43020148877999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335173323/625000000 : ℝ)|^5031 ≤ (2286673439779/5000000000000 : ℝ)^4007
        have hw : |(335173323/625000000 : ℝ)|=(335173323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-877279247/5000000000 : ℝ)|^5031 ≤ (11246382305233/100000000000000 : ℝ)^4007
        have hw : |(-877279247/5000000000 : ℝ)|=(877279247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5107796891/10000000000 : ℝ)|^5031 ≤ (43020148877999/100000000000000 : ℝ)^4007
        have hw : |(5107796891/10000000000 : ℝ)|=(5107796891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s1_2 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362772751/10000000000 : ℝ)*x 0 + (319237331/625000000 : ℝ)*x 1 + (-1754558517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362772751/10000000000 : ℝ)^5031 ≤ (45733464330639/100000000000000 : ℝ)^4007 := by
    have hnat : (5362772751 : ℕ)^5031*100000000000000^4007 ≤ 45733464330639^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362772751 10000000000 45733464330639 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319237331/625000000 : ℝ)^5031 ≤ (10755038290201/25000000000000 : ℝ)^4007 := by
    have hnat : (319237331 : ℕ)^5031*25000000000000^4007 ≤ 10755038290201^4007*625000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319237331 625000000 10755038290201 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1754558517/10000000000 : ℝ)^5031 ≤ (5623191245167/50000000000000 : ℝ)^4007 := by
    have hnat : (1754558517 : ℕ)^5031*50000000000000^4007 ≤ 5623191245167^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754558517 10000000000 5623191245167 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362772751/10000000000 : ℝ), (319237331/625000000 : ℝ), (-1754558517/10000000000 : ℝ)] ![(45733464330639/100000000000000 : ℝ), (10755038290201/25000000000000 : ℝ), (5623191245167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362772751/10000000000 : ℝ)|^5031 ≤ (45733464330639/100000000000000 : ℝ)^4007
        have hw : |(5362772751/10000000000 : ℝ)|=(5362772751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(319237331/625000000 : ℝ)|^5031 ≤ (10755038290201/25000000000000 : ℝ)^4007
        have hw : |(319237331/625000000 : ℝ)|=(319237331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1754558517/10000000000 : ℝ)|^5031 ≤ (5623191245167/50000000000000 : ℝ)^4007
        have hw : |(-1754558517/10000000000 : ℝ)|=(1754558517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s1_3 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4145134809/10000000000 : ℝ)*x 0 + (723186363/2000000000 : ℝ)*x 1 + (2362916157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4145134809/10000000000 : ℝ)^5031 ≤ (33097835983667/100000000000000 : ℝ)^4007 := by
    have hnat : (4145134809 : ℕ)^5031*100000000000000^4007 ≤ 33097835983667^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145134809 10000000000 33097835983667 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (723186363/2000000000 : ℝ)^5031 ≤ (5576377667181/20000000000000 : ℝ)^4007 := by
    have hnat : (723186363 : ℕ)^5031*20000000000000^4007 ≤ 5576377667181^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723186363 2000000000 5576377667181 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2362916157/5000000000 : ℝ)^5031 ≤ (1219383614651/3125000000000 : ℝ)^4007 := by
    have hnat : (2362916157 : ℕ)^5031*3125000000000^4007 ≤ 1219383614651^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2362916157 5000000000 1219383614651 3125000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4145134809/10000000000 : ℝ), (723186363/2000000000 : ℝ), (2362916157/5000000000 : ℝ)] ![(33097835983667/100000000000000 : ℝ), (5576377667181/20000000000000 : ℝ), (1219383614651/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4145134809/10000000000 : ℝ)|^5031 ≤ (33097835983667/100000000000000 : ℝ)^4007
        have hw : |(4145134809/10000000000 : ℝ)|=(4145134809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(723186363/2000000000 : ℝ)|^5031 ≤ (5576377667181/20000000000000 : ℝ)^4007
        have hw : |(723186363/2000000000 : ℝ)|=(723186363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2362916157/5000000000 : ℝ)|^5031 ≤ (1219383614651/3125000000000 : ℝ)^4007
        have hw : |(2362916157/5000000000 : ℝ)|=(2362916157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s1_4 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-307554849/2000000000 : ℝ)*x 0 + (5112923977/10000000000 : ℝ)*x 1 + (2758713643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (307554849/2000000000 : ℝ)^5031 ≤ (238254289649/2500000000000 : ℝ)^4007 := by
    have hnat : (307554849 : ℕ)^5031*2500000000000^4007 ≤ 238254289649^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307554849 2000000000 238254289649 2500000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5112923977/10000000000 : ℝ)^5031 ≤ (10768593469209/25000000000000 : ℝ)^4007 := by
    have hnat : (5112923977 : ℕ)^5031*25000000000000^4007 ≤ 10768593469209^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5112923977 10000000000 10768593469209 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2758713643/5000000000 : ℝ)^5031 ≤ (23697727259583/50000000000000 : ℝ)^4007 := by
    have hnat : (2758713643 : ℕ)^5031*50000000000000^4007 ≤ 23697727259583^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758713643 5000000000 23697727259583 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-307554849/2000000000 : ℝ), (5112923977/10000000000 : ℝ), (2758713643/5000000000 : ℝ)] ![(238254289649/2500000000000 : ℝ), (10768593469209/25000000000000 : ℝ), (23697727259583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-307554849/2000000000 : ℝ)|^5031 ≤ (238254289649/2500000000000 : ℝ)^4007
        have hw : |(-307554849/2000000000 : ℝ)|=(307554849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5112923977/10000000000 : ℝ)|^5031 ≤ (10768593469209/25000000000000 : ℝ)^4007
        have hw : |(5112923977/10000000000 : ℝ)|=(5112923977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2758713643/5000000000 : ℝ)|^5031 ≤ (23697727259583/50000000000000 : ℝ)^4007
        have hw : |(2758713643/5000000000 : ℝ)|=(2758713643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s1_5 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131298919/250000000 : ℝ)*x 0 + (-134493011/1000000000 : ℝ)*x 1 + (1379357051/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131298919/250000000 : ℝ)^5031 ≤ (44550074166789/100000000000000 : ℝ)^4007 := by
    have hnat : (131298919 : ℕ)^5031*100000000000000^4007 ≤ 44550074166789^4007*250000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131298919 250000000 44550074166789 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134493011/1000000000 : ℝ)^5031 ≤ (8054461401801/100000000000000 : ℝ)^4007 := by
    have hnat : (134493011 : ℕ)^5031*100000000000000^4007 ≤ 8054461401801^4007*1000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134493011 1000000000 8054461401801 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379357051/2500000000 : ℝ)^5031 ≤ (9479092884027/20000000000000 : ℝ)^4007 := by
    have hnat : (1379357051 : ℕ)^5031*20000000000000^4007 ≤ 9479092884027^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379357051 2500000000 9479092884027 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131298919/250000000 : ℝ), (-134493011/1000000000 : ℝ), (1379357051/2500000000 : ℝ)] ![(44550074166789/100000000000000 : ℝ), (8054461401801/100000000000000 : ℝ), (9479092884027/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131298919/250000000 : ℝ)|^5031 ≤ (44550074166789/100000000000000 : ℝ)^4007
        have hw : |(131298919/250000000 : ℝ)|=(131298919/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134493011/1000000000 : ℝ)|^5031 ≤ (8054461401801/100000000000000 : ℝ)^4007
        have hw : |(-134493011/1000000000 : ℝ)|=(134493011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1379357051/2500000000 : ℝ)|^5031 ≤ (9479092884027/20000000000000 : ℝ)^4007
        have hw : |(1379357051/2500000000 : ℝ)|=(1379357051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s1_6 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251958217/10000000000 : ℝ)*x 0 + (5517427777/10000000000 : ℝ)*x 1 + (-672464329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251958217/10000000000 : ℝ)^5031 ≤ (11137522421073/25000000000000 : ℝ)^4007 := by
    have hnat : (5251958217 : ℕ)^5031*25000000000000^4007 ≤ 11137522421073^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251958217 10000000000 11137522421073 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5517427777/10000000000 : ℝ)^5031 ≤ (23697729907391/50000000000000 : ℝ)^4007 := by
    have hnat : (5517427777 : ℕ)^5031*50000000000000^4007 ≤ 23697729907391^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517427777 10000000000 23697729907391 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672464329/5000000000 : ℝ)^5031 ≤ (8054450483921/100000000000000 : ℝ)^4007 := by
    have hnat : (672464329 : ℕ)^5031*100000000000000^4007 ≤ 8054450483921^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672464329 5000000000 8054450483921 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251958217/10000000000 : ℝ), (5517427777/10000000000 : ℝ), (-672464329/5000000000 : ℝ)] ![(11137522421073/25000000000000 : ℝ), (23697729907391/50000000000000 : ℝ), (8054450483921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251958217/10000000000 : ℝ)|^5031 ≤ (11137522421073/25000000000000 : ℝ)^4007
        have hw : |(5251958217/10000000000 : ℝ)|=(5251958217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5517427777/10000000000 : ℝ)|^5031 ≤ (23697729907391/50000000000000 : ℝ)^4007
        have hw : |(5517427777/10000000000 : ℝ)|=(5517427777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-672464329/5000000000 : ℝ)|^5031 ≤ (8054450483921/100000000000000 : ℝ)^4007
        have hw : |(-672464329/5000000000 : ℝ)|=(672464329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s1_7 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4145834429/10000000000 : ℝ)*x 0 + (4712112373/10000000000 : ℝ)*x 1 + (362988637/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4145834429/10000000000 : ℝ)^5031 ≤ (8276212502923/25000000000000 : ℝ)^4007 := by
    have hnat : (4145834429 : ℕ)^5031*25000000000000^4007 ≤ 8276212502923^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145834429 10000000000 8276212502923 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4712112373/10000000000 : ℝ)^5031 ≤ (9719523959491/25000000000000 : ℝ)^4007 := by
    have hnat : (4712112373 : ℕ)^5031*25000000000000^4007 ≤ 9719523959491^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4712112373 10000000000 9719523959491 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (362988637/1000000000 : ℝ)^5031 ≤ (2801705413507/10000000000000 : ℝ)^4007 := by
    have hnat : (362988637 : ℕ)^5031*10000000000000^4007 ≤ 2801705413507^4007*1000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362988637 1000000000 2801705413507 10000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4145834429/10000000000 : ℝ), (4712112373/10000000000 : ℝ), (362988637/1000000000 : ℝ)] ![(8276212502923/25000000000000 : ℝ), (9719523959491/25000000000000 : ℝ), (2801705413507/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4145834429/10000000000 : ℝ)|^5031 ≤ (8276212502923/25000000000000 : ℝ)^4007
        have hw : |(4145834429/10000000000 : ℝ)|=(4145834429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4712112373/10000000000 : ℝ)|^5031 ≤ (9719523959491/25000000000000 : ℝ)^4007
        have hw : |(4712112373/10000000000 : ℝ)|=(4712112373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(362988637/1000000000 : ℝ)|^5031 ≤ (2801705413507/10000000000000 : ℝ)^4007
        have hw : |(362988637/1000000000 : ℝ)|=(362988637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1676_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11593/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (619/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (4571/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8977/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11593/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (619/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11593/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (619/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11593/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (619/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11593/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (619/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11593/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (619/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11593/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (619/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (619/12500 : ℝ) ^ (5023/1024 : ℝ) ≤ (39586045884461/100000000000000000000 : ℝ) := by
    have hpowers : (619/12500 : ℝ)^5023 ≤ (39586045884461/100000000000000000000 : ℝ)^1024 := by
      have hnat : (619 : ℕ)^5023*100000000000000000000^1024 ≤ 39586045884461^1024*12500^5023 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        619 12500 39586045884461 100000000000000000000 5023 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (619/12500 : ℝ)) (X := (39586045884461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11593/50000 : ℝ) ^ (5023/1024 : ℝ) ≤ (76958949800187489/100000000000000000000 : ℝ) := by
    have hpowers : (11593/50000 : ℝ)^5023 ≤ (76958949800187489/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11593 : ℕ)^5023*100000000000000000000^1024 ≤ 76958949800187489^1024*50000^5023 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11593 50000 76958949800187489 100000000000000000000 5023 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11593/50000 : ℝ)) (X := (76958949800187489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000039586045884461/50000000000000000000 : ℝ) ≤ (10000001614019439/10000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (50000039586045884461/50000000000000000000 : ℝ)^1024 ≤ (10000001614019439/10000000000000000 : ℝ)^5023 := by
      have hnat : (50000039586045884461 : ℕ)^1024*10000000000000000^5023 ≤ 10000001614019439^5023*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000039586045884461 50000000000000000000 10000001614019439 10000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001614019439/10000000000000000 : ℝ)) (X := (50000039586045884461/50000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2001539970716921439/2000000000000000000 : ℝ) ≤ (10001569228445557/10000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (2001539970716921439/2000000000000000000 : ℝ)^1024 ≤ (10001569228445557/10000000000000000 : ℝ)^5023 := by
      have hnat : (2001539970716921439 : ℕ)^1024*10000000000000000^5023 ≤ 10001569228445557^5023*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001539970716921439 2000000000000000000 10001569228445557 10000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001569228445557/10000000000000000 : ℝ)) (X := (2001539970716921439/2000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50076958949800187489/50000000000000000000 : ℝ) ≤ (400125473714867/400000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (50076958949800187489/50000000000000000000 : ℝ)^1024 ≤ (400125473714867/400000000000000 : ℝ)^5023 := by
      have hnat : (50076958949800187489 : ℕ)^1024*400000000000000^5023 ≤ 400125473714867^5023*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50076958949800187489 50000000000000000000 400125473714867 400000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400125473714867/400000000000000 : ℝ)) (X := (50076958949800187489/50000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(39586045884461/100000000000000000000 : ℝ) ≤ ((91162251888377089027/91170000000000000000 : ℝ)+2*(783807213059/911700000000000 : ℝ)*(619/12500 : ℝ))^(5023/1024 : ℝ) := by
    rw [show (91162251888377089027/91170000000000000000 : ℝ)+2*(783807213059/911700000000000 : ℝ)*(619/12500 : ℝ)=(10000001614019439/10000000000000000 : ℝ) by norm_num, show 1+2*(39586045884461/100000000000000000000 : ℝ)=(50000039586045884461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(76958949800187489/100000000000000000000 : ℝ)+(39586045884461/100000000000000000000 : ℝ) ≤ ((91162251888377089027/91170000000000000000 : ℝ)+(783807213059/911700000000000 : ℝ)*((11593/50000 : ℝ)+(619/12500 : ℝ)))^(5023/1024 : ℝ) := by
    rw [show (91162251888377089027/91170000000000000000 : ℝ)+(783807213059/911700000000000 : ℝ)*((11593/50000 : ℝ)+(619/12500 : ℝ))=(10001569228445557/10000000000000000 : ℝ) by norm_num, show 1+(76958949800187489/100000000000000000000 : ℝ)+(39586045884461/100000000000000000000 : ℝ)=(2001539970716921439/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(76958949800187489/100000000000000000000 : ℝ) ≤ ((91162251888377089027/91170000000000000000 : ℝ)+2*(783807213059/911700000000000 : ℝ)*(11593/50000 : ℝ))^(5023/1024 : ℝ) := by
    rw [show (91162251888377089027/91170000000000000000 : ℝ)+2*(783807213059/911700000000000 : ℝ)*(11593/50000 : ℝ)=(400125473714867/400000000000000 : ℝ) by norm_num, show 1+2*(76958949800187489/100000000000000000000 : ℝ)=(50076958949800187489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (91162251888377089027/91170000000000000000 : ℝ)*(X 1 0+X 2 0)+(783807213059/911700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (619/12500 : ℝ)) (hi := (11593/50000 : ℝ)) (c := (91162251888377089027/91170000000000000000 : ℝ)) (alpha := (783807213059/911700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (91162251888377089027/91170000000000000000 : ℝ)*(X 0 1+X 2 1)+(783807213059/911700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (619/12500 : ℝ)) (hi := (11593/50000 : ℝ)) (c := (91162251888377089027/91170000000000000000 : ℝ)) (alpha := (783807213059/911700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (91162251888377089027/91170000000000000000 : ℝ)*(X 0 2+X 1 2)+(783807213059/911700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (619/12500 : ℝ)) (hi := (11593/50000 : ℝ)) (c := (91162251888377089027/91170000000000000000 : ℝ)) (alpha := (783807213059/911700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1537512143/10000000000 : ℝ)*X 0 0+(552264337/1000000000 : ℝ)*X 0 1+(5107796911/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335173323/625000000 : ℝ)*X 1 0+(-877279247/5000000000 : ℝ)*X 1 1+(5107796891/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5362772751/10000000000 : ℝ)*X 2 0+(319237331/625000000 : ℝ)*X 2 1+(-1754558517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4145134809/10000000000 : ℝ)*X 0 0+(723186363/2000000000 : ℝ)*X 0 1+(2362916157/5000000000 : ℝ)*X 0 2+(4145134809/10000000000 : ℝ)*X 1 0+(723186363/2000000000 : ℝ)*X 1 1+(2362916157/5000000000 : ℝ)*X 1 2+(4145134809/10000000000 : ℝ)*X 2 0+(723186363/2000000000 : ℝ)*X 2 1+(2362916157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-307554849/2000000000 : ℝ)*X 0 0+(5112923977/10000000000 : ℝ)*X 0 1+(2758713643/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((131298919/250000000 : ℝ)*X 1 0+(-134493011/1000000000 : ℝ)*X 1 1+(1379357051/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251958217/10000000000 : ℝ)*X 2 0+(5517427777/10000000000 : ℝ)*X 2 1+(-672464329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4145834429/10000000000 : ℝ)*X 0 0+(4712112373/10000000000 : ℝ)*X 0 1+(362988637/1000000000 : ℝ)*X 0 2+(4145834429/10000000000 : ℝ)*X 1 0+(4712112373/10000000000 : ℝ)*X 1 1+(362988637/1000000000 : ℝ)*X 1 2+(4145834429/10000000000 : ℝ)*X 2 0+(4712112373/10000000000 : ℝ)*X 2 1+(362988637/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (711553421114579876113946119/60780000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7052723/100000000000000 : ℝ)*(base1) + (1774813193/100000000000000 : ℝ)*(base19) + (1587372277/100000000000000 : ℝ)*(base23) + (128620653/50000000000000 : ℝ)*(upper3) + (107462951/50000000000000 : ℝ)*(upper5) + (66231074728403/4000000000000 : ℝ)*(major0) + (66231074728403/4000000000000 : ℝ)*(major1) + (66231074728403/4000000000000 : ℝ)*(major2) + (1205272952691747/50000000000000 : ℝ)*(sp0) + (1205279417290563/50000000000000 : ℝ)*(sp1) + (1205279511011021/50000000000000 : ℝ)*(sp2) + (112623388750607/12500000000000 : ℝ)*(sp3) + (14711063547/100000000000000 : ℝ)*(sp4) + (1123946767/20000000000000 : ℝ)*(sp7) + (450496368395707/50000000000000 : ℝ)*(f.failure) + (2410560609394319/100000000000000 : ℝ)*(f.sum) + (1387786882369/9117000000000000000000000000 : ℝ)*base66 + (403686970746104627/121560000000000000000000000000000 : ℝ)*base67 + (494475160997144627/121560000000000000000000000000000 : ℝ)*base69 + (3896845421024627/121560000000000000000000000000000 : ℝ)*base71 + (1869684841159/4558500000000000000000000000 : ℝ)*base73 + (561485258084744627/121560000000000000000000000000000 : ℝ)*base75 + (327591242042415373/121560000000000000000000000000000 : ℝ)*base78 + (22562832897375373/121560000000000000000000000000000 : ℝ)*base80 + (3981048629291/1823400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (53738207/5000000000000000000000 : ℝ)*base90 + (53738207/5000000000000000000000 : ℝ)*base92 + (53738207/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3610185523913629492417/1266250000000000000000000000 : ℝ) := by norm_num
    linear_combination (76697309/100000000000000 : ℝ)*(base15) + (79090483/100000000000000 : ℝ)*(lower2) + (11539289/6250000000000 : ℝ)*(upper3) + (33962733/12500000000000 : ℝ)*(upper4) + (383301289/100000000000000 : ℝ)*(upper5) + (424524933916703/25000000000000 : ℝ)*(major0) + (424524933916703/25000000000000 : ℝ)*(major1) + (424524933916703/25000000000000 : ℝ)*(major2) + (304703163/12500000000000 : ℝ)*(sp2) + (88298483/20000000000000 : ℝ)*(sp3) + (1236088303173553/50000000000000 : ℝ)*(sp4) + (2472176529649797/100000000000000 : ℝ)*(sp5) + (1236087084360901/50000000000000 : ℝ)*(sp6) + (924022328457953/100000000000000 : ℝ)*(sp7) + (28875711560949/3125000000000 : ℝ)*(f.failure) + (1236088303173553/50000000000000 : ℝ)*(f.sum) + (172516506032131/22792500000000000000000000000 : ℝ)*base66 + (3022895343735660673/759750000000000000000000000000000 : ℝ)*base68 + (5106917689290660673/759750000000000000000000000000000 : ℝ)*base70 + (5265506843663339327/759750000000000000000000000000000 : ℝ)*base71 + (61931765594033/11396250000000000000000000000 : ℝ)*base74 + (3418130489057339327/759750000000000000000000000000000 : ℝ)*base75 + (8450609860862160673/759750000000000000000000000000000 : ℝ)*base78 + (2507544036398339327/759750000000000000000000000000000 : ℝ)*base79 + (34943373549769/5698125000000000000000000000 : ℝ)*base82 + (1041551/312500000000000000000 : ℝ)*base89 + (1041551/312500000000000000000 : ℝ)*base91 + (1041551/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1676_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11593/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (619/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8977/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1676_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1676_s2_0 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1544636953/10000000000 : ℝ)*x 0 + (5494666271/10000000000 : ℝ)*x 1 + (641382559/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1544636953/10000000000 : ℝ)^5031 ≤ (9583601679937/100000000000000 : ℝ)^4007 := by
    have hnat : (1544636953 : ℕ)^5031*100000000000000^4007 ≤ 9583601679937^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1544636953 10000000000 9583601679937 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5494666271/10000000000 : ℝ)^5031 ≤ (2946881130163/6250000000000 : ℝ)^4007 := by
    have hnat : (5494666271 : ℕ)^5031*6250000000000^4007 ≤ 2946881130163^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494666271 10000000000 2946881130163 6250000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641382559/1250000000 : ℝ)^5031 ≤ (8653260044863/20000000000000 : ℝ)^4007 := by
    have hnat : (641382559 : ℕ)^5031*20000000000000^4007 ≤ 8653260044863^4007*1250000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641382559 1250000000 8653260044863 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1544636953/10000000000 : ℝ), (5494666271/10000000000 : ℝ), (641382559/1250000000 : ℝ)] ![(9583601679937/100000000000000 : ℝ), (2946881130163/6250000000000 : ℝ), (8653260044863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1544636953/10000000000 : ℝ)|^5031 ≤ (9583601679937/100000000000000 : ℝ)^4007
        have hw : |(-1544636953/10000000000 : ℝ)|=(1544636953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5494666271/10000000000 : ℝ)|^5031 ≤ (2946881130163/6250000000000 : ℝ)^4007
        have hw : |(5494666271/10000000000 : ℝ)|=(5494666271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(641382559/1250000000 : ℝ)|^5031 ≤ (8653260044863/20000000000000 : ℝ)^4007
        have hw : |(641382559/1250000000 : ℝ)|=(641382559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s2_1 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071067671/2000000000 : ℝ)*x 0 + (-866915807/5000000000 : ℝ)*x 1 + (5131060057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071067671/2000000000 : ℝ)^5031 ≤ (45653876180693/100000000000000 : ℝ)^4007 := by
    have hnat : (1071067671 : ℕ)^5031*100000000000000^4007 ≤ 45653876180693^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071067671 2000000000 45653876180693 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (866915807/5000000000 : ℝ)^5031 ≤ (2769956993919/25000000000000 : ℝ)^4007 := by
    have hnat : (866915807 : ℕ)^5031*25000000000000^4007 ≤ 2769956993919^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866915807 5000000000 2769956993919 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5131060057/10000000000 : ℝ)^5031 ≤ (43266295830663/100000000000000 : ℝ)^4007 := by
    have hnat : (5131060057 : ℕ)^5031*100000000000000^4007 ≤ 43266295830663^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131060057 10000000000 43266295830663 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071067671/2000000000 : ℝ), (-866915807/5000000000 : ℝ), (5131060057/10000000000 : ℝ)] ![(45653876180693/100000000000000 : ℝ), (2769956993919/25000000000000 : ℝ), (43266295830663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071067671/2000000000 : ℝ)|^5031 ≤ (45653876180693/100000000000000 : ℝ)^4007
        have hw : |(1071067671/2000000000 : ℝ)|=(1071067671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-866915807/5000000000 : ℝ)|^5031 ≤ (2769956993919/25000000000000 : ℝ)^4007
        have hw : |(-866915807/5000000000 : ℝ)|=(866915807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5131060057/10000000000 : ℝ)|^5031 ≤ (43266295830663/100000000000000 : ℝ)^4007
        have hw : |(5131060057/10000000000 : ℝ)|=(5131060057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s2_2 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355337669/10000000000 : ℝ)*x 0 + (256553049/500000000 : ℝ)*x 1 + (-1733831311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355337669/10000000000 : ℝ)^5031 ≤ (22826934419047/50000000000000 : ℝ)^4007 := by
    have hnat : (5355337669 : ℕ)^5031*50000000000000^4007 ≤ 22826934419047^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355337669 10000000000 22826934419047 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256553049/500000000 : ℝ)^5031 ≤ (43266305602569/100000000000000 : ℝ)^4007 := by
    have hnat : (256553049 : ℕ)^5031*100000000000000^4007 ≤ 43266305602569^4007*500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256553049 500000000 43266305602569 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1733831311/10000000000 : ℝ)^5031 ≤ (11079825544571/100000000000000 : ℝ)^4007 := by
    have hnat : (1733831311 : ℕ)^5031*100000000000000^4007 ≤ 11079825544571^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733831311 10000000000 11079825544571 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355337669/10000000000 : ℝ), (256553049/500000000 : ℝ), (-1733831311/10000000000 : ℝ)] ![(22826934419047/50000000000000 : ℝ), (43266305602569/100000000000000 : ℝ), (11079825544571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355337669/10000000000 : ℝ)|^5031 ≤ (22826934419047/50000000000000 : ℝ)^4007
        have hw : |(5355337669/10000000000 : ℝ)|=(5355337669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256553049/500000000 : ℝ)|^5031 ≤ (43266305602569/100000000000000 : ℝ)^4007
        have hw : |(256553049/500000000 : ℝ)|=(256553049/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1733831311/10000000000 : ℝ)|^5031 ≤ (11079825544571/100000000000000 : ℝ)^4007
        have hw : |(-1733831311/10000000000 : ℝ)|=(1733831311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s2_3 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4150580749/10000000000 : ℝ)*x 0 + (147358089/400000000 : ℝ)*x 1 + (4656760757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4150580749/10000000000 : ℝ)^5031 ≤ (33152442144563/100000000000000 : ℝ)^4007 := by
    have hnat : (4150580749 : ℕ)^5031*100000000000000^4007 ≤ 33152442144563^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150580749 10000000000 33152442144563 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147358089/400000000 : ℝ)^5031 ≤ (7135498699821/25000000000000 : ℝ)^4007 := by
    have hnat : (147358089 : ℕ)^5031*25000000000000^4007 ≤ 7135498699821^4007*400000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147358089 400000000 7135498699821 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4656760757/10000000000 : ℝ)^5031 ≤ (957639075973/2500000000000 : ℝ)^4007 := by
    have hnat : (4656760757 : ℕ)^5031*2500000000000^4007 ≤ 957639075973^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4656760757 10000000000 957639075973 2500000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4150580749/10000000000 : ℝ), (147358089/400000000 : ℝ), (4656760757/10000000000 : ℝ)] ![(33152442144563/100000000000000 : ℝ), (7135498699821/25000000000000 : ℝ), (957639075973/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4150580749/10000000000 : ℝ)|^5031 ≤ (33152442144563/100000000000000 : ℝ)^4007
        have hw : |(4150580749/10000000000 : ℝ)|=(4150580749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(147358089/400000000 : ℝ)|^5031 ≤ (7135498699821/25000000000000 : ℝ)^4007
        have hw : |(147358089/400000000 : ℝ)|=(147358089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4656760757/10000000000 : ℝ)|^5031 ≤ (957639075973/2500000000000 : ℝ)^4007
        have hw : |(4656760757/10000000000 : ℝ)|=(4656760757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s2_4 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-772406237/5000000000 : ℝ)*x 0 + (5135004417/10000000000 : ℝ)*x 1 + (5490663067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (772406237/5000000000 : ℝ)^5031 ≤ (1198121125989/12500000000000 : ℝ)^4007 := by
    have hnat : (772406237 : ℕ)^5031*12500000000000^4007 ≤ 1198121125989^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772406237 5000000000 1198121125989 12500000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5135004417/10000000000 : ℝ)^5031 ≤ (10827014830233/25000000000000 : ℝ)^4007 := by
    have hnat : (5135004417 : ℕ)^5031*25000000000000^4007 ≤ 10827014830233^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135004417 10000000000 10827014830233 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490663067/10000000000 : ℝ)^5031 ≤ (9421394329931/20000000000000 : ℝ)^4007 := by
    have hnat : (5490663067 : ℕ)^5031*20000000000000^4007 ≤ 9421394329931^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490663067 10000000000 9421394329931 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-772406237/5000000000 : ℝ), (5135004417/10000000000 : ℝ), (5490663067/10000000000 : ℝ)] ![(1198121125989/12500000000000 : ℝ), (10827014830233/25000000000000 : ℝ), (9421394329931/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-772406237/5000000000 : ℝ)|^5031 ≤ (1198121125989/12500000000000 : ℝ)^4007
        have hw : |(-772406237/5000000000 : ℝ)|=(772406237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5135004417/10000000000 : ℝ)|^5031 ≤ (10827014830233/25000000000000 : ℝ)^4007
        have hw : |(5135004417/10000000000 : ℝ)|=(5135004417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490663067/10000000000 : ℝ)|^5031 ≤ (9421394329931/20000000000000 : ℝ)^4007
        have hw : |(5490663067/10000000000 : ℝ)|=(5490663067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s2_5 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314575283/2500000000 : ℝ)*x 0 + (-1374228819/10000000000 : ℝ)*x 1 + (2745331531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314575283/2500000000 : ℝ)^5031 ≤ (44617654124251/100000000000000 : ℝ)^4007 := by
    have hnat : (1314575283 : ℕ)^5031*100000000000000^4007 ≤ 44617654124251^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314575283 2500000000 44617654124251 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374228819/10000000000 : ℝ)^5031 ≤ (1034421782431/12500000000000 : ℝ)^4007 := by
    have hnat : (1374228819 : ℕ)^5031*12500000000000^4007 ≤ 1034421782431^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374228819 10000000000 1034421782431 12500000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745331531/5000000000 : ℝ)^5031 ≤ (11776742898949/25000000000000 : ℝ)^4007 := by
    have hnat : (2745331531 : ℕ)^5031*25000000000000^4007 ≤ 11776742898949^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745331531 5000000000 11776742898949 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314575283/2500000000 : ℝ), (-1374228819/10000000000 : ℝ), (2745331531/5000000000 : ℝ)] ![(44617654124251/100000000000000 : ℝ), (1034421782431/12500000000000 : ℝ), (11776742898949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314575283/2500000000 : ℝ)|^5031 ≤ (44617654124251/100000000000000 : ℝ)^4007
        have hw : |(1314575283/2500000000 : ℝ)|=(1314575283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1374228819/10000000000 : ℝ)|^5031 ≤ (1034421782431/12500000000000 : ℝ)^4007
        have hw : |(-1374228819/10000000000 : ℝ)|=(1374228819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745331531/5000000000 : ℝ)|^5031 ≤ (11776742898949/25000000000000 : ℝ)^4007
        have hw : |(2745331531/5000000000 : ℝ)|=(2745331531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s2_6 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328643821/625000000 : ℝ)*x 0 + (5490663059/10000000000 : ℝ)*x 1 + (-687114409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328643821/625000000 : ℝ)^5031 ≤ (22308827083433/50000000000000 : ℝ)^4007 := by
    have hnat : (328643821 : ℕ)^5031*50000000000000^4007 ≤ 22308827083433^4007*625000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328643821 625000000 22308827083433 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490663059/10000000000 : ℝ)^5031 ≤ (1177674289087/2500000000000 : ℝ)^4007 := by
    have hnat : (5490663059 : ℕ)^5031*2500000000000^4007 ≤ 1177674289087^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490663059 10000000000 1177674289087 2500000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687114409/5000000000 : ℝ)^5031 ≤ (8275374251887/100000000000000 : ℝ)^4007 := by
    have hnat : (687114409 : ℕ)^5031*100000000000000^4007 ≤ 8275374251887^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687114409 5000000000 8275374251887 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328643821/625000000 : ℝ), (5490663059/10000000000 : ℝ), (-687114409/5000000000 : ℝ)] ![(22308827083433/50000000000000 : ℝ), (1177674289087/2500000000000 : ℝ), (8275374251887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328643821/625000000 : ℝ)|^5031 ≤ (22308827083433/50000000000000 : ℝ)^4007
        have hw : |(328643821/625000000 : ℝ)|=(328643821/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490663059/10000000000 : ℝ)|^5031 ≤ (1177674289087/2500000000000 : ℝ)^4007
        have hw : |(5490663059/10000000000 : ℝ)|=(5490663059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-687114409/5000000000 : ℝ)|^5031 ≤ (8275374251887/100000000000000 : ℝ)^4007
        have hw : |(-687114409/5000000000 : ℝ)|=(687114409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s2_7 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103776269/250000000 : ℝ)*x 0 + (2323104819/5000000000 : ℝ)*x 1 + (3694662713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103776269/250000000 : ℝ)^5031 ≤ (33157155779447/100000000000000 : ℝ)^4007 := by
    have hnat : (103776269 : ℕ)^5031*100000000000000^4007 ≤ 33157155779447^4007*250000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103776269 250000000 33157155779447 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2323104819/5000000000 : ℝ)^5031 ≤ (9549155870921/25000000000000 : ℝ)^4007 := by
    have hnat : (2323104819 : ℕ)^5031*25000000000000^4007 ≤ 9549155870921^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323104819 5000000000 9549155870921 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3694662713/10000000000 : ℝ)^5031 ≤ (28646220723887/100000000000000 : ℝ)^4007 := by
    have hnat : (3694662713 : ℕ)^5031*100000000000000^4007 ≤ 28646220723887^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3694662713 10000000000 28646220723887 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103776269/250000000 : ℝ), (2323104819/5000000000 : ℝ), (3694662713/10000000000 : ℝ)] ![(33157155779447/100000000000000 : ℝ), (9549155870921/25000000000000 : ℝ), (28646220723887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103776269/250000000 : ℝ)|^5031 ≤ (33157155779447/100000000000000 : ℝ)^4007
        have hw : |(103776269/250000000 : ℝ)|=(103776269/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2323104819/5000000000 : ℝ)|^5031 ≤ (9549155870921/25000000000000 : ℝ)^4007
        have hw : |(2323104819/5000000000 : ℝ)|=(2323104819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3694662713/10000000000 : ℝ)|^5031 ≤ (28646220723887/100000000000000 : ℝ)^4007
        have hw : |(3694662713/10000000000 : ℝ)|=(3694662713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1676_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8977/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (603/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17371/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8977/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4571/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8977/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4571/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8977/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4571/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8977/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4571/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8977/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4571/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8977/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4571/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4571/50000 : ℝ) ^ (5023/1024 : ℝ) ≤ (800982594456549/100000000000000000000 : ℝ) := by
    have hpowers : (4571/50000 : ℝ)^5023 ≤ (800982594456549/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4571 : ℕ)^5023*100000000000000000000^1024 ≤ 800982594456549^1024*50000^5023 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4571 50000 800982594456549 100000000000000000000 5023 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4571/50000 : ℝ)) (X := (800982594456549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8977/50000 : ℝ) ^ (5023/1024 : ℝ) ≤ (2195112829189739/10000000000000000000 : ℝ) := by
    have hpowers : (8977/50000 : ℝ)^5023 ≤ (2195112829189739/10000000000000000000 : ℝ)^1024 := by
      have hnat : (8977 : ℕ)^5023*10000000000000000000^1024 ≤ 2195112829189739^1024*50000^5023 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8977 50000 2195112829189739 10000000000000000000 5023 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8977/50000 : ℝ)) (X := (2195112829189739/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000800982594456549/50000000000000000000 : ℝ) ≤ (10000032657811921/10000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (50000800982594456549/50000000000000000000 : ℝ)^1024 ≤ (10000032657811921/10000000000000000 : ℝ)^5023 := by
      have hnat : (50000800982594456549 : ℕ)^1024*10000000000000000^5023 ≤ 10000032657811921^5023*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000800982594456549 50000000000000000000 10000032657811921 10000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000032657811921/10000000000000000 : ℝ)) (X := (50000800982594456549/50000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022752110886353939/100000000000000000000 : ℝ) ≤ (2500115946902957/2500000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (100022752110886353939/100000000000000000000 : ℝ)^1024 ≤ (2500115946902957/2500000000000000 : ℝ)^5023 := by
      have hnat : (100022752110886353939 : ℕ)^1024*2500000000000000^5023 ≤ 2500115946902957^5023*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022752110886353939 100000000000000000000 2500115946902957 2500000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500115946902957/2500000000000000 : ℝ)) (X := (100022752110886353939/100000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002195112829189739/5000000000000000000 : ℝ) ≤ (2000178983482347/2000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (5002195112829189739/5000000000000000000 : ℝ)^1024 ≤ (2000178983482347/2000000000000000 : ℝ)^5023 := by
      have hnat : (5002195112829189739 : ℕ)^1024*2000000000000000^5023 ≤ 2000178983482347^5023*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002195112829189739 5000000000000000000 2000178983482347 2000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000178983482347/2000000000000000 : ℝ)) (X := (5002195112829189739/5000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(800982594456549/100000000000000000000 : ℝ) ≤ ((11014050625422143533/11015000000000000000 : ℝ)+2*(431129799907/881200000000000 : ℝ)*(4571/50000 : ℝ))^(5023/1024 : ℝ) := by
    rw [show (11014050625422143533/11015000000000000000 : ℝ)+2*(431129799907/881200000000000 : ℝ)*(4571/50000 : ℝ)=(10000032657811921/10000000000000000 : ℝ) by norm_num, show 1+2*(800982594456549/100000000000000000000 : ℝ)=(50000800982594456549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2195112829189739/10000000000000000000 : ℝ)+(800982594456549/100000000000000000000 : ℝ) ≤ ((11014050625422143533/11015000000000000000 : ℝ)+(431129799907/881200000000000 : ℝ)*((8977/50000 : ℝ)+(4571/50000 : ℝ)))^(5023/1024 : ℝ) := by
    rw [show (11014050625422143533/11015000000000000000 : ℝ)+(431129799907/881200000000000 : ℝ)*((8977/50000 : ℝ)+(4571/50000 : ℝ))=(2500115946902957/2500000000000000 : ℝ) by norm_num, show 1+(2195112829189739/10000000000000000000 : ℝ)+(800982594456549/100000000000000000000 : ℝ)=(100022752110886353939/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2195112829189739/10000000000000000000 : ℝ) ≤ ((11014050625422143533/11015000000000000000 : ℝ)+2*(431129799907/881200000000000 : ℝ)*(8977/50000 : ℝ))^(5023/1024 : ℝ) := by
    rw [show (11014050625422143533/11015000000000000000 : ℝ)+2*(431129799907/881200000000000 : ℝ)*(8977/50000 : ℝ)=(2000178983482347/2000000000000000 : ℝ) by norm_num, show 1+2*(2195112829189739/10000000000000000000 : ℝ)=(5002195112829189739/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11014050625422143533/11015000000000000000 : ℝ)*(X 1 0+X 2 0)+(431129799907/881200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (4571/50000 : ℝ)) (hi := (8977/50000 : ℝ)) (c := (11014050625422143533/11015000000000000000 : ℝ)) (alpha := (431129799907/881200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11014050625422143533/11015000000000000000 : ℝ)*(X 0 1+X 2 1)+(431129799907/881200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (4571/50000 : ℝ)) (hi := (8977/50000 : ℝ)) (c := (11014050625422143533/11015000000000000000 : ℝ)) (alpha := (431129799907/881200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11014050625422143533/11015000000000000000 : ℝ)*(X 0 2+X 1 2)+(431129799907/881200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (4571/50000 : ℝ)) (hi := (8977/50000 : ℝ)) (c := (11014050625422143533/11015000000000000000 : ℝ)) (alpha := (431129799907/881200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1544636953/10000000000 : ℝ)*X 0 0+(5494666271/10000000000 : ℝ)*X 0 1+(641382559/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071067671/2000000000 : ℝ)*X 1 0+(-866915807/5000000000 : ℝ)*X 1 1+(5131060057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355337669/10000000000 : ℝ)*X 2 0+(256553049/500000000 : ℝ)*X 2 1+(-1733831311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4150580749/10000000000 : ℝ)*X 0 0+(147358089/400000000 : ℝ)*X 0 1+(4656760757/10000000000 : ℝ)*X 0 2+(4150580749/10000000000 : ℝ)*X 1 0+(147358089/400000000 : ℝ)*X 1 1+(4656760757/10000000000 : ℝ)*X 1 2+(4150580749/10000000000 : ℝ)*X 2 0+(147358089/400000000 : ℝ)*X 2 1+(4656760757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-772406237/5000000000 : ℝ)*X 0 0+(5135004417/10000000000 : ℝ)*X 0 1+(5490663067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1314575283/2500000000 : ℝ)*X 1 0+(-1374228819/10000000000 : ℝ)*X 1 1+(2745331531/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328643821/625000000 : ℝ)*X 2 0+(5490663059/10000000000 : ℝ)*X 2 1+(-687114409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((103776269/250000000 : ℝ)*X 0 0+(2323104819/5000000000 : ℝ)*X 0 1+(3694662713/10000000000 : ℝ)*X 0 2+(103776269/250000000 : ℝ)*X 1 0+(2323104819/5000000000 : ℝ)*X 1 1+(3694662713/10000000000 : ℝ)*X 1 2+(103776269/250000000 : ℝ)*X 2 0+(2323104819/5000000000 : ℝ)*X 2 1+(3694662713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (860807846104152407785362159/137687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158145647/12500000000000 : ℝ)*(base19) + (894640223/100000000000000 : ℝ)*(base23) + (32559867/25000000000000 : ℝ)*(upper3) + (9761529/100000000000000 : ℝ)*(upper4) + (49031103/20000000000000 : ℝ)*(upper5) + (944552212186309/50000000000000 : ℝ)*(major0) + (944552212186309/50000000000000 : ℝ)*(major1) + (944552212186309/50000000000000 : ℝ)*(major2) + (2750240132343453/100000000000000 : ℝ)*(sp0) + (137512460077187/5000000000000 : ℝ)*(sp1) + (2750249572068693/100000000000000 : ℝ)*(sp2) + (1027955303279651/100000000000000 : ℝ)*(sp3) + (5167182731/50000000000000 : ℝ)*(sp4) + (2870360147/100000000000000 : ℝ)*(sp7) + (1027958173639799/100000000000000 : ℝ)*(f.failure) + (687562616677229/25000000000000 : ℝ)*(f.sum) + (84469835930603/22030000000000000000000000000 : ℝ)*base65 + (3415464039892777197/550750000000000000000000000000000 : ℝ)*base67 + (7570847064360277197/550750000000000000000000000000000 : ℝ)*base69 + (2704303508587027197/550750000000000000000000000000000 : ℝ)*base71 + (14380212165767/22030000000000000000000000000 : ℝ)*base74 + (5614411555302777197/550750000000000000000000000000000 : ℝ)*base75 + (4991926842549277197/550750000000000000000000000000000 : ℝ)*base77 + (375281967549472803/550750000000000000000000000000000 : ℝ)*base80 + (126525117540413/22030000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (11912299/10000000000000000000000 : ℝ)*base90 + (11912299/10000000000000000000000 : ℝ)*base92 + (11912299/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2814273218587011835381200471/275375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1500443403/100000000000000 : ℝ)*(base19) + (1621994111/100000000000000 : ℝ)*(base23) + (55146807/25000000000000 : ℝ)*(upper3) + (831623/1562500000000 : ℝ)*(lower4) + (1341941/625000000000 : ℝ)*(upper5) + (965651146723071/50000000000000 : ℝ)*(major0) + (965651146723071/50000000000000 : ℝ)*(major1) + (965651146723071/50000000000000 : ℝ)*(major2) + (1580240603/12500000000000 : ℝ)*(sp1) + (13627878223/100000000000000 : ℝ)*(sp2) + (5491570424681/195312500000 : ℝ)*(sp4) + (1405834957534223/50000000000000 : ℝ)*(sp5) + (1405834403782169/50000000000000 : ℝ)*(sp6) + (1050920188796117/100000000000000 : ℝ)*(sp7) + (1050920188796117/100000000000000 : ℝ)*(f.failure) + (5491570424681/195312500000 : ℝ)*(f.sum) + (61468199641363/22030000000000000000000000000 : ℝ)*base66 + (2054737240092012343/550750000000000000000000000000000 : ℝ)*base67 + (3073447081910762343/550750000000000000000000000000000 : ℝ)*base69 + (2198180939339487657/550750000000000000000000000000000 : ℝ)*base72 + (63622721629317/22030000000000000000000000000 : ℝ)*base73 + (2453496373586237657/550750000000000000000000000000000 : ℝ)*base76 + (212966892438262343/550750000000000000000000000000000 : ℝ)*base77 + (3028656961998512343/550750000000000000000000000000000 : ℝ)*base79 + (3504875128877/22030000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (22586383/10000000000000000000000 : ℝ)*base89 + (22586383/10000000000000000000000 : ℝ)*base91 + (22586383/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1676_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8977/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (603/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17371/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1676_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1676_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (603/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17371/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1676_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1676_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1676_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (603/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17371/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1676_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
