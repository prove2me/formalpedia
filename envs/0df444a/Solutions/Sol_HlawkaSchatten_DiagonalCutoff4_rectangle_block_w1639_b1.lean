-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1639_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:10:42.170039+00:00
-- url     : https://prove2.me/submissions/3fa28392-88c6-4b27-8889-3375781e17c9

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
theorem support_rectangle_w1639_s3_0 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1633873271/10000000000 : ℝ)*x 0 + (2725461891/5000000000 : ℝ)*x 1 + (5183043347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1633873271/10000000000 : ℝ)^4875 ≤ (10092743356217/100000000000000 : ℝ)^3851 := by
    have hnat : (1633873271 : ℕ)^4875*100000000000000^3851 ≤ 10092743356217^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633873271 10000000000 10092743356217 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725461891/5000000000 : ℝ)^4875 ≤ (46386991285841/100000000000000 : ℝ)^3851 := by
    have hnat : (2725461891 : ℕ)^4875*100000000000000^3851 ≤ 46386991285841^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725461891 5000000000 46386991285841 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183043347/10000000000 : ℝ)^4875 ≤ (43520265342307/100000000000000 : ℝ)^3851 := by
    have hnat : (5183043347 : ℕ)^4875*100000000000000^3851 ≤ 43520265342307^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183043347 10000000000 43520265342307 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1633873271/10000000000 : ℝ), (2725461891/5000000000 : ℝ), (5183043347/10000000000 : ℝ)] ![(10092743356217/100000000000000 : ℝ), (46386991285841/100000000000000 : ℝ), (43520265342307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1633873271/10000000000 : ℝ)|^4875 ≤ (10092743356217/100000000000000 : ℝ)^3851
        have hw : |(-1633873271/10000000000 : ℝ)|=(1633873271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725461891/5000000000 : ℝ)|^4875 ≤ (46386991285841/100000000000000 : ℝ)^3851
        have hw : |(2725461891/5000000000 : ℝ)|=(2725461891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183043347/10000000000 : ℝ)|^4875 ≤ (43520265342307/100000000000000 : ℝ)^3851
        have hw : |(5183043347/10000000000 : ℝ)|=(5183043347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s3_1 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349421733/10000000000 : ℝ)*x 0 + (-885920189/5000000000 : ℝ)*x 1 + (5183043493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349421733/10000000000 : ℝ)^4875 ≤ (11324063266823/25000000000000 : ℝ)^3851 := by
    have hnat : (5349421733 : ℕ)^4875*25000000000000^3851 ≤ 11324063266823^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349421733 10000000000 11324063266823 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (885920189/5000000000 : ℝ)^4875 ≤ (1397935003593/12500000000000 : ℝ)^3851 := by
    have hnat : (885920189 : ℕ)^4875*12500000000000^3851 ≤ 1397935003593^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885920189 5000000000 1397935003593 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183043493/10000000000 : ℝ)^4875 ≤ (10880066723549/25000000000000 : ℝ)^3851 := by
    have hnat : (5183043493 : ℕ)^4875*25000000000000^3851 ≤ 10880066723549^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183043493 10000000000 10880066723549 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349421733/10000000000 : ℝ), (-885920189/5000000000 : ℝ), (5183043493/10000000000 : ℝ)] ![(11324063266823/25000000000000 : ℝ), (1397935003593/12500000000000 : ℝ), (10880066723549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349421733/10000000000 : ℝ)|^4875 ≤ (11324063266823/25000000000000 : ℝ)^3851
        have hw : |(5349421733/10000000000 : ℝ)|=(5349421733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-885920189/5000000000 : ℝ)|^4875 ≤ (1397935003593/12500000000000 : ℝ)^3851
        have hw : |(-885920189/5000000000 : ℝ)|=(885920189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183043493/10000000000 : ℝ)|^4875 ≤ (10880066723549/25000000000000 : ℝ)^3851
        have hw : |(5183043493/10000000000 : ℝ)|=(5183043493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s3_2 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668677637/1250000000 : ℝ)*x 0 + (2591522107/5000000000 : ℝ)*x 1 + (-110740017/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668677637/1250000000 : ℝ)^4875 ≤ (45296246239253/100000000000000 : ℝ)^3851 := by
    have hnat : (668677637 : ℕ)^4875*100000000000000^3851 ≤ 45296246239253^3851*1250000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668677637 1250000000 45296246239253 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591522107/5000000000 : ℝ)^4875 ≤ (43520274557977/100000000000000 : ℝ)^3851 := by
    have hnat : (2591522107 : ℕ)^4875*100000000000000^3851 ≤ 43520274557977^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591522107 5000000000 43520274557977 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110740017/625000000 : ℝ)^4875 ≤ (11183479181791/100000000000000 : ℝ)^3851 := by
    have hnat : (110740017 : ℕ)^4875*100000000000000^3851 ≤ 11183479181791^3851*625000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110740017 625000000 11183479181791 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668677637/1250000000 : ℝ), (2591522107/5000000000 : ℝ), (-110740017/625000000 : ℝ)] ![(45296246239253/100000000000000 : ℝ), (43520274557977/100000000000000 : ℝ), (11183479181791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668677637/1250000000 : ℝ)|^4875 ≤ (45296246239253/100000000000000 : ℝ)^3851
        have hw : |(668677637/1250000000 : ℝ)|=(668677637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591522107/5000000000 : ℝ)|^4875 ≤ (43520274557977/100000000000000 : ℝ)^3851
        have hw : |(2591522107/5000000000 : ℝ)|=(2591522107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110740017/625000000 : ℝ)|^4875 ≤ (11183479181791/100000000000000 : ℝ)^3851
        have hw : |(-110740017/625000000 : ℝ)|=(110740017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s3_3 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2094612971/5000000000 : ℝ)*x 0 + (3857762549/10000000000 : ℝ)*x 1 + (181649579/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094612971/5000000000 : ℝ)^4875 ≤ (16619857190871/50000000000000 : ℝ)^3851 := by
    have hnat : (2094612971 : ℕ)^4875*50000000000000^3851 ≤ 16619857190871^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094612971 5000000000 16619857190871 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3857762549/10000000000 : ℝ)^4875 ≤ (233953786649/781250000000 : ℝ)^3851 := by
    have hnat : (3857762549 : ℕ)^4875*781250000000^3851 ≤ 233953786649^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3857762549 10000000000 233953786649 781250000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181649579/400000000 : ℝ)^4875 ≤ (7362840182063/20000000000000 : ℝ)^3851 := by
    have hnat : (181649579 : ℕ)^4875*20000000000000^3851 ≤ 7362840182063^3851*400000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181649579 400000000 7362840182063 20000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2094612971/5000000000 : ℝ), (3857762549/10000000000 : ℝ), (181649579/400000000 : ℝ)] ![(16619857190871/50000000000000 : ℝ), (233953786649/781250000000 : ℝ), (7362840182063/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2094612971/5000000000 : ℝ)|^4875 ≤ (16619857190871/50000000000000 : ℝ)^3851
        have hw : |(2094612971/5000000000 : ℝ)|=(2094612971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3857762549/10000000000 : ℝ)|^4875 ≤ (233953786649/781250000000 : ℝ)^3851
        have hw : |(3857762549/10000000000 : ℝ)|=(3857762549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181649579/400000000 : ℝ)|^4875 ≤ (7362840182063/20000000000000 : ℝ)^3851
        have hw : |(181649579/400000000 : ℝ)|=(181649579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s3_4 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-408484909/2500000000 : ℝ)*x 0 + (2592531579/5000000000 : ℝ)*x 1 + (2724441239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408484909/2500000000 : ℝ)^4875 ≤ (5046631157823/50000000000000 : ℝ)^3851 := by
    have hnat : (408484909 : ℕ)^4875*50000000000000^3851 ≤ 5046631157823^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408484909 2500000000 5046631157823 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592531579/5000000000 : ℝ)^4875 ≤ (43541735786359/100000000000000 : ℝ)^3851 := by
    have hnat : (2592531579 : ℕ)^4875*100000000000000^3851 ≤ 43541735786359^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592531579 5000000000 43541735786359 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724441239/5000000000 : ℝ)^4875 ≤ (46365001892017/100000000000000 : ℝ)^3851 := by
    have hnat : (2724441239 : ℕ)^4875*100000000000000^3851 ≤ 46365001892017^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724441239 5000000000 46365001892017 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408484909/2500000000 : ℝ), (2592531579/5000000000 : ℝ), (2724441239/5000000000 : ℝ)] ![(5046631157823/50000000000000 : ℝ), (43541735786359/100000000000000 : ℝ), (46365001892017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408484909/2500000000 : ℝ)|^4875 ≤ (5046631157823/50000000000000 : ℝ)^3851
        have hw : |(-408484909/2500000000 : ℝ)|=(408484909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592531579/5000000000 : ℝ)|^4875 ≤ (43541735786359/100000000000000 : ℝ)^3851
        have hw : |(2592531579/5000000000 : ℝ)|=(2592531579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724441239/5000000000 : ℝ)|^4875 ≤ (46365001892017/100000000000000 : ℝ)^3851
        have hw : |(2724441239/5000000000 : ℝ)|=(2724441239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s3_5 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638977759/5000000000 : ℝ)*x 0 + (-1506001393/10000000000 : ℝ)*x 1 + (5448882491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638977759/5000000000 : ℝ)^4875 ≤ (11132891957687/25000000000000 : ℝ)^3851 := by
    have hnat : (2638977759 : ℕ)^4875*25000000000000^3851 ≤ 11132891957687^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638977759 5000000000 11132891957687 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1506001393/10000000000 : ℝ)^4875 ≤ (4551715057993/50000000000000 : ℝ)^3851 := by
    have hnat : (1506001393 : ℕ)^4875*50000000000000^3851 ≤ 4551715057993^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506001393 10000000000 4551715057993 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448882491/10000000000 : ℝ)^4875 ≤ (46365002032049/100000000000000 : ℝ)^3851 := by
    have hnat : (5448882491 : ℕ)^4875*100000000000000^3851 ≤ 46365002032049^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448882491 10000000000 46365002032049 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638977759/5000000000 : ℝ), (-1506001393/10000000000 : ℝ), (5448882491/10000000000 : ℝ)] ![(11132891957687/25000000000000 : ℝ), (4551715057993/50000000000000 : ℝ), (46365002032049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638977759/5000000000 : ℝ)|^4875 ≤ (11132891957687/25000000000000 : ℝ)^3851
        have hw : |(2638977759/5000000000 : ℝ)|=(2638977759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1506001393/10000000000 : ℝ)|^4875 ≤ (4551715057993/50000000000000 : ℝ)^3851
        have hw : |(-1506001393/10000000000 : ℝ)|=(1506001393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448882491/10000000000 : ℝ)|^4875 ≤ (46365002032049/100000000000000 : ℝ)^3851
        have hw : |(5448882491/10000000000 : ℝ)|=(5448882491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s3_6 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638977799/5000000000 : ℝ)*x 0 + (5448882559/10000000000 : ℝ)*x 1 + (-753000593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638977799/5000000000 : ℝ)^4875 ≤ (44531568685211/100000000000000 : ℝ)^3851 := by
    have hnat : (2638977799 : ℕ)^4875*100000000000000^3851 ≤ 44531568685211^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638977799 5000000000 44531568685211 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448882559/10000000000 : ℝ)^4875 ≤ (11591250691131/25000000000000 : ℝ)^3851 := by
    have hnat : (5448882559 : ℕ)^4875*25000000000000^3851 ≤ 11591250691131^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448882559 10000000000 11591250691131 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (753000593/5000000000 : ℝ)^4875 ≤ (9103428532001/100000000000000 : ℝ)^3851 := by
    have hnat : (753000593 : ℕ)^4875*100000000000000^3851 ≤ 9103428532001^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753000593 5000000000 9103428532001 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638977799/5000000000 : ℝ), (5448882559/10000000000 : ℝ), (-753000593/5000000000 : ℝ)] ![(44531568685211/100000000000000 : ℝ), (11591250691131/25000000000000 : ℝ), (9103428532001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638977799/5000000000 : ℝ)|^4875 ≤ (44531568685211/100000000000000 : ℝ)^3851
        have hw : |(2638977799/5000000000 : ℝ)|=(2638977799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448882559/10000000000 : ℝ)|^4875 ≤ (11591250691131/25000000000000 : ℝ)^3851
        have hw : |(5448882559/10000000000 : ℝ)|=(5448882559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-753000593/5000000000 : ℝ)|^4875 ≤ (9103428532001/100000000000000 : ℝ)^3851
        have hw : |(-753000593/5000000000 : ℝ)|=(753000593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s3_7 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4189395391/10000000000 : ℝ)*x 0 + (181443461/400000000 : ℝ)*x 1 + (1931484481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4189395391/10000000000 : ℝ)^4875 ≤ (16620708203393/50000000000000 : ℝ)^3851 := by
    have hnat : (4189395391 : ℕ)^4875*50000000000000^3851 ≤ 16620708203393^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4189395391 10000000000 16620708203393 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181443461/400000000 : ℝ)^4875 ≤ (36761328091789/100000000000000 : ℝ)^3851 := by
    have hnat : (181443461 : ℕ)^4875*100000000000000^3851 ≤ 36761328091789^3851*400000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181443461 400000000 36761328091789 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1931484481/5000000000 : ℝ)^4875 ≤ (7499313871581/25000000000000 : ℝ)^3851 := by
    have hnat : (1931484481 : ℕ)^4875*25000000000000^3851 ≤ 7499313871581^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931484481 5000000000 7499313871581 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4189395391/10000000000 : ℝ), (181443461/400000000 : ℝ), (1931484481/5000000000 : ℝ)] ![(16620708203393/50000000000000 : ℝ), (36761328091789/100000000000000 : ℝ), (7499313871581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4189395391/10000000000 : ℝ)|^4875 ≤ (16620708203393/50000000000000 : ℝ)^3851
        have hw : |(4189395391/10000000000 : ℝ)|=(4189395391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(181443461/400000000 : ℝ)|^4875 ≤ (36761328091789/100000000000000 : ℝ)^3851
        have hw : |(181443461/400000000 : ℝ)|=(181443461/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1931484481/5000000000 : ℝ)|^4875 ≤ (7499313871581/25000000000000 : ℝ)^3851
        have hw : |(1931484481/5000000000 : ℝ)|=(1931484481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1639_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2121/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3259/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16383/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16383/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16383/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16383/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16383/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16383/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10527/100000 : ℝ) ^ (4871/1024 : ℝ) ≤ (1117463891679607/50000000000000000000 : ℝ) := by
    have hpowers : (10527/100000 : ℝ)^4871 ≤ (1117463891679607/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10527 : ℕ)^4871*50000000000000000000^1024 ≤ 1117463891679607^1024*100000^4871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10527 100000 1117463891679607 50000000000000000000 4871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10527/100000 : ℝ)) (X := (1117463891679607/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16383/100000 : ℝ) ^ (4871/1024 : ℝ) ≤ (18323078451163257/100000000000000000000 : ℝ) := by
    have hpowers : (16383/100000 : ℝ)^4871 ≤ (18323078451163257/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16383 : ℕ)^4871*100000000000000000000^1024 ≤ 18323078451163257^1024*100000^4871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16383 100000 18323078451163257 100000000000000000000 4871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16383/100000 : ℝ)) (X := (18323078451163257/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001117463891679607/25000000000000000000 : ℝ) ≤ (5000046982665899/5000000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (25001117463891679607/25000000000000000000 : ℝ)^1024 ≤ (5000046982665899/5000000000000000 : ℝ)^4871 := by
      have hnat : (25001117463891679607 : ℕ)^1024*5000000000000000^4871 ≤ 5000046982665899^4871*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001117463891679607 25000000000000000000 5000046982665899 5000000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000046982665899/5000000000000000 : ℝ)) (X := (25001117463891679607/25000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100020558006234522471/100000000000000000000 : ℝ) ≤ (10000432143083917/10000000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (100020558006234522471/100000000000000000000 : ℝ)^1024 ≤ (10000432143083917/10000000000000000 : ℝ)^4871 := by
      have hnat : (100020558006234522471 : ℕ)^1024*10000000000000000^4871 ≤ 10000432143083917^4871*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100020558006234522471 100000000000000000000 10000432143083917 10000000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000432143083917/10000000000000000 : ℝ)) (X := (100020558006234522471/100000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018323078451163257/50000000000000000000 : ℝ) ≤ (2500192580209009/2500000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (50018323078451163257/50000000000000000000 : ℝ)^1024 ≤ (2500192580209009/2500000000000000 : ℝ)^4871 := by
      have hnat : (50018323078451163257 : ℕ)^1024*2500000000000000^4871 ≤ 2500192580209009^4871*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018323078451163257 50000000000000000000 2500192580209009 2500000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500192580209009/2500000000000000 : ℝ)) (X := (50018323078451163257/50000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1117463891679607/50000000000000000000 : ℝ) ≤ ((9758905044431649277/9760000000000000000 : ℝ)+2*(112725917373/195200000000000 : ℝ)*(10527/100000 : ℝ))^(4871/1024 : ℝ) := by
    rw [show (9758905044431649277/9760000000000000000 : ℝ)+2*(112725917373/195200000000000 : ℝ)*(10527/100000 : ℝ)=(5000046982665899/5000000000000000 : ℝ) by norm_num, show 1+2*(1117463891679607/50000000000000000000 : ℝ)=(25001117463891679607/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18323078451163257/100000000000000000000 : ℝ)+(1117463891679607/50000000000000000000 : ℝ) ≤ ((9758905044431649277/9760000000000000000 : ℝ)+(112725917373/195200000000000 : ℝ)*((16383/100000 : ℝ)+(10527/100000 : ℝ)))^(4871/1024 : ℝ) := by
    rw [show (9758905044431649277/9760000000000000000 : ℝ)+(112725917373/195200000000000 : ℝ)*((16383/100000 : ℝ)+(10527/100000 : ℝ))=(10000432143083917/10000000000000000 : ℝ) by norm_num, show 1+(18323078451163257/100000000000000000000 : ℝ)+(1117463891679607/50000000000000000000 : ℝ)=(100020558006234522471/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18323078451163257/100000000000000000000 : ℝ) ≤ ((9758905044431649277/9760000000000000000 : ℝ)+2*(112725917373/195200000000000 : ℝ)*(16383/100000 : ℝ))^(4871/1024 : ℝ) := by
    rw [show (9758905044431649277/9760000000000000000 : ℝ)+2*(112725917373/195200000000000 : ℝ)*(16383/100000 : ℝ)=(2500192580209009/2500000000000000 : ℝ) by norm_num, show 1+2*(18323078451163257/100000000000000000000 : ℝ)=(50018323078451163257/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9758905044431649277/9760000000000000000 : ℝ)*(X 1 0+X 2 0)+(112725917373/195200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (10527/100000 : ℝ)) (hi := (16383/100000 : ℝ)) (c := (9758905044431649277/9760000000000000000 : ℝ)) (alpha := (112725917373/195200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9758905044431649277/9760000000000000000 : ℝ)*(X 0 1+X 2 1)+(112725917373/195200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (10527/100000 : ℝ)) (hi := (16383/100000 : ℝ)) (c := (9758905044431649277/9760000000000000000 : ℝ)) (alpha := (112725917373/195200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9758905044431649277/9760000000000000000 : ℝ)*(X 0 2+X 1 2)+(112725917373/195200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (10527/100000 : ℝ)) (hi := (16383/100000 : ℝ)) (c := (9758905044431649277/9760000000000000000 : ℝ)) (alpha := (112725917373/195200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1633873271/10000000000 : ℝ)*X 0 0+(2725461891/5000000000 : ℝ)*X 0 1+(5183043347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349421733/10000000000 : ℝ)*X 1 0+(-885920189/5000000000 : ℝ)*X 1 1+(5183043493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668677637/1250000000 : ℝ)*X 2 0+(2591522107/5000000000 : ℝ)*X 2 1+(-110740017/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2094612971/5000000000 : ℝ)*X 0 0+(3857762549/10000000000 : ℝ)*X 0 1+(181649579/400000000 : ℝ)*X 0 2+(2094612971/5000000000 : ℝ)*X 1 0+(3857762549/10000000000 : ℝ)*X 1 1+(181649579/400000000 : ℝ)*X 1 2+(2094612971/5000000000 : ℝ)*X 2 0+(3857762549/10000000000 : ℝ)*X 2 1+(181649579/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-408484909/2500000000 : ℝ)*X 0 0+(2592531579/5000000000 : ℝ)*X 0 1+(2724441239/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638977759/5000000000 : ℝ)*X 1 0+(-1506001393/10000000000 : ℝ)*X 1 1+(5448882491/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638977799/5000000000 : ℝ)*X 2 0+(5448882559/10000000000 : ℝ)*X 2 1+(-753000593/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4189395391/10000000000 : ℝ)*X 0 0+(181443461/400000000 : ℝ)*X 0 1+(1931484481/5000000000 : ℝ)*X 0 2+(4189395391/10000000000 : ℝ)*X 1 0+(181443461/400000000 : ℝ)*X 1 1+(1931484481/5000000000 : ℝ)*X 1 2+(4189395391/10000000000 : ℝ)*X 2 0+(181443461/400000000 : ℝ)*X 2 1+(1931484481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133721827884433681923963/9760000000000000000000000000 : ℝ) := by norm_num
    linear_combination (308696173/20000000000000 : ℝ)*(base19) + (935001089/100000000000000 : ℝ)*(base23) + (43852997/50000000000000 : ℝ)*(lower2) + (11261133/5000000000000 : ℝ)*(upper3) + (12601001/10000000000000 : ℝ)*(upper5) + (2598088045675683/100000000000000 : ℝ)*(major0) + (2598088045675683/100000000000000 : ℝ)*(major1) + (2598088045675683/100000000000000 : ℝ)*(major2) + (233314546842213/6250000000000 : ℝ)*(sp0) + (1866526375827237/50000000000000 : ℝ)*(sp1) + (14932213440537/400000000000 : ℝ)*(sp2) + (146311397902711/10000000000000 : ℝ)*(sp3) + (5386414983/25000000000000 : ℝ)*(sp4) + (7360488677/100000000000000 : ℝ)*(sp7) + (365780334878947/25000000000000 : ℝ)*(f.failure) + (186652714756767/5000000000000 : ℝ)*(f.sum) + (11870477112439/9760000000000000000000000000 : ℝ)*base65 + (1501070297370618809/976000000000000000000000000000000 : ℝ)*base68 + (3019787596885381191/976000000000000000000000000000000 : ℝ)*base69 + (6588564612037381191/976000000000000000000000000000000 : ℝ)*base71 + (242059974921/9760000000000000000000000000 : ℝ)*base74 + (1717770678474618809/976000000000000000000000000000000 : ℝ)*base76 + (653213436570618809/976000000000000000000000000000000 : ℝ)*base78 + (3355123903141381191/976000000000000000000000000000000 : ℝ)*base79 + (31739850786519/9760000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4899987/500000000000000000000 : ℝ)*base89 + (4899987/500000000000000000000 : ℝ)*base91 + (4899987/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (407494692044131291811757957/122000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (210526749/50000000000000 : ℝ)*(base19) + (129067757/20000000000000 : ℝ)*(base23) + (108583997/100000000000000 : ℝ)*(upper3) + (12450709/25000000000000 : ℝ)*(lower4) + (49120517/100000000000000 : ℝ)*(upper5) + (1319024097722053/50000000000000 : ℝ)*(major0) + (1319024097722053/50000000000000 : ℝ)*(major1) + (1319024097722053/50000000000000 : ℝ)*(major2) + (3309146189/100000000000000 : ℝ)*(sp1) + (4330718507/50000000000000 : ℝ)*(sp2) + (15161885031111/400000000000 : ℝ)*(sp4) + (1895233763789031/50000000000000 : ℝ)*(sp5) + (118451935968811/3125000000000 : ℝ)*(sp6) + (1485625021773107/100000000000000 : ℝ)*(sp7) + (1485625021773107/100000000000000 : ℝ)*(f.failure) + (15161885031111/400000000000 : ℝ)*(f.sum) + (1088901842209/4880000000000000000000000000 : ℝ)*base65 + (1049549104462855681/488000000000000000000000000000000 : ℝ)*base67 + (1179087846070855681/488000000000000000000000000000000 : ℝ)*base69 + (2381396842742855681/488000000000000000000000000000000 : ℝ)*base71 + (1337300104191/4880000000000000000000000000 : ℝ)*base74 + (5689942139998855681/488000000000000000000000000000000 : ℝ)*base75 + (1529827014913144319/488000000000000000000000000000000 : ℝ)*base78 + (2665435364430855681/488000000000000000000000000000000 : ℝ)*base79 + (10650231103249/4880000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (8834653/2000000000000000000000 : ℝ)*base90 + (8834653/2000000000000000000000 : ℝ)*base92 + (8834653/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1639_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1639_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1639_s4_0 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-163393359/1000000000 : ℝ)*x 0 + (5450625419/10000000000 : ℝ)*x 1 + (1295825339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163393359/1000000000 : ℝ)^4875 ≤ (10093215037049/100000000000000 : ℝ)^3851 := by
    have hnat : (163393359 : ℕ)^4875*100000000000000^3851 ≤ 10093215037049^3851*1000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163393359 1000000000 10093215037049 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450625419/10000000000 : ℝ)^4875 ≤ (2898986069667/6250000000000 : ℝ)^3851 := by
    have hnat : (5450625419 : ℕ)^4875*6250000000000^3851 ≤ 2898986069667^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450625419 10000000000 2898986069667 6250000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295825339/2500000000 : ℝ)^4875 ≤ (5440375979411/12500000000000 : ℝ)^3851 := by
    have hnat : (1295825339 : ℕ)^4875*12500000000000^3851 ≤ 5440375979411^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295825339 2500000000 5440375979411 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-163393359/1000000000 : ℝ), (5450625419/10000000000 : ℝ), (1295825339/2500000000 : ℝ)] ![(10093215037049/100000000000000 : ℝ), (2898986069667/6250000000000 : ℝ), (5440375979411/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-163393359/1000000000 : ℝ)|^4875 ≤ (10093215037049/100000000000000 : ℝ)^3851
        have hw : |(-163393359/1000000000 : ℝ)|=(163393359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450625419/10000000000 : ℝ)|^4875 ≤ (2898986069667/6250000000000 : ℝ)^3851
        have hw : |(5450625419/10000000000 : ℝ)|=(5450625419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295825339/2500000000 : ℝ)|^4875 ≤ (5440375979411/12500000000000 : ℝ)^3851
        have hw : |(1295825339/2500000000 : ℝ)|=(1295825339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s4_1 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349340931/10000000000 : ℝ)*x 0 + (-885802871/5000000000 : ℝ)*x 1 + (1295825337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349340931/10000000000 : ℝ)^4875 ≤ (5661923368483/12500000000000 : ℝ)^3851 := by
    have hnat : (5349340931 : ℕ)^4875*12500000000000^3851 ≤ 5661923368483^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349340931 10000000000 5661923368483 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (885802871/5000000000 : ℝ)^4875 ≤ (698850330701/6250000000000 : ℝ)^3851 := by
    have hnat : (885802871 : ℕ)^4875*6250000000000^3851 ≤ 698850330701^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885802871 5000000000 698850330701 6250000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295825337/2500000000 : ℝ)^4875 ≤ (10880751937563/25000000000000 : ℝ)^3851 := by
    have hnat : (1295825337 : ℕ)^4875*25000000000000^3851 ≤ 10880751937563^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295825337 2500000000 10880751937563 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349340931/10000000000 : ℝ), (-885802871/5000000000 : ℝ), (1295825337/2500000000 : ℝ)] ![(5661923368483/12500000000000 : ℝ), (698850330701/6250000000000 : ℝ), (10880751937563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349340931/10000000000 : ℝ)|^4875 ≤ (5661923368483/12500000000000 : ℝ)^3851
        have hw : |(5349340931/10000000000 : ℝ)|=(5349340931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-885802871/5000000000 : ℝ)|^4875 ≤ (698850330701/6250000000000 : ℝ)^3851
        have hw : |(-885802871/5000000000 : ℝ)|=(885802871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295825337/2500000000 : ℝ)|^4875 ≤ (10880751937563/25000000000000 : ℝ)^3851
        have hw : |(1295825337/2500000000 : ℝ)|=(1295825337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s4_2 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334333809/625000000 : ℝ)*x 0 + (5183301369/10000000000 : ℝ)*x 1 + (-27681339/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334333809/625000000 : ℝ)^4875 ≤ (45295387087211/100000000000000 : ℝ)^3851 := by
    have hnat : (334333809 : ℕ)^4875*100000000000000^3851 ≤ 45295387087211^3851*625000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334333809 625000000 45295387087211 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183301369/10000000000 : ℝ)^4875 ≤ (1360093999171/3125000000000 : ℝ)^3851 := by
    have hnat : (5183301369 : ℕ)^4875*3125000000000^3851 ≤ 1360093999171^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183301369 10000000000 1360093999171 3125000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27681339/156250000 : ℝ)^4875 ≤ (11181604923683/100000000000000 : ℝ)^3851 := by
    have hnat : (27681339 : ℕ)^4875*100000000000000^3851 ≤ 11181604923683^3851*156250000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27681339 156250000 11181604923683 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334333809/625000000 : ℝ), (5183301369/10000000000 : ℝ), (-27681339/156250000 : ℝ)] ![(45295387087211/100000000000000 : ℝ), (1360093999171/3125000000000 : ℝ), (11181604923683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334333809/625000000 : ℝ)|^4875 ≤ (45295387087211/100000000000000 : ℝ)^3851
        have hw : |(334333809/625000000 : ℝ)|=(334333809/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183301369/10000000000 : ℝ)|^4875 ≤ (1360093999171/3125000000000 : ℝ)^3851
        have hw : |(5183301369/10000000000 : ℝ)|=(5183301369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27681339/156250000 : ℝ)|^4875 ≤ (11181604923683/100000000000000 : ℝ)^3851
        have hw : |(-27681339/156250000 : ℝ)|=(27681339/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s4_3 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16757061/40000000 : ℝ)*x 0 + (60288549/156250000 : ℝ)*x 1 + (454052629/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16757061/40000000 : ℝ)^4875 ≤ (4155013651007/12500000000000 : ℝ)^3851 := by
    have hnat : (16757061 : ℕ)^4875*12500000000000^3851 ≤ 4155013651007^3851*40000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16757061 40000000 4155013651007 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60288549/156250000 : ℝ)^4875 ≤ (14976504295867/50000000000000 : ℝ)^3851 := by
    have hnat : (60288549 : ℕ)^4875*50000000000000^3851 ≤ 14976504295867^3851*156250000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60288549 156250000 14976504295867 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454052629/1000000000 : ℝ)^4875 ≤ (36806882189053/100000000000000 : ℝ)^3851 := by
    have hnat : (454052629 : ℕ)^4875*100000000000000^3851 ≤ 36806882189053^3851*1000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454052629 1000000000 36806882189053 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16757061/40000000 : ℝ), (60288549/156250000 : ℝ), (454052629/1000000000 : ℝ)] ![(4155013651007/12500000000000 : ℝ), (14976504295867/50000000000000 : ℝ), (36806882189053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16757061/40000000 : ℝ)|^4875 ≤ (4155013651007/12500000000000 : ℝ)^3851
        have hw : |(16757061/40000000 : ℝ)|=(16757061/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60288549/156250000 : ℝ)|^4875 ≤ (14976504295867/50000000000000 : ℝ)^3851
        have hw : |(60288549/156250000 : ℝ)|=(60288549/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(454052629/1000000000 : ℝ)|^4875 ≤ (36806882189053/100000000000000 : ℝ)^3851
        have hw : |(454052629/1000000000 : ℝ)|=(454052629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s4_4 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-816999579/5000000000 : ℝ)*x 0 + (5185312551/10000000000 : ℝ)*x 1 + (5448593139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (816999579/5000000000 : ℝ)^4875 ≤ (10093727769117/100000000000000 : ℝ)^3851 := by
    have hnat : (816999579 : ℕ)^4875*100000000000000^3851 ≤ 10093727769117^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      816999579 5000000000 10093727769117 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185312551/10000000000 : ℝ)^4875 ≤ (21772193485043/50000000000000 : ℝ)^3851 := by
    have hnat : (5185312551 : ℕ)^4875*50000000000000^3851 ≤ 21772193485043^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185312551 10000000000 21772193485043 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448593139/10000000000 : ℝ)^4875 ≤ (1159047131083/2500000000000 : ℝ)^3851 := by
    have hnat : (5448593139 : ℕ)^4875*2500000000000^3851 ≤ 1159047131083^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448593139 10000000000 1159047131083 2500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-816999579/5000000000 : ℝ), (5185312551/10000000000 : ℝ), (5448593139/10000000000 : ℝ)] ![(10093727769117/100000000000000 : ℝ), (21772193485043/50000000000000 : ℝ), (1159047131083/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-816999579/5000000000 : ℝ)|^4875 ≤ (10093727769117/100000000000000 : ℝ)^3851
        have hw : |(-816999579/5000000000 : ℝ)|=(816999579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185312551/10000000000 : ℝ)|^4875 ≤ (21772193485043/50000000000000 : ℝ)^3851
        have hw : |(5185312551/10000000000 : ℝ)|=(5185312551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448593139/10000000000 : ℝ)|^4875 ≤ (1159047131083/2500000000000 : ℝ)^3851
        have hw : |(5448593139/10000000000 : ℝ)|=(5448593139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s4_5 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639011851/5000000000 : ℝ)*x 0 + (-188289249/1250000000 : ℝ)*x 1 + (5448592807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639011851/5000000000 : ℝ)^4875 ≤ (44532296090959/100000000000000 : ℝ)^3851 := by
    have hnat : (2639011851 : ℕ)^4875*100000000000000^3851 ≤ 44532296090959^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639011851 5000000000 44532296090959 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188289249/1250000000 : ℝ)^4875 ≤ (9105822221649/100000000000000 : ℝ)^3851 := by
    have hnat : (188289249 : ℕ)^4875*100000000000000^3851 ≤ 9105822221649^3851*1250000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188289249 1250000000 9105822221649 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448592807/10000000000 : ℝ)^4875 ≤ (46361881667169/100000000000000 : ℝ)^3851 := by
    have hnat : (5448592807 : ℕ)^4875*100000000000000^3851 ≤ 46361881667169^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448592807 10000000000 46361881667169 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639011851/5000000000 : ℝ), (-188289249/1250000000 : ℝ), (5448592807/10000000000 : ℝ)] ![(44532296090959/100000000000000 : ℝ), (9105822221649/100000000000000 : ℝ), (46361881667169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639011851/5000000000 : ℝ)|^4875 ≤ (44532296090959/100000000000000 : ℝ)^3851
        have hw : |(2639011851/5000000000 : ℝ)|=(2639011851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-188289249/1250000000 : ℝ)|^4875 ≤ (9105822221649/100000000000000 : ℝ)^3851
        have hw : |(-188289249/1250000000 : ℝ)|=(188289249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448592807/10000000000 : ℝ)|^4875 ≤ (46361881667169/100000000000000 : ℝ)^3851
        have hw : |(5448592807/10000000000 : ℝ)|=(5448592807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s4_6 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278023343/10000000000 : ℝ)*x 0 + (5448593079/10000000000 : ℝ)*x 1 + (-1506314111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278023343/10000000000 : ℝ)^4875 ≤ (44532292256543/100000000000000 : ℝ)^3851 := by
    have hnat : (5278023343 : ℕ)^4875*100000000000000^3851 ≤ 44532292256543^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278023343 10000000000 44532292256543 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448593079/10000000000 : ℝ)^4875 ≤ (11590471149257/25000000000000 : ℝ)^3851 := by
    have hnat : (5448593079 : ℕ)^4875*25000000000000^3851 ≤ 11590471149257^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448593079 10000000000 11590471149257 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506314111/10000000000 : ℝ)^4875 ≤ (9105823132299/100000000000000 : ℝ)^3851 := by
    have hnat : (1506314111 : ℕ)^4875*100000000000000^3851 ≤ 9105823132299^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506314111 10000000000 9105823132299 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278023343/10000000000 : ℝ), (5448593079/10000000000 : ℝ), (-1506314111/10000000000 : ℝ)] ![(44532292256543/100000000000000 : ℝ), (11590471149257/25000000000000 : ℝ), (9105823132299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278023343/10000000000 : ℝ)|^4875 ≤ (44532292256543/100000000000000 : ℝ)^3851
        have hw : |(5278023343/10000000000 : ℝ)|=(5278023343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448593079/10000000000 : ℝ)|^4875 ≤ (11590471149257/25000000000000 : ℝ)^3851
        have hw : |(5448593079/10000000000 : ℝ)|=(5448593079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1506314111/10000000000 : ℝ)|^4875 ≤ (9105823132299/100000000000000 : ℝ)^3851
        have hw : |(-1506314111/10000000000 : ℝ)|=(1506314111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s4_7 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2094716481/5000000000 : ℝ)*x 0 + (4535394961/10000000000 : ℝ)*x 1 + (965913071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094716481/5000000000 : ℝ)^4875 ≤ (3324179378997/10000000000000 : ℝ)^3851 := by
    have hnat : (2094716481 : ℕ)^4875*10000000000000^3851 ≤ 3324179378997^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094716481 5000000000 3324179378997 10000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4535394961/10000000000 : ℝ)^4875 ≤ (36754233383581/100000000000000 : ℝ)^3851 := by
    have hnat : (4535394961 : ℕ)^4875*100000000000000^3851 ≤ 36754233383581^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535394961 10000000000 36754233383581 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965913071/2500000000 : ℝ)^4875 ≤ (937624150673/3125000000000 : ℝ)^3851 := by
    have hnat : (965913071 : ℕ)^4875*3125000000000^3851 ≤ 937624150673^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965913071 2500000000 937624150673 3125000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2094716481/5000000000 : ℝ), (4535394961/10000000000 : ℝ), (965913071/2500000000 : ℝ)] ![(3324179378997/10000000000000 : ℝ), (36754233383581/100000000000000 : ℝ), (937624150673/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2094716481/5000000000 : ℝ)|^4875 ≤ (3324179378997/10000000000000 : ℝ)^3851
        have hw : |(2094716481/5000000000 : ℝ)|=(2094716481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4535394961/10000000000 : ℝ)|^4875 ≤ (36754233383581/100000000000000 : ℝ)^3851
        have hw : |(4535394961/10000000000 : ℝ)|=(4535394961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(965913071/2500000000 : ℝ)|^4875 ≤ (937624150673/3125000000000 : ℝ)^3851
        have hw : |(965913071/2500000000 : ℝ)|=(965913071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1639_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10611/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16289/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3259/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2121/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3259/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2121/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3259/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2121/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3259/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2121/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3259/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2121/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3259/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2121/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2121/20000 : ℝ) ^ (4871/1024 : ℝ) ≤ (9042201537617/390625000000000000 : ℝ) := by
    have hpowers : (2121/20000 : ℝ)^4871 ≤ (9042201537617/390625000000000000 : ℝ)^1024 := by
      have hnat : (2121 : ℕ)^4871*390625000000000000^1024 ≤ 9042201537617^1024*20000^4871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2121 20000 9042201537617 390625000000000000 4871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2121/20000 : ℝ)) (X := (9042201537617/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3259/20000 : ℝ) ^ (4871/1024 : ℝ) ≤ (1785960649280429/10000000000000000000 : ℝ) := by
    have hpowers : (3259/20000 : ℝ)^4871 ≤ (1785960649280429/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3259 : ℕ)^4871*10000000000000000000^1024 ≤ 1785960649280429^1024*20000^4871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3259 20000 1785960649280429 10000000000000000000 4871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3259/20000 : ℝ)) (X := (1785960649280429/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (195321542201537617/195312500000000000 : ℝ) ≤ (400003892942799/400000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (195321542201537617/195312500000000000 : ℝ)^1024 ≤ (400003892942799/400000000000000 : ℝ)^4871 := by
      have hnat : (195321542201537617 : ℕ)^1024*400000000000000^4871 ≤ 400003892942799^4871*195312500000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195321542201537617 195312500000000000 400003892942799 400000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400003892942799/400000000000000 : ℝ)) (X := (195321542201537617/195312500000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010087205043217121/50000000000000000000 : ℝ) ≤ (5000212040138901/5000000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (50010087205043217121/50000000000000000000 : ℝ)^1024 ≤ (5000212040138901/5000000000000000 : ℝ)^4871 := by
      have hnat : (50010087205043217121 : ℕ)^1024*5000000000000000^4871 ≤ 5000212040138901^4871*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010087205043217121 50000000000000000000 5000212040138901 5000000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000212040138901/5000000000000000 : ℝ)) (X := (50010087205043217121/50000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001785960649280429/5000000000000000000 : ℝ) ≤ (10000750836985629/10000000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (5001785960649280429/5000000000000000000 : ℝ)^1024 ≤ (10000750836985629/10000000000000000 : ℝ)^4871 := by
      have hnat : (5001785960649280429 : ℕ)^1024*10000000000000000^4871 ≤ 10000750836985629^4871*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001785960649280429 5000000000000000000 10000750836985629 10000000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000750836985629/10000000000000000 : ℝ)) (X := (5001785960649280429/5000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9042201537617/390625000000000000 : ℝ) ≤ ((1422340581533503677/1422500000000000000 : ℝ)+2*(326756707827/569000000000000 : ℝ)*(2121/20000 : ℝ))^(4871/1024 : ℝ) := by
    rw [show (1422340581533503677/1422500000000000000 : ℝ)+2*(326756707827/569000000000000 : ℝ)*(2121/20000 : ℝ)=(400003892942799/400000000000000 : ℝ) by norm_num, show 1+2*(9042201537617/390625000000000000 : ℝ)=(195321542201537617/195312500000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1785960649280429/10000000000000000000 : ℝ)+(9042201537617/390625000000000000 : ℝ) ≤ ((1422340581533503677/1422500000000000000 : ℝ)+(326756707827/569000000000000 : ℝ)*((3259/20000 : ℝ)+(2121/20000 : ℝ)))^(4871/1024 : ℝ) := by
    rw [show (1422340581533503677/1422500000000000000 : ℝ)+(326756707827/569000000000000 : ℝ)*((3259/20000 : ℝ)+(2121/20000 : ℝ))=(5000212040138901/5000000000000000 : ℝ) by norm_num, show 1+(1785960649280429/10000000000000000000 : ℝ)+(9042201537617/390625000000000000 : ℝ)=(50010087205043217121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1785960649280429/10000000000000000000 : ℝ) ≤ ((1422340581533503677/1422500000000000000 : ℝ)+2*(326756707827/569000000000000 : ℝ)*(3259/20000 : ℝ))^(4871/1024 : ℝ) := by
    rw [show (1422340581533503677/1422500000000000000 : ℝ)+2*(326756707827/569000000000000 : ℝ)*(3259/20000 : ℝ)=(10000750836985629/10000000000000000 : ℝ) by norm_num, show 1+2*(1785960649280429/10000000000000000000 : ℝ)=(5001785960649280429/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1422340581533503677/1422500000000000000 : ℝ)*(X 1 0+X 2 0)+(326756707827/569000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (2121/20000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (1422340581533503677/1422500000000000000 : ℝ)) (alpha := (326756707827/569000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1422340581533503677/1422500000000000000 : ℝ)*(X 0 1+X 2 1)+(326756707827/569000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (2121/20000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (1422340581533503677/1422500000000000000 : ℝ)) (alpha := (326756707827/569000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1422340581533503677/1422500000000000000 : ℝ)*(X 0 2+X 1 2)+(326756707827/569000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (2121/20000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (1422340581533503677/1422500000000000000 : ℝ)) (alpha := (326756707827/569000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-163393359/1000000000 : ℝ)*X 0 0+(5450625419/10000000000 : ℝ)*X 0 1+(1295825339/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349340931/10000000000 : ℝ)*X 1 0+(-885802871/5000000000 : ℝ)*X 1 1+(1295825337/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334333809/625000000 : ℝ)*X 2 0+(5183301369/10000000000 : ℝ)*X 2 1+(-27681339/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((16757061/40000000 : ℝ)*X 0 0+(60288549/156250000 : ℝ)*X 0 1+(454052629/1000000000 : ℝ)*X 0 2+(16757061/40000000 : ℝ)*X 1 0+(60288549/156250000 : ℝ)*X 1 1+(454052629/1000000000 : ℝ)*X 1 2+(16757061/40000000 : ℝ)*X 2 0+(60288549/156250000 : ℝ)*X 2 1+(454052629/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-816999579/5000000000 : ℝ)*X 0 0+(5185312551/10000000000 : ℝ)*X 0 1+(5448593139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639011851/5000000000 : ℝ)*X 1 0+(-188289249/1250000000 : ℝ)*X 1 1+(5448592807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278023343/10000000000 : ℝ)*X 2 0+(5448593079/10000000000 : ℝ)*X 2 1+(-1506314111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2094716481/5000000000 : ℝ)*X 0 0+(4535394961/10000000000 : ℝ)*X 0 1+(965913071/2500000000 : ℝ)*X 0 2+(2094716481/5000000000 : ℝ)*X 1 0+(4535394961/10000000000 : ℝ)*X 1 1+(965913071/2500000000 : ℝ)*X 1 2+(2094716481/5000000000 : ℝ)*X 2 0+(4535394961/10000000000 : ℝ)*X 2 1+(965913071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (246965525939259144408943077/35562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1104515359/100000000000000 : ℝ)*(base19) + (1039477563/100000000000000 : ℝ)*(base23) + (39653981/100000000000000 : ℝ)*(lower2) + (6160467/4000000000000 : ℝ)*(upper3) + (34446953/25000000000000 : ℝ)*(upper5) + (1301741375036567/50000000000000 : ℝ)*(major0) + (1301741375036567/50000000000000 : ℝ)*(major1) + (1301741375036567/50000000000000 : ℝ)*(major2) + (187039587448761/5000000000000 : ℝ)*(sp0) + (3740804780119903/100000000000000 : ℝ)*(sp1) + (37408048451577/1000000000000 : ℝ)*(sp2) + (733076867304077/50000000000000 : ℝ)*(sp3) + (7067830021/50000000000000 : ℝ)*(sp4) + (1412354469/25000000000000 : ℝ)*(sp7) + (146615938402603/10000000000000 : ℝ)*(f.failure) + (1870402942317631/50000000000000 : ℝ)*(f.sum) + (9093002128691/14225000000000000000000000000 : ℝ)*base66 + (155448173773979359/71125000000000000000000000000000 : ℝ)*base67 + (851681363913520641/71125000000000000000000000000000 : ℝ)*base70 + (434012554339395641/71125000000000000000000000000000 : ℝ)*base72 + (40272385534259/14225000000000000000000000000 : ℝ)*base73 + (51074186094729359/71125000000000000000000000000000 : ℝ)*base75 + (614756763324770641/71125000000000000000000000000000 : ℝ)*base78 + (957372650036270641/71125000000000000000000000000000 : ℝ)*base80 + (84735086410991/14225000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2177563/200000000000000000000 : ℝ)*base89 + (2177563/200000000000000000000 : ℝ)*base91 + (2177563/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102885366631628980407777369/17781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (249828869/25000000000000 : ℝ)*(base19) + (926216657/100000000000000 : ℝ)*(base23) + (206499869/100000000000000 : ℝ)*(lower1) + (122228449/100000000000000 : ℝ)*(upper3) + (5990709/6250000000000 : ℝ)*(lower4) + (54758803/50000000000000 : ℝ)*(upper5) + (1321720016096101/50000000000000 : ℝ)*(major0) + (1321720016096101/50000000000000 : ℝ)*(major1) + (1321720016096101/50000000000000 : ℝ)*(major2) + (269629137/100000000000000 : ℝ)*(sp2) + (1899109210077137/50000000000000 : ℝ)*(sp4) + (1899108710419399/50000000000000 : ℝ)*(sp5) + (2967357206491/78125000000 : ℝ)*(sp6) + (744330725678861/50000000000000 : ℝ)*(sp7) + (744330725678861/50000000000000 : ℝ)*(f.failure) + (1899109210077137/50000000000000 : ℝ)*(f.sum) + (13050561461673/14225000000000000000000000000 : ℝ)*base66 + (966382739362180877/71125000000000000000000000000000 : ℝ)*base67 + (551792886869430877/71125000000000000000000000000000 : ℝ)*base69 + (2318844804029819123/71125000000000000000000000000000 : ℝ)*base72 + (2462569842677/14225000000000000000000000000 : ℝ)*base73 + (4104387068981930877/71125000000000000000000000000000 : ℝ)*base75 + (372728345186680877/71125000000000000000000000000000 : ℝ)*base77 + (163032585745805877/71125000000000000000000000000000 : ℝ)*base79 + (22932386510073/14225000000000000000000000000 : ℝ)*base82 + (7531619/1000000000000000000000 : ℝ)*base90 + (7531619/1000000000000000000000 : ℝ)*base92 + (7531619/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1639_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10611/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16289/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1639_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1639_box_0 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1371937611/10000000000 : ℝ)*x 0 + (169087037/312500000 : ℝ)*x 1 + (5410785141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1371937611/10000000000 : ℝ)^4875 ≤ (8089977067847/100000000000000 : ℝ)^3851 := by
    have hnat : (1371937611 : ℕ)^4875*100000000000000^3851 ≤ 8089977067847^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371937611 10000000000 8089977067847 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169087037/312500000 : ℝ)^4875 ≤ (45955011685983/100000000000000 : ℝ)^3851 := by
    have hnat : (169087037 : ℕ)^4875*100000000000000^3851 ≤ 45955011685983^3851*312500000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169087037 312500000 45955011685983 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410785141/10000000000 : ℝ)^4875 ≤ (2872188201479/6250000000000 : ℝ)^3851 := by
    have hnat : (5410785141 : ℕ)^4875*6250000000000^3851 ≤ 2872188201479^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410785141 10000000000 2872188201479 6250000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1371937611/10000000000 : ℝ), (169087037/312500000 : ℝ), (5410785141/10000000000 : ℝ)] ![(8089977067847/100000000000000 : ℝ), (45955011685983/100000000000000 : ℝ), (2872188201479/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1371937611/10000000000 : ℝ)|^4875 ≤ (8089977067847/100000000000000 : ℝ)^3851
        have hw : |(-1371937611/10000000000 : ℝ)|=(1371937611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169087037/312500000 : ℝ)|^4875 ≤ (45955011685983/100000000000000 : ℝ)^3851
        have hw : |(169087037/312500000 : ℝ)|=(169087037/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410785141/10000000000 : ℝ)|^4875 ≤ (2872188201479/6250000000000 : ℝ)^3851
        have hw : |(5410785141/10000000000 : ℝ)|=(5410785141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_1 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525120367/1000000000 : ℝ)*x 0 + (-1596187493/10000000000 : ℝ)*x 1 + (2705392549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525120367/1000000000 : ℝ)^4875 ≤ (22123014879233/50000000000000 : ℝ)^3851 := by
    have hnat : (525120367 : ℕ)^4875*50000000000000^3851 ≤ 22123014879233^3851*1000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525120367 1000000000 22123014879233 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1596187493/10000000000 : ℝ)^4875 ≤ (9798959461827/100000000000000 : ℝ)^3851 := by
    have hnat : (1596187493 : ℕ)^4875*100000000000000^3851 ≤ 9798959461827^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596187493 10000000000 9798959461827 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705392549/5000000000 : ℝ)^4875 ≤ (359023521573/781250000000 : ℝ)^3851 := by
    have hnat : (2705392549 : ℕ)^4875*781250000000^3851 ≤ 359023521573^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705392549 5000000000 359023521573 781250000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525120367/1000000000 : ℝ), (-1596187493/10000000000 : ℝ), (2705392549/5000000000 : ℝ)] ![(22123014879233/50000000000000 : ℝ), (9798959461827/100000000000000 : ℝ), (359023521573/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525120367/1000000000 : ℝ)|^4875 ≤ (22123014879233/50000000000000 : ℝ)^3851
        have hw : |(525120367/1000000000 : ℝ)|=(525120367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1596187493/10000000000 : ℝ)|^4875 ≤ (9798959461827/100000000000000 : ℝ)^3851
        have hw : |(-1596187493/10000000000 : ℝ)|=(1596187493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705392549/5000000000 : ℝ)|^4875 ≤ (359023521573/781250000000 : ℝ)^3851
        have hw : |(2705392549/5000000000 : ℝ)|=(2705392549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_2 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251203793/10000000000 : ℝ)*x 0 + (5410785123/10000000000 : ℝ)*x 1 + (-1596187289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251203793/10000000000 : ℝ)^4875 ≤ (4424603107043/10000000000000 : ℝ)^3851 := by
    have hnat : (5251203793 : ℕ)^4875*10000000000000^3851 ≤ 4424603107043^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251203793 10000000000 4424603107043 10000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410785123/10000000000 : ℝ)^4875 ≤ (9191002206027/20000000000000 : ℝ)^3851 := by
    have hnat : (5410785123 : ℕ)^4875*20000000000000^3851 ≤ 9191002206027^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410785123 10000000000 9191002206027 20000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1596187289/10000000000 : ℝ)^4875 ≤ (9798957876469/100000000000000 : ℝ)^3851 := by
    have hnat : (1596187289 : ℕ)^4875*100000000000000^3851 ≤ 9798957876469^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596187289 10000000000 9798957876469 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251203793/10000000000 : ℝ), (5410785123/10000000000 : ℝ), (-1596187289/10000000000 : ℝ)] ![(4424603107043/10000000000000 : ℝ), (9191002206027/20000000000000 : ℝ), (9798957876469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251203793/10000000000 : ℝ)|^4875 ≤ (4424603107043/10000000000000 : ℝ)^3851
        have hw : |(5251203793/10000000000 : ℝ)|=(5251203793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410785123/10000000000 : ℝ)|^4875 ≤ (9191002206027/20000000000000 : ℝ)^3851
        have hw : |(5410785123/10000000000 : ℝ)|=(5410785123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1596187289/10000000000 : ℝ)|^4875 ≤ (9798957876469/100000000000000 : ℝ)^3851
        have hw : |(-1596187289/10000000000 : ℝ)|=(1596187289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_3 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (55835323/125000000 : ℝ)*x 0 + (2031345569/5000000000 : ℝ)*x 1 + (1015672831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55835323/125000000 : ℝ)^4875 ≤ (4506527610817/12500000000000 : ℝ)^3851 := by
    have hnat : (55835323 : ℕ)^4875*12500000000000^3851 ≤ 4506527610817^3851*125000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55835323 125000000 4506527610817 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2031345569/5000000000 : ℝ)^4875 ≤ (15986944311531/50000000000000 : ℝ)^3851 := by
    have hnat : (2031345569 : ℕ)^4875*50000000000000^3851 ≤ 15986944311531^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031345569 5000000000 15986944311531 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015672831/2500000000 : ℝ)^4875 ≤ (7993472619037/25000000000000 : ℝ)^3851 := by
    have hnat : (1015672831 : ℕ)^4875*25000000000000^3851 ≤ 7993472619037^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015672831 2500000000 7993472619037 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(55835323/125000000 : ℝ), (2031345569/5000000000 : ℝ), (1015672831/2500000000 : ℝ)] ![(4506527610817/12500000000000 : ℝ), (15986944311531/50000000000000 : ℝ), (7993472619037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(55835323/125000000 : ℝ)|^4875 ≤ (4506527610817/12500000000000 : ℝ)^3851
        have hw : |(55835323/125000000 : ℝ)|=(55835323/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2031345569/5000000000 : ℝ)|^4875 ≤ (15986944311531/50000000000000 : ℝ)^3851
        have hw : |(2031345569/5000000000 : ℝ)|=(2031345569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1015672831/2500000000 : ℝ)|^4875 ≤ (7993472619037/25000000000000 : ℝ)^3851
        have hw : |(1015672831/2500000000 : ℝ)|=(1015672831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_4 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-47664337/250000000 : ℝ)*x 0 + (1043083161/2000000000 : ℝ)*x 1 + (5215415707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47664337/250000000 : ℝ)^4875 ≤ (12270701638459/100000000000000 : ℝ)^3851 := by
    have hnat : (47664337 : ℕ)^4875*100000000000000^3851 ≤ 12270701638459^3851*250000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47664337 250000000 12270701638459 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043083161/2000000000 : ℝ)^4875 ≤ (8772929938923/20000000000000 : ℝ)^3851 := by
    have hnat : (1043083161 : ℕ)^4875*20000000000000^3851 ≤ 8772929938923^3851*2000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043083161 2000000000 8772929938923 20000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215415707/10000000000 : ℝ)^4875 ≤ (4386464865121/10000000000000 : ℝ)^3851 := by
    have hnat : (5215415707 : ℕ)^4875*10000000000000^3851 ≤ 4386464865121^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215415707 10000000000 4386464865121 10000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-47664337/250000000 : ℝ), (1043083161/2000000000 : ℝ), (5215415707/10000000000 : ℝ)] ![(12270701638459/100000000000000 : ℝ), (8772929938923/20000000000000 : ℝ), (4386464865121/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-47664337/250000000 : ℝ)|^4875 ≤ (12270701638459/100000000000000 : ℝ)^3851
        have hw : |(-47664337/250000000 : ℝ)|=(47664337/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043083161/2000000000 : ℝ)|^4875 ≤ (8772929938923/20000000000000 : ℝ)^3851
        have hw : |(1043083161/2000000000 : ℝ)|=(1043083161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215415707/10000000000 : ℝ)|^4875 ≤ (4386464865121/10000000000000 : ℝ)^3851
        have hw : |(5215415707/10000000000 : ℝ)|=(5215415707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_5 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385501043/10000000000 : ℝ)*x 0 + (-167964821/1000000000 : ℝ)*x 1 + (5215415749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385501043/10000000000 : ℝ)^4875 ≤ (22841667714881/50000000000000 : ℝ)^3851 := by
    have hnat : (5385501043 : ℕ)^4875*50000000000000^3851 ≤ 22841667714881^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385501043 10000000000 22841667714881 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167964821/1000000000 : ℝ)^4875 ≤ (1306501931379/12500000000000 : ℝ)^3851 := by
    have hnat : (167964821 : ℕ)^4875*12500000000000^3851 ≤ 1306501931379^3851*1000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167964821 1000000000 1306501931379 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215415749/10000000000 : ℝ)^4875 ≤ (2741540568649/6250000000000 : ℝ)^3851 := by
    have hnat : (5215415749 : ℕ)^4875*6250000000000^3851 ≤ 2741540568649^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215415749 10000000000 2741540568649 6250000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385501043/10000000000 : ℝ), (-167964821/1000000000 : ℝ), (5215415749/10000000000 : ℝ)] ![(22841667714881/50000000000000 : ℝ), (1306501931379/12500000000000 : ℝ), (2741540568649/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385501043/10000000000 : ℝ)|^4875 ≤ (22841667714881/50000000000000 : ℝ)^3851
        have hw : |(5385501043/10000000000 : ℝ)|=(5385501043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-167964821/1000000000 : ℝ)|^4875 ≤ (1306501931379/12500000000000 : ℝ)^3851
        have hw : |(-167964821/1000000000 : ℝ)|=(167964821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215415749/10000000000 : ℝ)|^4875 ≤ (2741540568649/6250000000000 : ℝ)^3851
        have hw : |(5215415749/10000000000 : ℝ)|=(5215415749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_6 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385501063/10000000000 : ℝ)*x 0 + (41723327/80000000 : ℝ)*x 1 + (-839824007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385501063/10000000000 : ℝ)^4875 ≤ (45683335644527/100000000000000 : ℝ)^3851 := by
    have hnat : (5385501063 : ℕ)^4875*100000000000000^3851 ≤ 45683335644527^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385501063 10000000000 45683335644527 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41723327/80000000 : ℝ)^4875 ≤ (1370770326247/3125000000000 : ℝ)^3851 := by
    have hnat : (41723327 : ℕ)^4875*3125000000000^3851 ≤ 1370770326247^3851*80000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41723327 80000000 1370770326247 3125000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (839824007/5000000000 : ℝ)^4875 ≤ (5226006953531/50000000000000 : ℝ)^3851 := by
    have hnat : (839824007 : ℕ)^4875*50000000000000^3851 ≤ 5226006953531^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839824007 5000000000 5226006953531 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385501063/10000000000 : ℝ), (41723327/80000000 : ℝ), (-839824007/5000000000 : ℝ)] ![(45683335644527/100000000000000 : ℝ), (1370770326247/3125000000000 : ℝ), (5226006953531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385501063/10000000000 : ℝ)|^4875 ≤ (45683335644527/100000000000000 : ℝ)^3851
        have hw : |(5385501063/10000000000 : ℝ)|=(5385501063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41723327/80000000 : ℝ)|^4875 ≤ (1370770326247/3125000000000 : ℝ)^3851
        have hw : |(41723327/80000000 : ℝ)|=(41723327/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-839824007/5000000000 : ℝ)|^4875 ≤ (5226006953531/50000000000000 : ℝ)^3851
        have hw : |(-839824007/5000000000 : ℝ)|=(839824007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_7 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3905364479/10000000000 : ℝ)*x 0 + (434309213/1000000000 : ℝ)*x 1 + (4343092323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3905364479/10000000000 : ℝ)^4875 ≤ (6082923492693/20000000000000 : ℝ)^3851 := by
    have hnat : (3905364479 : ℕ)^4875*20000000000000^3851 ≤ 6082923492693^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3905364479 10000000000 6082923492693 20000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434309213/1000000000 : ℝ)^4875 ≤ (34792690277581/100000000000000 : ℝ)^3851 := by
    have hnat : (434309213 : ℕ)^4875*100000000000000^3851 ≤ 34792690277581^3851*1000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434309213 1000000000 34792690277581 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4343092323/10000000000 : ℝ)^4875 ≤ (8698173058709/25000000000000 : ℝ)^3851 := by
    have hnat : (4343092323 : ℕ)^4875*25000000000000^3851 ≤ 8698173058709^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343092323 10000000000 8698173058709 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3905364479/10000000000 : ℝ), (434309213/1000000000 : ℝ), (4343092323/10000000000 : ℝ)] ![(6082923492693/20000000000000 : ℝ), (34792690277581/100000000000000 : ℝ), (8698173058709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3905364479/10000000000 : ℝ)|^4875 ≤ (6082923492693/20000000000000 : ℝ)^3851
        have hw : |(3905364479/10000000000 : ℝ)|=(3905364479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(434309213/1000000000 : ℝ)|^4875 ≤ (34792690277581/100000000000000 : ℝ)^3851
        have hw : |(434309213/1000000000 : ℝ)|=(434309213/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4343092323/10000000000 : ℝ)|^4875 ≤ (8698173058709/25000000000000 : ℝ)^3851
        have hw : |(4343092323/10000000000 : ℝ)|=(4343092323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_8 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1792622629/10000000000 : ℝ)*x 0 + (5075167157/10000000000 : ℝ)*x 1 + (5440377787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1792622629/10000000000 : ℝ)^4875 ≤ (141872387263/1250000000000 : ℝ)^3851 := by
    have hnat : (1792622629 : ℕ)^4875*1250000000000^3851 ≤ 141872387263^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792622629 10000000000 141872387263 1250000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075167157/10000000000 : ℝ)^4875 ≤ (339014384019/800000000000 : ℝ)^3851 := by
    have hnat : (5075167157 : ℕ)^4875*800000000000^3851 ≤ 339014384019^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075167157 10000000000 339014384019 800000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440377787/10000000000 : ℝ)^4875 ≤ (46273410994411/100000000000000 : ℝ)^3851 := by
    have hnat : (5440377787 : ℕ)^4875*100000000000000^3851 ≤ 46273410994411^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440377787 10000000000 46273410994411 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1792622629/10000000000 : ℝ), (5075167157/10000000000 : ℝ), (5440377787/10000000000 : ℝ)] ![(141872387263/1250000000000 : ℝ), (339014384019/800000000000 : ℝ), (46273410994411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1792622629/10000000000 : ℝ)|^4875 ≤ (141872387263/1250000000000 : ℝ)^3851
        have hw : |(-1792622629/10000000000 : ℝ)|=(1792622629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5075167157/10000000000 : ℝ)|^4875 ≤ (339014384019/800000000000 : ℝ)^3851
        have hw : |(5075167157/10000000000 : ℝ)|=(5075167157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440377787/10000000000 : ℝ)|^4875 ≤ (46273410994411/100000000000000 : ℝ)^3851
        have hw : |(5440377787/10000000000 : ℝ)|=(5440377787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_9 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230862457/10000000000 : ℝ)*x 0 + (-395777263/2500000000 : ℝ)*x 1 + (1088075207/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230862457/10000000000 : ℝ)^4875 ≤ (44029174749697/100000000000000 : ℝ)^3851 := by
    have hnat : (5230862457 : ℕ)^4875*100000000000000^3851 ≤ 44029174749697^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230862457 10000000000 44029174749697 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395777263/2500000000 : ℝ)^4875 ≤ (9697433099521/100000000000000 : ℝ)^3851 := by
    have hnat : (395777263 : ℕ)^4875*100000000000000^3851 ≤ 9697433099521^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395777263 2500000000 9697433099521 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088075207/2000000000 : ℝ)^4875 ≤ (11568348032561/25000000000000 : ℝ)^3851 := by
    have hnat : (1088075207 : ℕ)^4875*25000000000000^3851 ≤ 11568348032561^3851*2000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088075207 2000000000 11568348032561 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230862457/10000000000 : ℝ), (-395777263/2500000000 : ℝ), (1088075207/2000000000 : ℝ)] ![(44029174749697/100000000000000 : ℝ), (9697433099521/100000000000000 : ℝ), (11568348032561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230862457/10000000000 : ℝ)|^4875 ≤ (44029174749697/100000000000000 : ℝ)^3851
        have hw : |(5230862457/10000000000 : ℝ)|=(5230862457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395777263/2500000000 : ℝ)|^4875 ≤ (9697433099521/100000000000000 : ℝ)^3851
        have hw : |(-395777263/2500000000 : ℝ)|=(395777263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088075207/2000000000 : ℝ)|^4875 ≤ (11568348032561/25000000000000 : ℝ)^3851
        have hw : |(1088075207/2000000000 : ℝ)|=(1088075207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_10 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653857949/1250000000 : ℝ)*x 0 + (5440376089/10000000000 : ℝ)*x 1 + (-791553709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653857949/1250000000 : ℝ)^4875 ≤ (44029186843537/100000000000000 : ℝ)^3851 := by
    have hnat : (653857949 : ℕ)^4875*100000000000000^3851 ≤ 44029186843537^3851*1250000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653857949 1250000000 44029186843537 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440376089/10000000000 : ℝ)^4875 ≤ (23136696355837/50000000000000 : ℝ)^3851 := by
    have hnat : (5440376089 : ℕ)^4875*50000000000000^3851 ≤ 23136696355837^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440376089 10000000000 23136696355837 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (791553709/5000000000 : ℝ)^4875 ≤ (9697420428867/100000000000000 : ℝ)^3851 := by
    have hnat : (791553709 : ℕ)^4875*100000000000000^3851 ≤ 9697420428867^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791553709 5000000000 9697420428867 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653857949/1250000000 : ℝ), (5440376089/10000000000 : ℝ), (-791553709/5000000000 : ℝ)] ![(44029186843537/100000000000000 : ℝ), (23136696355837/50000000000000 : ℝ), (9697420428867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653857949/1250000000 : ℝ)|^4875 ≤ (44029186843537/100000000000000 : ℝ)^3851
        have hw : |(653857949/1250000000 : ℝ)|=(653857949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440376089/10000000000 : ℝ)|^4875 ≤ (23136696355837/50000000000000 : ℝ)^3851
        have hw : |(5440376089/10000000000 : ℝ)|=(5440376089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-791553709/5000000000 : ℝ)|^4875 ≤ (9697420428867/100000000000000 : ℝ)^3851
        have hw : |(-791553709/5000000000 : ℝ)|=(791553709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_11 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4549486773/10000000000 : ℝ)*x 0 + (2010071349/5000000000 : ℝ)*x 1 + (804028297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4549486773/10000000000 : ℝ)^4875 ≤ (36898857070351/100000000000000 : ℝ)^3851 := by
    have hnat : (4549486773 : ℕ)^4875*100000000000000^3851 ≤ 36898857070351^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549486773 10000000000 36898857070351 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010071349/5000000000 : ℝ)^4875 ≤ (197191109261/625000000000 : ℝ)^3851 := by
    have hnat : (2010071349 : ℕ)^4875*625000000000^3851 ≤ 197191109261^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010071349 5000000000 197191109261 625000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (804028297/2000000000 : ℝ)^4875 ≤ (3943820678829/12500000000000 : ℝ)^3851 := by
    have hnat : (804028297 : ℕ)^4875*12500000000000^3851 ≤ 3943820678829^3851*2000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804028297 2000000000 3943820678829 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4549486773/10000000000 : ℝ), (2010071349/5000000000 : ℝ), (804028297/2000000000 : ℝ)] ![(36898857070351/100000000000000 : ℝ), (197191109261/625000000000 : ℝ), (3943820678829/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4549486773/10000000000 : ℝ)|^4875 ≤ (36898857070351/100000000000000 : ℝ)^3851
        have hw : |(4549486773/10000000000 : ℝ)|=(4549486773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010071349/5000000000 : ℝ)|^4875 ≤ (197191109261/625000000000 : ℝ)^3851
        have hw : |(2010071349/5000000000 : ℝ)|=(2010071349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(804028297/2000000000 : ℝ)|^4875 ≤ (3943820678829/12500000000000 : ℝ)^3851
        have hw : |(804028297/2000000000 : ℝ)|=(804028297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_12 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-742131001/5000000000 : ℝ)*x 0 + (2772792389/5000000000 : ℝ)*x 1 + (5195574361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (742131001/5000000000 : ℝ)^4875 ≤ (446869922983/5000000000000 : ℝ)^3851 := by
    have hnat : (742131001 : ℕ)^4875*5000000000000^3851 ≤ 446869922983^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742131001 5000000000 446869922983 5000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2772792389/5000000000 : ℝ)^4875 ≤ (47409096527701/100000000000000 : ℝ)^3851 := by
    have hnat : (2772792389 : ℕ)^4875*100000000000000^3851 ≤ 47409096527701^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2772792389 5000000000 47409096527701 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195574361/10000000000 : ℝ)^4875 ≤ (4365350499877/10000000000000 : ℝ)^3851 := by
    have hnat : (5195574361 : ℕ)^4875*10000000000000^3851 ≤ 4365350499877^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195574361 10000000000 4365350499877 10000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-742131001/5000000000 : ℝ), (2772792389/5000000000 : ℝ), (5195574361/10000000000 : ℝ)] ![(446869922983/5000000000000 : ℝ), (47409096527701/100000000000000 : ℝ), (4365350499877/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-742131001/5000000000 : ℝ)|^4875 ≤ (446869922983/5000000000000 : ℝ)^3851
        have hw : |(-742131001/5000000000 : ℝ)|=(742131001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2772792389/5000000000 : ℝ)|^4875 ≤ (47409096527701/100000000000000 : ℝ)^3851
        have hw : |(2772792389/5000000000 : ℝ)|=(2772792389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195574361/10000000000 : ℝ)|^4875 ≤ (4365350499877/10000000000000 : ℝ)^3851
        have hw : |(5195574361/10000000000 : ℝ)|=(5195574361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_13 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168723399/312500000 : ℝ)*x 0 + (-168783591/1000000000 : ℝ)*x 1 + (162361707/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168723399/312500000 : ℝ)^4875 ≤ (45829937216579/100000000000000 : ℝ)^3851 := by
    have hnat : (168723399 : ℕ)^4875*100000000000000^3851 ≤ 45829937216579^3851*312500000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168723399 312500000 45829937216579 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168783591/1000000000 : ℝ)^4875 ≤ (2629138744337/25000000000000 : ℝ)^3851 := by
    have hnat : (168783591 : ℕ)^4875*25000000000000^3851 ≤ 2629138744337^3851*1000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168783591 1000000000 2629138744337 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162361707/312500000 : ℝ)^4875 ≤ (10913376949023/25000000000000 : ℝ)^3851 := by
    have hnat : (162361707 : ℕ)^4875*25000000000000^3851 ≤ 10913376949023^3851*312500000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162361707 312500000 10913376949023 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168723399/312500000 : ℝ), (-168783591/1000000000 : ℝ), (162361707/312500000 : ℝ)] ![(45829937216579/100000000000000 : ℝ), (2629138744337/25000000000000 : ℝ), (10913376949023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168723399/312500000 : ℝ)|^4875 ≤ (45829937216579/100000000000000 : ℝ)^3851
        have hw : |(168723399/312500000 : ℝ)|=(168723399/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-168783591/1000000000 : ℝ)|^4875 ≤ (2629138744337/25000000000000 : ℝ)^3851
        have hw : |(-168783591/1000000000 : ℝ)|=(168783591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162361707/312500000 : ℝ)|^4875 ≤ (10913376949023/25000000000000 : ℝ)^3851
        have hw : |(162361707/312500000 : ℝ)|=(162361707/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_14 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5399149697/10000000000 : ℝ)*x 0 + (2597786679/5000000000 : ℝ)*x 1 + (-33756727/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399149697/10000000000 : ℝ)^4875 ≤ (45829947199113/100000000000000 : ℝ)^3851 := by
    have hnat : (5399149697 : ℕ)^4875*100000000000000^3851 ≤ 45829947199113^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399149697 10000000000 45829947199113 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597786679/5000000000 : ℝ)^4875 ≤ (21826747165329/50000000000000 : ℝ)^3851 := by
    have hnat : (2597786679 : ℕ)^4875*50000000000000^3851 ≤ 21826747165329^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597786679 5000000000 21826747165329 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33756727/200000000 : ℝ)^4875 ≤ (657284902993/6250000000000 : ℝ)^3851 := by
    have hnat : (33756727 : ℕ)^4875*6250000000000^3851 ≤ 657284902993^3851*200000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33756727 200000000 657284902993 6250000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399149697/10000000000 : ℝ), (2597786679/5000000000 : ℝ), (-33756727/200000000 : ℝ)] ![(45829947199113/100000000000000 : ℝ), (21826747165329/50000000000000 : ℝ), (657284902993/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399149697/10000000000 : ℝ)|^4875 ≤ (45829947199113/100000000000000 : ℝ)^3851
        have hw : |(5399149697/10000000000 : ℝ)|=(5399149697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2597786679/5000000000 : ℝ)|^4875 ≤ (21826747165329/50000000000000 : ℝ)^3851
        have hw : |(2597786679/5000000000 : ℝ)|=(2597786679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33756727/200000000 : ℝ)|^4875 ≤ (657284902993/6250000000000 : ℝ)^3851
        have hw : |(-33756727/200000000 : ℝ)|=(33756727/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_box_15 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3846716889/10000000000 : ℝ)*x 0 + (1092879281/2500000000 : ℝ)*x 1 + (1092879437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3846716889/10000000000 : ℝ)^4875 ≤ (1864849010119/6250000000000 : ℝ)^3851 := by
    have hnat : (3846716889 : ℕ)^4875*6250000000000^3851 ≤ 1864849010119^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3846716889 10000000000 1864849010119 6250000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092879281/2500000000 : ℝ)^4875 ≤ (8770301185199/25000000000000 : ℝ)^3851 := by
    have hnat : (1092879281 : ℕ)^4875*25000000000000^3851 ≤ 8770301185199^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092879281 2500000000 8770301185199 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092879437/2500000000 : ℝ)^4875 ≤ (17540605539951/50000000000000 : ℝ)^3851 := by
    have hnat : (1092879437 : ℕ)^4875*50000000000000^3851 ≤ 17540605539951^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092879437 2500000000 17540605539951 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3846716889/10000000000 : ℝ), (1092879281/2500000000 : ℝ), (1092879437/2500000000 : ℝ)] ![(1864849010119/6250000000000 : ℝ), (8770301185199/25000000000000 : ℝ), (17540605539951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3846716889/10000000000 : ℝ)|^4875 ≤ (1864849010119/6250000000000 : ℝ)^3851
        have hw : |(3846716889/10000000000 : ℝ)|=(3846716889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092879281/2500000000 : ℝ)|^4875 ≤ (8770301185199/25000000000000 : ℝ)^3851
        have hw : |(1092879281/2500000000 : ℝ)|=(1092879281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092879437/2500000000 : ℝ)|^4875 ≤ (17540605539951/50000000000000 : ℝ)^3851
        have hw : |(1092879437/2500000000 : ℝ)|=(1092879437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1639_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16289/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10611/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65023/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58507/100000 : ℝ) ∧ (40497/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (22029/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16289/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10611/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16289/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10611/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16289/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10611/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16289/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10611/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16289/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10611/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16289/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10611/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10611/100000 : ℝ) ^ (4871/1024 : ℝ) ≤ (1160520000250279/50000000000000000000 : ℝ) := by
    have hpowers : (10611/100000 : ℝ)^4871 ≤ (1160520000250279/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10611 : ℕ)^4871*50000000000000000000^1024 ≤ 1160520000250279^1024*100000^4871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10611 100000 1160520000250279 50000000000000000000 4871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10611/100000 : ℝ)) (X := (1160520000250279/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16289/100000 : ℝ) ^ (4871/1024 : ℝ) ≤ (8914173333258247/50000000000000000000 : ℝ) := by
    have hpowers : (16289/100000 : ℝ)^4871 ≤ (8914173333258247/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16289 : ℕ)^4871*50000000000000000000^1024 ≤ 8914173333258247^1024*100000^4871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16289 100000 8914173333258247 50000000000000000000 4871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16289/100000 : ℝ)) (X := (8914173333258247/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001160520000250279/25000000000000000000 : ℝ) ≤ (2500024396442143/2500000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (25001160520000250279/25000000000000000000 : ℝ)^1024 ≤ (2500024396442143/2500000000000000 : ℝ)^4871 := by
      have hnat : (25001160520000250279 : ℕ)^1024*2500000000000000^4871 ≤ 2500024396442143^4871*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001160520000250279 25000000000000000000 2500024396442143 2500000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500024396442143/2500000000000000 : ℝ)) (X := (25001160520000250279/25000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25005037346666754263/25000000000000000000 : ℝ) ≤ (5000211777154893/5000000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (25005037346666754263/25000000000000000000 : ℝ)^1024 ≤ (5000211777154893/5000000000000000 : ℝ)^4871 := by
      have hnat : (25005037346666754263 : ℕ)^1024*5000000000000000^4871 ≤ 5000211777154893^4871*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005037346666754263 25000000000000000000 5000211777154893 5000000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000211777154893/5000000000000000 : ℝ)) (X := (25005037346666754263/25000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008914173333258247/25000000000000000000 : ℝ) ≤ (10000749522851/10000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (25008914173333258247/25000000000000000000 : ℝ)^1024 ≤ (10000749522851/10000000000000 : ℝ)^4871 := by
      have hnat : (25008914173333258247 : ℕ)^1024*10000000000000^4871 ≤ 10000749522851^4871*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008914173333258247 25000000000000000000 10000749522851 10000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000749522851/10000000000000 : ℝ)) (X := (25008914173333258247/25000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1160520000250279/50000000000000000000 : ℝ) ≤ ((14193409096903077077/14195000000000000000 : ℝ)+2*(162984270607/283900000000000 : ℝ)*(10611/100000 : ℝ))^(4871/1024 : ℝ) := by
    rw [show (14193409096903077077/14195000000000000000 : ℝ)+2*(162984270607/283900000000000 : ℝ)*(10611/100000 : ℝ)=(2500024396442143/2500000000000000 : ℝ) by norm_num, show 1+2*(1160520000250279/50000000000000000000 : ℝ)=(25001160520000250279/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8914173333258247/50000000000000000000 : ℝ)+(1160520000250279/50000000000000000000 : ℝ) ≤ ((14193409096903077077/14195000000000000000 : ℝ)+(162984270607/283900000000000 : ℝ)*((16289/100000 : ℝ)+(10611/100000 : ℝ)))^(4871/1024 : ℝ) := by
    rw [show (14193409096903077077/14195000000000000000 : ℝ)+(162984270607/283900000000000 : ℝ)*((16289/100000 : ℝ)+(10611/100000 : ℝ))=(5000211777154893/5000000000000000 : ℝ) by norm_num, show 1+(8914173333258247/50000000000000000000 : ℝ)+(1160520000250279/50000000000000000000 : ℝ)=(25005037346666754263/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8914173333258247/50000000000000000000 : ℝ) ≤ ((14193409096903077077/14195000000000000000 : ℝ)+2*(162984270607/283900000000000 : ℝ)*(16289/100000 : ℝ))^(4871/1024 : ℝ) := by
    rw [show (14193409096903077077/14195000000000000000 : ℝ)+2*(162984270607/283900000000000 : ℝ)*(16289/100000 : ℝ)=(10000749522851/10000000000000 : ℝ) by norm_num, show 1+2*(8914173333258247/50000000000000000000 : ℝ)=(25008914173333258247/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14193409096903077077/14195000000000000000 : ℝ)*(X 1 0+X 2 0)+(162984270607/283900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (10611/100000 : ℝ)) (hi := (16289/100000 : ℝ)) (c := (14193409096903077077/14195000000000000000 : ℝ)) (alpha := (162984270607/283900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14193409096903077077/14195000000000000000 : ℝ)*(X 0 1+X 2 1)+(162984270607/283900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (10611/100000 : ℝ)) (hi := (16289/100000 : ℝ)) (c := (14193409096903077077/14195000000000000000 : ℝ)) (alpha := (162984270607/283900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14193409096903077077/14195000000000000000 : ℝ)*(X 0 2+X 1 2)+(162984270607/283900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (10611/100000 : ℝ)) (hi := (16289/100000 : ℝ)) (c := (14193409096903077077/14195000000000000000 : ℝ)) (alpha := (162984270607/283900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1371937611/10000000000 : ℝ)*X 0 0+(169087037/312500000 : ℝ)*X 0 1+(5410785141/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((525120367/1000000000 : ℝ)*X 1 0+(-1596187493/10000000000 : ℝ)*X 1 1+(2705392549/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5251203793/10000000000 : ℝ)*X 2 0+(5410785123/10000000000 : ℝ)*X 2 1+(-1596187289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((55835323/125000000 : ℝ)*X 0 0+(2031345569/5000000000 : ℝ)*X 0 1+(1015672831/2500000000 : ℝ)*X 0 2+(55835323/125000000 : ℝ)*X 1 0+(2031345569/5000000000 : ℝ)*X 1 1+(1015672831/2500000000 : ℝ)*X 1 2+(55835323/125000000 : ℝ)*X 2 0+(2031345569/5000000000 : ℝ)*X 2 1+(1015672831/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-47664337/250000000 : ℝ)*X 0 0+(1043083161/2000000000 : ℝ)*X 0 1+(5215415707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5385501043/10000000000 : ℝ)*X 1 0+(-167964821/1000000000 : ℝ)*X 1 1+(5215415749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5385501063/10000000000 : ℝ)*X 2 0+(41723327/80000000 : ℝ)*X 2 1+(-839824007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3905364479/10000000000 : ℝ)*X 0 0+(434309213/1000000000 : ℝ)*X 0 1+(4343092323/10000000000 : ℝ)*X 0 2+(3905364479/10000000000 : ℝ)*X 1 0+(434309213/1000000000 : ℝ)*X 1 1+(4343092323/10000000000 : ℝ)*X 1 2+(3905364479/10000000000 : ℝ)*X 2 0+(434309213/1000000000 : ℝ)*X 2 1+(4343092323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1792622629/10000000000 : ℝ)*X 0 0+(5075167157/10000000000 : ℝ)*X 0 1+(5440377787/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230862457/10000000000 : ℝ)*X 1 0+(-395777263/2500000000 : ℝ)*X 1 1+(1088075207/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((653857949/1250000000 : ℝ)*X 2 0+(5440376089/10000000000 : ℝ)*X 2 1+(-791553709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4549486773/10000000000 : ℝ)*X 0 0+(2010071349/5000000000 : ℝ)*X 0 1+(804028297/2000000000 : ℝ)*X 0 2+(4549486773/10000000000 : ℝ)*X 1 0+(2010071349/5000000000 : ℝ)*X 1 1+(804028297/2000000000 : ℝ)*X 1 2+(4549486773/10000000000 : ℝ)*X 2 0+(2010071349/5000000000 : ℝ)*X 2 1+(804028297/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-742131001/5000000000 : ℝ)*X 0 0+(2772792389/5000000000 : ℝ)*X 0 1+(5195574361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((168723399/312500000 : ℝ)*X 1 0+(-168783591/1000000000 : ℝ)*X 1 1+(162361707/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5399149697/10000000000 : ℝ)*X 2 0+(2597786679/5000000000 : ℝ)*X 2 1+(-33756727/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3846716889/10000000000 : ℝ)*X 0 0+(1092879281/2500000000 : ℝ)*X 0 1+(1092879437/2500000000 : ℝ)*X 0 2+(3846716889/10000000000 : ℝ)*X 1 0+(1092879281/2500000000 : ℝ)*X 1 1+(1092879437/2500000000 : ℝ)*X 1 2+(3846716889/10000000000 : ℝ)*X 2 0+(1092879281/2500000000 : ℝ)*X 2 1+(1092879437/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65023/100000 : ℝ) ≤ (-461482794628935911588880008389479/709750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7072537/25000000000000 : ℝ)*(lower1) + (38387273/100000000000000 : ℝ)*(lower2) + (7534129/20000000000000 : ℝ)*(lower3) + (204553/25000000000000 : ℝ)*(lower4) + (17219281/100000000000000 : ℝ)*(lower5) + (1737937863363591/100000000000000 : ℝ)*(major0) + (1737937863363591/100000000000000 : ℝ)*(major1) + (1737937863363591/100000000000000 : ℝ)*(major2) + (2518823232852989/100000000000000 : ℝ)*(sp4) + (1259412060046987/50000000000000 : ℝ)*(sp5) + (1259400142585727/50000000000000 : ℝ)*(sp6) + (244681274261669/25000000000000 : ℝ)*(sp7) + (177448197/20000000000000 : ℝ)*(sp8) + (23834922521/100000000000000 : ℝ)*(sp14) + (244681274261669/25000000000000 : ℝ)*(f.failure) + (1259412060046987/50000000000000 : ℝ)*(f.sum) + (5878547474367/3548750000000000000000000000 : ℝ)*base66 + (307532811437038029/83500000000000000000000000000000 : ℝ)*base68 + (273912249546961971/83500000000000000000000000000000 : ℝ)*base69 + (237158061226961971/83500000000000000000000000000000 : ℝ)*base71 + (33668339291563/14195000000000000000000000000 : ℝ)*base74 + (193445442471038029/83500000000000000000000000000000 : ℝ)*base76 + (739363321332538029/83500000000000000000000000000000 : ℝ)*base78 + (48833694100038029/83500000000000000000000000000000 : ℝ)*base80 + (30878251941547/14195000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4138251/500000000000000000000 : ℝ)*base90 + (4138251/500000000000000000000 : ℝ)*base92 + (4138251/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58507/100000 : ℝ) ≤ (8305445374874117373250132923/14195000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2109893/4000000000000 : ℝ)*(upper0) + (50102767/50000000000000 : ℝ)*(upper2) + (3991967/20000000000000 : ℝ)*(upper3) + (83515959/50000000000000 : ℝ)*(upper4) + (17420271/100000000000000 : ℝ)*(upper5) + (913393298248909/50000000000000 : ℝ)*(major0) + (913393298248909/50000000000000 : ℝ)*(major1) + (913393298248909/50000000000000 : ℝ)*(major2) + (130265471919581/5000000000000 : ℝ)*(sp0) + (1302649453619819/50000000000000 : ℝ)*(sp1) + (104212337745023/4000000000000 : ℝ)*(sp2) + (128595067078561/12500000000000 : ℝ)*(sp3) + (248691511/25000000000000 : ℝ)*(sp6) + (5265575991/50000000000000 : ℝ)*(sp9) + (128595067078561/12500000000000 : ℝ)*(f.failure) + (130265471919581/5000000000000 : ℝ)*(f.sum) + (16700169916987/7097500000000000000000000000 : ℝ)*base66 + (317668798108099471/41750000000000000000000000000000 : ℝ)*base68 + (19743265867099471/41750000000000000000000000000000 : ℝ)*base70 + (564346323835599471/41750000000000000000000000000000 : ℝ)*base72 + (51325206149507/1774375000000000000000000000 : ℝ)*base73 + (22593427093400529/41750000000000000000000000000000 : ℝ)*base75 + (50627021496650529/41750000000000000000000000000000 : ℝ)*base77 + (1147960311588150529/41750000000000000000000000000000 : ℝ)*base79 + (40014858096069/14195000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2572081/250000000000000000000 : ℝ)*base89 + (2572081/250000000000000000000 : ℝ)*base91 + (2572081/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40497/50000 : ℝ) ≤ (287435402490954401565471543490131/354875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10727833/10000000000000 : ℝ)*(upper1) + (91986751/25000000000000 : ℝ)*(lower3) + (102415613/25000000000000 : ℝ)*(upper4) + (4144871/50000000000000 : ℝ)*(lower5) + (962232830148967/50000000000000 : ℝ)*(major0) + (962232830148967/50000000000000 : ℝ)*(major1) + (962232830148967/50000000000000 : ℝ)*(major2) + (1520972083/100000000000000 : ℝ)*(sp0) + (1944540547/4000000000000 : ℝ)*(sp2) + (35655213909/50000000000000 : ℝ)*(sp3) + (2738162249045083/100000000000000 : ℝ)*(sp8) + (1369081885008583/50000000000000 : ℝ)*(sp9) + (2738115156503491/100000000000000 : ℝ)*(sp10) + (67731093367473/6250000000000 : ℝ)*(sp11) + (541884402153693/50000000000000 : ℝ)*(f.failure) + (1369081885008583/50000000000000 : ℝ)*(f.sum) + (2765563424229/7097500000000000000000000000 : ℝ)*base65 + (165500447694462973/41750000000000000000000000000000 : ℝ)*base68 + (213583542143212973/41750000000000000000000000000000 : ℝ)*base70 + (172592912435712973/41750000000000000000000000000000 : ℝ)*base72 + (3607252741159/7097500000000000000000000000 : ℝ)*base73 + (353781160458712973/41750000000000000000000000000000 : ℝ)*base76 + (107263851984462973/41750000000000000000000000000000 : ℝ)*base78 + (286597425771212973/41750000000000000000000000000000 : ℝ)*base80 + (61922440281133/14195000000000000000000000000 : ℝ)*base81 + (4537453/1000000000000000000000 : ℝ)*base89 + (4537453/1000000000000000000000 : ℝ)*base91 + (4537453/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-22029/25000 : ℝ) ≤ (-62538437145954815086878167659839/70975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55502111/100000000000000 : ℝ)*(lower1) + (12590753/100000000000000 : ℝ)*(lower2) + (39626123/100000000000000 : ℝ)*(upper5) + (196798353570677/10000000000000 : ℝ)*(major0) + (196798353570677/10000000000000 : ℝ)*(major1) + (196798353570677/10000000000000 : ℝ)*(major2) + (148285283/4000000000000 : ℝ)*(sp0) + (1515611033/5000000000000 : ℝ)*(sp5) + (215552418119/100000000000000 : ℝ)*(sp6) + (1304303413/20000000000000 : ℝ)*(sp7) + (2857058444043411/100000000000000 : ℝ)*(sp12) + (1428515919477413/50000000000000 : ℝ)*(sp13) + (357105824844671/12500000000000 : ℝ)*(sp14) + (1108269509274441/100000000000000 : ℝ)*(sp15) + (554138015395753/50000000000000 : ℝ)*(f.failure) + (1428531075587743/50000000000000 : ℝ)*(f.sum) + (449935931333/567800000000000000000000000 : ℝ)*base66 + (52779241304963463/8350000000000000000000000000000 : ℝ)*base68 + (34577519831913463/8350000000000000000000000000000 : ℝ)*base70 + (25778432808963463/8350000000000000000000000000000 : ℝ)*base72 + (1371839961801/354875000000000000000000000 : ℝ)*base74 + (113719043762213463/8350000000000000000000000000000 : ℝ)*base76 + (49383676104713463/8350000000000000000000000000000 : ℝ)*base78 + (121276515001813463/8350000000000000000000000000000 : ℝ)*base80 + (2369810737441/567800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (14078713/1000000000000000000000 : ℝ)*base89 + (14078713/1000000000000000000000 : ℝ)*base91 + (14078713/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1639_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16289/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10611/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65023/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58507/100000 : ℝ) else (40497/50000 : ℝ) ≤ X j i ∧ X j i ≤ (22029/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1639_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1639_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65023/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58507/100000 : ℝ) else (40497/50000 : ℝ) ≤ X j i ∧ X j i ≤ (22029/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1639_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1639_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1639_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65023/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58507/100000 : ℝ) else (40497/50000 : ℝ) ≤ X j i ∧ X j i ≤ (22029/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1639_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
