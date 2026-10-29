-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1311_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:39:54.323166+00:00
-- url     : https://prove2.me/submissions/10a1292e-91b3-4985-99fa-9dd81b58bff5

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
theorem support_rectangle_w1311_box_0 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-475325659/2500000000 : ℝ)*x 0 + (336951741/625000000 : ℝ)*x 1 + (16847587/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (475325659/2500000000 : ℝ)^4271 ≤ (11263855279699/100000000000000 : ℝ)^3247 := by
    have hnat : (475325659 : ℕ)^4271*100000000000000^3247 ≤ 11263855279699^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475325659 2500000000 11263855279699 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336951741/625000000 : ℝ)^4271 ≤ (44368072440577/100000000000000 : ℝ)^3247 := by
    have hnat : (336951741 : ℕ)^4271*100000000000000^3247 ≤ 44368072440577^3247*625000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336951741 625000000 44368072440577 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16847587/31250000 : ℝ)^4271 ≤ (2773004516711/6250000000000 : ℝ)^3247 := by
    have hnat : (16847587 : ℕ)^4271*6250000000000^3247 ≤ 2773004516711^3247*31250000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16847587 31250000 2773004516711 6250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-475325659/2500000000 : ℝ), (336951741/625000000 : ℝ), (16847587/31250000 : ℝ)] ![(11263855279699/100000000000000 : ℝ), (44368072440577/100000000000000 : ℝ), (2773004516711/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-475325659/2500000000 : ℝ)|^4271 ≤ (11263855279699/100000000000000 : ℝ)^3247
        have hw : |(-475325659/2500000000 : ℝ)|=(475325659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336951741/625000000 : ℝ)|^4271 ≤ (44368072440577/100000000000000 : ℝ)^3247
        have hw : |(336951741/625000000 : ℝ)|=(336951741/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16847587/31250000 : ℝ)|^4271 ≤ (2773004516711/6250000000000 : ℝ)^3247
        have hw : |(16847587/31250000 : ℝ)|=(16847587/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_1 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5284696517/10000000000 : ℝ)*x 0 + (-2047093509/10000000000 : ℝ)*x 1 + (2695614041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284696517/10000000000 : ℝ)^4271 ≤ (4321847428569/10000000000000 : ℝ)^3247 := by
    have hnat : (5284696517 : ℕ)^4271*10000000000000^3247 ≤ 4321847428569^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284696517 10000000000 4321847428569 10000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2047093509/10000000000 : ℝ)^4271 ≤ (6206725401789/50000000000000 : ℝ)^3247 := by
    have hnat : (2047093509 : ℕ)^4271*50000000000000^3247 ≤ 6206725401789^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047093509 10000000000 6206725401789 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695614041/5000000000 : ℝ)^4271 ≤ (69325117011/156250000000 : ℝ)^3247 := by
    have hnat : (2695614041 : ℕ)^4271*156250000000^3247 ≤ 69325117011^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695614041 5000000000 69325117011 156250000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284696517/10000000000 : ℝ), (-2047093509/10000000000 : ℝ), (2695614041/5000000000 : ℝ)] ![(4321847428569/10000000000000 : ℝ), (6206725401789/50000000000000 : ℝ), (69325117011/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284696517/10000000000 : ℝ)|^4271 ≤ (4321847428569/10000000000000 : ℝ)^3247
        have hw : |(5284696517/10000000000 : ℝ)|=(5284696517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2047093509/10000000000 : ℝ)|^4271 ≤ (6206725401789/50000000000000 : ℝ)^3247
        have hw : |(-2047093509/10000000000 : ℝ)|=(2047093509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695614041/5000000000 : ℝ)|^4271 ≤ (69325117011/156250000000 : ℝ)^3247
        have hw : |(2695614041/5000000000 : ℝ)|=(2695614041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_2 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5284696809/10000000000 : ℝ)*x 0 + (336951739/625000000 : ℝ)*x 1 + (-1023546733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284696809/10000000000 : ℝ)^4271 ≤ (43218477426773/100000000000000 : ℝ)^3247 := by
    have hnat : (5284696809 : ℕ)^4271*100000000000000^3247 ≤ 43218477426773^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284696809 10000000000 43218477426773 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336951739/625000000 : ℝ)^4271 ≤ (1774722883767/4000000000000 : ℝ)^3247 := by
    have hnat : (336951739 : ℕ)^4271*4000000000000^3247 ≤ 1774722883767^3247*625000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336951739 625000000 1774722883767 4000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023546733/5000000000 : ℝ)^4271 ≤ (3103362615149/25000000000000 : ℝ)^3247 := by
    have hnat : (1023546733 : ℕ)^4271*25000000000000^3247 ≤ 3103362615149^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023546733 5000000000 3103362615149 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284696809/10000000000 : ℝ), (336951739/625000000 : ℝ), (-1023546733/5000000000 : ℝ)] ![(43218477426773/100000000000000 : ℝ), (1774722883767/4000000000000 : ℝ), (3103362615149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284696809/10000000000 : ℝ)|^4271 ≤ (43218477426773/100000000000000 : ℝ)^3247
        have hw : |(5284696809/10000000000 : ℝ)|=(5284696809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336951739/625000000 : ℝ)|^4271 ≤ (1774722883767/4000000000000 : ℝ)^3247
        have hw : |(336951739/625000000 : ℝ)|=(336951739/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1023546733/5000000000 : ℝ)|^4271 ≤ (3103362615149/25000000000000 : ℝ)^3247
        have hw : |(-1023546733/5000000000 : ℝ)|=(1023546733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_3 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4483734059/10000000000 : ℝ)*x 0 + (4264283647/10000000000 : ℝ)*x 1 + (2132141853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4483734059/10000000000 : ℝ)^4271 ≤ (17407972568621/50000000000000 : ℝ)^3247 := by
    have hnat : (4483734059 : ℕ)^4271*50000000000000^3247 ≤ 17407972568621^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483734059 10000000000 17407972568621 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4264283647/10000000000 : ℝ)^4271 ≤ (32592027129303/100000000000000 : ℝ)^3247 := by
    have hnat : (4264283647 : ℕ)^4271*100000000000000^3247 ≤ 32592027129303^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4264283647 10000000000 32592027129303 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132141853/5000000000 : ℝ)^4271 ≤ (32592027722453/100000000000000 : ℝ)^3247 := by
    have hnat : (2132141853 : ℕ)^4271*100000000000000^3247 ≤ 32592027722453^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132141853 5000000000 32592027722453 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4483734059/10000000000 : ℝ), (4264283647/10000000000 : ℝ), (2132141853/5000000000 : ℝ)] ![(17407972568621/50000000000000 : ℝ), (32592027129303/100000000000000 : ℝ), (32592027722453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4483734059/10000000000 : ℝ)|^4271 ≤ (17407972568621/50000000000000 : ℝ)^3247
        have hw : |(4483734059/10000000000 : ℝ)|=(4483734059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4264283647/10000000000 : ℝ)|^4271 ≤ (32592027129303/100000000000000 : ℝ)^3247
        have hw : |(4264283647/10000000000 : ℝ)|=(4264283647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2132141853/5000000000 : ℝ)|^4271 ≤ (32592027722453/100000000000000 : ℝ)^3247
        have hw : |(2132141853/5000000000 : ℝ)|=(2132141853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_4 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-112179159/500000000 : ℝ)*x 0 + (658023913/1250000000 : ℝ)*x 1 + (1316047849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112179159/500000000 : ℝ)^4271 ≤ (2800787002449/20000000000000 : ℝ)^3247 := by
    have hnat : (112179159 : ℕ)^4271*20000000000000^3247 ≤ 2800787002449^3247*500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112179159 500000000 2800787002449 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658023913/1250000000 : ℝ)^4271 ≤ (10749507998853/25000000000000 : ℝ)^3247 := by
    have hnat : (658023913 : ℕ)^4271*25000000000000^3247 ≤ 10749507998853^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658023913 1250000000 10749507998853 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316047849/2500000000 : ℝ)^4271 ≤ (2687377061491/6250000000000 : ℝ)^3247 := by
    have hnat : (1316047849 : ℕ)^4271*6250000000000^3247 ≤ 2687377061491^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316047849 2500000000 2687377061491 6250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-112179159/500000000 : ℝ), (658023913/1250000000 : ℝ), (1316047849/2500000000 : ℝ)] ![(2800787002449/20000000000000 : ℝ), (10749507998853/25000000000000 : ℝ), (2687377061491/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-112179159/500000000 : ℝ)|^4271 ≤ (2800787002449/20000000000000 : ℝ)^3247
        have hw : |(-112179159/500000000 : ℝ)|=(112179159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658023913/1250000000 : ℝ)|^4271 ≤ (10749507998853/25000000000000 : ℝ)^3247
        have hw : |(658023913/1250000000 : ℝ)|=(658023913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316047849/2500000000 : ℝ)|^4271 ≤ (2687377061491/6250000000000 : ℝ)^3247
        have hw : |(1316047849/2500000000 : ℝ)|=(1316047849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_5 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374042451/10000000000 : ℝ)*x 0 + (-262230613/1250000000 : ℝ)*x 1 + (5264191447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374042451/10000000000 : ℝ)^4271 ≤ (4418213304321/10000000000000 : ℝ)^3247 := by
    have hnat : (5374042451 : ℕ)^4271*10000000000000^3247 ≤ 4418213304321^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374042451 10000000000 4418213304321 10000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262230613/1250000000 : ℝ)^4271 ≤ (3204958353763/25000000000000 : ℝ)^3247 := by
    have hnat : (262230613 : ℕ)^4271*25000000000000^3247 ≤ 3204958353763^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262230613 1250000000 3204958353763 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264191447/10000000000 : ℝ)^4271 ≤ (21499016765899/50000000000000 : ℝ)^3247 := by
    have hnat : (5264191447 : ℕ)^4271*50000000000000^3247 ≤ 21499016765899^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264191447 10000000000 21499016765899 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374042451/10000000000 : ℝ), (-262230613/1250000000 : ℝ), (5264191447/10000000000 : ℝ)] ![(4418213304321/10000000000000 : ℝ), (3204958353763/25000000000000 : ℝ), (21499016765899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374042451/10000000000 : ℝ)|^4271 ≤ (4418213304321/10000000000000 : ℝ)^3247
        have hw : |(5374042451/10000000000 : ℝ)|=(5374042451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262230613/1250000000 : ℝ)|^4271 ≤ (3204958353763/25000000000000 : ℝ)^3247
        have hw : |(-262230613/1250000000 : ℝ)|=(262230613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264191447/10000000000 : ℝ)|^4271 ≤ (21499016765899/50000000000000 : ℝ)^3247
        have hw : |(5264191447/10000000000 : ℝ)|=(5264191447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_6 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268702121/500000000 : ℝ)*x 0 + (658023923/1250000000 : ℝ)*x 1 + (-209784503/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268702121/500000000 : ℝ)^4271 ≤ (44182132707971/100000000000000 : ℝ)^3247 := by
    have hnat : (268702121 : ℕ)^4271*100000000000000^3247 ≤ 44182132707971^3247*500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268702121 500000000 44182132707971 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658023923/1250000000 : ℝ)^4271 ≤ (42998032854929/100000000000000 : ℝ)^3247 := by
    have hnat : (658023923 : ℕ)^4271*100000000000000^3247 ≤ 42998032854929^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658023923 1250000000 42998032854929 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209784503/1000000000 : ℝ)^4271 ≤ (12819834427859/100000000000000 : ℝ)^3247 := by
    have hnat : (209784503 : ℕ)^4271*100000000000000^3247 ≤ 12819834427859^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209784503 1000000000 12819834427859 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268702121/500000000 : ℝ), (658023923/1250000000 : ℝ), (-209784503/1000000000 : ℝ)] ![(44182132707971/100000000000000 : ℝ), (42998032854929/100000000000000 : ℝ), (12819834427859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268702121/500000000 : ℝ)|^4271 ≤ (44182132707971/100000000000000 : ℝ)^3247
        have hw : |(268702121/500000000 : ℝ)|=(268702121/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658023923/1250000000 : ℝ)|^4271 ≤ (42998032854929/100000000000000 : ℝ)^3247
        have hw : |(658023923/1250000000 : ℝ)|=(658023923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209784503/1000000000 : ℝ)|^4271 ≤ (12819834427859/100000000000000 : ℝ)^3247
        have hw : |(-209784503/1000000000 : ℝ)|=(209784503/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_7 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209248711/500000000 : ℝ)*x 0 + (4413608969/10000000000 : ℝ)*x 1 + (2206804441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209248711/500000000 : ℝ)^4271 ≤ (3974630847097/12500000000000 : ℝ)^3247 := by
    have hnat : (209248711 : ℕ)^4271*12500000000000^3247 ≤ 3974630847097^3247*500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209248711 500000000 3974630847097 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4413608969/10000000000 : ℝ)^4271 ≤ (6820295409097/20000000000000 : ℝ)^3247 := by
    have hnat : (4413608969 : ℕ)^4271*20000000000000^3247 ≤ 6820295409097^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413608969 10000000000 6820295409097 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206804441/5000000000 : ℝ)^4271 ≤ (17050738080647/50000000000000 : ℝ)^3247 := by
    have hnat : (2206804441 : ℕ)^4271*50000000000000^3247 ≤ 17050738080647^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206804441 5000000000 17050738080647 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209248711/500000000 : ℝ), (4413608969/10000000000 : ℝ), (2206804441/5000000000 : ℝ)] ![(3974630847097/12500000000000 : ℝ), (6820295409097/20000000000000 : ℝ), (17050738080647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209248711/500000000 : ℝ)|^4271 ≤ (3974630847097/12500000000000 : ℝ)^3247
        have hw : |(209248711/500000000 : ℝ)|=(209248711/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4413608969/10000000000 : ℝ)|^4271 ≤ (6820295409097/20000000000000 : ℝ)^3247
        have hw : |(4413608969/10000000000 : ℝ)|=(4413608969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2206804441/5000000000 : ℝ)|^4271 ≤ (17050738080647/50000000000000 : ℝ)^3247
        have hw : |(2206804441/5000000000 : ℝ)|=(2206804441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_8 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171789991/10000000000 : ℝ)*x 0 + (1294221229/2500000000 : ℝ)*x 1 + (2702629779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171789991/10000000000 : ℝ)^4271 ≤ (13417492790517/100000000000000 : ℝ)^3247 := by
    have hnat : (2171789991 : ℕ)^4271*100000000000000^3247 ≤ 13417492790517^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171789991 10000000000 13417492790517 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294221229/2500000000 : ℝ)^4271 ≤ (8412495697469/20000000000000 : ℝ)^3247 := by
    have hnat : (1294221229 : ℕ)^4271*20000000000000^3247 ≤ 8412495697469^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294221229 2500000000 8412495697469 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702629779/5000000000 : ℝ)^4271 ≤ (44520028703/100000000000 : ℝ)^3247 := by
    have hnat : (2702629779 : ℕ)^4271*100000000000^3247 ≤ 44520028703^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702629779 5000000000 44520028703 100000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171789991/10000000000 : ℝ), (1294221229/2500000000 : ℝ), (2702629779/5000000000 : ℝ)] ![(13417492790517/100000000000000 : ℝ), (8412495697469/20000000000000 : ℝ), (44520028703/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171789991/10000000000 : ℝ)|^4271 ≤ (13417492790517/100000000000000 : ℝ)^3247
        have hw : |(-2171789991/10000000000 : ℝ)|=(2171789991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294221229/2500000000 : ℝ)|^4271 ≤ (8412495697469/20000000000000 : ℝ)^3247
        have hw : |(1294221229/2500000000 : ℝ)|=(1294221229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702629779/5000000000 : ℝ)|^4271 ≤ (44520028703/100000000000 : ℝ)^3247
        have hw : |(2702629779/5000000000 : ℝ)|=(2702629779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_9 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274822027/10000000000 : ℝ)*x 0 + (-2041353909/10000000000 : ℝ)*x 1 + (5405259253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274822027/10000000000 : ℝ)^4271 ≤ (43112284362939/100000000000000 : ℝ)^3247 := by
    have hnat : (5274822027 : ℕ)^4271*100000000000000^3247 ≤ 43112284362939^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274822027 10000000000 43112284362939 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2041353909/10000000000 : ℝ)^4271 ≤ (12367690216883/100000000000000 : ℝ)^3247 := by
    have hnat : (2041353909 : ℕ)^4271*100000000000000^3247 ≤ 12367690216883^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041353909 10000000000 12367690216883 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405259253/10000000000 : ℝ)^4271 ≤ (890400507973/2000000000000 : ℝ)^3247 := by
    have hnat : (5405259253 : ℕ)^4271*2000000000000^3247 ≤ 890400507973^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405259253 10000000000 890400507973 2000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274822027/10000000000 : ℝ), (-2041353909/10000000000 : ℝ), (5405259253/10000000000 : ℝ)] ![(43112284362939/100000000000000 : ℝ), (12367690216883/100000000000000 : ℝ), (890400507973/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274822027/10000000000 : ℝ)|^4271 ≤ (43112284362939/100000000000000 : ℝ)^3247
        have hw : |(5274822027/10000000000 : ℝ)|=(5274822027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2041353909/10000000000 : ℝ)|^4271 ≤ (12367690216883/100000000000000 : ℝ)^3247
        have hw : |(-2041353909/10000000000 : ℝ)|=(2041353909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405259253/10000000000 : ℝ)|^4271 ≤ (890400507973/2000000000000 : ℝ)^3247
        have hw : |(5405259253/10000000000 : ℝ)|=(5405259253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_10 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274822343/10000000000 : ℝ)*x 0 + (5405259707/10000000000 : ℝ)*x 1 + (-1020676433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274822343/10000000000 : ℝ)^4271 ≤ (4311228776019/10000000000000 : ℝ)^3247 := by
    have hnat : (5274822343 : ℕ)^4271*10000000000000^3247 ≤ 4311228776019^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274822343 10000000000 4311228776019 10000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405259707/10000000000 : ℝ)^4271 ≤ (5565003789657/12500000000000 : ℝ)^3247 := by
    have hnat : (5405259707 : ℕ)^4271*12500000000000^3247 ≤ 5565003789657^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405259707 10000000000 5565003789657 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020676433/5000000000 : ℝ)^4271 ≤ (12367681904953/100000000000000 : ℝ)^3247 := by
    have hnat : (1020676433 : ℕ)^4271*100000000000000^3247 ≤ 12367681904953^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020676433 5000000000 12367681904953 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274822343/10000000000 : ℝ), (5405259707/10000000000 : ℝ), (-1020676433/5000000000 : ℝ)] ![(4311228776019/10000000000000 : ℝ), (5565003789657/12500000000000 : ℝ), (12367681904953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274822343/10000000000 : ℝ)|^4271 ≤ (4311228776019/10000000000000 : ℝ)^3247
        have hw : |(5274822343/10000000000 : ℝ)|=(5274822343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405259707/10000000000 : ℝ)|^4271 ≤ (5565003789657/12500000000000 : ℝ)^3247
        have hw : |(5405259707/10000000000 : ℝ)|=(5405259707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020676433/5000000000 : ℝ)|^4271 ≤ (12367681904953/100000000000000 : ℝ)^3247
        have hw : |(-1020676433/5000000000 : ℝ)|=(1020676433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_11 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (14113043/31250000 : ℝ)*x 0 + (2123887991/5000000000 : ℝ)*x 1 + (849555299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14113043/31250000 : ℝ)^4271 ≤ (35147653814497/100000000000000 : ℝ)^3247 := by
    have hnat : (14113043 : ℕ)^4271*100000000000000^3247 ≤ 35147653814497^3247*31250000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14113043 31250000 35147653814497 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123887991/5000000000 : ℝ)^4271 ≤ (32426170512917/100000000000000 : ℝ)^3247 := by
    have hnat : (2123887991 : ℕ)^4271*100000000000000^3247 ≤ 32426170512917^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123887991 5000000000 32426170512917 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849555299/2000000000 : ℝ)^4271 ≤ (16213087832001/50000000000000 : ℝ)^3247 := by
    have hnat : (849555299 : ℕ)^4271*50000000000000^3247 ≤ 16213087832001^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849555299 2000000000 16213087832001 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(14113043/31250000 : ℝ), (2123887991/5000000000 : ℝ), (849555299/2000000000 : ℝ)] ![(35147653814497/100000000000000 : ℝ), (32426170512917/100000000000000 : ℝ), (16213087832001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(14113043/31250000 : ℝ)|^4271 ≤ (35147653814497/100000000000000 : ℝ)^3247
        have hw : |(14113043/31250000 : ℝ)|=(14113043/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123887991/5000000000 : ℝ)|^4271 ≤ (32426170512917/100000000000000 : ℝ)^3247
        have hw : |(2123887991/5000000000 : ℝ)|=(2123887991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849555299/2000000000 : ℝ)|^4271 ≤ (16213087832001/50000000000000 : ℝ)^3247
        have hw : |(849555299/2000000000 : ℝ)|=(849555299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_12 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1973494633/10000000000 : ℝ)*x 0 + (2738128391/5000000000 : ℝ)*x 1 + (5253150069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1973494633/10000000000 : ℝ)^4271 ≤ (369679969541/3125000000000 : ℝ)^3247 := by
    have hnat : (1973494633 : ℕ)^4271*3125000000000^3247 ≤ 369679969541^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973494633 10000000000 369679969541 3125000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738128391/5000000000 : ℝ)^4271 ≤ (22645398122783/50000000000000 : ℝ)^3247 := by
    have hnat : (2738128391 : ℕ)^4271*50000000000000^3247 ≤ 22645398122783^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738128391 5000000000 22645398122783 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253150069/10000000000 : ℝ)^4271 ≤ (343035557687/800000000000 : ℝ)^3247 := by
    have hnat : (5253150069 : ℕ)^4271*800000000000^3247 ≤ 343035557687^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253150069 10000000000 343035557687 800000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1973494633/10000000000 : ℝ), (2738128391/5000000000 : ℝ), (5253150069/10000000000 : ℝ)] ![(369679969541/3125000000000 : ℝ), (22645398122783/50000000000000 : ℝ), (343035557687/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1973494633/10000000000 : ℝ)|^4271 ≤ (369679969541/3125000000000 : ℝ)^3247
        have hw : |(-1973494633/10000000000 : ℝ)|=(1973494633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738128391/5000000000 : ℝ)|^4271 ≤ (22645398122783/50000000000000 : ℝ)^3247
        have hw : |(2738128391/5000000000 : ℝ)|=(2738128391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253150069/10000000000 : ℝ)|^4271 ≤ (343035557687/800000000000 : ℝ)^3247
        have hw : |(5253150069/10000000000 : ℝ)|=(5253150069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_13 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381806807/10000000000 : ℝ)*x 0 + (-2102151169/10000000000 : ℝ)*x 1 + (131328703/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381806807/10000000000 : ℝ)^4271 ≤ (11066529292261/25000000000000 : ℝ)^3247 := by
    have hnat : (5381806807 : ℕ)^4271*25000000000000^3247 ≤ 11066529292261^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381806807 10000000000 11066529292261 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2102151169/10000000000 : ℝ)^4271 ≤ (1606807379029/12500000000000 : ℝ)^3247 := by
    have hnat : (2102151169 : ℕ)^4271*12500000000000^3247 ≤ 1606807379029^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102151169 10000000000 1606807379029 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131328703/250000000 : ℝ)^4271 ≤ (669990996637/1562500000000 : ℝ)^3247 := by
    have hnat : (131328703 : ℕ)^4271*1562500000000^3247 ≤ 669990996637^3247*250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131328703 250000000 669990996637 1562500000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381806807/10000000000 : ℝ), (-2102151169/10000000000 : ℝ), (131328703/250000000 : ℝ)] ![(11066529292261/25000000000000 : ℝ), (1606807379029/12500000000000 : ℝ), (669990996637/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381806807/10000000000 : ℝ)|^4271 ≤ (11066529292261/25000000000000 : ℝ)^3247
        have hw : |(5381806807/10000000000 : ℝ)|=(5381806807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2102151169/10000000000 : ℝ)|^4271 ≤ (1606807379029/12500000000000 : ℝ)^3247
        have hw : |(-2102151169/10000000000 : ℝ)|=(2102151169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131328703/250000000 : ℝ)|^4271 ≤ (669990996637/1562500000000 : ℝ)^3247
        have hw : |(131328703/250000000 : ℝ)|=(131328703/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_14 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672725653/1250000000 : ℝ)*x 0 + (5253150461/10000000000 : ℝ)*x 1 + (-2102150173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672725653/1250000000 : ℝ)^4271 ≤ (4426610004243/10000000000000 : ℝ)^3247 := by
    have hnat : (672725653 : ℕ)^4271*10000000000000^3247 ≤ 4426610004243^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672725653 1250000000 4426610004243 10000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253150461/10000000000 : ℝ)^4271 ≤ (21439724459859/50000000000000 : ℝ)^3247 := by
    have hnat : (5253150461 : ℕ)^4271*50000000000000^3247 ≤ 21439724459859^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253150461 10000000000 21439724459859 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2102150173/10000000000 : ℝ)^4271 ≤ (12854451021053/100000000000000 : ℝ)^3247 := by
    have hnat : (2102150173 : ℕ)^4271*100000000000000^3247 ≤ 12854451021053^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102150173 10000000000 12854451021053 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672725653/1250000000 : ℝ), (5253150461/10000000000 : ℝ), (-2102150173/10000000000 : ℝ)] ![(4426610004243/10000000000000 : ℝ), (21439724459859/50000000000000 : ℝ), (12854451021053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672725653/1250000000 : ℝ)|^4271 ≤ (4426610004243/10000000000000 : ℝ)^3247
        have hw : |(672725653/1250000000 : ℝ)|=(672725653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253150461/10000000000 : ℝ)|^4271 ≤ (21439724459859/50000000000000 : ℝ)^3247
        have hw : |(5253150461/10000000000 : ℝ)|=(5253150461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2102150173/10000000000 : ℝ)|^4271 ≤ (12854451021053/100000000000000 : ℝ)^3247
        have hw : |(-2102150173/10000000000 : ℝ)|=(2102150173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_box_15 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4158559389/10000000000 : ℝ)*x 0 + (2213288903/5000000000 : ℝ)*x 1 + (110664439/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4158559389/10000000000 : ℝ)^4271 ≤ (15766659450783/50000000000000 : ℝ)^3247 := by
    have hnat : (4158559389 : ℕ)^4271*50000000000000^3247 ≤ 15766659450783^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158559389 10000000000 15766659450783 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213288903/5000000000 : ℝ)^4271 ≤ (34233341788773/100000000000000 : ℝ)^3247 := by
    have hnat : (2213288903 : ℕ)^4271*100000000000000^3247 ≤ 34233341788773^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213288903 5000000000 34233341788773 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110664439/250000000 : ℝ)^4271 ≤ (17116669643167/50000000000000 : ℝ)^3247 := by
    have hnat : (110664439 : ℕ)^4271*50000000000000^3247 ≤ 17116669643167^3247*250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110664439 250000000 17116669643167 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4158559389/10000000000 : ℝ), (2213288903/5000000000 : ℝ), (110664439/250000000 : ℝ)] ![(15766659450783/50000000000000 : ℝ), (34233341788773/100000000000000 : ℝ), (17116669643167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4158559389/10000000000 : ℝ)|^4271 ≤ (15766659450783/50000000000000 : ℝ)^3247
        have hw : |(4158559389/10000000000 : ℝ)|=(4158559389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2213288903/5000000000 : ℝ)|^4271 ≤ (34233341788773/100000000000000 : ℝ)^3247
        have hw : |(2213288903/5000000000 : ℝ)|=(2213288903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110664439/250000000 : ℝ)|^4271 ≤ (17116669643167/50000000000000 : ℝ)^3247
        have hw : |(110664439/250000000 : ℝ)|=(110664439/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1311_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15711/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58881/100000 : ℝ) ∧ (79771/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8423/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2937/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (443/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2937/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (443/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2937/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (443/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2937/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (443/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2937/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (443/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2937/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (443/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (443/4000 : ℝ) ^ (2135/512 : ℝ) ≤ (646946030523153/6250000000000000000 : ℝ) := by
    have hpowers : (443/4000 : ℝ)^2135 ≤ (646946030523153/6250000000000000000 : ℝ)^512 := by
      have hnat : (443 : ℕ)^2135*6250000000000000000^512 ≤ 646946030523153^512*4000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        443 4000 646946030523153 6250000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (443/4000 : ℝ)) (X := (646946030523153/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2937/20000 : ℝ) ^ (2135/512 : ℝ) ≤ (16784154453361767/50000000000000000000 : ℝ) := by
    have hpowers : (2937/20000 : ℝ)^2135 ≤ (16784154453361767/50000000000000000000 : ℝ)^512 := by
      have hnat : (2937 : ℕ)^2135*50000000000000000000^512 ≤ 16784154453361767^512*20000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2937 20000 16784154453361767 50000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2937/20000 : ℝ)) (X := (16784154453361767/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125646946030523153/3125000000000000000 : ℝ) ≤ (5000248213812801/5000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (3125646946030523153/3125000000000000000 : ℝ)^512 ≤ (5000248213812801/5000000000000000 : ℝ)^2135 := by
      have hnat : (3125646946030523153 : ℕ)^512*5000000000000000^2135 ≤ 5000248213812801^2135*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125646946030523153 3125000000000000000 5000248213812801 5000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000248213812801/5000000000000000 : ℝ)) (X := (3125646946030523153/3125000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021959722697546991/50000000000000000000 : ℝ) ≤ (10001053068064727/10000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (50021959722697546991/50000000000000000000 : ℝ)^512 ≤ (10001053068064727/10000000000000000 : ℝ)^2135 := by
      have hnat : (50021959722697546991 : ℕ)^512*10000000000000000^2135 ≤ 10001053068064727^2135*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021959722697546991 50000000000000000000 10001053068064727 10000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001053068064727/10000000000000000 : ℝ)) (X := (50021959722697546991/50000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016784154453361767/25000000000000000000 : ℝ) ≤ (2500402427125963/2500000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (25016784154453361767/25000000000000000000 : ℝ)^512 ≤ (2500402427125963/2500000000000000 : ℝ)^2135 := by
      have hnat : (25016784154453361767 : ℕ)^512*2500000000000000^2135 ≤ 2500402427125963^2135*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016784154453361767 25000000000000000000 2500402427125963 2500000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500402427125963/2500000000000000 : ℝ)) (X := (25016784154453361767/25000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(646946030523153/6250000000000000000 : ℝ) ≤ ((3608946251800180447/3610000000000000000 : ℝ)+2*(4453123513/2888000000000 : ℝ)*(443/4000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (3608946251800180447/3610000000000000000 : ℝ)+2*(4453123513/2888000000000 : ℝ)*(443/4000 : ℝ)=(5000248213812801/5000000000000000 : ℝ) by norm_num, show 1+2*(646946030523153/6250000000000000000 : ℝ)=(3125646946030523153/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16784154453361767/50000000000000000000 : ℝ)+(646946030523153/6250000000000000000 : ℝ) ≤ ((3608946251800180447/3610000000000000000 : ℝ)+(4453123513/2888000000000 : ℝ)*((2937/20000 : ℝ)+(443/4000 : ℝ)))^(2135/512 : ℝ) := by
    rw [show (3608946251800180447/3610000000000000000 : ℝ)+(4453123513/2888000000000 : ℝ)*((2937/20000 : ℝ)+(443/4000 : ℝ))=(10001053068064727/10000000000000000 : ℝ) by norm_num, show 1+(16784154453361767/50000000000000000000 : ℝ)+(646946030523153/6250000000000000000 : ℝ)=(50021959722697546991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16784154453361767/50000000000000000000 : ℝ) ≤ ((3608946251800180447/3610000000000000000 : ℝ)+2*(4453123513/2888000000000 : ℝ)*(2937/20000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (3608946251800180447/3610000000000000000 : ℝ)+2*(4453123513/2888000000000 : ℝ)*(2937/20000 : ℝ)=(2500402427125963/2500000000000000 : ℝ) by norm_num, show 1+2*(16784154453361767/50000000000000000000 : ℝ)=(25016784154453361767/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3608946251800180447/3610000000000000000 : ℝ)*(X 1 0+X 2 0)+(4453123513/2888000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (443/4000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (3608946251800180447/3610000000000000000 : ℝ)) (alpha := (4453123513/2888000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3608946251800180447/3610000000000000000 : ℝ)*(X 0 1+X 2 1)+(4453123513/2888000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (443/4000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (3608946251800180447/3610000000000000000 : ℝ)) (alpha := (4453123513/2888000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3608946251800180447/3610000000000000000 : ℝ)*(X 0 2+X 1 2)+(4453123513/2888000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (443/4000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (3608946251800180447/3610000000000000000 : ℝ)) (alpha := (4453123513/2888000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-475325659/2500000000 : ℝ)*X 0 0+(336951741/625000000 : ℝ)*X 0 1+(16847587/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284696517/10000000000 : ℝ)*X 1 0+(-2047093509/10000000000 : ℝ)*X 1 1+(2695614041/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5284696809/10000000000 : ℝ)*X 2 0+(336951739/625000000 : ℝ)*X 2 1+(-1023546733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4483734059/10000000000 : ℝ)*X 0 0+(4264283647/10000000000 : ℝ)*X 0 1+(2132141853/5000000000 : ℝ)*X 0 2+(4483734059/10000000000 : ℝ)*X 1 0+(4264283647/10000000000 : ℝ)*X 1 1+(2132141853/5000000000 : ℝ)*X 1 2+(4483734059/10000000000 : ℝ)*X 2 0+(4264283647/10000000000 : ℝ)*X 2 1+(2132141853/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-112179159/500000000 : ℝ)*X 0 0+(658023913/1250000000 : ℝ)*X 0 1+(1316047849/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374042451/10000000000 : ℝ)*X 1 0+(-262230613/1250000000 : ℝ)*X 1 1+(5264191447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((268702121/500000000 : ℝ)*X 2 0+(658023923/1250000000 : ℝ)*X 2 1+(-209784503/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((209248711/500000000 : ℝ)*X 0 0+(4413608969/10000000000 : ℝ)*X 0 1+(2206804441/5000000000 : ℝ)*X 0 2+(209248711/500000000 : ℝ)*X 1 0+(4413608969/10000000000 : ℝ)*X 1 1+(2206804441/5000000000 : ℝ)*X 1 2+(209248711/500000000 : ℝ)*X 2 0+(4413608969/10000000000 : ℝ)*X 2 1+(2206804441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2171789991/10000000000 : ℝ)*X 0 0+(1294221229/2500000000 : ℝ)*X 0 1+(2702629779/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274822027/10000000000 : ℝ)*X 1 0+(-2041353909/10000000000 : ℝ)*X 1 1+(5405259253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274822343/10000000000 : ℝ)*X 2 0+(5405259707/10000000000 : ℝ)*X 2 1+(-1020676433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((14113043/31250000 : ℝ)*X 0 0+(2123887991/5000000000 : ℝ)*X 0 1+(849555299/2000000000 : ℝ)*X 0 2+(14113043/31250000 : ℝ)*X 1 0+(2123887991/5000000000 : ℝ)*X 1 1+(849555299/2000000000 : ℝ)*X 1 2+(14113043/31250000 : ℝ)*X 2 0+(2123887991/5000000000 : ℝ)*X 2 1+(849555299/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1973494633/10000000000 : ℝ)*X 0 0+(2738128391/5000000000 : ℝ)*X 0 1+(5253150069/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5381806807/10000000000 : ℝ)*X 1 0+(-2102151169/10000000000 : ℝ)*X 1 1+(131328703/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((672725653/1250000000 : ℝ)*X 2 0+(5253150461/10000000000 : ℝ)*X 2 1+(-2102150173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4158559389/10000000000 : ℝ)*X 0 0+(2213288903/5000000000 : ℝ)*X 0 1+(110664439/250000000 : ℝ)*X 0 2+(4158559389/10000000000 : ℝ)*X 1 0+(2213288903/5000000000 : ℝ)*X 1 1+(110664439/250000000 : ℝ)*X 1 2+(4158559389/10000000000 : ℝ)*X 2 0+(2213288903/5000000000 : ℝ)*X 2 1+(110664439/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15711/25000 : ℝ) ≤ (-7089361131903775449479742906987/11281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15391081/25000000000000 : ℝ)*(upper1) + (31242409/50000000000000 : ℝ)*(upper2) + (2808043/100000000000000 : ℝ)*(lower4) + (25397877/100000000000000 : ℝ)*(upper5) + (360713506618893/12500000000000 : ℝ)*(major0) + (360713506618893/12500000000000 : ℝ)*(major1) + (360713506618893/12500000000000 : ℝ)*(major2) + (115569471/20000000000000 : ℝ)*(sp3) + (1956263206227293/50000000000000 : ℝ)*(sp4) + (391245259574239/10000000000000 : ℝ)*(sp5) + (78250421331689/2000000000000 : ℝ)*(sp6) + (469959110761141/25000000000000 : ℝ)*(sp7) + (14763342439/20000000000000 : ℝ)*(sp13) + (668233767/12500000000000 : ℝ)*(sp14) + (1879837020891919/100000000000000 : ℝ)*(f.failure) + (1956263206227293/50000000000000 : ℝ)*(f.sum) + (30812842913/72200000000000000000000000 : ℝ)*base66 + (170306640172489829/45125000000000000000000000000000 : ℝ)*base68 + (349675753026114829/45125000000000000000000000000000 : ℝ)*base70 + (39258899114364829/45125000000000000000000000000000 : ℝ)*base72 + (222780648233/180500000000000000000000000 : ℝ)*base74 + (59304771684635171/45125000000000000000000000000000 : ℝ)*base75 + (329487114795489829/45125000000000000000000000000000 : ℝ)*base78 + (281169349931489829/45125000000000000000000000000000 : ℝ)*base80 + (236067712613/36100000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (13782223/10000000000000000000000 : ℝ)*base89 + (13782223/10000000000000000000000 : ℝ)*base91 + (13782223/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58881/100000 : ℝ) ≤ (106285391471683959974866050312549/180500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2852807/20000000000000 : ℝ)*(upper0) + (35152731/100000000000000 : ℝ)*(lower1) + (7871311/10000000000000 : ℝ)*(upper4) + (2953362942765289/100000000000000 : ℝ)*(major0) + (2953362942765289/100000000000000 : ℝ)*(major1) + (2953362942765289/100000000000000 : ℝ)*(major2) + (99079704748769/2500000000000 : ℝ)*(sp0) + (123849491431333/3125000000000 : ℝ)*(sp1) + (1981593934174883/50000000000000 : ℝ)*(sp2) + (961954460379619/50000000000000 : ℝ)*(sp3) + (4750916541/100000000000000 : ℝ)*(sp5) + (608369431/100000000000000 : ℝ)*(sp6) + (265127481/50000000000000 : ℝ)*(sp7) + (286768437/100000000000000 : ℝ)*(sp8) + (9619547255071/500000000000 : ℝ)*(f.failure) + (3963188476719197/100000000000000 : ℝ)*(f.sum) + (12989554433/28880000000000000000000000 : ℝ)*base66 + (1303470449086645817/361000000000000000000000000000000 : ℝ)*base68 + (3561588891948645817/361000000000000000000000000000000 : ℝ)*base70 + (1083426963864354183/361000000000000000000000000000000 : ℝ)*base71 + (23531096036227/722000000000000000000000000 : ℝ)*base74 + (2475802467601645817/361000000000000000000000000000000 : ℝ)*base76 + (1799387949733354183/361000000000000000000000000000000 : ℝ)*base77 + (9213595894882645817/361000000000000000000000000000000 : ℝ)*base80 + (610545447313/722000000000000000000000000 : ℝ)*base81 + (67393/50000000000000000000 : ℝ)*base90 + (67393/50000000000000000000 : ℝ)*base92 + (67393/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79771/100000 : ℝ) ≤ (57596436768940541648951079/72200000000000000000000000 : ℝ) := by norm_num
    linear_combination (58758063/20000000000000 : ℝ)*(upper0) + (83630937/100000000000000 : ℝ)*(lower3) + (231250353/50000000000000 : ℝ)*(upper4) + (1633351449961467/50000000000000 : ℝ)*(major0) + (1633351449961467/50000000000000 : ℝ)*(major1) + (1633351449961467/50000000000000 : ℝ)*(major2) + (26289470459/25000000000000 : ℝ)*(sp1) + (433409878031/100000000000000 : ℝ)*(sp2) + (157456535673/100000000000000 : ℝ)*(sp3) + (3499564663/25000000000000 : ℝ)*(sp4) + (136836628914191/3125000000000 : ℝ)*(sp8) + (273667560351933/6250000000000 : ℝ)*(sp9) + (1094588178408683/25000000000000 : ℝ)*(sp10) + (425574213417569/20000000000000 : ℝ)*(sp11) + (1064014261811759/50000000000000 : ℝ)*(f.failure) + (1094696530878191/25000000000000 : ℝ)*(f.sum) + (5428310761/722000000000000000000000 : ℝ)*base65 + (424894937529914251/180500000000000000000000000000000 : ℝ)*base68 + (910438688469914251/180500000000000000000000000000000 : ℝ)*base70 + (938054217173085749/180500000000000000000000000000000 : ℝ)*base71 + (502561624249/36100000000000000000000000 : ℝ)*base74 + (825266992433914251/180500000000000000000000000000000 : ℝ)*base76 + (608514665569585749/180500000000000000000000000000000 : ℝ)*base77 + (4721531663596085749/180500000000000000000000000000000 : ℝ)*base79 + (16354183/5640625000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (23924497/5000000000000000000000 : ℝ)*base90 + (23924497/5000000000000000000000 : ℝ)*base92 + (23924497/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-8423/10000 : ℝ) ≤ (-1900390164543767892130299/2256250000000000000000000 : ℝ) := by norm_num
    linear_combination (221868247/100000000000000 : ℝ)*(lower0) + (97102193/50000000000000 : ℝ)*(lower1) + (17297939/20000000000000 : ℝ)*(lower2) + (18324021/50000000000000 : ℝ)*(lower4) + (412853326753439/12500000000000 : ℝ)*(major0) + (412853326753439/12500000000000 : ℝ)*(major1) + (412853326753439/12500000000000 : ℝ)*(major2) + (11121469051/100000000000000 : ℝ)*(sp4) + (489009615521/50000000000000 : ℝ)*(sp5) + (96778711479/100000000000000 : ℝ)*(sp7) + (2241078724361067/50000000000000 : ℝ)*(sp12) + (280074409435009/6250000000000 : ℝ)*(sp13) + (2241084285095593/50000000000000 : ℝ)*(sp14) + (2151463818794723/100000000000000 : ℝ)*(sp15) + (1075780298753101/50000000000000 : ℝ)*(f.failure) + (2241084285095593/50000000000000 : ℝ)*(f.sum) + (2155550613497/72200000000000000000000000 : ℝ)*base66 + (453257236468932233/45125000000000000000000000000000 : ℝ)*base67 + (85497657213442767/45125000000000000000000000000000 : ℝ)*base70 + (1910635824449432233/45125000000000000000000000000000 : ℝ)*base71 + (111001696209/72200000000000000000000000 : ℝ)*base74 + (361816741579942767/45125000000000000000000000000000 : ℝ)*base76 + (2964835755119817767/45125000000000000000000000000000 : ℝ)*base78 + (450383159607182233/45125000000000000000000000000000 : ℝ)*base79 + (19464046973/4512500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (8351117/5000000000000000000000 : ℝ)*base89 + (8351117/5000000000000000000000 : ℝ)*base91 + (8351117/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1311_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15711/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58881/100000 : ℝ) else (79771/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8423/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1311_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1311_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15711/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58881/100000 : ℝ) else (79771/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8423/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1311_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15711/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58881/100000 : ℝ) else (79771/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8423/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1311_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
