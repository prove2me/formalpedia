-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1054_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:58:06.745055+00:00
-- url     : https://prove2.me/submissions/a1d5405f-e4e4-4ed0-a021-17192a922bc4

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
theorem support_rectangle_w1054_s6_0 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209637467/10000000000 : ℝ)*x 0 + (134879141/250000000 : ℝ)*x 1 + (2631832757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209637467/10000000000 : ℝ)^8247 ≤ (6709196624513/50000000000000 : ℝ)^6199 := by
    have hnat : (2209637467 : ℕ)^8247*50000000000000^6199 ≤ 6709196624513^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209637467 10000000000 6709196624513 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134879141/250000000 : ℝ)^8247 ≤ (880026248719/2000000000000 : ℝ)^6199 := by
    have hnat : (134879141 : ℕ)^8247*2000000000000^6199 ≤ 880026248719^6199*250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134879141 250000000 880026248719 2000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631832757/5000000000 : ℝ)^8247 ≤ (2661268393619/6250000000000 : ℝ)^6199 := by
    have hnat : (2631832757 : ℕ)^8247*6250000000000^6199 ≤ 2661268393619^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631832757 5000000000 2661268393619 6250000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209637467/10000000000 : ℝ), (134879141/250000000 : ℝ), (2631832757/5000000000 : ℝ)] ![(6709196624513/50000000000000 : ℝ), (880026248719/2000000000000 : ℝ), (2661268393619/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209637467/10000000000 : ℝ)|^8247 ≤ (6709196624513/50000000000000 : ℝ)^6199
        have hw : |(-2209637467/10000000000 : ℝ)|=(2209637467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134879141/250000000 : ℝ)|^8247 ≤ (880026248719/2000000000000 : ℝ)^6199
        have hw : |(134879141/250000000 : ℝ)|=(134879141/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631832757/5000000000 : ℝ)|^8247 ≤ (2661268393619/6250000000000 : ℝ)^6199
        have hw : |(2631832757/5000000000 : ℝ)|=(2631832757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s6_1 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213806209/400000000 : ℝ)*x 0 + (-1138184273/5000000000 : ℝ)*x 1 + (526366551/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213806209/400000000 : ℝ)^8247 ≤ (43459525190899/100000000000000 : ℝ)^6199 := by
    have hnat : (213806209 : ℕ)^8247*100000000000000^6199 ≤ 43459525190899^6199*400000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213806209 400000000 43459525190899 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138184273/5000000000 : ℝ)^8247 ≤ (139601805391/1000000000000 : ℝ)^6199 := by
    have hnat : (1138184273 : ℕ)^8247*1000000000000^6199 ≤ 139601805391^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138184273 5000000000 139601805391 1000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526366551/1000000000 : ℝ)^8247 ≤ (5322536781857/12500000000000 : ℝ)^6199 := by
    have hnat : (526366551 : ℕ)^8247*12500000000000^6199 ≤ 5322536781857^6199*1000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526366551 1000000000 5322536781857 12500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213806209/400000000 : ℝ), (-1138184273/5000000000 : ℝ), (526366551/1000000000 : ℝ)] ![(43459525190899/100000000000000 : ℝ), (139601805391/1000000000000 : ℝ), (5322536781857/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213806209/400000000 : ℝ)|^8247 ≤ (43459525190899/100000000000000 : ℝ)^6199
        have hw : |(213806209/400000000 : ℝ)|=(213806209/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1138184273/5000000000 : ℝ)|^8247 ≤ (139601805391/1000000000000 : ℝ)^6199
        have hw : |(-1138184273/5000000000 : ℝ)|=(1138184273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526366551/1000000000 : ℝ)|^8247 ≤ (5322536781857/12500000000000 : ℝ)^6199
        have hw : |(526366551/1000000000 : ℝ)|=(526366551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s6_2 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345155379/10000000000 : ℝ)*x 0 + (1315916353/2500000000 : ℝ)*x 1 + (-2276368471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345155379/10000000000 : ℝ)^8247 ≤ (43459526856687/100000000000000 : ℝ)^6199 := by
    have hnat : (5345155379 : ℕ)^8247*100000000000000^6199 ≤ 43459526856687^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345155379 10000000000 43459526856687 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315916353/2500000000 : ℝ)^8247 ≤ (1703211728007/4000000000000 : ℝ)^6199 := by
    have hnat : (1315916353 : ℕ)^8247*4000000000000^6199 ≤ 1703211728007^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315916353 2500000000 1703211728007 4000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2276368471/10000000000 : ℝ)^8247 ≤ (2792035985439/20000000000000 : ℝ)^6199 := by
    have hnat : (2276368471 : ℕ)^8247*20000000000000^6199 ≤ 2792035985439^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276368471 10000000000 2792035985439 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345155379/10000000000 : ℝ), (1315916353/2500000000 : ℝ), (-2276368471/10000000000 : ℝ)] ![(43459526856687/100000000000000 : ℝ), (1703211728007/4000000000000 : ℝ), (2792035985439/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345155379/10000000000 : ℝ)|^8247 ≤ (43459526856687/100000000000000 : ℝ)^6199
        have hw : |(5345155379/10000000000 : ℝ)|=(5345155379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315916353/2500000000 : ℝ)|^8247 ≤ (1703211728007/4000000000000 : ℝ)^6199
        have hw : |(1315916353/2500000000 : ℝ)|=(1315916353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2276368471/10000000000 : ℝ)|^8247 ≤ (2792035985439/20000000000000 : ℝ)^6199
        have hw : |(-2276368471/10000000000 : ℝ)|=(2276368471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s6_3 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188595501/5000000000 : ℝ)*x 0 + (2125277451/5000000000 : ℝ)*x 1 + (4507662913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188595501/5000000000 : ℝ)^8247 ≤ (16658088060923/50000000000000 : ℝ)^6199 := by
    have hnat : (2188595501 : ℕ)^8247*50000000000000^6199 ≤ 16658088060923^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188595501 5000000000 16658088060923 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125277451/5000000000 : ℝ)^8247 ≤ (400500484651/1250000000000 : ℝ)^6199 := by
    have hnat : (2125277451 : ℕ)^8247*1250000000000^6199 ≤ 400500484651^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125277451 5000000000 400500484651 1250000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507662913/10000000000 : ℝ)^8247 ≤ (34643785092059/100000000000000 : ℝ)^6199 := by
    have hnat : (4507662913 : ℕ)^8247*100000000000000^6199 ≤ 34643785092059^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507662913 10000000000 34643785092059 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188595501/5000000000 : ℝ), (2125277451/5000000000 : ℝ), (4507662913/10000000000 : ℝ)] ![(16658088060923/50000000000000 : ℝ), (400500484651/1250000000000 : ℝ), (34643785092059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188595501/5000000000 : ℝ)|^8247 ≤ (16658088060923/50000000000000 : ℝ)^6199
        have hw : |(2188595501/5000000000 : ℝ)|=(2188595501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125277451/5000000000 : ℝ)|^8247 ≤ (400500484651/1250000000000 : ℝ)^6199
        have hw : |(2125277451/5000000000 : ℝ)|=(2125277451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507662913/10000000000 : ℝ)|^8247 ≤ (34643785092059/100000000000000 : ℝ)^6199
        have hw : |(4507662913/10000000000 : ℝ)|=(4507662913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s6_4 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-220964273/1000000000 : ℝ)*x 0 + (164499927/312500000 : ℝ)*x 1 + (2697416131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220964273/1000000000 : ℝ)^8247 ≤ (13418435768451/100000000000000 : ℝ)^6199 := by
    have hnat : (220964273 : ℕ)^8247*100000000000000^6199 ≤ 13418435768451^6199*1000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220964273 1000000000 13418435768451 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164499927/312500000 : ℝ)^8247 ≤ (5322983618479/12500000000000 : ℝ)^6199 := by
    have hnat : (164499927 : ℕ)^8247*12500000000000^6199 ≤ 5322983618479^6199*312500000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164499927 312500000 5322983618479 12500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697416131/5000000000 : ℝ)^8247 ≤ (42966499293/97656250000 : ℝ)^6199 := by
    have hnat : (2697416131 : ℕ)^8247*97656250000^6199 ≤ 42966499293^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697416131 5000000000 42966499293 97656250000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220964273/1000000000 : ℝ), (164499927/312500000 : ℝ), (2697416131/5000000000 : ℝ)] ![(13418435768451/100000000000000 : ℝ), (5322983618479/12500000000000 : ℝ), (42966499293/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220964273/1000000000 : ℝ)|^8247 ≤ (13418435768451/100000000000000 : ℝ)^6199
        have hw : |(-220964273/1000000000 : ℝ)|=(220964273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164499927/312500000 : ℝ)|^8247 ≤ (5322983618479/12500000000000 : ℝ)^6199
        have hw : |(164499927/312500000 : ℝ)|=(164499927/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697416131/5000000000 : ℝ)|^8247 ≤ (42966499293/97656250000 : ℝ)^6199
        have hw : |(2697416131/5000000000 : ℝ)|=(2697416131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s6_5 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312064807/10000000000 : ℝ)*x 0 + (-33518777/156250000 : ℝ)*x 1 + (2697416131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312064807/10000000000 : ℝ)^8247 ≤ (10775489780601/25000000000000 : ℝ)^6199 := by
    have hnat : (5312064807 : ℕ)^8247*25000000000000^6199 ≤ 10775489780601^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312064807 10000000000 10775489780601 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33518777/156250000 : ℝ)^8247 ≤ (12900345581969/100000000000000 : ℝ)^6199 := by
    have hnat : (33518777 : ℕ)^8247*100000000000000^6199 ≤ 12900345581969^6199*156250000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33518777 156250000 12900345581969 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697416131/5000000000 : ℝ)^8247 ≤ (42966499293/97656250000 : ℝ)^6199 := by
    have hnat : (2697416131 : ℕ)^8247*97656250000^6199 ≤ 42966499293^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697416131 5000000000 42966499293 97656250000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312064807/10000000000 : ℝ), (-33518777/156250000 : ℝ), (2697416131/5000000000 : ℝ)] ![(10775489780601/25000000000000 : ℝ), (12900345581969/100000000000000 : ℝ), (42966499293/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312064807/10000000000 : ℝ)|^8247 ≤ (10775489780601/25000000000000 : ℝ)^6199
        have hw : |(5312064807/10000000000 : ℝ)|=(5312064807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33518777/156250000 : ℝ)|^8247 ≤ (12900345581969/100000000000000 : ℝ)^6199
        have hw : |(-33518777/156250000 : ℝ)|=(33518777/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697416131/5000000000 : ℝ)|^8247 ≤ (42966499293/97656250000 : ℝ)^6199
        have hw : |(2697416131/5000000000 : ℝ)|=(2697416131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s6_6 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656032403/5000000000 : ℝ)*x 0 + (2697416131/5000000000 : ℝ)*x 1 + (-2145201729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656032403/5000000000 : ℝ)^8247 ≤ (43101959111609/100000000000000 : ℝ)^6199 := by
    have hnat : (2656032403 : ℕ)^8247*100000000000000^6199 ≤ 43101959111609^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656032403 5000000000 43101959111609 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697416131/5000000000 : ℝ)^8247 ≤ (42966499293/97656250000 : ℝ)^6199 := by
    have hnat : (2697416131 : ℕ)^8247*97656250000^6199 ≤ 42966499293^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697416131 5000000000 42966499293 97656250000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145201729/10000000000 : ℝ)^8247 ≤ (12900345589969/100000000000000 : ℝ)^6199 := by
    have hnat : (2145201729 : ℕ)^8247*100000000000000^6199 ≤ 12900345589969^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145201729 10000000000 12900345589969 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656032403/5000000000 : ℝ), (2697416131/5000000000 : ℝ), (-2145201729/10000000000 : ℝ)] ![(43101959111609/100000000000000 : ℝ), (42966499293/97656250000 : ℝ), (12900345589969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656032403/5000000000 : ℝ)|^8247 ≤ (43101959111609/100000000000000 : ℝ)^6199
        have hw : |(2656032403/5000000000 : ℝ)|=(2656032403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697416131/5000000000 : ℝ)|^8247 ≤ (42966499293/97656250000 : ℝ)^6199
        have hw : |(2697416131/5000000000 : ℝ)|=(2697416131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145201729/10000000000 : ℝ)|^8247 ≤ (12900345589969/100000000000000 : ℝ)^6199
        have hw : |(-2145201729/10000000000 : ℝ)|=(2145201729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s6_7 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4377201233/10000000000 : ℝ)*x 0 + (4507013537/10000000000 : ℝ)*x 1 + (2125603319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377201233/10000000000 : ℝ)^8247 ≤ (33316279720059/100000000000000 : ℝ)^6199 := by
    have hnat : (4377201233 : ℕ)^8247*100000000000000^6199 ≤ 33316279720059^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377201233 10000000000 33316279720059 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507013537/10000000000 : ℝ)^8247 ≤ (34637145610627/100000000000000 : ℝ)^6199 := by
    have hnat : (4507013537 : ℕ)^8247*100000000000000^6199 ≤ 34637145610627^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507013537 10000000000 34637145610627 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125603319/5000000000 : ℝ)^8247 ≤ (16023287329061/50000000000000 : ℝ)^6199 := by
    have hnat : (2125603319 : ℕ)^8247*50000000000000^6199 ≤ 16023287329061^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125603319 5000000000 16023287329061 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377201233/10000000000 : ℝ), (4507013537/10000000000 : ℝ), (2125603319/5000000000 : ℝ)] ![(33316279720059/100000000000000 : ℝ), (34637145610627/100000000000000 : ℝ), (16023287329061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377201233/10000000000 : ℝ)|^8247 ≤ (33316279720059/100000000000000 : ℝ)^6199
        have hw : |(4377201233/10000000000 : ℝ)|=(4377201233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507013537/10000000000 : ℝ)|^8247 ≤ (34637145610627/100000000000000 : ℝ)^6199
        have hw : |(4507013537/10000000000 : ℝ)|=(4507013537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125603319/5000000000 : ℝ)|^8247 ≤ (16023287329061/50000000000000 : ℝ)^6199
        have hw : |(2125603319/5000000000 : ℝ)|=(2125603319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1054_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11223/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1751/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11179/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11179/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11179/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11179/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11179/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11179/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11179/100000 : ℝ) ^ (4123/1024 : ℝ) ≤ (14740794335522547/100000000000000000000 : ℝ) := by
    have hpowers : (11179/100000 : ℝ)^4123 ≤ (14740794335522547/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11179 : ℕ)^4123*100000000000000000000^1024 ≤ 14740794335522547^1024*100000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11179 100000 14740794335522547 100000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11179/100000 : ℝ)) (X := (14740794335522547/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7027/50000 : ℝ) ^ (4123/1024 : ℝ) ≤ (18522503376121719/50000000000000000000 : ℝ) := by
    have hpowers : (7027/50000 : ℝ)^4123 ≤ (18522503376121719/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7027 : ℕ)^4123*50000000000000000000^1024 ≤ 18522503376121719^1024*50000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7027 50000 18522503376121719 50000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7027/50000 : ℝ)) (X := (18522503376121719/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014740794335522547/50000000000000000000 : ℝ) ≤ (10000732132003377/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (50014740794335522547/50000000000000000000 : ℝ)^1024 ≤ (10000732132003377/10000000000000000 : ℝ)^4123 := by
      have hnat : (50014740794335522547 : ℕ)^1024*10000000000000000^4123 ≤ 10000732132003377^4123*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014740794335522547 50000000000000000000 10000732132003377 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000732132003377/10000000000000000 : ℝ)) (X := (50014740794335522547/50000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010357160217553197/20000000000000000000 : ℝ) ≤ (10001285916637409/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (20010357160217553197/20000000000000000000 : ℝ)^1024 ≤ (10001285916637409/10000000000000000 : ℝ)^4123 := by
      have hnat : (20010357160217553197 : ℕ)^1024*10000000000000000^4123 ≤ 10001285916637409^4123*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010357160217553197 20000000000000000000 10001285916637409 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001285916637409/10000000000000000 : ℝ)) (X := (20010357160217553197/20000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018522503376121719/25000000000000000000 : ℝ) ≤ (10001839701271441/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (25018522503376121719/25000000000000000000 : ℝ)^1024 ≤ (10001839701271441/10000000000000000 : ℝ)^4123 := by
      have hnat : (25018522503376121719 : ℕ)^1024*10000000000000000^4123 ≤ 10001839701271441^4123*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018522503376121719 25000000000000000000 10001839701271441 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001839701271441/10000000000000000 : ℝ)) (X := (25018522503376121719/25000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14740794335522547/100000000000000000000 : ℝ) ≤ ((1249553189680957453/1250000000000000000 : ℝ)+2*(1504849549/781250000000 : ℝ)*(11179/100000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (1249553189680957453/1250000000000000000 : ℝ)+2*(1504849549/781250000000 : ℝ)*(11179/100000 : ℝ)=(10000732132003377/10000000000000000 : ℝ) by norm_num, show 1+2*(14740794335522547/100000000000000000000 : ℝ)=(50014740794335522547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18522503376121719/50000000000000000000 : ℝ)+(14740794335522547/100000000000000000000 : ℝ) ≤ ((1249553189680957453/1250000000000000000 : ℝ)+(1504849549/781250000000 : ℝ)*((7027/50000 : ℝ)+(11179/100000 : ℝ)))^(4123/1024 : ℝ) := by
    rw [show (1249553189680957453/1250000000000000000 : ℝ)+(1504849549/781250000000 : ℝ)*((7027/50000 : ℝ)+(11179/100000 : ℝ))=(10001285916637409/10000000000000000 : ℝ) by norm_num, show 1+(18522503376121719/50000000000000000000 : ℝ)+(14740794335522547/100000000000000000000 : ℝ)=(20010357160217553197/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18522503376121719/50000000000000000000 : ℝ) ≤ ((1249553189680957453/1250000000000000000 : ℝ)+2*(1504849549/781250000000 : ℝ)*(7027/50000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (1249553189680957453/1250000000000000000 : ℝ)+2*(1504849549/781250000000 : ℝ)*(7027/50000 : ℝ)=(10001839701271441/10000000000000000 : ℝ) by norm_num, show 1+2*(18522503376121719/50000000000000000000 : ℝ)=(25018522503376121719/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1249553189680957453/1250000000000000000 : ℝ)*(X 1 0+X 2 0)+(1504849549/781250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (11179/100000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (1249553189680957453/1250000000000000000 : ℝ)) (alpha := (1504849549/781250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1249553189680957453/1250000000000000000 : ℝ)*(X 0 1+X 2 1)+(1504849549/781250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (11179/100000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (1249553189680957453/1250000000000000000 : ℝ)) (alpha := (1504849549/781250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1249553189680957453/1250000000000000000 : ℝ)*(X 0 2+X 1 2)+(1504849549/781250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (11179/100000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (1249553189680957453/1250000000000000000 : ℝ)) (alpha := (1504849549/781250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2209637467/10000000000 : ℝ)*X 0 0+(134879141/250000000 : ℝ)*X 0 1+(2631832757/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213806209/400000000 : ℝ)*X 1 0+(-1138184273/5000000000 : ℝ)*X 1 1+(526366551/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345155379/10000000000 : ℝ)*X 2 0+(1315916353/2500000000 : ℝ)*X 2 1+(-2276368471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188595501/5000000000 : ℝ)*X 0 0+(2125277451/5000000000 : ℝ)*X 0 1+(4507662913/10000000000 : ℝ)*X 0 2+(2188595501/5000000000 : ℝ)*X 1 0+(2125277451/5000000000 : ℝ)*X 1 1+(4507662913/10000000000 : ℝ)*X 1 2+(2188595501/5000000000 : ℝ)*X 2 0+(2125277451/5000000000 : ℝ)*X 2 1+(4507662913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-220964273/1000000000 : ℝ)*X 0 0+(164499927/312500000 : ℝ)*X 0 1+(2697416131/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312064807/10000000000 : ℝ)*X 1 0+(-33518777/156250000 : ℝ)*X 1 1+(2697416131/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656032403/5000000000 : ℝ)*X 2 0+(2697416131/5000000000 : ℝ)*X 2 1+(-2145201729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377201233/10000000000 : ℝ)*X 0 0+(4507013537/10000000000 : ℝ)*X 0 1+(2125603319/5000000000 : ℝ)*X 0 2+(4377201233/10000000000 : ℝ)*X 1 0+(4507013537/10000000000 : ℝ)*X 1 1+(2125603319/5000000000 : ℝ)*X 1 2+(4377201233/10000000000 : ℝ)*X 2 0+(4507013537/10000000000 : ℝ)*X 2 1+(2125603319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7000339529083434677984349/1953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (648536867/100000000000000 : ℝ)*(base19) + (776115043/100000000000000 : ℝ)*(base23) + (24459089/50000000000000 : ℝ)*(lower2) + (16773837/100000000000000 : ℝ)*(upper3) + (53441249/50000000000000 : ℝ)*(upper5) + (359188245260111/6250000000000 : ℝ)*(major0) + (359188245260111/6250000000000 : ℝ)*(major1) + (359188245260111/6250000000000 : ℝ)*(major2) + (1520913864631099/20000000000000 : ℝ)*(sp0) + (7604590582082713/100000000000000 : ℝ)*(sp1) + (7604590454504537/100000000000000 : ℝ)*(sp2) + (1944712141990379/50000000000000 : ℝ)*(sp3) + (4381492817/20000000000000 : ℝ)*(sp4) + (4107125373/50000000000000 : ℝ)*(sp7) + (243089531139469/6250000000000 : ℝ)*(f.failure) + (380229561530979/5000000000000 : ℝ)*(f.sum) + (2745575099991/625000000000000000000000000 : ℝ)*base66 + (90081473510417717/7812500000000000000000000000000 : ℝ)*base68 + (105735193385417717/7812500000000000000000000000000 : ℝ)*base70 + (44759764143230217/7812500000000000000000000000000 : ℝ)*base72 + (816948915779/156250000000000000000000000 : ℝ)*base74 + (86999814973957283/7812500000000000000000000000000 : ℝ)*base75 + (13129522721355217/7812500000000000000000000000000 : ℝ)*base78 + (15072762604167717/7812500000000000000000000000000 : ℝ)*base80 + (4517325697491/625000000000000000000000000 : ℝ)*base82 + (726197/156250000000000000000 : ℝ)*base89 + (726197/156250000000000000000 : ℝ)*base91 + (726197/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18972869580004461718813773/3125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (284391033/25000000000000 : ℝ)*(base19) + (616591493/50000000000000 : ℝ)*(base23) + (122425059/100000000000000 : ℝ)*(upper3) + (44219811/100000000000000 : ℝ)*(lower4) + (123204111/100000000000000 : ℝ)*(upper5) + (288810891401049/5000000000000 : ℝ)*(major0) + (288810891401049/5000000000000 : ℝ)*(major1) + (288810891401049/5000000000000 : ℝ)*(major2) + (15302746231/50000000000000 : ℝ)*(sp1) + (8205714741/25000000000000 : ℝ)*(sp2) + (7643237137455199/100000000000000 : ℝ)*(sp4) + (1528641078879721/20000000000000 : ℝ)*(sp5) + (7643203081413249/100000000000000 : ℝ)*(sp6) + (156367932648379/4000000000000 : ℝ)*(sp7) + (156367932648379/4000000000000 : ℝ)*(f.failure) + (7643237137455199/100000000000000 : ℝ)*(f.sum) + (565443953961/125000000000000000000000000 : ℝ)*base66 + (120059366848581803/6250000000000000000000000000000 : ℝ)*base68 + (4472535454831803/6250000000000000000000000000000 : ℝ)*base70 + (135617945904831803/6250000000000000000000000000000 : ℝ)*base72 + (485911951211/125000000000000000000000000 : ℝ)*base74 + (73168472904831803/6250000000000000000000000000000 : ℝ)*base76 + (115806532561081803/6250000000000000000000000000000 : ℝ)*base78 + (92432724786081803/6250000000000000000000000000000 : ℝ)*base80 + (286351786039/125000000000000000000000000 : ℝ)*base81 + (148973/100000000000000000000 : ℝ)*base90 + (148973/100000000000000000000 : ℝ)*base92 + (148973/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1054_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1054_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1054_s7_0 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209680399/10000000000 : ℝ)*x 0 + (5394671833/10000000000 : ℝ)*x 1 + (65801639/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209680399/10000000000 : ℝ)^8247 ≤ (3354685023691/25000000000000 : ℝ)^6199 := by
    have hnat : (2209680399 : ℕ)^8247*25000000000000^6199 ≤ 3354685023691^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209680399 10000000000 3354685023691 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394671833/10000000000 : ℝ)^8247 ≤ (21997977321777/50000000000000 : ℝ)^6199 := by
    have hnat : (5394671833 : ℕ)^8247*50000000000000^6199 ≤ 21997977321777^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394671833 10000000000 21997977321777 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65801639/125000000 : ℝ)^8247 ≤ (42585305243033/100000000000000 : ℝ)^6199 := by
    have hnat : (65801639 : ℕ)^8247*100000000000000^6199 ≤ 42585305243033^6199*125000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65801639 125000000 42585305243033 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209680399/10000000000 : ℝ), (5394671833/10000000000 : ℝ), (65801639/125000000 : ℝ)] ![(3354685023691/25000000000000 : ℝ), (21997977321777/50000000000000 : ℝ), (42585305243033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209680399/10000000000 : ℝ)|^8247 ≤ (3354685023691/25000000000000 : ℝ)^6199
        have hw : |(-2209680399/10000000000 : ℝ)|=(2209680399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394671833/10000000000 : ℝ)|^8247 ≤ (21997977321777/50000000000000 : ℝ)^6199
        have hw : |(5394671833/10000000000 : ℝ)|=(5394671833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65801639/125000000 : ℝ)|^8247 ≤ (42585305243033/100000000000000 : ℝ)^6199
        have hw : |(65801639/125000000 : ℝ)|=(65801639/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s7_1 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069006427/2000000000 : ℝ)*x 0 + (-35561217/156250000 : ℝ)*x 1 + (5264130853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069006427/2000000000 : ℝ)^8247 ≤ (43458193755397/100000000000000 : ℝ)^6199 := by
    have hnat : (1069006427 : ℕ)^8247*100000000000000^6199 ≤ 43458193755397^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069006427 2000000000 43458193755397 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35561217/156250000 : ℝ)^8247 ≤ (3489125965059/25000000000000 : ℝ)^6199 := by
    have hnat : (35561217 : ℕ)^8247*25000000000000^6199 ≤ 3489125965059^6199*156250000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35561217 156250000 3489125965059 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264130853/10000000000 : ℝ)^8247 ≤ (10646325592371/25000000000000 : ℝ)^6199 := by
    have hnat : (5264130853 : ℕ)^8247*25000000000000^6199 ≤ 10646325592371^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264130853 10000000000 10646325592371 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069006427/2000000000 : ℝ), (-35561217/156250000 : ℝ), (5264130853/10000000000 : ℝ)] ![(43458193755397/100000000000000 : ℝ), (3489125965059/25000000000000 : ℝ), (10646325592371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069006427/2000000000 : ℝ)|^8247 ≤ (43458193755397/100000000000000 : ℝ)^6199
        have hw : |(1069006427/2000000000 : ℝ)|=(1069006427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35561217/156250000 : ℝ)|^8247 ≤ (3489125965059/25000000000000 : ℝ)^6199
        have hw : |(-35561217/156250000 : ℝ)|=(35561217/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264130853/10000000000 : ℝ)|^8247 ≤ (10646325592371/25000000000000 : ℝ)^6199
        have hw : |(5264130853/10000000000 : ℝ)|=(5264130853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s7_2 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (41758063/78125000 : ℝ)*x 0 + (1052826217/2000000000 : ℝ)*x 1 + (-568979419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41758063/78125000 : ℝ)^8247 ≤ (43458192987409/100000000000000 : ℝ)^6199 := by
    have hnat : (41758063 : ℕ)^8247*100000000000000^6199 ≤ 43458192987409^6199*78125000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41758063 78125000 43458192987409 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052826217/2000000000 : ℝ)^8247 ≤ (42585304866351/100000000000000 : ℝ)^6199 := by
    have hnat : (1052826217 : ℕ)^8247*100000000000000^6199 ≤ 42585304866351^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052826217 2000000000 42585304866351 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568979419/2500000000 : ℝ)^8247 ≤ (13956502130697/100000000000000 : ℝ)^6199 := by
    have hnat : (568979419 : ℕ)^8247*100000000000000^6199 ≤ 13956502130697^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568979419 2500000000 13956502130697 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41758063/78125000 : ℝ), (1052826217/2000000000 : ℝ), (-568979419/2500000000 : ℝ)] ![(43458192987409/100000000000000 : ℝ), (42585304866351/100000000000000 : ℝ), (13956502130697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41758063/78125000 : ℝ)|^8247 ≤ (43458192987409/100000000000000 : ℝ)^6199
        have hw : |(41758063/78125000 : ℝ)|=(41758063/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052826217/2000000000 : ℝ)|^8247 ≤ (42585304866351/100000000000000 : ℝ)^6199
        have hw : |(1052826217/2000000000 : ℝ)|=(1052826217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-568979419/2500000000 : ℝ)|^8247 ≤ (13956502130697/100000000000000 : ℝ)^6199
        have hw : |(-568979419/2500000000 : ℝ)|=(568979419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s7_3 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875443153/2000000000 : ℝ)*x 0 + (4251488951/10000000000 : ℝ)*x 1 + (4506722223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875443153/2000000000 : ℝ)^8247 ≤ (33316426869959/100000000000000 : ℝ)^6199 := by
    have hnat : (875443153 : ℕ)^8247*100000000000000^6199 ≤ 33316426869959^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875443153 2000000000 33316426869959 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4251488951/10000000000 : ℝ)^8247 ≤ (1602470295791/5000000000000 : ℝ)^6199 := by
    have hnat : (4251488951 : ℕ)^8247*5000000000000^6199 ≤ 1602470295791^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251488951 10000000000 1602470295791 5000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506722223/10000000000 : ℝ)^8247 ≤ (34634167201799/100000000000000 : ℝ)^6199 := by
    have hnat : (4506722223 : ℕ)^8247*100000000000000^6199 ≤ 34634167201799^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506722223 10000000000 34634167201799 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875443153/2000000000 : ℝ), (4251488951/10000000000 : ℝ), (4506722223/10000000000 : ℝ)] ![(33316426869959/100000000000000 : ℝ), (1602470295791/5000000000000 : ℝ), (34634167201799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875443153/2000000000 : ℝ)|^8247 ≤ (33316426869959/100000000000000 : ℝ)^6199
        have hw : |(875443153/2000000000 : ℝ)|=(875443153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4251488951/10000000000 : ℝ)|^8247 ≤ (1602470295791/5000000000000 : ℝ)^6199
        have hw : |(4251488951/10000000000 : ℝ)|=(4251488951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506722223/10000000000 : ℝ)|^8247 ≤ (34634167201799/100000000000000 : ℝ)^6199
        have hw : |(4506722223/10000000000 : ℝ)|=(4506722223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s7_4 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209685643/10000000000 : ℝ)*x 0 + (5264458237/10000000000 : ℝ)*x 1 + (5394343441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209685643/10000000000 : ℝ)^8247 ≤ (6709391230481/50000000000000 : ℝ)^6199 := by
    have hnat : (2209685643 : ℕ)^8247*50000000000000^6199 ≤ 6709391230481^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209685643 10000000000 6709391230481 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264458237/10000000000 : ℝ)^8247 ≤ (42588825829353/100000000000000 : ℝ)^6199 := by
    have hnat : (5264458237 : ℕ)^8247*100000000000000^6199 ≤ 42588825829353^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264458237 10000000000 42588825829353 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394343441/10000000000 : ℝ)^8247 ≤ (4399239168907/10000000000000 : ℝ)^6199 := by
    have hnat : (5394343441 : ℕ)^8247*10000000000000^6199 ≤ 4399239168907^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394343441 10000000000 4399239168907 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209685643/10000000000 : ℝ), (5264458237/10000000000 : ℝ), (5394343441/10000000000 : ℝ)] ![(6709391230481/50000000000000 : ℝ), (42588825829353/100000000000000 : ℝ), (4399239168907/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209685643/10000000000 : ℝ)|^8247 ≤ (6709391230481/50000000000000 : ℝ)^6199
        have hw : |(-2209685643/10000000000 : ℝ)|=(2209685643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264458237/10000000000 : ℝ)|^8247 ≤ (42588825829353/100000000000000 : ℝ)^6199
        have hw : |(5264458237/10000000000 : ℝ)|=(5264458237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394343441/10000000000 : ℝ)|^8247 ≤ (4399239168907/10000000000000 : ℝ)^6199
        have hw : |(5394343441/10000000000 : ℝ)|=(5394343441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s7_5 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312182969/10000000000 : ℝ)*x 0 + (-2145705197/10000000000 : ℝ)*x 1 + (5394343441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312182969/10000000000 : ℝ)^8247 ≤ (344825877143/800000000000 : ℝ)^6199 := by
    have hnat : (5312182969 : ℕ)^8247*800000000000^6199 ≤ 344825877143^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312182969 10000000000 344825877143 800000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145705197/10000000000 : ℝ)^8247 ≤ (6452186826571/50000000000000 : ℝ)^6199 := by
    have hnat : (2145705197 : ℕ)^8247*50000000000000^6199 ≤ 6452186826571^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145705197 10000000000 6452186826571 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394343441/10000000000 : ℝ)^8247 ≤ (4399239168907/10000000000000 : ℝ)^6199 := by
    have hnat : (5394343441 : ℕ)^8247*10000000000000^6199 ≤ 4399239168907^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394343441 10000000000 4399239168907 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312182969/10000000000 : ℝ), (-2145705197/10000000000 : ℝ), (5394343441/10000000000 : ℝ)] ![(344825877143/800000000000 : ℝ), (6452186826571/50000000000000 : ℝ), (4399239168907/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312182969/10000000000 : ℝ)|^8247 ≤ (344825877143/800000000000 : ℝ)^6199
        have hw : |(5312182969/10000000000 : ℝ)|=(5312182969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2145705197/10000000000 : ℝ)|^8247 ≤ (6452186826571/50000000000000 : ℝ)^6199
        have hw : |(-2145705197/10000000000 : ℝ)|=(2145705197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394343441/10000000000 : ℝ)|^8247 ≤ (4399239168907/10000000000000 : ℝ)^6199
        have hw : |(5394343441/10000000000 : ℝ)|=(5394343441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s7_6 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312182969/10000000000 : ℝ)*x 0 + (5394343441/10000000000 : ℝ)*x 1 + (-2145705197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312182969/10000000000 : ℝ)^8247 ≤ (344825877143/800000000000 : ℝ)^6199 := by
    have hnat : (5312182969 : ℕ)^8247*800000000000^6199 ≤ 344825877143^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312182969 10000000000 344825877143 800000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394343441/10000000000 : ℝ)^8247 ≤ (4399239168907/10000000000000 : ℝ)^6199 := by
    have hnat : (5394343441 : ℕ)^8247*10000000000000^6199 ≤ 4399239168907^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394343441 10000000000 4399239168907 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145705197/10000000000 : ℝ)^8247 ≤ (6452186826571/50000000000000 : ℝ)^6199 := by
    have hnat : (2145705197 : ℕ)^8247*50000000000000^6199 ≤ 6452186826571^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145705197 10000000000 6452186826571 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312182969/10000000000 : ℝ), (5394343441/10000000000 : ℝ), (-2145705197/10000000000 : ℝ)] ![(344825877143/800000000000 : ℝ), (4399239168907/10000000000000 : ℝ), (6452186826571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312182969/10000000000 : ℝ)|^8247 ≤ (344825877143/800000000000 : ℝ)^6199
        have hw : |(5312182969/10000000000 : ℝ)|=(5312182969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394343441/10000000000 : ℝ)|^8247 ≤ (4399239168907/10000000000000 : ℝ)^6199
        have hw : |(5394343441/10000000000 : ℝ)|=(5394343441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145705197/10000000000 : ℝ)|^8247 ≤ (6452186826571/50000000000000 : ℝ)^6199
        have hw : |(-2145705197/10000000000 : ℝ)|=(2145705197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s7_7 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218861281/500000000 : ℝ)*x 0 + (140815067/312500000 : ℝ)*x 1 + (4252131497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218861281/500000000 : ℝ)^8247 ≤ (33316526661013/100000000000000 : ℝ)^6199 := by
    have hnat : (218861281 : ℕ)^8247*100000000000000^6199 ≤ 33316526661013^6199*500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218861281 500000000 33316526661013 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140815067/312500000 : ℝ)^8247 ≤ (17313811612837/50000000000000 : ℝ)^6199 := by
    have hnat : (140815067 : ℕ)^8247*50000000000000^6199 ≤ 17313811612837^6199*312500000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140815067 312500000 17313811612837 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4252131497/10000000000 : ℝ)^8247 ≤ (8013962526517/25000000000000 : ℝ)^6199 := by
    have hnat : (4252131497 : ℕ)^8247*25000000000000^6199 ≤ 8013962526517^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252131497 10000000000 8013962526517 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218861281/500000000 : ℝ), (140815067/312500000 : ℝ), (4252131497/10000000000 : ℝ)] ![(33316526661013/100000000000000 : ℝ), (17313811612837/50000000000000 : ℝ), (8013962526517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218861281/500000000 : ℝ)|^8247 ≤ (33316526661013/100000000000000 : ℝ)^6199
        have hw : |(218861281/500000000 : ℝ)|=(218861281/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140815067/312500000 : ℝ)|^8247 ≤ (17313811612837/50000000000000 : ℝ)^6199
        have hw : |(140815067/312500000 : ℝ)|=(140815067/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4252131497/10000000000 : ℝ)|^8247 ≤ (8013962526517/25000000000000 : ℝ)^6199
        have hw : |(4252131497/10000000000 : ℝ)|=(4252131497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1054_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11233/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6999/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1751/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1751/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1751/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1751/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1751/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1751/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11223/100000 : ℝ) ^ (4123/1024 : ℝ) ≤ (7487897674286359/50000000000000000000 : ℝ) := by
    have hpowers : (11223/100000 : ℝ)^4123 ≤ (7487897674286359/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11223 : ℕ)^4123*50000000000000000000^1024 ≤ 7487897674286359^1024*100000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11223 100000 7487897674286359 50000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11223/100000 : ℝ)) (X := (7487897674286359/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1751/12500 : ℝ) ^ (4123/1024 : ℝ) ≤ (36559215821894273/100000000000000000000 : ℝ) := by
    have hpowers : (1751/12500 : ℝ)^4123 ≤ (36559215821894273/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1751 : ℕ)^4123*100000000000000000000^1024 ≤ 36559215821894273^1024*12500^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1751 12500 36559215821894273 100000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1751/12500 : ℝ)) (X := (36559215821894273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007487897674286359/25000000000000000000 : ℝ) ≤ (10000743802500663/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (25007487897674286359/25000000000000000000 : ℝ)^1024 ≤ (10000743802500663/10000000000000000 : ℝ)^4123 := by
      have hnat : (25007487897674286359 : ℕ)^1024*10000000000000000^4123 ≤ 10000743802500663^4123*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007487897674286359 25000000000000000000 10000743802500663 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000743802500663/10000000000000000 : ℝ)) (X := (25007487897674286359/25000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051535011170466991/100000000000000000000 : ℝ) ≤ (10001279690365233/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (100051535011170466991/100000000000000000000 : ℝ)^1024 ≤ (10001279690365233/10000000000000000 : ℝ)^4123 := by
      have hnat : (100051535011170466991 : ℕ)^1024*10000000000000000^4123 ≤ 10001279690365233^4123*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051535011170466991 100000000000000000000 10001279690365233 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001279690365233/10000000000000000 : ℝ)) (X := (100051535011170466991/100000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036559215821894273/50000000000000000000 : ℝ) ≤ (10001815578229803/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (50036559215821894273/50000000000000000000 : ℝ)^1024 ≤ (10001815578229803/10000000000000000 : ℝ)^4123 := by
      have hnat : (50036559215821894273 : ℕ)^1024*10000000000000000^4123 ≤ 10001815578229803^4123*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036559215821894273 50000000000000000000 10001815578229803 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001815578229803/10000000000000000 : ℝ)) (X := (50036559215821894273/50000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7487897674286359/50000000000000000000 : ℝ) ≤ ((5568008590191241647/5570000000000000000 : ℝ)+2*(53588786457/27850000000000 : ℝ)*(11223/100000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (5568008590191241647/5570000000000000000 : ℝ)+2*(53588786457/27850000000000 : ℝ)*(11223/100000 : ℝ)=(10000743802500663/10000000000000000 : ℝ) by norm_num, show 1+2*(7487897674286359/50000000000000000000 : ℝ)=(25007487897674286359/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36559215821894273/100000000000000000000 : ℝ)+(7487897674286359/50000000000000000000 : ℝ) ≤ ((5568008590191241647/5570000000000000000 : ℝ)+(53588786457/27850000000000 : ℝ)*((1751/12500 : ℝ)+(11223/100000 : ℝ)))^(4123/1024 : ℝ) := by
    rw [show (5568008590191241647/5570000000000000000 : ℝ)+(53588786457/27850000000000 : ℝ)*((1751/12500 : ℝ)+(11223/100000 : ℝ))=(10001279690365233/10000000000000000 : ℝ) by norm_num, show 1+(36559215821894273/100000000000000000000 : ℝ)+(7487897674286359/50000000000000000000 : ℝ)=(100051535011170466991/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36559215821894273/100000000000000000000 : ℝ) ≤ ((5568008590191241647/5570000000000000000 : ℝ)+2*(53588786457/27850000000000 : ℝ)*(1751/12500 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (5568008590191241647/5570000000000000000 : ℝ)+2*(53588786457/27850000000000 : ℝ)*(1751/12500 : ℝ)=(10001815578229803/10000000000000000 : ℝ) by norm_num, show 1+2*(36559215821894273/100000000000000000000 : ℝ)=(50036559215821894273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5568008590191241647/5570000000000000000 : ℝ)*(X 1 0+X 2 0)+(53588786457/27850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (1751/12500 : ℝ)) (c := (5568008590191241647/5570000000000000000 : ℝ)) (alpha := (53588786457/27850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5568008590191241647/5570000000000000000 : ℝ)*(X 0 1+X 2 1)+(53588786457/27850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (1751/12500 : ℝ)) (c := (5568008590191241647/5570000000000000000 : ℝ)) (alpha := (53588786457/27850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5568008590191241647/5570000000000000000 : ℝ)*(X 0 2+X 1 2)+(53588786457/27850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (1751/12500 : ℝ)) (c := (5568008590191241647/5570000000000000000 : ℝ)) (alpha := (53588786457/27850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2209680399/10000000000 : ℝ)*X 0 0+(5394671833/10000000000 : ℝ)*X 0 1+(65801639/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069006427/2000000000 : ℝ)*X 1 0+(-35561217/156250000 : ℝ)*X 1 1+(5264130853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((41758063/78125000 : ℝ)*X 2 0+(1052826217/2000000000 : ℝ)*X 2 1+(-568979419/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875443153/2000000000 : ℝ)*X 0 0+(4251488951/10000000000 : ℝ)*X 0 1+(4506722223/10000000000 : ℝ)*X 0 2+(875443153/2000000000 : ℝ)*X 1 0+(4251488951/10000000000 : ℝ)*X 1 1+(4506722223/10000000000 : ℝ)*X 1 2+(875443153/2000000000 : ℝ)*X 2 0+(4251488951/10000000000 : ℝ)*X 2 1+(4506722223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2209685643/10000000000 : ℝ)*X 0 0+(5264458237/10000000000 : ℝ)*X 0 1+(5394343441/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312182969/10000000000 : ℝ)*X 1 0+(-2145705197/10000000000 : ℝ)*X 1 1+(5394343441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312182969/10000000000 : ℝ)*X 2 0+(5394343441/10000000000 : ℝ)*X 2 1+(-2145705197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218861281/500000000 : ℝ)*X 0 0+(140815067/312500000 : ℝ)*X 0 1+(4252131497/10000000000 : ℝ)*X 0 2+(218861281/500000000 : ℝ)*X 1 0+(140815067/312500000 : ℝ)*X 1 1+(4252131497/10000000000 : ℝ)*X 1 2+(218861281/500000000 : ℝ)*X 2 0+(140815067/312500000 : ℝ)*X 2 1+(4252131497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (537023481757206206191607127/139250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103060057/20000000000000 : ℝ)*(base19) + (68256421/100000000000000 : ℝ)*(base23) + (92278633/50000000000000 : ℝ)*(lower2) + (34821301/100000000000000 : ℝ)*(upper3) + (22479491/25000000000000 : ℝ)*(upper5) + (2894608959218947/50000000000000 : ℝ)*(major0) + (2894608959218947/50000000000000 : ℝ)*(major1) + (2894608959218947/50000000000000 : ℝ)*(major2) + (7660438899554381/100000000000000 : ℝ)*(sp0) + (478777421500527/6250000000000 : ℝ)*(sp1) + (957554898881537/12500000000000 : ℝ)*(sp2) + (39179903432101/1000000000000 : ℝ)*(sp3) + (11242323/3125000000000 : ℝ)*(sp4) + (6105805557/100000000000000 : ℝ)*(sp7) + (1958998224507829/50000000000000 : ℝ)*(f.failure) + (7660439259308717/100000000000000 : ℝ)*(f.sum) + (9401550250311/2785000000000000000000000000 : ℝ)*base65 + (4177670097256814291/278500000000000000000000000000000 : ℝ)*base68 + (1679840557548814291/278500000000000000000000000000000 : ℝ)*base70 + (5789228128646314291/278500000000000000000000000000000 : ℝ)*base72 + (165503336903/87031250000000000000000000 : ℝ)*base73 + (3373261882851185709/278500000000000000000000000000000 : ℝ)*base75 + (819616801569685709/278500000000000000000000000000000 : ℝ)*base77 + (4832174382924314291/278500000000000000000000000000000 : ℝ)*base80 + (14055072866211/2785000000000000000000000000 : ℝ)*base81 + (3921123/1250000000000000000000 : ℝ)*base90 + (3921123/1250000000000000000000 : ℝ)*base92 + (3921123/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2606247034442076864962351523/278500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (872550359/50000000000000 : ℝ)*(base19) + (474274847/25000000000000 : ℝ)*(base23) + (187853907/100000000000000 : ℝ)*(upper3) + (69126389/100000000000000 : ℝ)*(lower4) + (95528253/50000000000000 : ℝ)*(upper5) + (5818438706701297/100000000000000 : ℝ)*(major0) + (5818438706701297/100000000000000 : ℝ)*(major1) + (5818438706701297/100000000000000 : ℝ)*(major2) + (23649001971/50000000000000 : ℝ)*(sp1) + (6354363993/12500000000000 : ℝ)*(sp2) + (384955238054079/5000000000000 : ℝ)*(sp4) + (192476392949423/2500000000000 : ℝ)*(sp5) + (962381503633781/12500000000000 : ℝ)*(sp6) + (787554468076481/20000000000000 : ℝ)*(sp7) + (787554468076481/20000000000000 : ℝ)*(f.failure) + (384955238054079/5000000000000 : ℝ)*(f.sum) + (2580185338071/1392500000000000000000000000 : ℝ)*base66 + (2159471561538883841/557000000000000000000000000000000 : ℝ)*base68 + (2298045547716116159/557000000000000000000000000000000 : ℝ)*base69 + (1498727886171116159/557000000000000000000000000000000 : ℝ)*base71 + (5580254768491/1392500000000000000000000000 : ℝ)*base74 + (3718235429154116159/557000000000000000000000000000000 : ℝ)*base75 + (5586884196274883841/557000000000000000000000000000000 : ℝ)*base78 + (8749235220025116159/557000000000000000000000000000000 : ℝ)*base79 + (6761325489267/2785000000000000000000000000 : ℝ)*base82 + (486153/500000000000000000000 : ℝ)*base89 + (486153/500000000000000000000 : ℝ)*base91 + (486153/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1054_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1054_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1054_s8_0 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-552422101/2500000000 : ℝ)*x 0 + (1348641169/2500000000 : ℝ)*x 1 + (2632116569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552422101/2500000000 : ℝ)^8247 ≤ (13418804767053/100000000000000 : ℝ)^6199 := by
    have hnat : (552422101 : ℕ)^8247*100000000000000^6199 ≤ 13418804767053^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552422101 2500000000 13418804767053 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348641169/2500000000 : ℝ)^8247 ≤ (1099869800361/2500000000000 : ℝ)^6199 := by
    have hnat : (1348641169 : ℕ)^8247*2500000000000^6199 ≤ 1099869800361^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348641169 2500000000 1099869800361 2500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632116569/5000000000 : ℝ)^8247 ≤ (21293201600381/50000000000000 : ℝ)^6199 := by
    have hnat : (2632116569 : ℕ)^8247*50000000000000^6199 ≤ 21293201600381^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632116569 5000000000 21293201600381 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-552422101/2500000000 : ℝ), (1348641169/2500000000 : ℝ), (2632116569/5000000000 : ℝ)] ![(13418804767053/100000000000000 : ℝ), (1099869800361/2500000000000 : ℝ), (21293201600381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-552422101/2500000000 : ℝ)|^8247 ≤ (13418804767053/100000000000000 : ℝ)^6199
        have hw : |(-552422101/2500000000 : ℝ)|=(552422101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348641169/2500000000 : ℝ)|^8247 ≤ (1099869800361/2500000000000 : ℝ)^6199
        have hw : |(1348641169/2500000000 : ℝ)|=(1348641169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632116569/5000000000 : ℝ)|^8247 ≤ (21293201600381/50000000000000 : ℝ)^6199
        have hw : |(2632116569/5000000000 : ℝ)|=(2632116569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s8_1 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345005929/10000000000 : ℝ)*x 0 + (-568954419/2500000000 : ℝ)*x 1 + (2632116577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345005929/10000000000 : ℝ)^8247 ≤ (21728955146291/50000000000000 : ℝ)^6199 := by
    have hnat : (5345005929 : ℕ)^8247*50000000000000^6199 ≤ 21728955146291^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345005929 10000000000 21728955146291 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568954419/2500000000 : ℝ)^8247 ≤ (13955686316529/100000000000000 : ℝ)^6199 := by
    have hnat : (568954419 : ℕ)^8247*100000000000000^6199 ≤ 13955686316529^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568954419 2500000000 13955686316529 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632116577/5000000000 : ℝ)^8247 ≤ (42586403372961/100000000000000 : ℝ)^6199 := by
    have hnat : (2632116577 : ℕ)^8247*100000000000000^6199 ≤ 42586403372961^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632116577 5000000000 42586403372961 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345005929/10000000000 : ℝ), (-568954419/2500000000 : ℝ), (2632116577/5000000000 : ℝ)] ![(21728955146291/50000000000000 : ℝ), (13955686316529/100000000000000 : ℝ), (42586403372961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345005929/10000000000 : ℝ)|^8247 ≤ (21728955146291/50000000000000 : ℝ)^6199
        have hw : |(5345005929/10000000000 : ℝ)|=(5345005929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-568954419/2500000000 : ℝ)|^8247 ≤ (13955686316529/100000000000000 : ℝ)^6199
        have hw : |(-568954419/2500000000 : ℝ)|=(568954419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632116577/5000000000 : ℝ)|^8247 ≤ (42586403372961/100000000000000 : ℝ)^6199
        have hw : |(2632116577/5000000000 : ℝ)|=(2632116577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s8_2 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336251469/2500000000 : ℝ)*x 0 + (2632116563/5000000000 : ℝ)*x 1 + (-455163557/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336251469/2500000000 : ℝ)^8247 ≤ (43457909719297/100000000000000 : ℝ)^6199 := by
    have hnat : (1336251469 : ℕ)^8247*100000000000000^6199 ≤ 43457909719297^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336251469 2500000000 43457909719297 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632116563/5000000000 : ℝ)^8247 ≤ (42586403071613/100000000000000 : ℝ)^6199 := by
    have hnat : (2632116563 : ℕ)^8247*100000000000000^6199 ≤ 42586403071613^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632116563 5000000000 42586403071613 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (455163557/2000000000 : ℝ)^8247 ≤ (21805761259/156250000000 : ℝ)^6199 := by
    have hnat : (455163557 : ℕ)^8247*156250000000^6199 ≤ 21805761259^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455163557 2000000000 21805761259 156250000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336251469/2500000000 : ℝ), (2632116563/5000000000 : ℝ), (-455163557/2000000000 : ℝ)] ![(43457909719297/100000000000000 : ℝ), (42586403071613/100000000000000 : ℝ), (21805761259/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336251469/2500000000 : ℝ)|^8247 ≤ (43457909719297/100000000000000 : ℝ)^6199
        have hw : |(1336251469/2500000000 : ℝ)|=(1336251469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632116563/5000000000 : ℝ)|^8247 ≤ (42586403071613/100000000000000 : ℝ)^6199
        have hw : |(2632116563/5000000000 : ℝ)|=(2632116563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-455163557/2000000000 : ℝ)|^8247 ≤ (21805761259/156250000000 : ℝ)^6199
        have hw : |(-455163557/2000000000 : ℝ)|=(455163557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s8_3 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (273576309/625000000 : ℝ)*x 0 + (265730831/625000000 : ℝ)*x 1 + (4506516643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273576309/625000000 : ℝ)^8247 ≤ (33316479312149/100000000000000 : ℝ)^6199 := by
    have hnat : (273576309 : ℕ)^8247*100000000000000^6199 ≤ 33316479312149^6199*625000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273576309 625000000 33316479312149 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265730831/625000000 : ℝ)^8247 ≤ (32051455287597/100000000000000 : ℝ)^6199 := by
    have hnat : (265730831 : ℕ)^8247*100000000000000^6199 ≤ 32051455287597^6199*625000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265730831 625000000 32051455287597 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506516643/10000000000 : ℝ)^8247 ≤ (8658016344983/25000000000000 : ℝ)^6199 := by
    have hnat : (4506516643 : ℕ)^8247*25000000000000^6199 ≤ 8658016344983^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506516643 10000000000 8658016344983 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273576309/625000000 : ℝ), (265730831/625000000 : ℝ), (4506516643/10000000000 : ℝ)] ![(33316479312149/100000000000000 : ℝ), (32051455287597/100000000000000 : ℝ), (8658016344983/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273576309/625000000 : ℝ)|^8247 ≤ (33316479312149/100000000000000 : ℝ)^6199
        have hw : |(273576309/625000000 : ℝ)|=(273576309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(265730831/625000000 : ℝ)|^8247 ≤ (32051455287597/100000000000000 : ℝ)^6199
        have hw : |(265730831/625000000 : ℝ)|=(265730831/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506516643/10000000000 : ℝ)|^8247 ≤ (8658016344983/25000000000000 : ℝ)^6199
        have hw : |(4506516643/10000000000 : ℝ)|=(4506516643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s8_4 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-441938691/2000000000 : ℝ)*x 0 + (2632279699/5000000000 : ℝ)*x 1 + (5394237273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441938691/2000000000 : ℝ)^8247 ≤ (2683769114811/20000000000000 : ℝ)^6199 := by
    have hnat : (441938691 : ℕ)^8247*20000000000000^6199 ≤ 2683769114811^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441938691 2000000000 2683769114811 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632279699/5000000000 : ℝ)^8247 ≤ (42589914586033/100000000000000 : ℝ)^6199 := by
    have hnat : (2632279699 : ℕ)^8247*100000000000000^6199 ≤ 42589914586033^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632279699 5000000000 42589914586033 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394237273/10000000000 : ℝ)^8247 ≤ (5498904976689/12500000000000 : ℝ)^6199 := by
    have hnat : (5394237273 : ℕ)^8247*12500000000000^6199 ≤ 5498904976689^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394237273 10000000000 5498904976689 12500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441938691/2000000000 : ℝ), (2632279699/5000000000 : ℝ), (5394237273/10000000000 : ℝ)] ![(2683769114811/20000000000000 : ℝ), (42589914586033/100000000000000 : ℝ), (5498904976689/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441938691/2000000000 : ℝ)|^8247 ≤ (2683769114811/20000000000000 : ℝ)^6199
        have hw : |(-441938691/2000000000 : ℝ)|=(441938691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632279699/5000000000 : ℝ)|^8247 ≤ (42589914586033/100000000000000 : ℝ)^6199
        have hw : |(2632279699/5000000000 : ℝ)|=(2632279699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394237273/10000000000 : ℝ)|^8247 ≤ (5498904976689/12500000000000 : ℝ)^6199
        have hw : |(5394237273/10000000000 : ℝ)|=(5394237273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s8_5 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531220939/1000000000 : ℝ)*x 0 + (-2145813601/10000000000 : ℝ)*x 1 + (539423721/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531220939/1000000000 : ℝ)^8247 ≤ (10775879962571/25000000000000 : ℝ)^6199 := by
    have hnat : (531220939 : ℕ)^8247*25000000000000^6199 ≤ 10775879962571^6199*1000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531220939 1000000000 10775879962571 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145813601/10000000000 : ℝ)^8247 ≤ (6452620497361/50000000000000 : ℝ)^6199 := by
    have hnat : (2145813601 : ℕ)^8247*50000000000000^6199 ≤ 6452620497361^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145813601 10000000000 6452620497361 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539423721/1000000000 : ℝ)^8247 ≤ (5498904891249/12500000000000 : ℝ)^6199 := by
    have hnat : (539423721 : ℕ)^8247*12500000000000^6199 ≤ 5498904891249^6199*1000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539423721 1000000000 5498904891249 12500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531220939/1000000000 : ℝ), (-2145813601/10000000000 : ℝ), (539423721/1000000000 : ℝ)] ![(10775879962571/25000000000000 : ℝ), (6452620497361/50000000000000 : ℝ), (5498904891249/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531220939/1000000000 : ℝ)|^8247 ≤ (10775879962571/25000000000000 : ℝ)^6199
        have hw : |(531220939/1000000000 : ℝ)|=(531220939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2145813601/10000000000 : ℝ)|^8247 ≤ (6452620497361/50000000000000 : ℝ)^6199
        have hw : |(-2145813601/10000000000 : ℝ)|=(2145813601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539423721/1000000000 : ℝ)|^8247 ≤ (5498904891249/12500000000000 : ℝ)^6199
        have hw : |(539423721/1000000000 : ℝ)|=(539423721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s8_6 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312209287/10000000000 : ℝ)*x 0 + (1078847433/2000000000 : ℝ)*x 1 + (-2145813803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312209287/10000000000 : ℝ)^8247 ≤ (43103518738427/100000000000000 : ℝ)^6199 := by
    have hnat : (5312209287 : ℕ)^8247*100000000000000^6199 ≤ 43103518738427^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312209287 10000000000 43103518738427 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078847433/2000000000 : ℝ)^8247 ≤ (10997809660441/25000000000000 : ℝ)^6199 := by
    have hnat : (1078847433 : ℕ)^8247*25000000000000^6199 ≤ 10997809660441^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078847433 2000000000 10997809660441 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145813803/10000000000 : ℝ)^8247 ≤ (12905242610939/100000000000000 : ℝ)^6199 := by
    have hnat : (2145813803 : ℕ)^8247*100000000000000^6199 ≤ 12905242610939^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145813803 10000000000 12905242610939 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312209287/10000000000 : ℝ), (1078847433/2000000000 : ℝ), (-2145813803/10000000000 : ℝ)] ![(43103518738427/100000000000000 : ℝ), (10997809660441/25000000000000 : ℝ), (12905242610939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312209287/10000000000 : ℝ)|^8247 ≤ (43103518738427/100000000000000 : ℝ)^6199
        have hw : |(5312209287/10000000000 : ℝ)|=(5312209287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078847433/2000000000 : ℝ)|^8247 ≤ (10997809660441/25000000000000 : ℝ)^6199
        have hw : |(1078847433/2000000000 : ℝ)|=(1078847433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145813803/10000000000 : ℝ)|^8247 ≤ (12905242610939/100000000000000 : ℝ)^6199
        have hw : |(-2145813803/10000000000 : ℝ)|=(2145813803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s8_7 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188615323/5000000000 : ℝ)*x 0 + (2252939397/5000000000 : ℝ)*x 1 + (531541713/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188615323/5000000000 : ℝ)^8247 ≤ (33316577553973/100000000000000 : ℝ)^6199 := by
    have hnat : (2188615323 : ℕ)^8247*100000000000000^6199 ≤ 33316577553973^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188615323 5000000000 33316577553973 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252939397/5000000000 : ℝ)^8247 ≤ (34625544300413/100000000000000 : ℝ)^6199 := by
    have hnat : (2252939397 : ℕ)^8247*100000000000000^6199 ≤ 34625544300413^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252939397 5000000000 34625544300413 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531541713/1250000000 : ℝ)^8247 ≤ (4007234767121/12500000000000 : ℝ)^6199 := by
    have hnat : (531541713 : ℕ)^8247*12500000000000^6199 ≤ 4007234767121^6199*1250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531541713 1250000000 4007234767121 12500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188615323/5000000000 : ℝ), (2252939397/5000000000 : ℝ), (531541713/1250000000 : ℝ)] ![(33316577553973/100000000000000 : ℝ), (34625544300413/100000000000000 : ℝ), (4007234767121/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188615323/5000000000 : ℝ)|^8247 ≤ (33316577553973/100000000000000 : ℝ)^6199
        have hw : |(2188615323/5000000000 : ℝ)|=(2188615323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252939397/5000000000 : ℝ)|^8247 ≤ (34625544300413/100000000000000 : ℝ)^6199
        have hw : |(2252939397/5000000000 : ℝ)|=(2252939397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531541713/1250000000 : ℝ)|^8247 ≤ (4007234767121/12500000000000 : ℝ)^6199
        have hw : |(531541713/1250000000 : ℝ)|=(531541713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1054_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2247/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2799/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6999/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11233/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6999/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11233/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6999/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11233/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6999/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11233/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6999/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11233/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6999/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11233/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11233/100000 : ℝ) ^ (4123/1024 : ℝ) ≤ (3005919008960073/20000000000000000000 : ℝ) := by
    have hpowers : (11233/100000 : ℝ)^4123 ≤ (3005919008960073/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11233 : ℕ)^4123*20000000000000000000^1024 ≤ 3005919008960073^1024*100000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11233 100000 3005919008960073 20000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11233/100000 : ℝ)) (X := (3005919008960073/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6999/50000 : ℝ) ^ (4123/1024 : ℝ) ≤ (36454245881025817/100000000000000000000 : ℝ) := by
    have hpowers : (6999/50000 : ℝ)^4123 ≤ (36454245881025817/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6999 : ℕ)^4123*100000000000000000000^1024 ≤ 36454245881025817^1024*50000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6999 50000 36454245881025817 100000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6999/50000 : ℝ)) (X := (36454245881025817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10003005919008960073/10000000000000000000 : ℝ) ≤ (2000149294853443/2000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (10003005919008960073/10000000000000000000 : ℝ)^1024 ≤ (2000149294853443/2000000000000000 : ℝ)^4123 := by
      have hnat : (10003005919008960073 : ℕ)^1024*2000000000000000^4123 ≤ 2000149294853443^4123*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003005919008960073 10000000000000000000 2000149294853443 2000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000149294853443/2000000000000000 : ℝ)) (X := (10003005919008960073/10000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025741920462913091/50000000000000000000 : ℝ) ≤ (2500319604994577/2500000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (50025741920462913091/50000000000000000000 : ℝ)^1024 ≤ (2500319604994577/2500000000000000 : ℝ)^4123 := by
      have hnat : (50025741920462913091 : ℕ)^1024*2500000000000000^4123 ≤ 2500319604994577^4123*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025741920462913091 50000000000000000000 2500319604994577 2500000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500319604994577/2500000000000000 : ℝ)) (X := (50025741920462913091/50000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036454245881025817/50000000000000000000 : ℝ) ≤ (10001810365689401/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (50036454245881025817/50000000000000000000 : ℝ)^1024 ≤ (10001810365689401/10000000000000000 : ℝ)^4123 := by
      have hnat : (50036454245881025817 : ℕ)^1024*10000000000000000^4123 ≤ 10001810365689401^4123*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036454245881025817 50000000000000000000 10001810365689401 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001810365689401/10000000000000000 : ℝ)) (X := (50036454245881025817/50000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3005919008960073/20000000000000000000 : ℝ) ≤ ((27640113309003434137/27650000000000000000 : ℝ)+2*(531945711093/276500000000000 : ℝ)*(11233/100000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (27640113309003434137/27650000000000000000 : ℝ)+2*(531945711093/276500000000000 : ℝ)*(11233/100000 : ℝ)=(2000149294853443/2000000000000000 : ℝ) by norm_num, show 1+2*(3005919008960073/20000000000000000000 : ℝ)=(10003005919008960073/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36454245881025817/100000000000000000000 : ℝ)+(3005919008960073/20000000000000000000 : ℝ) ≤ ((27640113309003434137/27650000000000000000 : ℝ)+(531945711093/276500000000000 : ℝ)*((6999/50000 : ℝ)+(11233/100000 : ℝ)))^(4123/1024 : ℝ) := by
    rw [show (27640113309003434137/27650000000000000000 : ℝ)+(531945711093/276500000000000 : ℝ)*((6999/50000 : ℝ)+(11233/100000 : ℝ))=(2500319604994577/2500000000000000 : ℝ) by norm_num, show 1+(36454245881025817/100000000000000000000 : ℝ)+(3005919008960073/20000000000000000000 : ℝ)=(50025741920462913091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36454245881025817/100000000000000000000 : ℝ) ≤ ((27640113309003434137/27650000000000000000 : ℝ)+2*(531945711093/276500000000000 : ℝ)*(6999/50000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (27640113309003434137/27650000000000000000 : ℝ)+2*(531945711093/276500000000000 : ℝ)*(6999/50000 : ℝ)=(10001810365689401/10000000000000000 : ℝ) by norm_num, show 1+2*(36454245881025817/100000000000000000000 : ℝ)=(50036454245881025817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27640113309003434137/27650000000000000000 : ℝ)*(X 1 0+X 2 0)+(531945711093/276500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (11233/100000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (27640113309003434137/27650000000000000000 : ℝ)) (alpha := (531945711093/276500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27640113309003434137/27650000000000000000 : ℝ)*(X 0 1+X 2 1)+(531945711093/276500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (11233/100000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (27640113309003434137/27650000000000000000 : ℝ)) (alpha := (531945711093/276500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27640113309003434137/27650000000000000000 : ℝ)*(X 0 2+X 1 2)+(531945711093/276500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (11233/100000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (27640113309003434137/27650000000000000000 : ℝ)) (alpha := (531945711093/276500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-552422101/2500000000 : ℝ)*X 0 0+(1348641169/2500000000 : ℝ)*X 0 1+(2632116569/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345005929/10000000000 : ℝ)*X 1 0+(-568954419/2500000000 : ℝ)*X 1 1+(2632116577/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336251469/2500000000 : ℝ)*X 2 0+(2632116563/5000000000 : ℝ)*X 2 1+(-455163557/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((273576309/625000000 : ℝ)*X 0 0+(265730831/625000000 : ℝ)*X 0 1+(4506516643/10000000000 : ℝ)*X 0 2+(273576309/625000000 : ℝ)*X 1 0+(265730831/625000000 : ℝ)*X 1 1+(4506516643/10000000000 : ℝ)*X 1 2+(273576309/625000000 : ℝ)*X 2 0+(265730831/625000000 : ℝ)*X 2 1+(4506516643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-441938691/2000000000 : ℝ)*X 0 0+(2632279699/5000000000 : ℝ)*X 0 1+(5394237273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531220939/1000000000 : ℝ)*X 1 0+(-2145813601/10000000000 : ℝ)*X 1 1+(539423721/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312209287/10000000000 : ℝ)*X 2 0+(1078847433/2000000000 : ℝ)*X 2 1+(-2145813803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2188615323/5000000000 : ℝ)*X 0 0+(2252939397/5000000000 : ℝ)*X 0 1+(531541713/1250000000 : ℝ)*X 0 2+(2188615323/5000000000 : ℝ)*X 1 0+(2252939397/5000000000 : ℝ)*X 1 1+(531541713/1250000000 : ℝ)*X 1 2+(2188615323/5000000000 : ℝ)*X 2 0+(2252939397/5000000000 : ℝ)*X 2 1+(531541713/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53134064859066432785404851/12343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95079531/10000000000000 : ℝ)*(base19) + (87775293/10000000000000 : ℝ)*(base23) + (601539/12500000000000 : ℝ)*(lower2) + (181988811/100000000000000 : ℝ)*(upper3) + (3218457/50000000000000 : ℝ)*(lower4) + (724819221103537/12500000000000 : ℝ)*(major0) + (724819221103537/12500000000000 : ℝ)*(major1) + (724819221103537/12500000000000 : ℝ)*(major2) + (959096387052857/12500000000000 : ℝ)*(sp0) + (767279172664467/10000000000000 : ℝ)*(sp1) + (7672791799687049/100000000000000 : ℝ)*(sp2) + (981074829552961/25000000000000 : ℝ)*(sp3) + (21581017123/100000000000000 : ℝ)*(sp4) + (3849630091/25000000000000 : ℝ)*(sp7) + (245269669795763/6250000000000 : ℝ)*(f.failure) + (7672792677439979/100000000000000 : ℝ)*(f.sum) + (24158210367221/1975000000000000000000000000 : ℝ)*base66 + (369153947032129633/49375000000000000000000000000000 : ℝ)*base68 + (140978750904004633/49375000000000000000000000000000 : ℝ)*base70 + (534235253244629633/49375000000000000000000000000000 : ℝ)*base72 + (548169416187/246875000000000000000000000 : ℝ)*base74 + (1179718223633379633/49375000000000000000000000000000 : ℝ)*base76 + (704077920760879633/49375000000000000000000000000000 : ℝ)*base78 + (739128236370370367/49375000000000000000000000000000 : ℝ)*base79 + (5105053783579/1975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (488619/156250000000000000000 : ℝ)*base89 + (488619/156250000000000000000 : ℝ)*base91 + (488619/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1033085546068556130797070159/345625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (344828241/100000000000000 : ℝ)*(base19) + (258456761/100000000000000 : ℝ)*(base23) + (4479861/20000000000000 : ℝ)*(lower1) + (67046391/100000000000000 : ℝ)*(upper2) + (1672411/20000000000000 : ℝ)*(lower3) + (2913871162250869/50000000000000 : ℝ)*(major0) + (2913871162250869/50000000000000 : ℝ)*(major1) + (2913871162250869/50000000000000 : ℝ)*(major2) + (1407515357/50000000000000 : ℝ)*(sp0) + (40859373/400000000000 : ℝ)*(sp1) + (7711412940441943/100000000000000 : ℝ)*(sp4) + (1927851298950291/25000000000000 : ℝ)*(sp5) + (1542283099403179/20000000000000 : ℝ)*(sp6) + (1972034396948139/50000000000000 : ℝ)*(sp7) + (1972034396948139/50000000000000 : ℝ)*(f.failure) + (481963484717041/6250000000000 : ℝ)*(f.sum) + (6454169946641/13825000000000000000000000000 : ℝ)*base66 + (5505625475380784947/1382500000000000000000000000000000 : ℝ)*base68 + (3764198023053284947/1382500000000000000000000000000000 : ℝ)*base70 + (7322060549540784947/1382500000000000000000000000000000 : ℝ)*base72 + (3440668096483/6912500000000000000000000000 : ℝ)*base74 + (55650839537304215053/1382500000000000000000000000000000 : ℝ)*base75 + (8948236757578284947/1382500000000000000000000000000000 : ℝ)*base78 + (6212426798983284947/1382500000000000000000000000000000 : ℝ)*base80 + (53056331131359/13825000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (4828093/1250000000000000000000 : ℝ)*base90 + (4828093/1250000000000000000000 : ℝ)*base92 + (4828093/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1054_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1054_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1054_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1054_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1054_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1054_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1054_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
