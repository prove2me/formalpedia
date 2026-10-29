-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1430_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:54:19.094192+00:00
-- url     : https://prove2.me/submissions/c0ae121d-1828-41a6-9200-49ecab93e31c

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
theorem support_rectangle_w1430_s3_0 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-98463329/500000000 : ℝ)*x 0 + (1083436649/2000000000 : ℝ)*x 1 + (5238606661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98463329/500000000 : ℝ)^2195 ≤ (1501511938159/12500000000000 : ℝ)^1683 := by
    have hnat : (98463329 : ℕ)^2195*12500000000000^1683 ≤ 1501511938159^1683*500000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98463329 500000000 1501511938159 12500000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083436649/2000000000 : ℝ)^2195 ≤ (11238865528429/25000000000000 : ℝ)^1683 := by
    have hnat : (1083436649 : ℕ)^2195*25000000000000^1683 ≤ 11238865528429^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083436649 2000000000 11238865528429 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238606661/10000000000 : ℝ)^2195 ≤ (21516221182083/50000000000000 : ℝ)^1683 := by
    have hnat : (5238606661 : ℕ)^2195*50000000000000^1683 ≤ 21516221182083^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238606661 10000000000 21516221182083 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98463329/500000000 : ℝ), (1083436649/2000000000 : ℝ), (5238606661/10000000000 : ℝ)] ![(1501511938159/12500000000000 : ℝ), (11238865528429/25000000000000 : ℝ), (21516221182083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98463329/500000000 : ℝ)|^2195 ≤ (1501511938159/12500000000000 : ℝ)^1683
        have hw : |(-98463329/500000000 : ℝ)|=(98463329/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083436649/2000000000 : ℝ)|^2195 ≤ (11238865528429/25000000000000 : ℝ)^1683
        have hw : |(1083436649/2000000000 : ℝ)|=(1083436649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238606661/10000000000 : ℝ)|^2195 ≤ (21516221182083/50000000000000 : ℝ)^1683
        have hw : |(5238606661/10000000000 : ℝ)|=(5238606661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s3_1 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349634737/10000000000 : ℝ)*x 0 + (-2060356553/10000000000 : ℝ)*x 1 + (654825831/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349634737/10000000000 : ℝ)^2195 ≤ (22112877817371/50000000000000 : ℝ)^1683 := by
    have hnat : (5349634737 : ℕ)^2195*50000000000000^1683 ≤ 22112877817371^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349634737 10000000000 22112877817371 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060356553/10000000000 : ℝ)^2195 ≤ (6370901062621/50000000000000 : ℝ)^1683 := by
    have hnat : (2060356553 : ℕ)^2195*50000000000000^1683 ≤ 6370901062621^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060356553 10000000000 6370901062621 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654825831/1250000000 : ℝ)^2195 ≤ (43032442224891/100000000000000 : ℝ)^1683 := by
    have hnat : (654825831 : ℕ)^2195*100000000000000^1683 ≤ 43032442224891^1683*1250000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654825831 1250000000 43032442224891 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349634737/10000000000 : ℝ), (-2060356553/10000000000 : ℝ), (654825831/1250000000 : ℝ)] ![(22112877817371/50000000000000 : ℝ), (6370901062621/50000000000000 : ℝ), (43032442224891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349634737/10000000000 : ℝ)|^2195 ≤ (22112877817371/50000000000000 : ℝ)^1683
        have hw : |(5349634737/10000000000 : ℝ)|=(5349634737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2060356553/10000000000 : ℝ)|^2195 ≤ (6370901062621/50000000000000 : ℝ)^1683
        have hw : |(-2060356553/10000000000 : ℝ)|=(2060356553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654825831/1250000000 : ℝ)|^2195 ≤ (43032442224891/100000000000000 : ℝ)^1683
        have hw : |(654825831/1250000000 : ℝ)|=(654825831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s3_2 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674817387/5000000000 : ℝ)*x 0 + (523860657/1000000000 : ℝ)*x 1 + (-2060356607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674817387/5000000000 : ℝ)^2195 ≤ (22112878016839/50000000000000 : ℝ)^1683 := by
    have hnat : (2674817387 : ℕ)^2195*50000000000000^1683 ≤ 22112878016839^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674817387 5000000000 22112878016839 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523860657/1000000000 : ℝ)^2195 ≤ (43032441389239/100000000000000 : ℝ)^1683 := by
    have hnat : (523860657 : ℕ)^2195*100000000000000^1683 ≤ 43032441389239^1683*1000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523860657 1000000000 43032441389239 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2060356607/10000000000 : ℝ)^2195 ≤ (12741802560787/100000000000000 : ℝ)^1683 := by
    have hnat : (2060356607 : ℕ)^2195*100000000000000^1683 ≤ 12741802560787^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060356607 10000000000 12741802560787 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674817387/5000000000 : ℝ), (523860657/1000000000 : ℝ), (-2060356607/10000000000 : ℝ)] ![(22112878016839/50000000000000 : ℝ), (43032441389239/100000000000000 : ℝ), (12741802560787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674817387/5000000000 : ℝ)|^2195 ≤ (22112878016839/50000000000000 : ℝ)^1683
        have hw : |(2674817387/5000000000 : ℝ)|=(2674817387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523860657/1000000000 : ℝ)|^2195 ≤ (43032441389239/100000000000000 : ℝ)^1683
        have hw : |(523860657/1000000000 : ℝ)|=(523860657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2060356607/10000000000 : ℝ)|^2195 ≤ (12741802560787/100000000000000 : ℝ)^1683
        have hw : |(-2060356607/10000000000 : ℝ)|=(2060356607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s3_3 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (860696203/2000000000 : ℝ)*x 0 + (2057074499/5000000000 : ℝ)*x 1 + (4500611007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860696203/2000000000 : ℝ)^2195 ≤ (16649111998541/50000000000000 : ℝ)^1683 := by
    have hnat : (860696203 : ℕ)^2195*50000000000000^1683 ≤ 16649111998541^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860696203 2000000000 16649111998541 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2057074499/5000000000 : ℝ)^2195 ≤ (15700258566313/50000000000000 : ℝ)^1683 := by
    have hnat : (2057074499 : ℕ)^2195*50000000000000^1683 ≤ 15700258566313^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057074499 5000000000 15700258566313 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500611007/10000000000 : ℝ)^2195 ≤ (7060251768851/20000000000000 : ℝ)^1683 := by
    have hnat : (4500611007 : ℕ)^2195*20000000000000^1683 ≤ 7060251768851^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500611007 10000000000 7060251768851 20000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860696203/2000000000 : ℝ), (2057074499/5000000000 : ℝ), (4500611007/10000000000 : ℝ)] ![(16649111998541/50000000000000 : ℝ), (15700258566313/50000000000000 : ℝ), (7060251768851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860696203/2000000000 : ℝ)|^2195 ≤ (16649111998541/50000000000000 : ℝ)^1683
        have hw : |(860696203/2000000000 : ℝ)|=(860696203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2057074499/5000000000 : ℝ)|^2195 ≤ (15700258566313/50000000000000 : ℝ)^1683
        have hw : |(2057074499/5000000000 : ℝ)|=(2057074499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500611007/10000000000 : ℝ)|^2195 ≤ (7060251768851/20000000000000 : ℝ)^1683
        have hw : |(4500611007/10000000000 : ℝ)|=(4500611007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s3_4 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1969281547/10000000000 : ℝ)*x 0 + (5239319681/10000000000 : ℝ)*x 1 + (5416466429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1969281547/10000000000 : ℝ)^2195 ≤ (12012214574609/100000000000000 : ℝ)^1683 := by
    have hnat : (1969281547 : ℕ)^2195*100000000000000^1683 ≤ 12012214574609^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969281547 10000000000 12012214574609 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239319681/10000000000 : ℝ)^2195 ≤ (10760020362177/25000000000000 : ℝ)^1683 := by
    have hnat : (5239319681 : ℕ)^2195*25000000000000^1683 ≤ 10760020362177^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239319681 10000000000 10760020362177 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416466429/10000000000 : ℝ)^2195 ≤ (44947703961481/100000000000000 : ℝ)^1683 := by
    have hnat : (5416466429 : ℕ)^2195*100000000000000^1683 ≤ 44947703961481^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416466429 10000000000 44947703961481 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1969281547/10000000000 : ℝ), (5239319681/10000000000 : ℝ), (5416466429/10000000000 : ℝ)] ![(12012214574609/100000000000000 : ℝ), (10760020362177/25000000000000 : ℝ), (44947703961481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1969281547/10000000000 : ℝ)|^2195 ≤ (12012214574609/100000000000000 : ℝ)^1683
        have hw : |(-1969281547/10000000000 : ℝ)|=(1969281547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239319681/10000000000 : ℝ)|^2195 ≤ (10760020362177/25000000000000 : ℝ)^1683
        have hw : |(5239319681/10000000000 : ℝ)|=(5239319681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416466429/10000000000 : ℝ)|^2195 ≤ (44947703961481/100000000000000 : ℝ)^1683
        have hw : |(5416466429/10000000000 : ℝ)|=(5416466429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s3_5 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1060641157/2000000000 : ℝ)*x 0 + (-941248429/5000000000 : ℝ)*x 1 + (541646639/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060641157/2000000000 : ℝ)^2195 ≤ (21862909160569/50000000000000 : ℝ)^1683 := by
    have hnat : (1060641157 : ℕ)^2195*50000000000000^1683 ≤ 21862909160569^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060641157 2000000000 21862909160569 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941248429/5000000000 : ℝ)^2195 ≤ (11326478123463/100000000000000 : ℝ)^1683 := by
    have hnat : (941248429 : ℕ)^2195*100000000000000^1683 ≤ 11326478123463^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941248429 5000000000 11326478123463 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541646639/1000000000 : ℝ)^2195 ≤ (44947703539389/100000000000000 : ℝ)^1683 := by
    have hnat : (541646639 : ℕ)^2195*100000000000000^1683 ≤ 44947703539389^1683*1000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541646639 1000000000 44947703539389 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060641157/2000000000 : ℝ), (-941248429/5000000000 : ℝ), (541646639/1000000000 : ℝ)] ![(21862909160569/50000000000000 : ℝ), (11326478123463/100000000000000 : ℝ), (44947703539389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060641157/2000000000 : ℝ)|^2195 ≤ (21862909160569/50000000000000 : ℝ)^1683
        have hw : |(1060641157/2000000000 : ℝ)|=(1060641157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-941248429/5000000000 : ℝ)|^2195 ≤ (11326478123463/100000000000000 : ℝ)^1683
        have hw : |(-941248429/5000000000 : ℝ)|=(941248429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541646639/1000000000 : ℝ)|^2195 ≤ (44947703539389/100000000000000 : ℝ)^1683
        have hw : |(541646639/1000000000 : ℝ)|=(541646639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s3_6 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (662900683/1250000000 : ℝ)*x 0 + (2708233367/5000000000 : ℝ)*x 1 + (-235312103/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662900683/1250000000 : ℝ)^2195 ≤ (8745162973853/20000000000000 : ℝ)^1683 := by
    have hnat : (662900683 : ℕ)^2195*20000000000000^1683 ≤ 8745162973853^1683*1250000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662900683 1250000000 8745162973853 20000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708233367/5000000000 : ℝ)^2195 ≤ (11236926815613/25000000000000 : ℝ)^1683 := by
    have hnat : (2708233367 : ℕ)^2195*25000000000000^1683 ≤ 11236926815613^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708233367 5000000000 11236926815613 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235312103/1250000000 : ℝ)^2195 ≤ (566323892833/5000000000000 : ℝ)^1683 := by
    have hnat : (235312103 : ℕ)^2195*5000000000000^1683 ≤ 566323892833^1683*1250000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235312103 1250000000 566323892833 5000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662900683/1250000000 : ℝ), (2708233367/5000000000 : ℝ), (-235312103/1250000000 : ℝ)] ![(8745162973853/20000000000000 : ℝ), (11236926815613/25000000000000 : ℝ), (566323892833/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662900683/1250000000 : ℝ)|^2195 ≤ (8745162973853/20000000000000 : ℝ)^1683
        have hw : |(662900683/1250000000 : ℝ)|=(662900683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708233367/5000000000 : ℝ)|^2195 ≤ (11236926815613/25000000000000 : ℝ)^1683
        have hw : |(2708233367/5000000000 : ℝ)|=(2708233367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-235312103/1250000000 : ℝ)|^2195 ≤ (566323892833/5000000000000 : ℝ)^1683
        have hw : |(-235312103/1250000000 : ℝ)|=(235312103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s3_7 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4303513863/10000000000 : ℝ)*x 0 + (449906867/1000000000 : ℝ)*x 1 + (411570057/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303513863/10000000000 : ℝ)^2195 ≤ (33298555479901/100000000000000 : ℝ)^1683 := by
    have hnat : (4303513863 : ℕ)^2195*100000000000000^1683 ≤ 33298555479901^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303513863 10000000000 33298555479901 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449906867/1000000000 : ℝ)^2195 ≤ (2205342612237/6250000000000 : ℝ)^1683 := by
    have hnat : (449906867 : ℕ)^2195*6250000000000^1683 ≤ 2205342612237^1683*1000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449906867 1000000000 2205342612237 6250000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411570057/1000000000 : ℝ)^2195 ≤ (31415962706079/100000000000000 : ℝ)^1683 := by
    have hnat : (411570057 : ℕ)^2195*100000000000000^1683 ≤ 31415962706079^1683*1000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411570057 1000000000 31415962706079 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303513863/10000000000 : ℝ), (449906867/1000000000 : ℝ), (411570057/1000000000 : ℝ)] ![(33298555479901/100000000000000 : ℝ), (2205342612237/6250000000000 : ℝ), (31415962706079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303513863/10000000000 : ℝ)|^2195 ≤ (33298555479901/100000000000000 : ℝ)^1683
        have hw : |(4303513863/10000000000 : ℝ)|=(4303513863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449906867/1000000000 : ℝ)|^2195 ≤ (2205342612237/6250000000000 : ℝ)^1683
        have hw : |(449906867/1000000000 : ℝ)|=(449906867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(411570057/1000000000 : ℝ)|^2195 ≤ (31415962706079/100000000000000 : ℝ)^1683
        have hw : |(411570057/1000000000 : ℝ)|=(411570057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1430_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15797/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2791/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7473/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15797/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15797/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15797/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15797/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15797/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15797/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10373/100000 : ℝ) ^ (4389/1024 : ℝ) ≤ (6053903074767091/100000000000000000000 : ℝ) := by
    have hpowers : (10373/100000 : ℝ)^4389 ≤ (6053903074767091/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10373 : ℕ)^4389*100000000000000000000^1024 ≤ 6053903074767091^1024*100000^4389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10373 100000 6053903074767091 100000000000000000000 4389 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10373/100000 : ℝ)) (X := (6053903074767091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15797/100000 : ℝ) ^ (4389/1024 : ℝ) ≤ (18363454295347803/50000000000000000000 : ℝ) := by
    have hpowers : (15797/100000 : ℝ)^4389 ≤ (18363454295347803/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15797 : ℕ)^4389*50000000000000000000^1024 ≤ 18363454295347803^1024*100000^4389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15797 100000 18363454295347803 50000000000000000000 4389 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15797/100000 : ℝ)) (X := (18363454295347803/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006053903074767091/50000000000000000000 : ℝ) ≤ (10000282474779477/10000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (50006053903074767091/50000000000000000000 : ℝ)^1024 ≤ (10000282474779477/10000000000000000 : ℝ)^4389 := by
      have hnat : (50006053903074767091 : ℕ)^1024*10000000000000000^4389 ≤ 10000282474779477^4389*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006053903074767091 50000000000000000000 10000282474779477 10000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000282474779477/10000000000000000 : ℝ)) (X := (50006053903074767091/50000000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042780811665462697/100000000000000000000 : ℝ) ≤ (500049897890869/500000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (100042780811665462697/100000000000000000000 : ℝ)^1024 ≤ (500049897890869/500000000000000 : ℝ)^4389 := by
      have hnat : (100042780811665462697 : ℕ)^1024*500000000000000^4389 ≤ 500049897890869^4389*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042780811665462697 100000000000000000000 500049897890869 500000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500049897890869/500000000000000 : ℝ)) (X := (100042780811665462697/100000000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018363454295347803/25000000000000000000 : ℝ) ≤ (10001713440855283/10000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (25018363454295347803/25000000000000000000 : ℝ)^1024 ≤ (10001713440855283/10000000000000000 : ℝ)^4389 := by
      have hnat : (25018363454295347803 : ℕ)^1024*10000000000000000^4389 ≤ 10001713440855283^4389*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018363454295347803 25000000000000000000 10001713440855283 10000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001713440855283/10000000000000000 : ℝ)) (X := (25018363454295347803/25000000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6053903074767091/100000000000000000000 : ℝ) ≤ ((5422668873209954761/5424000000000000000 : ℝ)+2*(715483037903/542400000000000 : ℝ)*(10373/100000 : ℝ))^(4389/1024 : ℝ) := by
    rw [show (5422668873209954761/5424000000000000000 : ℝ)+2*(715483037903/542400000000000 : ℝ)*(10373/100000 : ℝ)=(10000282474779477/10000000000000000 : ℝ) by norm_num, show 1+2*(6053903074767091/100000000000000000000 : ℝ)=(50006053903074767091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18363454295347803/50000000000000000000 : ℝ)+(6053903074767091/100000000000000000000 : ℝ) ≤ ((5422668873209954761/5424000000000000000 : ℝ)+(715483037903/542400000000000 : ℝ)*((15797/100000 : ℝ)+(10373/100000 : ℝ)))^(4389/1024 : ℝ) := by
    rw [show (5422668873209954761/5424000000000000000 : ℝ)+(715483037903/542400000000000 : ℝ)*((15797/100000 : ℝ)+(10373/100000 : ℝ))=(500049897890869/500000000000000 : ℝ) by norm_num, show 1+(18363454295347803/50000000000000000000 : ℝ)+(6053903074767091/100000000000000000000 : ℝ)=(100042780811665462697/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18363454295347803/50000000000000000000 : ℝ) ≤ ((5422668873209954761/5424000000000000000 : ℝ)+2*(715483037903/542400000000000 : ℝ)*(15797/100000 : ℝ))^(4389/1024 : ℝ) := by
    rw [show (5422668873209954761/5424000000000000000 : ℝ)+2*(715483037903/542400000000000 : ℝ)*(15797/100000 : ℝ)=(10001713440855283/10000000000000000 : ℝ) by norm_num, show 1+2*(18363454295347803/50000000000000000000 : ℝ)=(25018363454295347803/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5422668873209954761/5424000000000000000 : ℝ)*(X 1 0+X 2 0)+(715483037903/542400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (10373/100000 : ℝ)) (hi := (15797/100000 : ℝ)) (c := (5422668873209954761/5424000000000000000 : ℝ)) (alpha := (715483037903/542400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5422668873209954761/5424000000000000000 : ℝ)*(X 0 1+X 2 1)+(715483037903/542400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (10373/100000 : ℝ)) (hi := (15797/100000 : ℝ)) (c := (5422668873209954761/5424000000000000000 : ℝ)) (alpha := (715483037903/542400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5422668873209954761/5424000000000000000 : ℝ)*(X 0 2+X 1 2)+(715483037903/542400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (10373/100000 : ℝ)) (hi := (15797/100000 : ℝ)) (c := (5422668873209954761/5424000000000000000 : ℝ)) (alpha := (715483037903/542400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-98463329/500000000 : ℝ)*X 0 0+(1083436649/2000000000 : ℝ)*X 0 1+(5238606661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349634737/10000000000 : ℝ)*X 1 0+(-2060356553/10000000000 : ℝ)*X 1 1+(654825831/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674817387/5000000000 : ℝ)*X 2 0+(523860657/1000000000 : ℝ)*X 2 1+(-2060356607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((860696203/2000000000 : ℝ)*X 0 0+(2057074499/5000000000 : ℝ)*X 0 1+(4500611007/10000000000 : ℝ)*X 0 2+(860696203/2000000000 : ℝ)*X 1 0+(2057074499/5000000000 : ℝ)*X 1 1+(4500611007/10000000000 : ℝ)*X 1 2+(860696203/2000000000 : ℝ)*X 2 0+(2057074499/5000000000 : ℝ)*X 2 1+(4500611007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1969281547/10000000000 : ℝ)*X 0 0+(5239319681/10000000000 : ℝ)*X 0 1+(5416466429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060641157/2000000000 : ℝ)*X 1 0+(-941248429/5000000000 : ℝ)*X 1 1+(541646639/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662900683/1250000000 : ℝ)*X 2 0+(2708233367/5000000000 : ℝ)*X 2 1+(-235312103/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4303513863/10000000000 : ℝ)*X 0 0+(449906867/1000000000 : ℝ)*X 0 1+(411570057/1000000000 : ℝ)*X 0 2+(4303513863/10000000000 : ℝ)*X 1 0+(449906867/1000000000 : ℝ)*X 1 1+(411570057/1000000000 : ℝ)*X 1 2+(4303513863/10000000000 : ℝ)*X 2 0+(449906867/1000000000 : ℝ)*X 2 1+(411570057/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (465652170001947189110646151/45200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1812618219/100000000000000 : ℝ)*(base19) + (905434979/50000000000000 : ℝ)*(base23) + (60257981/20000000000000 : ℝ)*(upper3) + (21654889/100000000000000 : ℝ)*(upper4) + (54037459/25000000000000 : ℝ)*(upper5) + (4093753319703991/100000000000000 : ℝ)*(major0) + (4093753319703991/100000000000000 : ℝ)*(major1) + (4093753319703991/100000000000000 : ℝ)*(major2) + (699983941445777/12500000000000 : ℝ)*(sp0) + (1119980178915879/20000000000000 : ℝ)*(sp1) + (699987612040957/12500000000000 : ℝ)*(sp2) + (323448658136159/12500000000000 : ℝ)*(sp3) + (31175631397/100000000000000 : ℝ)*(sp4) + (14323719781/100000000000000 : ℝ)*(sp7) + (1293801794404527/50000000000000 : ℝ)*(f.failure) + (2799951353598807/50000000000000 : ℝ)*(f.sum) + (54964822334407/27120000000000000000000000000 : ℝ)*base66 + (317756921099106283/180800000000000000000000000000000 : ℝ)*base68 + (479616703627106283/180800000000000000000000000000000 : ℝ)*base70 + (653204778755106283/180800000000000000000000000000000 : ℝ)*base72 + (41065351721047/27120000000000000000000000000 : ℝ)*base74 + (1295517134096093717/180800000000000000000000000000000 : ℝ)*base75 + (822987844478306283/180800000000000000000000000000000 : ℝ)*base78 + (5338107296553506283/180800000000000000000000000000000 : ℝ)*base80 + (44696669291033/27120000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (12433817/1000000000000000000000 : ℝ)*base89 + (12433817/1000000000000000000000 : ℝ)*base91 + (12433817/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (184890241105870169391846909/22600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82705493/25000000000000 : ℝ)*(base19) + (34207579/20000000000000 : ℝ)*(base23) + (6251587/12500000000000 : ℝ)*(upper3) + (83041989/100000000000000 : ℝ)*(lower4) + (48329347/100000000000000 : ℝ)*(upper5) + (1031686380975531/25000000000000 : ℝ)*(major0) + (1031686380975531/25000000000000 : ℝ)*(major1) + (1031686380975531/25000000000000 : ℝ)*(major2) + (4475719801/100000000000000 : ℝ)*(sp1) + (7367563169/100000000000000 : ℝ)*(sp2) + (5645033280523011/100000000000000 : ℝ)*(sp4) + (5645028473981239/100000000000000 : ℝ)*(sp5) + (1411256435480487/25000000000000 : ℝ)*(sp6) + (1018928708821/39062500000 : ℝ)*(sp7) + (1018928708821/39062500000 : ℝ)*(f.failure) + (5645033280523011/100000000000000 : ℝ)*(f.sum) + (6287023366549/2260000000000000000000000000 : ℝ)*base66 + (60558988475572303/45200000000000000000000000000000 : ℝ)*base68 + (612154318818827697/45200000000000000000000000000000 : ℝ)*base69 + (55930288848772303/45200000000000000000000000000000 : ℝ)*base72 + (8870305794269/2260000000000000000000000000 : ℝ)*base74 + (341207595256027697/45200000000000000000000000000000 : ℝ)*base75 + (40591249936027697/45200000000000000000000000000000 : ℝ)*base77 + (71686327595227697/45200000000000000000000000000000 : ℝ)*base79 + (1480728612931/2260000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7741/781250000000000000 : ℝ)*base89 + (7741/781250000000000000 : ℝ)*base91 + (7741/781250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1430_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15797/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7473/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1430_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1430_s4_0 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-985082659/5000000000 : ℝ)*x 0 + (5409533677/10000000000 : ℝ)*x 1 + (327854007/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (985082659/5000000000 : ℝ)^2195 ≤ (12019245865533/100000000000000 : ℝ)^1683 := by
    have hnat : (985082659 : ℕ)^2195*100000000000000^1683 ≤ 12019245865533^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985082659 5000000000 12019245865533 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409533677/10000000000 : ℝ)^2195 ≤ (22436343199993/50000000000000 : ℝ)^1683 := by
    have hnat : (5409533677 : ℕ)^2195*50000000000000^1683 ≤ 22436343199993^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409533677 10000000000 22436343199993 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327854007/625000000 : ℝ)^2195 ≤ (10777016930583/25000000000000 : ℝ)^1683 := by
    have hnat : (327854007 : ℕ)^2195*25000000000000^1683 ≤ 10777016930583^1683*625000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327854007 625000000 10777016930583 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-985082659/5000000000 : ℝ), (5409533677/10000000000 : ℝ), (327854007/625000000 : ℝ)] ![(12019245865533/100000000000000 : ℝ), (22436343199993/50000000000000 : ℝ), (10777016930583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-985082659/5000000000 : ℝ)|^2195 ≤ (12019245865533/100000000000000 : ℝ)^1683
        have hw : |(-985082659/5000000000 : ℝ)|=(985082659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409533677/10000000000 : ℝ)|^2195 ≤ (22436343199993/50000000000000 : ℝ)^1683
        have hw : |(5409533677/10000000000 : ℝ)|=(5409533677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327854007/625000000 : ℝ)|^2195 ≤ (10777016930583/25000000000000 : ℝ)^1683
        have hw : |(327854007/625000000 : ℝ)|=(327854007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s4_1 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347659313/10000000000 : ℝ)*x 0 + (-256702189/1250000000 : ℝ)*x 1 + (2622832059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347659313/10000000000 : ℝ)^2195 ≤ (44204457701091/100000000000000 : ℝ)^1683 := by
    have hnat : (5347659313 : ℕ)^2195*100000000000000^1683 ≤ 44204457701091^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347659313 10000000000 44204457701091 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256702189/1250000000 : ℝ)^2195 ≤ (3171868625939/25000000000000 : ℝ)^1683 := by
    have hnat : (256702189 : ℕ)^2195*25000000000000^1683 ≤ 3171868625939^1683*1250000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256702189 1250000000 3171868625939 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622832059/5000000000 : ℝ)^2195 ≤ (43108067786639/100000000000000 : ℝ)^1683 := by
    have hnat : (2622832059 : ℕ)^2195*100000000000000^1683 ≤ 43108067786639^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622832059 5000000000 43108067786639 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347659313/10000000000 : ℝ), (-256702189/1250000000 : ℝ), (2622832059/5000000000 : ℝ)] ![(44204457701091/100000000000000 : ℝ), (3171868625939/25000000000000 : ℝ), (43108067786639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347659313/10000000000 : ℝ)|^2195 ≤ (44204457701091/100000000000000 : ℝ)^1683
        have hw : |(5347659313/10000000000 : ℝ)|=(5347659313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256702189/1250000000 : ℝ)|^2195 ≤ (3171868625939/25000000000000 : ℝ)^1683
        have hw : |(-256702189/1250000000 : ℝ)|=(256702189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622832059/5000000000 : ℝ)|^2195 ≤ (43108067786639/100000000000000 : ℝ)^1683
        have hw : |(2622832059/5000000000 : ℝ)|=(2622832059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s4_2 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (213906373/400000000 : ℝ)*x 0 + (327854007/625000000 : ℝ)*x 1 + (-2053617503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213906373/400000000 : ℝ)^2195 ≤ (22102228915231/50000000000000 : ℝ)^1683 := by
    have hnat : (213906373 : ℕ)^2195*50000000000000^1683 ≤ 22102228915231^1683*400000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213906373 400000000 22102228915231 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327854007/625000000 : ℝ)^2195 ≤ (10777016930583/25000000000000 : ℝ)^1683 := by
    have hnat : (327854007 : ℕ)^2195*25000000000000^1683 ≤ 10777016930583^1683*625000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327854007 625000000 10777016930583 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2053617503/10000000000 : ℝ)^2195 ≤ (6343737215619/50000000000000 : ℝ)^1683 := by
    have hnat : (2053617503 : ℕ)^2195*50000000000000^1683 ≤ 6343737215619^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053617503 10000000000 6343737215619 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213906373/400000000 : ℝ), (327854007/625000000 : ℝ), (-2053617503/10000000000 : ℝ)] ![(22102228915231/50000000000000 : ℝ), (10777016930583/25000000000000 : ℝ), (6343737215619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213906373/400000000 : ℝ)|^2195 ≤ (22102228915231/50000000000000 : ℝ)^1683
        have hw : |(213906373/400000000 : ℝ)|=(213906373/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327854007/625000000 : ℝ)|^2195 ≤ (10777016930583/25000000000000 : ℝ)^1683
        have hw : |(327854007/625000000 : ℝ)|=(327854007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2053617503/10000000000 : ℝ)|^2195 ≤ (6343737215619/50000000000000 : ℝ)^1683
        have hw : |(-2053617503/10000000000 : ℝ)|=(2053617503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s4_3 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2152015023/5000000000 : ℝ)*x 0 + (412999657/1000000000 : ℝ)*x 1 + (1121157787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152015023/5000000000 : ℝ)^2195 ≤ (33303764598157/100000000000000 : ℝ)^1683 := by
    have hnat : (2152015023 : ℕ)^2195*100000000000000^1683 ≤ 33303764598157^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152015023 5000000000 33303764598157 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412999657/1000000000 : ℝ)^2195 ≤ (246549685017/781250000000 : ℝ)^1683 := by
    have hnat : (412999657 : ℕ)^2195*781250000000^1683 ≤ 246549685017^1683*1000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412999657 1000000000 246549685017 781250000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121157787/2500000000 : ℝ)^2195 ≤ (17568937848819/50000000000000 : ℝ)^1683 := by
    have hnat : (1121157787 : ℕ)^2195*50000000000000^1683 ≤ 17568937848819^1683*2500000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121157787 2500000000 17568937848819 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152015023/5000000000 : ℝ), (412999657/1000000000 : ℝ), (1121157787/2500000000 : ℝ)] ![(33303764598157/100000000000000 : ℝ), (246549685017/781250000000 : ℝ), (17568937848819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152015023/5000000000 : ℝ)|^2195 ≤ (33303764598157/100000000000000 : ℝ)^1683
        have hw : |(2152015023/5000000000 : ℝ)|=(2152015023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(412999657/1000000000 : ℝ)|^2195 ≤ (246549685017/781250000000 : ℝ)^1683
        have hw : |(412999657/1000000000 : ℝ)|=(412999657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121157787/2500000000 : ℝ)|^2195 ≤ (17568937848819/50000000000000 : ℝ)^1683
        have hw : |(1121157787/2500000000 : ℝ)|=(1121157787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s4_4 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1970177211/10000000000 : ℝ)*x 0 + (1049252957/2000000000 : ℝ)*x 1 + (676116229/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1970177211/10000000000 : ℝ)^2195 ≤ (1502417561613/12500000000000 : ℝ)^1683 := by
    have hnat : (1970177211 : ℕ)^2195*12500000000000^1683 ≤ 1502417561613^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970177211 10000000000 1502417561613 12500000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049252957/2000000000 : ℝ)^2195 ≤ (43114505769611/100000000000000 : ℝ)^1683 := by
    have hnat : (1049252957 : ℕ)^2195*100000000000000^1683 ≤ 43114505769611^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049252957 2000000000 43114505769611 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676116229/1250000000 : ℝ)^2195 ≤ (44866153729533/100000000000000 : ℝ)^1683 := by
    have hnat : (676116229 : ℕ)^2195*100000000000000^1683 ≤ 44866153729533^1683*1250000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676116229 1250000000 44866153729533 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1970177211/10000000000 : ℝ), (1049252957/2000000000 : ℝ), (676116229/1250000000 : ℝ)] ![(1502417561613/12500000000000 : ℝ), (43114505769611/100000000000000 : ℝ), (44866153729533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1970177211/10000000000 : ℝ)|^2195 ≤ (1502417561613/12500000000000 : ℝ)^1683
        have hw : |(-1970177211/10000000000 : ℝ)|=(1970177211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049252957/2000000000 : ℝ)|^2195 ≤ (43114505769611/100000000000000 : ℝ)^1683
        have hw : |(1049252957/2000000000 : ℝ)|=(1049252957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676116229/1250000000 : ℝ)|^2195 ≤ (44866153729533/100000000000000 : ℝ)^1683
        have hw : |(676116229/1250000000 : ℝ)|=(676116229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s4_5 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305053667/10000000000 : ℝ)*x 0 + (-7561407/40000000 : ℝ)*x 1 + (67611623/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305053667/10000000000 : ℝ)^2195 ≤ (43745690574971/100000000000000 : ℝ)^1683 := by
    have hnat : (5305053667 : ℕ)^2195*100000000000000^1683 ≤ 43745690574971^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305053667 10000000000 43745690574971 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7561407/40000000 : ℝ)^2195 ≤ (11388155592813/100000000000000 : ℝ)^1683 := by
    have hnat : (7561407 : ℕ)^2195*100000000000000^1683 ≤ 11388155592813^1683*40000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7561407 40000000 11388155592813 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67611623/125000000 : ℝ)^2195 ≤ (44866153816079/100000000000000 : ℝ)^1683 := by
    have hnat : (67611623 : ℕ)^2195*100000000000000^1683 ≤ 44866153816079^1683*125000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67611623 125000000 44866153816079 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305053667/10000000000 : ℝ), (-7561407/40000000 : ℝ), (67611623/125000000 : ℝ)] ![(43745690574971/100000000000000 : ℝ), (11388155592813/100000000000000 : ℝ), (44866153816079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305053667/10000000000 : ℝ)|^2195 ≤ (43745690574971/100000000000000 : ℝ)^1683
        have hw : |(5305053667/10000000000 : ℝ)|=(5305053667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7561407/40000000 : ℝ)|^2195 ≤ (11388155592813/100000000000000 : ℝ)^1683
        have hw : |(-7561407/40000000 : ℝ)|=(7561407/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67611623/125000000 : ℝ)|^2195 ≤ (44866153816079/100000000000000 : ℝ)^1683
        have hw : |(67611623/125000000 : ℝ)|=(67611623/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s4_6 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652526823/5000000000 : ℝ)*x 0 + (1081785969/2000000000 : ℝ)*x 1 + (-1890351771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652526823/5000000000 : ℝ)^2195 ≤ (43745690349123/100000000000000 : ℝ)^1683 := by
    have hnat : (2652526823 : ℕ)^2195*100000000000000^1683 ≤ 43745690349123^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652526823 5000000000 43745690349123 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081785969/2000000000 : ℝ)^2195 ≤ (4486615387017/10000000000000 : ℝ)^1683 := by
    have hnat : (1081785969 : ℕ)^2195*10000000000000^1683 ≤ 4486615387017^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081785969 2000000000 4486615387017 10000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1890351771/10000000000 : ℝ)^2195 ≤ (2847038939453/25000000000000 : ℝ)^1683 := by
    have hnat : (1890351771 : ℕ)^2195*25000000000000^1683 ≤ 2847038939453^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890351771 10000000000 2847038939453 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652526823/5000000000 : ℝ), (1081785969/2000000000 : ℝ), (-1890351771/10000000000 : ℝ)] ![(43745690349123/100000000000000 : ℝ), (4486615387017/10000000000000 : ℝ), (2847038939453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652526823/5000000000 : ℝ)|^2195 ≤ (43745690349123/100000000000000 : ℝ)^1683
        have hw : |(2652526823/5000000000 : ℝ)|=(2652526823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081785969/2000000000 : ℝ)|^2195 ≤ (4486615387017/10000000000000 : ℝ)^1683
        have hw : |(1081785969/2000000000 : ℝ)|=(1081785969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1890351771/10000000000 : ℝ)|^2195 ≤ (2847038939453/25000000000000 : ℝ)^1683
        have hw : |(-1890351771/10000000000 : ℝ)|=(1890351771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s4_7 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2152027861/5000000000 : ℝ)*x 0 + (1120832819/2500000000 : ℝ)*x 1 + (4131303309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152027861/5000000000 : ℝ)^2195 ≤ (16652011857667/50000000000000 : ℝ)^1683 := by
    have hnat : (2152027861 : ℕ)^2195*50000000000000^1683 ≤ 16652011857667^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152027861 5000000000 16652011857667 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120832819/2500000000 : ℝ)^2195 ≤ (35124593173269/100000000000000 : ℝ)^1683 := by
    have hnat : (1120832819 : ℕ)^2195*100000000000000^1683 ≤ 35124593173269^1683*2500000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120832819 2500000000 35124593173269 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4131303309/10000000000 : ℝ)^2195 ≤ (15785691548767/50000000000000 : ℝ)^1683 := by
    have hnat : (4131303309 : ℕ)^2195*50000000000000^1683 ≤ 15785691548767^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131303309 10000000000 15785691548767 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152027861/5000000000 : ℝ), (1120832819/2500000000 : ℝ), (4131303309/10000000000 : ℝ)] ![(16652011857667/50000000000000 : ℝ), (35124593173269/100000000000000 : ℝ), (15785691548767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152027861/5000000000 : ℝ)|^2195 ≤ (16652011857667/50000000000000 : ℝ)^1683
        have hw : |(2152027861/5000000000 : ℝ)|=(2152027861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120832819/2500000000 : ℝ)|^2195 ≤ (35124593173269/100000000000000 : ℝ)^1683
        have hw : |(1120832819/2500000000 : ℝ)|=(1120832819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4131303309/10000000000 : ℝ)|^2195 ≤ (15785691548767/50000000000000 : ℝ)^1683
        have hw : |(4131303309/10000000000 : ℝ)|=(4131303309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1430_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7473/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2263/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7393/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7473/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2791/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7473/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2791/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7473/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2791/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7473/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2791/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7473/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2791/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7473/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2791/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2791/25000 : ℝ) ^ (4389/1024 : ℝ) ≤ (1659049394076643/20000000000000000000 : ℝ) := by
    have hpowers : (2791/25000 : ℝ)^4389 ≤ (1659049394076643/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2791 : ℕ)^4389*20000000000000000000^1024 ≤ 1659049394076643^1024*25000^4389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2791 25000 1659049394076643 20000000000000000000 4389 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2791/25000 : ℝ)) (X := (1659049394076643/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7473/50000 : ℝ) ^ (4389/1024 : ℝ) ≤ (28967060204507659/100000000000000000000 : ℝ) := by
    have hpowers : (7473/50000 : ℝ)^4389 ≤ (28967060204507659/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7473 : ℕ)^4389*100000000000000000000^1024 ≤ 28967060204507659^1024*50000^4389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7473 50000 28967060204507659 100000000000000000000 4389 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7473/50000 : ℝ)) (X := (28967060204507659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001659049394076643/10000000000000000000 : ℝ) ≤ (10000387049110103/10000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (10001659049394076643/10000000000000000000 : ℝ)^1024 ≤ (10000387049110103/10000000000000000 : ℝ)^4389 := by
      have hnat : (10001659049394076643 : ℕ)^1024*10000000000000000^4389 ≤ 10000387049110103^4389*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001659049394076643 10000000000000000000 10000387049110103 10000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000387049110103/10000000000000000 : ℝ)) (X := (10001659049394076643/10000000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018631153587445437/50000000000000000000 : ℝ) ≤ (1000086924477867/1000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (50018631153587445437/50000000000000000000 : ℝ)^1024 ≤ (1000086924477867/1000000000000000 : ℝ)^4389 := by
      have hnat : (50018631153587445437 : ℕ)^1024*1000000000000000^4389 ≤ 1000086924477867^4389*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018631153587445437 50000000000000000000 1000086924477867 1000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000086924477867/1000000000000000 : ℝ)) (X := (50018631153587445437/50000000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028967060204507659/50000000000000000000 : ℝ) ≤ (10001351440447237/10000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (50028967060204507659/50000000000000000000 : ℝ)^1024 ≤ (10001351440447237/10000000000000000 : ℝ)^4389 := by
      have hnat : (50028967060204507659 : ℕ)^1024*10000000000000000^4389 ≤ 10001351440447237^4389*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028967060204507659 50000000000000000000 10001351440447237 10000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001351440447237/10000000000000000 : ℝ)) (X := (50028967060204507659/50000000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1659049394076643/20000000000000000000 : ℝ) ≤ ((3781069735484664557/3782000000000000000 : ℝ)+2*(482195668567/378200000000000 : ℝ)*(2791/25000 : ℝ))^(4389/1024 : ℝ) := by
    rw [show (3781069735484664557/3782000000000000000 : ℝ)+2*(482195668567/378200000000000 : ℝ)*(2791/25000 : ℝ)=(10000387049110103/10000000000000000 : ℝ) by norm_num, show 1+2*(1659049394076643/20000000000000000000 : ℝ)=(10001659049394076643/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28967060204507659/100000000000000000000 : ℝ)+(1659049394076643/20000000000000000000 : ℝ) ≤ ((3781069735484664557/3782000000000000000 : ℝ)+(482195668567/378200000000000 : ℝ)*((7473/50000 : ℝ)+(2791/25000 : ℝ)))^(4389/1024 : ℝ) := by
    rw [show (3781069735484664557/3782000000000000000 : ℝ)+(482195668567/378200000000000 : ℝ)*((7473/50000 : ℝ)+(2791/25000 : ℝ))=(1000086924477867/1000000000000000 : ℝ) by norm_num, show 1+(28967060204507659/100000000000000000000 : ℝ)+(1659049394076643/20000000000000000000 : ℝ)=(50018631153587445437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28967060204507659/100000000000000000000 : ℝ) ≤ ((3781069735484664557/3782000000000000000 : ℝ)+2*(482195668567/378200000000000 : ℝ)*(7473/50000 : ℝ))^(4389/1024 : ℝ) := by
    rw [show (3781069735484664557/3782000000000000000 : ℝ)+2*(482195668567/378200000000000 : ℝ)*(7473/50000 : ℝ)=(10001351440447237/10000000000000000 : ℝ) by norm_num, show 1+2*(28967060204507659/100000000000000000000 : ℝ)=(50028967060204507659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3781069735484664557/3782000000000000000 : ℝ)*(X 1 0+X 2 0)+(482195668567/378200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (2791/25000 : ℝ)) (hi := (7473/50000 : ℝ)) (c := (3781069735484664557/3782000000000000000 : ℝ)) (alpha := (482195668567/378200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3781069735484664557/3782000000000000000 : ℝ)*(X 0 1+X 2 1)+(482195668567/378200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (2791/25000 : ℝ)) (hi := (7473/50000 : ℝ)) (c := (3781069735484664557/3782000000000000000 : ℝ)) (alpha := (482195668567/378200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3781069735484664557/3782000000000000000 : ℝ)*(X 0 2+X 1 2)+(482195668567/378200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (2791/25000 : ℝ)) (hi := (7473/50000 : ℝ)) (c := (3781069735484664557/3782000000000000000 : ℝ)) (alpha := (482195668567/378200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-985082659/5000000000 : ℝ)*X 0 0+(5409533677/10000000000 : ℝ)*X 0 1+(327854007/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347659313/10000000000 : ℝ)*X 1 0+(-256702189/1250000000 : ℝ)*X 1 1+(2622832059/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213906373/400000000 : ℝ)*X 2 0+(327854007/625000000 : ℝ)*X 2 1+(-2053617503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152015023/5000000000 : ℝ)*X 0 0+(412999657/1000000000 : ℝ)*X 0 1+(1121157787/2500000000 : ℝ)*X 0 2+(2152015023/5000000000 : ℝ)*X 1 0+(412999657/1000000000 : ℝ)*X 1 1+(1121157787/2500000000 : ℝ)*X 1 2+(2152015023/5000000000 : ℝ)*X 2 0+(412999657/1000000000 : ℝ)*X 2 1+(1121157787/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1970177211/10000000000 : ℝ)*X 0 0+(1049252957/2000000000 : ℝ)*X 0 1+(676116229/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305053667/10000000000 : ℝ)*X 1 0+(-7561407/40000000 : ℝ)*X 1 1+(67611623/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652526823/5000000000 : ℝ)*X 2 0+(1081785969/2000000000 : ℝ)*X 2 1+(-1890351771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2152027861/5000000000 : ℝ)*X 0 0+(1120832819/2500000000 : ℝ)*X 0 1+(4131303309/10000000000 : ℝ)*X 0 2+(2152027861/5000000000 : ℝ)*X 1 0+(1120832819/2500000000 : ℝ)*X 1 1+(4131303309/10000000000 : ℝ)*X 1 2+(2152027861/5000000000 : ℝ)*X 2 0+(1120832819/2500000000 : ℝ)*X 2 1+(4131303309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (700237994458904432497476933/94550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1313571541/100000000000000 : ℝ)*(base19) + (604971143/50000000000000 : ℝ)*(base23) + (62740357/100000000000000 : ℝ)*(lower2) + (36608787/20000000000000 : ℝ)*(upper3) + (110483867/100000000000000 : ℝ)*(upper5) + (2230575018364159/50000000000000 : ℝ)*(major0) + (2230575018364159/50000000000000 : ℝ)*(major1) + (2230575018364159/50000000000000 : ℝ)*(major2) + (244097708139129/4000000000000 : ℝ)*(sp0) + (6102468654269253/100000000000000 : ℝ)*(sp1) + (6102468757898507/100000000000000 : ℝ)*(sp2) + (1409908038039029/50000000000000 : ℝ)*(sp3) + (3408045321/12500000000000 : ℝ)*(sp4) + (13782670863/100000000000000 : ℝ)*(sp7) + (1409914929374461/50000000000000 : ℝ)*(f.failure) + (6102469967840793/100000000000000 : ℝ)*(f.sum) + (4165413724173/9455000000000000000000000000 : ℝ)*base65 + (1207819808925642563/189100000000000000000000000000000 : ℝ)*base67 + (2121002132182242563/189100000000000000000000000000000 : ℝ)*base69 + (3120748130466642563/189100000000000000000000000000000 : ℝ)*base71 + (14214250543193/9455000000000000000000000000 : ℝ)*base73 + (1932379784032442563/189100000000000000000000000000000 : ℝ)*base75 + (3055106871254042563/189100000000000000000000000000000 : ℝ)*base77 + (2046661815536742563/189100000000000000000000000000000 : ℝ)*base79 + (7655679924497/9455000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (979931/1000000000000000000000 : ℝ)*base89 + (979931/1000000000000000000000 : ℝ)*base91 + (979931/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (265869828759606549450821187/47275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19487971/2000000000000 : ℝ)*(base19) + (128069919/12500000000000 : ℝ)*(base23) + (126876351/100000000000000 : ℝ)*(upper3) + (16768253/50000000000000 : ℝ)*(lower4) + (47606999/50000000000000 : ℝ)*(upper5) + (2247070946371803/50000000000000 : ℝ)*(major0) + (2247070946371803/50000000000000 : ℝ)*(major1) + (2247070946371803/50000000000000 : ℝ)*(major2) + (2491298653/12500000000000 : ℝ)*(sp1) + (5333721929/25000000000000 : ℝ)*(sp2) + (6147600053583721/100000000000000 : ℝ)*(sp4) + (6147579148795947/100000000000000 : ℝ)*(sp5) + (6147577694136653/100000000000000 : ℝ)*(sp6) + (1420341772220087/50000000000000 : ℝ)*(sp7) + (1420341772220087/50000000000000 : ℝ)*(f.failure) + (6147600053583721/100000000000000 : ℝ)*(f.sum) + (26980875351083/4727500000000000000000000000 : ℝ)*base65 + (1639968398419396271/189100000000000000000000000000000 : ℝ)*base67 + (130807887175496271/189100000000000000000000000000000 : ℝ)*base69 + (3045953489661396271/189100000000000000000000000000000 : ℝ)*base71 + (38629138933171/9455000000000000000000000000 : ℝ)*base73 + (1927272938188503729/189100000000000000000000000000000 : ℝ)*base76 + (2401177749030696271/189100000000000000000000000000000 : ℝ)*base77 + (1496367372732196271/189100000000000000000000000000000 : ℝ)*base79 + (1256413706153/1181875000000000000000000000 : ℝ)*base82 + (15589423/1000000000000000000000 : ℝ)*base90 + (15589423/1000000000000000000000 : ℝ)*base92 + (15589423/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1430_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7473/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1430_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1430_s5_0 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1970298857/10000000000 : ℝ)*x 0 + (2704173513/5000000000 : ℝ)*x 1 + (5246762709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1970298857/10000000000 : ℝ)^2195 ≤ (12020308386613/100000000000000 : ℝ)^1683 := by
    have hnat : (1970298857 : ℕ)^2195*100000000000000^1683 ≤ 12020308386613^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970298857 10000000000 12020308386613 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704173513/5000000000 : ℝ)^2195 ≤ (44859848878973/100000000000000 : ℝ)^1683 := by
    have hnat : (2704173513 : ℕ)^2195*100000000000000^1683 ≤ 44859848878973^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704173513 5000000000 44859848878973 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246762709/10000000000 : ℝ)^2195 ≤ (21559921358637/50000000000000 : ℝ)^1683 := by
    have hnat : (5246762709 : ℕ)^2195*50000000000000^1683 ≤ 21559921358637^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246762709 10000000000 21559921358637 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1970298857/10000000000 : ℝ), (2704173513/5000000000 : ℝ), (5246762709/10000000000 : ℝ)] ![(12020308386613/100000000000000 : ℝ), (44859848878973/100000000000000 : ℝ), (21559921358637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1970298857/10000000000 : ℝ)|^2195 ≤ (12020308386613/100000000000000 : ℝ)^1683
        have hw : |(-1970298857/10000000000 : ℝ)|=(1970298857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704173513/5000000000 : ℝ)|^2195 ≤ (44859848878973/100000000000000 : ℝ)^1683
        have hw : |(2704173513/5000000000 : ℝ)|=(2704173513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246762709/10000000000 : ℝ)|^2195 ≤ (21559921358637/50000000000000 : ℝ)^1683
        have hw : |(5246762709/10000000000 : ℝ)|=(5246762709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s5_1 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673676259/5000000000 : ℝ)*x 0 + (-2052566331/10000000000 : ℝ)*x 1 + (1311690721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673676259/5000000000 : ℝ)^2195 ≤ (8840230044211/20000000000000 : ℝ)^1683 := by
    have hnat : (2673676259 : ℕ)^2195*20000000000000^1683 ≤ 8840230044211^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673676259 5000000000 8840230044211 20000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2052566331/10000000000 : ℝ)^2195 ≤ (6339502580443/50000000000000 : ℝ)^1683 := by
    have hnat : (2052566331 : ℕ)^2195*50000000000000^1683 ≤ 6339502580443^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052566331 10000000000 6339502580443 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311690721/2500000000 : ℝ)^2195 ≤ (43119844593021/100000000000000 : ℝ)^1683 := by
    have hnat : (1311690721 : ℕ)^2195*100000000000000^1683 ≤ 43119844593021^1683*2500000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311690721 2500000000 43119844593021 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673676259/5000000000 : ℝ), (-2052566331/10000000000 : ℝ), (1311690721/2500000000 : ℝ)] ![(8840230044211/20000000000000 : ℝ), (6339502580443/50000000000000 : ℝ), (43119844593021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673676259/5000000000 : ℝ)|^2195 ≤ (8840230044211/20000000000000 : ℝ)^1683
        have hw : |(2673676259/5000000000 : ℝ)|=(2673676259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2052566331/10000000000 : ℝ)|^2195 ≤ (6339502580443/50000000000000 : ℝ)^1683
        have hw : |(-2052566331/10000000000 : ℝ)|=(2052566331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311690721/2500000000 : ℝ)|^2195 ≤ (43119844593021/100000000000000 : ℝ)^1683
        have hw : |(1311690721/2500000000 : ℝ)|=(1311690721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s5_2 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347352733/10000000000 : ℝ)*x 0 + (5246762709/10000000000 : ℝ)*x 1 + (-1026283139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347352733/10000000000 : ℝ)^2195 ≤ (2762572033681/6250000000000 : ℝ)^1683 := by
    have hnat : (5347352733 : ℕ)^2195*6250000000000^1683 ≤ 2762572033681^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347352733 10000000000 2762572033681 6250000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246762709/10000000000 : ℝ)^2195 ≤ (21559921358637/50000000000000 : ℝ)^1683 := by
    have hnat : (5246762709 : ℕ)^2195*50000000000000^1683 ≤ 21559921358637^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246762709 10000000000 21559921358637 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026283139/5000000000 : ℝ)^2195 ≤ (126790047339/1000000000000 : ℝ)^1683 := by
    have hnat : (1026283139 : ℕ)^2195*1000000000000^1683 ≤ 126790047339^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026283139 5000000000 126790047339 1000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347352733/10000000000 : ℝ), (5246762709/10000000000 : ℝ), (-1026283139/5000000000 : ℝ)] ![(2762572033681/6250000000000 : ℝ), (21559921358637/50000000000000 : ℝ), (126790047339/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347352733/10000000000 : ℝ)|^2195 ≤ (2762572033681/6250000000000 : ℝ)^1683
        have hw : |(5347352733/10000000000 : ℝ)|=(5347352733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246762709/10000000000 : ℝ)|^2195 ≤ (21559921358637/50000000000000 : ℝ)^1683
        have hw : |(5246762709/10000000000 : ℝ)|=(5246762709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1026283139/5000000000 : ℝ)|^2195 ≤ (126790047339/1000000000000 : ℝ)^1683
        have hw : |(-1026283139/5000000000 : ℝ)|=(1026283139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s5_3 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (538013919/1250000000 : ℝ)*x 0 + (516557459/1250000000 : ℝ)*x 1 + (896429657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538013919/1250000000 : ℝ)^2195 ≤ (16652292562021/50000000000000 : ℝ)^1683 := by
    have hnat : (538013919 : ℕ)^2195*50000000000000^1683 ≤ 16652292562021^1683*1250000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538013919 1250000000 16652292562021 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516557459/1250000000 : ℝ)^2195 ≤ (31582908858591/100000000000000 : ℝ)^1683 := by
    have hnat : (516557459 : ℕ)^2195*100000000000000^1683 ≤ 31582908858591^1683*1250000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516557459 1250000000 31582908858591 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896429657/2000000000 : ℝ)^2195 ≤ (1755625299803/5000000000000 : ℝ)^1683 := by
    have hnat : (896429657 : ℕ)^2195*5000000000000^1683 ≤ 1755625299803^1683*2000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896429657 2000000000 1755625299803 5000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538013919/1250000000 : ℝ), (516557459/1250000000 : ℝ), (896429657/2000000000 : ℝ)] ![(16652292562021/50000000000000 : ℝ), (31582908858591/100000000000000 : ℝ), (1755625299803/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538013919/1250000000 : ℝ)|^2195 ≤ (16652292562021/50000000000000 : ℝ)^1683
        have hw : |(538013919/1250000000 : ℝ)|=(538013919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(516557459/1250000000 : ℝ)|^2195 ≤ (31582908858591/100000000000000 : ℝ)^1683
        have hw : |(516557459/1250000000 : ℝ)|=(516557459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(896429657/2000000000 : ℝ)|^2195 ≤ (1755625299803/5000000000000 : ℝ)^1683
        have hw : |(896429657/2000000000 : ℝ)|=(896429657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s5_4 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-492577659/2500000000 : ℝ)*x 0 + (655918299/1250000000 : ℝ)*x 1 + (5407760021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (492577659/2500000000 : ℝ)^2195 ≤ (3005100527217/25000000000000 : ℝ)^1683 := by
    have hnat : (492577659 : ℕ)^2195*25000000000000^1683 ≤ 3005100527217^1683*2500000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492577659 2500000000 3005100527217 25000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655918299/1250000000 : ℝ)^2195 ≤ (21563049530109/50000000000000 : ℝ)^1683 := by
    have hnat : (655918299 : ℕ)^2195*50000000000000^1683 ≤ 21563049530109^1683*1250000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655918299 1250000000 21563049530109 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407760021/10000000000 : ℝ)^2195 ≤ (35041795947/78125000000 : ℝ)^1683 := by
    have hnat : (5407760021 : ℕ)^2195*78125000000^1683 ≤ 35041795947^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407760021 10000000000 35041795947 78125000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-492577659/2500000000 : ℝ), (655918299/1250000000 : ℝ), (5407760021/10000000000 : ℝ)] ![(3005100527217/25000000000000 : ℝ), (21563049530109/50000000000000 : ℝ), (35041795947/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-492577659/2500000000 : ℝ)|^2195 ≤ (3005100527217/25000000000000 : ℝ)^1683
        have hw : |(-492577659/2500000000 : ℝ)|=(492577659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655918299/1250000000 : ℝ)|^2195 ≤ (21563049530109/50000000000000 : ℝ)^1683
        have hw : |(655918299/1250000000 : ℝ)|=(655918299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407760021/10000000000 : ℝ)|^2195 ≤ (35041795947/78125000000 : ℝ)^1683
        have hw : |(5407760021/10000000000 : ℝ)|=(5407760021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s5_5 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305340497/10000000000 : ℝ)*x 0 + (-118223103/625000000 : ℝ)*x 1 + (5407760037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305340497/10000000000 : ℝ)^2195 ≤ (21874387676959/50000000000000 : ℝ)^1683 := by
    have hnat : (5305340497 : ℕ)^2195*50000000000000^1683 ≤ 21874387676959^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305340497 10000000000 21874387676959 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118223103/625000000 : ℝ)^2195 ≤ (1424715706563/12500000000000 : ℝ)^1683 := by
    have hnat : (118223103 : ℕ)^2195*12500000000000^1683 ≤ 1424715706563^1683*625000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118223103 625000000 1424715706563 12500000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407760037/10000000000 : ℝ)^2195 ≤ (44853498985241/100000000000000 : ℝ)^1683 := by
    have hnat : (5407760037 : ℕ)^2195*100000000000000^1683 ≤ 44853498985241^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407760037 10000000000 44853498985241 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305340497/10000000000 : ℝ), (-118223103/625000000 : ℝ), (5407760037/10000000000 : ℝ)] ![(21874387676959/50000000000000 : ℝ), (1424715706563/12500000000000 : ℝ), (44853498985241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305340497/10000000000 : ℝ)|^2195 ≤ (21874387676959/50000000000000 : ℝ)^1683
        have hw : |(5305340497/10000000000 : ℝ)|=(5305340497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-118223103/625000000 : ℝ)|^2195 ≤ (1424715706563/12500000000000 : ℝ)^1683
        have hw : |(-118223103/625000000 : ℝ)|=(118223103/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407760037/10000000000 : ℝ)|^2195 ≤ (44853498985241/100000000000000 : ℝ)^1683
        have hw : |(5407760037/10000000000 : ℝ)|=(5407760037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s5_6 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331583813/625000000 : ℝ)*x 0 + (5407759809/10000000000 : ℝ)*x 1 + (-945784631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331583813/625000000 : ℝ)^2195 ≤ (43748780849629/100000000000000 : ℝ)^1683 := by
    have hnat : (331583813 : ℕ)^2195*100000000000000^1683 ≤ 43748780849629^1683*625000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331583813 625000000 43748780849629 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407759809/10000000000 : ℝ)^2195 ≤ (44853496518837/100000000000000 : ℝ)^1683 := by
    have hnat : (5407759809 : ℕ)^2195*100000000000000^1683 ≤ 44853496518837^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407759809 10000000000 44853496518837 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945784631/5000000000 : ℝ)^2195 ≤ (11397722619077/100000000000000 : ℝ)^1683 := by
    have hnat : (945784631 : ℕ)^2195*100000000000000^1683 ≤ 11397722619077^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945784631 5000000000 11397722619077 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331583813/625000000 : ℝ), (5407759809/10000000000 : ℝ), (-945784631/5000000000 : ℝ)] ![(43748780849629/100000000000000 : ℝ), (44853496518837/100000000000000 : ℝ), (11397722619077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331583813/625000000 : ℝ)|^2195 ≤ (43748780849629/100000000000000 : ℝ)^1683
        have hw : |(331583813/625000000 : ℝ)|=(331583813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407759809/10000000000 : ℝ)|^2195 ≤ (44853496518837/100000000000000 : ℝ)^1683
        have hw : |(5407759809/10000000000 : ℝ)|=(5407759809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-945784631/5000000000 : ℝ)|^2195 ≤ (11397722619077/100000000000000 : ℝ)^1683
        have hw : |(-945784631/5000000000 : ℝ)|=(945784631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1430_s5_7 (p : ℝ) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4304135863/10000000000 : ℝ)*x 0 + (2240442139/5000000000 : ℝ)*x 1 + (4133730373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304135863/10000000000 : ℝ)^2195 ≤ (16652416242839/50000000000000 : ℝ)^1683 := by
    have hnat : (4304135863 : ℕ)^2195*50000000000000^1683 ≤ 16652416242839^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304135863 10000000000 16652416242839 50000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240442139/5000000000 : ℝ)^2195 ≤ (35099592112613/100000000000000 : ℝ)^1683 := by
    have hnat : (2240442139 : ℕ)^2195*100000000000000^1683 ≤ 35099592112613^1683*5000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240442139 5000000000 35099592112613 100000000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4133730373/10000000000 : ℝ)^2195 ≤ (3949446923349/12500000000000 : ℝ)^1683 := by
    have hnat : (4133730373 : ℕ)^2195*12500000000000^1683 ≤ 3949446923349^1683*10000000000^2195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133730373 10000000000 3949446923349 12500000000000 2195 1683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2195/512 : ℝ)) 2195 1683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304135863/10000000000 : ℝ), (2240442139/5000000000 : ℝ), (4133730373/10000000000 : ℝ)] ![(16652416242839/50000000000000 : ℝ), (35099592112613/100000000000000 : ℝ), (3949446923349/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304135863/10000000000 : ℝ)|^2195 ≤ (16652416242839/50000000000000 : ℝ)^1683
        have hw : |(4304135863/10000000000 : ℝ)|=(4304135863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240442139/5000000000 : ℝ)|^2195 ≤ (35099592112613/100000000000000 : ℝ)^1683
        have hw : |(2240442139/5000000000 : ℝ)|=(2240442139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4133730373/10000000000 : ℝ)|^2195 ≤ (3949446923349/12500000000000 : ℝ)^1683
        have hw : |(4133730373/10000000000 : ℝ)|=(4133730373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1430_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5669/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14761/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7393/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2263/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7393/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2263/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7393/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2263/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7393/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2263/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7393/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2263/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7393/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2263/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2263/20000 : ℝ) ^ (4389/1024 : ℝ) ≤ (2196735452294421/25000000000000000000 : ℝ) := by
    have hpowers : (2263/20000 : ℝ)^4389 ≤ (2196735452294421/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2263 : ℕ)^4389*25000000000000000000^1024 ≤ 2196735452294421^1024*20000^4389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2263 20000 2196735452294421 25000000000000000000 4389 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2263/20000 : ℝ)) (X := (2196735452294421/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7393/50000 : ℝ) ^ (4389/1024 : ℝ) ≤ (27661125938790859/100000000000000000000 : ℝ) := by
    have hpowers : (7393/50000 : ℝ)^4389 ≤ (27661125938790859/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7393 : ℕ)^4389*100000000000000000000^1024 ≤ 27661125938790859^1024*50000^4389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7393 50000 27661125938790859 100000000000000000000 4389 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7393/50000 : ℝ)) (X := (27661125938790859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502196735452294421/12500000000000000000 : ℝ) ≤ (10000409989624271/10000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (12502196735452294421/12500000000000000000 : ℝ)^1024 ≤ (10000409989624271/10000000000000000 : ℝ)^4389 := by
      have hnat : (12502196735452294421 : ℕ)^1024*10000000000000000^4389 ≤ 10000409989624271^4389*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502196735452294421 12500000000000000000 10000409989624271 10000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000409989624271/10000000000000000 : ℝ)) (X := (12502196735452294421/12500000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036448067747968543/100000000000000000000 : ℝ) ≤ (5000425126540023/5000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (100036448067747968543/100000000000000000000 : ℝ)^1024 ≤ (5000425126540023/5000000000000000 : ℝ)^4389 := by
      have hnat : (100036448067747968543 : ℕ)^1024*5000000000000000^4389 ≤ 5000425126540023^4389*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036448067747968543 100000000000000000000 5000425126540023 5000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000425126540023/5000000000000000 : ℝ)) (X := (100036448067747968543/100000000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027661125938790859/50000000000000000000 : ℝ) ≤ (10001290516535821/10000000000000000 : ℝ) ^ (4389/1024 : ℝ) := by
    have hpowers : (50027661125938790859/50000000000000000000 : ℝ)^1024 ≤ (10001290516535821/10000000000000000 : ℝ)^4389 := by
      have hnat : (50027661125938790859 : ℕ)^1024*10000000000000000^4389 ≤ 10001290516535821^4389*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027661125938790859 50000000000000000000 10001290516535821 10000000000000000 1024 4389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001290516535821/10000000000000000 : ℝ)) (X := (50027661125938790859/50000000000000000000 : ℝ)) (by norm_num) 4389 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2196735452294421/25000000000000000000 : ℝ) ≤ ((2669343070152435107/2670000000000000000 : ℝ)+2*(1354656787/1068000000000 : ℝ)*(2263/20000 : ℝ))^(4389/1024 : ℝ) := by
    rw [show (2669343070152435107/2670000000000000000 : ℝ)+2*(1354656787/1068000000000 : ℝ)*(2263/20000 : ℝ)=(10000409989624271/10000000000000000 : ℝ) by norm_num, show 1+2*(2196735452294421/25000000000000000000 : ℝ)=(12502196735452294421/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27661125938790859/100000000000000000000 : ℝ)+(2196735452294421/25000000000000000000 : ℝ) ≤ ((2669343070152435107/2670000000000000000 : ℝ)+(1354656787/1068000000000 : ℝ)*((7393/50000 : ℝ)+(2263/20000 : ℝ)))^(4389/1024 : ℝ) := by
    rw [show (2669343070152435107/2670000000000000000 : ℝ)+(1354656787/1068000000000 : ℝ)*((7393/50000 : ℝ)+(2263/20000 : ℝ))=(5000425126540023/5000000000000000 : ℝ) by norm_num, show 1+(27661125938790859/100000000000000000000 : ℝ)+(2196735452294421/25000000000000000000 : ℝ)=(100036448067747968543/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27661125938790859/100000000000000000000 : ℝ) ≤ ((2669343070152435107/2670000000000000000 : ℝ)+2*(1354656787/1068000000000 : ℝ)*(7393/50000 : ℝ))^(4389/1024 : ℝ) := by
    rw [show (2669343070152435107/2670000000000000000 : ℝ)+2*(1354656787/1068000000000 : ℝ)*(7393/50000 : ℝ)=(10001290516535821/10000000000000000 : ℝ) by norm_num, show 1+2*(27661125938790859/100000000000000000000 : ℝ)=(50027661125938790859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2669343070152435107/2670000000000000000 : ℝ)*(X 1 0+X 2 0)+(1354656787/1068000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (2669343070152435107/2670000000000000000 : ℝ)) (alpha := (1354656787/1068000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2669343070152435107/2670000000000000000 : ℝ)*(X 0 1+X 2 1)+(1354656787/1068000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (2669343070152435107/2670000000000000000 : ℝ)) (alpha := (1354656787/1068000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2669343070152435107/2670000000000000000 : ℝ)*(X 0 2+X 1 2)+(1354656787/1068000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4389/1024 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (2669343070152435107/2670000000000000000 : ℝ)) (alpha := (1354656787/1068000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1970298857/10000000000 : ℝ)*X 0 0+(2704173513/5000000000 : ℝ)*X 0 1+(5246762709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673676259/5000000000 : ℝ)*X 1 0+(-2052566331/10000000000 : ℝ)*X 1 1+(1311690721/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347352733/10000000000 : ℝ)*X 2 0+(5246762709/10000000000 : ℝ)*X 2 1+(-1026283139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((538013919/1250000000 : ℝ)*X 0 0+(516557459/1250000000 : ℝ)*X 0 1+(896429657/2000000000 : ℝ)*X 0 2+(538013919/1250000000 : ℝ)*X 1 0+(516557459/1250000000 : ℝ)*X 1 1+(896429657/2000000000 : ℝ)*X 1 2+(538013919/1250000000 : ℝ)*X 2 0+(516557459/1250000000 : ℝ)*X 2 1+(896429657/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-492577659/2500000000 : ℝ)*X 0 0+(655918299/1250000000 : ℝ)*X 0 1+(5407760021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305340497/10000000000 : ℝ)*X 1 0+(-118223103/625000000 : ℝ)*X 1 1+(5407760037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331583813/625000000 : ℝ)*X 2 0+(5407759809/10000000000 : ℝ)*X 2 1+(-945784631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4304135863/10000000000 : ℝ)*X 0 0+(2240442139/5000000000 : ℝ)*X 0 1+(4133730373/10000000000 : ℝ)*X 0 2+(4304135863/10000000000 : ℝ)*X 1 0+(2240442139/5000000000 : ℝ)*X 1 1+(4133730373/10000000000 : ℝ)*X 1 2+(4304135863/10000000000 : ℝ)*X 2 0+(2240442139/5000000000 : ℝ)*X 2 1+(4133730373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1430_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (315905077719975714401461/27812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (88046603/4000000000000 : ℝ)*(base19) + (1089254121/50000000000000 : ℝ)*(base23) + (145175043/100000000000000 : ℝ)*(lower2) + (61245453/20000000000000 : ℝ)*(upper3) + (218804019/100000000000000 : ℝ)*(upper5) + (5655346579057/125000000000 : ℝ)*(major0) + (5655346579057/125000000000 : ℝ)*(major1) + (5655346579057/125000000000 : ℝ)*(major2) + (618876976885343/10000000000000 : ℝ)*(sp0) + (773602532585609/12500000000000 : ℝ)*(sp1) + (1237764056668341/20000000000000 : ℝ)*(sp2) + (714926907747081/25000000000000 : ℝ)*(sp3) + (52692996517/100000000000000 : ℝ)*(sp4) + (6013760023/25000000000000 : ℝ)*(sp7) + (22341653797097/781250000000 : ℝ)*(f.failure) + (6188822461849947/100000000000000 : ℝ)*(f.sum) + (60464120213/133500000000000000000000000 : ℝ)*base65 + (1830859776796967/111250000000000000000000000000 : ℝ)*base68 + (1293207242940717/111250000000000000000000000000 : ℝ)*base70 + (1130187473406967/111250000000000000000000000000 : ℝ)*base72 + (18157755661/16687500000000000000000000 : ℝ)*base73 + (2772198353901967/111250000000000000000000000000 : ℝ)*base76 + (1565277553583217/111250000000000000000000000000 : ℝ)*base78 + (604836160658217/111250000000000000000000000000 : ℝ)*base80 + (175620689911/133500000000000000000000000 : ℝ)*base82 + (190287/15625000000000000000 : ℝ)*base89 + (190287/15625000000000000000 : ℝ)*base91 + (190287/15625000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83686434342199546224909107/22250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (217132337/100000000000000 : ℝ)*(base19) + (633197491/50000000000000 : ℝ)*(base23) + (46642847/25000000000000 : ℝ)*(upper2) + (2497837/50000000000000 : ℝ)*(upper3) + (422957437/100000000000000 : ℝ)*(upper5) + (4557231638682001/100000000000000 : ℝ)*(major0) + (4557231638682001/100000000000000 : ℝ)*(major1) + (4557231638682001/100000000000000 : ℝ)*(major2) + (650265831/10000000000000 : ℝ)*(sp1) + (4693026401/25000000000000 : ℝ)*(sp2) + (311695073560767/5000000000000 : ℝ)*(sp4) + (6233894751424693/100000000000000 : ℝ)*(sp5) + (6233881432714753/100000000000000 : ℝ)*(sp6) + (2880561680775719/100000000000000 : ℝ)*(sp7) + (2880561680775719/100000000000000 : ℝ)*(f.failure) + (311695073560767/5000000000000 : ℝ)*(f.sum) + (78413191829/66750000000000000000000000 : ℝ)*base65 + (641839217708363631/89000000000000000000000000000000 : ℝ)*base68 + (550599636393363631/89000000000000000000000000000000 : ℝ)*base70 + (397643539612363631/89000000000000000000000000000000 : ℝ)*base72 + (597408090601/267000000000000000000000000 : ℝ)*base74 + (900248377542363631/89000000000000000000000000000000 : ℝ)*base76 + (191224927807363631/89000000000000000000000000000000 : ℝ)*base78 + (1555763900454636369/89000000000000000000000000000000 : ℝ)*base79 + (54791491633/16687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4901151/2000000000000000000000 : ℝ)*base90 + (4901151/2000000000000000000000 : ℝ)*base92 + (4901151/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1430_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1430_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1430_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15797/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1430_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1430_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1430_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15797/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1430_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
