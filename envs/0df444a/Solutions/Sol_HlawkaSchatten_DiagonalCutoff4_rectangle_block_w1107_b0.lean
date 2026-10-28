-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1107_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:03:22.081988+00:00
-- url     : https://prove2.me/submissions/910fe572-680d-4574-a8cc-20ed9f812d96

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
theorem support_rectangle_w1107_s0_0 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-951468921/5000000000 : ℝ)*x 0 + (6062455059/10000000000 : ℝ)*x 1 + (597003721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (951468921/5000000000 : ℝ)^2075 ≤ (2762625388903/25000000000000 : ℝ)^1563 := by
    have hnat : (951468921 : ℕ)^2075*25000000000000^1563 ≤ 2762625388903^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951468921 5000000000 2762625388903 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6062455059/10000000000 : ℝ)^2075 ≤ (1029152142619/2000000000000 : ℝ)^1563 := by
    have hnat : (6062455059 : ℕ)^2075*2000000000000^1563 ≤ 1029152142619^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6062455059 10000000000 1029152142619 2000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (597003721/1250000000 : ℝ)^2075 ≤ (37491891303047/100000000000000 : ℝ)^1563 := by
    have hnat : (597003721 : ℕ)^2075*100000000000000^1563 ≤ 37491891303047^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597003721 1250000000 37491891303047 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-951468921/5000000000 : ℝ), (6062455059/10000000000 : ℝ), (597003721/1250000000 : ℝ)] ![(2762625388903/25000000000000 : ℝ), (1029152142619/2000000000000 : ℝ), (37491891303047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-951468921/5000000000 : ℝ)|^2075 ≤ (2762625388903/25000000000000 : ℝ)^1563
        have hw : |(-951468921/5000000000 : ℝ)|=(951468921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6062455059/10000000000 : ℝ)|^2075 ≤ (1029152142619/2000000000000 : ℝ)^1563
        have hw : |(6062455059/10000000000 : ℝ)|=(6062455059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(597003721/1250000000 : ℝ)|^2075 ≤ (37491891303047/100000000000000 : ℝ)^1563
        have hw : |(597003721/1250000000 : ℝ)|=(597003721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s0_1 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5518764741/10000000000 : ℝ)*x 0 + (-1321104603/5000000000 : ℝ)*x 1 + (1194007509/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518764741/10000000000 : ℝ)^2075 ≤ (22711493489917/50000000000000 : ℝ)^1563 := by
    have hnat : (5518764741 : ℕ)^2075*50000000000000^1563 ≤ 22711493489917^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518764741 10000000000 22711493489917 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1321104603/5000000000 : ℝ)^2075 ≤ (8542559453483/50000000000000 : ℝ)^1563 := by
    have hnat : (1321104603 : ℕ)^2075*50000000000000^1563 ≤ 8542559453483^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321104603 5000000000 8542559453483 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194007509/2500000000 : ℝ)^2075 ≤ (9372973524001/25000000000000 : ℝ)^1563 := by
    have hnat : (1194007509 : ℕ)^2075*25000000000000^1563 ≤ 9372973524001^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194007509 2500000000 9372973524001 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518764741/10000000000 : ℝ), (-1321104603/5000000000 : ℝ), (1194007509/2500000000 : ℝ)] ![(22711493489917/50000000000000 : ℝ), (8542559453483/50000000000000 : ℝ), (9372973524001/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518764741/10000000000 : ℝ)|^2075 ≤ (22711493489917/50000000000000 : ℝ)^1563
        have hw : |(5518764741/10000000000 : ℝ)|=(5518764741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1321104603/5000000000 : ℝ)|^2075 ≤ (8542559453483/50000000000000 : ℝ)^1563
        have hw : |(-1321104603/5000000000 : ℝ)|=(1321104603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1194007509/2500000000 : ℝ)|^2075 ≤ (9372973524001/25000000000000 : ℝ)^1563
        have hw : |(1194007509/2500000000 : ℝ)|=(1194007509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s0_2 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5518765177/10000000000 : ℝ)*x 0 + (2388014799/5000000000 : ℝ)*x 1 + (-2642209183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518765177/10000000000 : ℝ)^2075 ≤ (22711495871959/50000000000000 : ℝ)^1563 := by
    have hnat : (5518765177 : ℕ)^2075*50000000000000^1563 ≤ 22711495871959^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518765177 10000000000 22711495871959 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2388014799/5000000000 : ℝ)^2075 ≤ (7498377906279/20000000000000 : ℝ)^1563 := by
    have hnat : (2388014799 : ℕ)^2075*20000000000000^1563 ≤ 7498377906279^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388014799 5000000000 7498377906279 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2642209183/10000000000 : ℝ)^2075 ≤ (683404748381/4000000000000 : ℝ)^1563 := by
    have hnat : (2642209183 : ℕ)^2075*4000000000000^1563 ≤ 683404748381^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642209183 10000000000 683404748381 4000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518765177/10000000000 : ℝ), (2388014799/5000000000 : ℝ), (-2642209183/10000000000 : ℝ)] ![(22711495871959/50000000000000 : ℝ), (7498377906279/20000000000000 : ℝ), (683404748381/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518765177/10000000000 : ℝ)|^2075 ≤ (22711495871959/50000000000000 : ℝ)^1563
        have hw : |(5518765177/10000000000 : ℝ)|=(5518765177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2388014799/5000000000 : ℝ)|^2075 ≤ (7498377906279/20000000000000 : ℝ)^1563
        have hw : |(2388014799/5000000000 : ℝ)|=(2388014799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2642209183/10000000000 : ℝ)|^2075 ≤ (683404748381/4000000000000 : ℝ)^1563
        have hw : |(-2642209183/10000000000 : ℝ)|=(2642209183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s0_3 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2101918333/5000000000 : ℝ)*x 0 + (3122755791/10000000000 : ℝ)*x 1 + (2832253973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101918333/5000000000 : ℝ)^2075 ≤ (1978069601803/6250000000000 : ℝ)^1563 := by
    have hnat : (2101918333 : ℕ)^2075*6250000000000^1563 ≤ 1978069601803^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101918333 5000000000 1978069601803 6250000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3122755791/10000000000 : ℝ)^2075 ≤ (21328544832893/100000000000000 : ℝ)^1563 := by
    have hnat : (3122755791 : ℕ)^2075*100000000000000^1563 ≤ 21328544832893^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122755791 10000000000 21328544832893 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2832253973/5000000000 : ℝ)^2075 ≤ (4702234152087/10000000000000 : ℝ)^1563 := by
    have hnat : (2832253973 : ℕ)^2075*10000000000000^1563 ≤ 4702234152087^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832253973 5000000000 4702234152087 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101918333/5000000000 : ℝ), (3122755791/10000000000 : ℝ), (2832253973/5000000000 : ℝ)] ![(1978069601803/6250000000000 : ℝ), (21328544832893/100000000000000 : ℝ), (4702234152087/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101918333/5000000000 : ℝ)|^2075 ≤ (1978069601803/6250000000000 : ℝ)^1563
        have hw : |(2101918333/5000000000 : ℝ)|=(2101918333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3122755791/10000000000 : ℝ)|^2075 ≤ (21328544832893/100000000000000 : ℝ)^1563
        have hw : |(3122755791/10000000000 : ℝ)|=(3122755791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2832253973/5000000000 : ℝ)|^2075 ≤ (4702234152087/10000000000000 : ℝ)^1563
        have hw : |(2832253973/5000000000 : ℝ)|=(2832253973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s0_4 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1908188187/10000000000 : ℝ)*x 0 + (4809232203/10000000000 : ℝ)*x 1 + (3014043691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1908188187/10000000000 : ℝ)^2075 ≤ (2772749116571/25000000000000 : ℝ)^1563 := by
    have hnat : (1908188187 : ℕ)^2075*25000000000000^1563 ≤ 2772749116571^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908188187 10000000000 2772749116571 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4809232203/10000000000 : ℝ)^2075 ≤ (37838303229613/100000000000000 : ℝ)^1563 := by
    have hnat : (4809232203 : ℕ)^2075*100000000000000^1563 ≤ 37838303229613^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4809232203 10000000000 37838303229613 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3014043691/5000000000 : ℝ)^2075 ≤ (51070700287627/100000000000000 : ℝ)^1563 := by
    have hnat : (3014043691 : ℕ)^2075*100000000000000^1563 ≤ 51070700287627^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014043691 5000000000 51070700287627 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1908188187/10000000000 : ℝ), (4809232203/10000000000 : ℝ), (3014043691/5000000000 : ℝ)] ![(2772749116571/25000000000000 : ℝ), (37838303229613/100000000000000 : ℝ), (51070700287627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1908188187/10000000000 : ℝ)|^2075 ≤ (2772749116571/25000000000000 : ℝ)^1563
        have hw : |(-1908188187/10000000000 : ℝ)|=(1908188187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4809232203/10000000000 : ℝ)|^2075 ≤ (37838303229613/100000000000000 : ℝ)^1563
        have hw : |(4809232203/10000000000 : ℝ)|=(4809232203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3014043691/5000000000 : ℝ)|^2075 ≤ (51070700287627/100000000000000 : ℝ)^1563
        have hw : |(3014043691/5000000000 : ℝ)|=(3014043691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s0_5 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5169389811/10000000000 : ℝ)*x 0 + (-278030533/2000000000 : ℝ)*x 1 + (6028089013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169389811/10000000000 : ℝ)^2075 ≤ (41645598231233/100000000000000 : ℝ)^1563 := by
    have hnat : (5169389811 : ℕ)^2075*100000000000000^1563 ≤ 41645598231233^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169389811 10000000000 41645598231233 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278030533/2000000000 : ℝ)^2075 ≤ (7283683116723/100000000000000 : ℝ)^1563 := by
    have hnat : (278030533 : ℕ)^2075*100000000000000^1563 ≤ 7283683116723^1563*2000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278030533 2000000000 7283683116723 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6028089013/10000000000 : ℝ)^2075 ≤ (25535359316053/50000000000000 : ℝ)^1563 := by
    have hnat : (6028089013 : ℕ)^2075*50000000000000^1563 ≤ 25535359316053^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6028089013 10000000000 25535359316053 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169389811/10000000000 : ℝ), (-278030533/2000000000 : ℝ), (6028089013/10000000000 : ℝ)] ![(41645598231233/100000000000000 : ℝ), (7283683116723/100000000000000 : ℝ), (25535359316053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169389811/10000000000 : ℝ)|^2075 ≤ (41645598231233/100000000000000 : ℝ)^1563
        have hw : |(5169389811/10000000000 : ℝ)|=(5169389811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-278030533/2000000000 : ℝ)|^2075 ≤ (7283683116723/100000000000000 : ℝ)^1563
        have hw : |(-278030533/2000000000 : ℝ)|=(278030533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6028089013/10000000000 : ℝ)|^2075 ≤ (25535359316053/50000000000000 : ℝ)^1563
        have hw : |(6028089013/10000000000 : ℝ)|=(6028089013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s0_6 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2584696051/5000000000 : ℝ)*x 0 + (1507021971/2500000000 : ℝ)*x 1 + (-173768871/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584696051/5000000000 : ℝ)^2075 ≤ (2082281136697/5000000000000 : ℝ)^1563 := by
    have hnat : (2584696051 : ℕ)^2075*5000000000000^1563 ≤ 2082281136697^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584696051 5000000000 2082281136697 5000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1507021971/2500000000 : ℝ)^2075 ≤ (51070705933813/100000000000000 : ℝ)^1563 := by
    have hnat : (1507021971 : ℕ)^2075*100000000000000^1563 ≤ 51070705933813^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507021971 2500000000 51070705933813 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173768871/1250000000 : ℝ)^2075 ≤ (7283671312717/100000000000000 : ℝ)^1563 := by
    have hnat : (173768871 : ℕ)^2075*100000000000000^1563 ≤ 7283671312717^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173768871 1250000000 7283671312717 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584696051/5000000000 : ℝ), (1507021971/2500000000 : ℝ), (-173768871/1250000000 : ℝ)] ![(2082281136697/5000000000000 : ℝ), (51070705933813/100000000000000 : ℝ), (7283671312717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584696051/5000000000 : ℝ)|^2075 ≤ (2082281136697/5000000000000 : ℝ)^1563
        have hw : |(2584696051/5000000000 : ℝ)|=(2584696051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1507021971/2500000000 : ℝ)|^2075 ≤ (51070705933813/100000000000000 : ℝ)^1563
        have hw : |(1507021971/2500000000 : ℝ)|=(1507021971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173768871/1250000000 : ℝ)|^2075 ≤ (7283671312717/100000000000000 : ℝ)^1563
        have hw : |(-173768871/1250000000 : ℝ)|=(173768871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s0_7 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4214207291/10000000000 : ℝ)*x 0 + (349931729/625000000 : ℝ)*x 1 + (3190658049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4214207291/10000000000 : ℝ)^2075 ≤ (6350561596921/20000000000000 : ℝ)^1563 := by
    have hnat : (4214207291 : ℕ)^2075*20000000000000^1563 ≤ 6350561596921^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214207291 10000000000 6350561596921 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349931729/625000000 : ℝ)^2075 ≤ (578759608471/1250000000000 : ℝ)^1563 := by
    have hnat : (349931729 : ℕ)^2075*1250000000000^1563 ≤ 578759608471^1563*625000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349931729 625000000 578759608471 1250000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3190658049/10000000000 : ℝ)^2075 ≤ (10973211657139/50000000000000 : ℝ)^1563 := by
    have hnat : (3190658049 : ℕ)^2075*50000000000000^1563 ≤ 10973211657139^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3190658049 10000000000 10973211657139 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4214207291/10000000000 : ℝ), (349931729/625000000 : ℝ), (3190658049/10000000000 : ℝ)] ![(6350561596921/20000000000000 : ℝ), (578759608471/1250000000000 : ℝ), (10973211657139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4214207291/10000000000 : ℝ)|^2075 ≤ (6350561596921/20000000000000 : ℝ)^1563
        have hw : |(4214207291/10000000000 : ℝ)|=(4214207291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(349931729/625000000 : ℝ)|^2075 ≤ (578759608471/1250000000000 : ℝ)^1563
        have hw : |(349931729/625000000 : ℝ)|=(349931729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3190658049/10000000000 : ℝ)|^2075 ≤ (10973211657139/50000000000000 : ℝ)^1563
        have hw : |(3190658049/10000000000 : ℝ)|=(3190658049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1107_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (559/2000 : ℝ)*pair X 0 0 := by
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
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8299/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8299 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8299*1^2048 ≤ 0^2048*1^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8299/2048 : ℝ) ≤ (2440333345572390707/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8299 ≤ (2440333345572390707/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8299*100000000000000000000^2048 ≤ 2440333345572390707^2048*5^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2440333345572390707 100000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2440333345572390707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8299 := by
      have hnat : (1 : ℕ)^2048*1^8299 ≤ 1^8299*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102440333345572390707/100000000000000000000 : ℝ) ≤ (2011935207260621/2000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (102440333345572390707/100000000000000000000 : ℝ)^2048 ≤ (2011935207260621/2000000000000000 : ℝ)^8299 := by
      have hnat : (102440333345572390707 : ℕ)^2048*2000000000000000^8299 ≤ 2011935207260621^8299*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102440333345572390707 100000000000000000000 2011935207260621 2000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011935207260621/2000000000000000 : ℝ)) (X := (102440333345572390707/100000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52440333345572390707/50000000000000000000 : ℝ) ≤ (1011935207260621/1000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (52440333345572390707/50000000000000000000 : ℝ)^2048 ≤ (1011935207260621/1000000000000000 : ℝ)^8299 := by
      have hnat : (52440333345572390707 : ℕ)^2048*1000000000000000^8299 ≤ 1011935207260621^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52440333345572390707 50000000000000000000 1011935207260621 1000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011935207260621/1000000000000000 : ℝ)) (X := (52440333345572390707/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11935207260621/800000000000000 : ℝ)*(0 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11935207260621/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2440333345572390707/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11935207260621/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8299/2048 : ℝ) := by
    rw [show (1 : ℝ)+(11935207260621/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011935207260621/2000000000000000 : ℝ) by norm_num, show 1+(2440333345572390707/100000000000000000000 : ℝ)+(0 : ℝ)=(102440333345572390707/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2440333345572390707/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11935207260621/800000000000000 : ℝ)*(2/5 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11935207260621/800000000000000 : ℝ)*(2/5 : ℝ)=(1011935207260621/1000000000000000 : ℝ) by norm_num, show 1+2*(2440333345572390707/100000000000000000000 : ℝ)=(52440333345572390707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11935207260621/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11935207260621/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11935207260621/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11935207260621/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11935207260621/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11935207260621/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-951468921/5000000000 : ℝ)*X 0 0+(6062455059/10000000000 : ℝ)*X 0 1+(597003721/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5518764741/10000000000 : ℝ)*X 1 0+(-1321104603/5000000000 : ℝ)*X 1 1+(1194007509/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5518765177/10000000000 : ℝ)*X 2 0+(2388014799/5000000000 : ℝ)*X 2 1+(-2642209183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2101918333/5000000000 : ℝ)*X 0 0+(3122755791/10000000000 : ℝ)*X 0 1+(2832253973/5000000000 : ℝ)*X 0 2+(2101918333/5000000000 : ℝ)*X 1 0+(3122755791/10000000000 : ℝ)*X 1 1+(2832253973/5000000000 : ℝ)*X 1 2+(2101918333/5000000000 : ℝ)*X 2 0+(3122755791/10000000000 : ℝ)*X 2 1+(2832253973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1908188187/10000000000 : ℝ)*X 0 0+(4809232203/10000000000 : ℝ)*X 0 1+(3014043691/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5169389811/10000000000 : ℝ)*X 1 0+(-278030533/2000000000 : ℝ)*X 1 1+(6028089013/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2584696051/5000000000 : ℝ)*X 2 0+(1507021971/2500000000 : ℝ)*X 2 1+(-173768871/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4214207291/10000000000 : ℝ)*X 0 0+(349931729/625000000 : ℝ)*X 0 1+(3190658049/10000000000 : ℝ)*X 0 2+(4214207291/10000000000 : ℝ)*X 1 0+(349931729/625000000 : ℝ)*X 1 1+(3190658049/10000000000 : ℝ)*X 1 2+(4214207291/10000000000 : ℝ)*X 2 0+(349931729/625000000 : ℝ)*X 2 1+(3190658049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (964344840056478488259/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2154653/25000000000000 : ℝ)*(base1) + (381086687/100000000000000 : ℝ)*(base19) + (25179067/6250000000000 : ℝ)*(base23) + (7926943/20000000000000 : ℝ)*(base24) + (105367993/100000000000000 : ℝ)*(upper3) + (9146724450359/1562500000000 : ℝ)*(major0) + (9146724450359/1562500000000 : ℝ)*(major1) + (9146724450359/1562500000000 : ℝ)*(major2) + (388674616263801/50000000000000 : ℝ)*(sp0) + (194337431197137/25000000000000 : ℝ)*(sp1) + (97168707921931/12500000000000 : ℝ)*(sp2) + (393429791870709/100000000000000 : ℝ)*(sp3) + (440983123/50000000000000 : ℝ)*(sp4) + (385924833/50000000000000 : ℝ)*(sp7) + (393430572338987/100000000000000 : ℝ)*(f.failure) + (194337526468809/25000000000000 : ℝ)*(f.sum) + (1971135058311/625000000000000000000000000 : ℝ)*base66 + (638365610811/1250000000000000000000000000 : ℝ)*base68 + (3522065442939/1250000000000000000000000000 : ℝ)*base69 + (2335143677939/1250000000000000000000000000 : ℝ)*base71 + (372471026117/78125000000000000000000000 : ℝ)*base74 + (4646236167939/1250000000000000000000000000 : ℝ)*base75 + (560091607061/1250000000000000000000000000 : ℝ)*base78 + (4473820079189/1250000000000000000000000000 : ℝ)*base79 + (196257714561/625000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (317537/400000000000000000000 : ℝ)*base89 + (317537/400000000000000000000 : ℝ)*base91 + (317537/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62150509156594042224981/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158121787/20000000000000 : ℝ)*(base19) + (330638929/20000000000000 : ℝ)*(base23) + (58330379/12500000000000 : ℝ)*(base39) + (282587017/100000000000000 : ℝ)*(base45) + (41312281/25000000000000 : ℝ)*(upper3) + (302305279/100000000000000 : ℝ)*(upper5) + (154459490121613/25000000000000 : ℝ)*(major0) + (154459490121613/25000000000000 : ℝ)*(major1) + (30891874692171/5000000000000 : ℝ)*(major2) + (677732869/100000000000000 : ℝ)*(sp2) + (820437216244399/100000000000000 : ℝ)*(sp4) + (164087285127093/20000000000000 : ℝ)*(sp5) + (410217675979959/50000000000000 : ℝ)*(sp6) + (415238030917103/100000000000000 : ℝ)*(sp7) + (415238030917103/100000000000000 : ℝ)*(f.failure) + (102554710360929/12500000000000 : ℝ)*(f.sum) + (4061733798157/5000000000000000000000000000 : ℝ)*base65 + (3859688257809/4000000000000000000000000000 : ℝ)*base68 + (161528166601673/20000000000000000000000000000 : ℝ)*base69 + (9963235053809/4000000000000000000000000000 : ℝ)*base72 + (10338584763157/5000000000000000000000000000 : ℝ)*base73 + (59863285938327/20000000000000000000000000000 : ℝ)*base76 + (25985492538327/20000000000000000000000000000 : ℝ)*base78 + (110221475418327/20000000000000000000000000000 : ℝ)*base80 + (45693121941673/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1012947/400000000000000000000 : ℝ)*base90 + (1012947/400000000000000000000 : ℝ)*base92 + (1012947/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1107_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (559/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1107_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1107_s1_0 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110124843/10000000000 : ℝ)*x 0 + (2855484361/5000000000 : ℝ)*x 1 + (1248714767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110124843/10000000000 : ℝ)^2075 ≤ (6337796326427/50000000000000 : ℝ)^1563 := by
    have hnat : (2110124843 : ℕ)^2075*50000000000000^1563 ≤ 6337796326427^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110124843 10000000000 6337796326427 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2855484361/5000000000 : ℝ)^2075 ≤ (23767524477929/50000000000000 : ℝ)^1563 := by
    have hnat : (2855484361 : ℕ)^2075*50000000000000^1563 ≤ 23767524477929^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2855484361 5000000000 23767524477929 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248714767/2500000000 : ℝ)^2075 ≤ (19894679183889/50000000000000 : ℝ)^1563 := by
    have hnat : (1248714767 : ℕ)^2075*50000000000000^1563 ≤ 19894679183889^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248714767 2500000000 19894679183889 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110124843/10000000000 : ℝ), (2855484361/5000000000 : ℝ), (1248714767/2500000000 : ℝ)] ![(6337796326427/50000000000000 : ℝ), (23767524477929/50000000000000 : ℝ), (19894679183889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110124843/10000000000 : ℝ)|^2075 ≤ (6337796326427/50000000000000 : ℝ)^1563
        have hw : |(-2110124843/10000000000 : ℝ)|=(2110124843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2855484361/5000000000 : ℝ)|^2075 ≤ (23767524477929/50000000000000 : ℝ)^1563
        have hw : |(2855484361/5000000000 : ℝ)|=(2855484361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1248714767/2500000000 : ℝ)|^2075 ≤ (19894679183889/50000000000000 : ℝ)^1563
        have hw : |(1248714767/2500000000 : ℝ)|=(1248714767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s1_1 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5421049727/10000000000 : ℝ)*x 0 + (-312159277/1250000000 : ℝ)*x 1 + (4994859093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421049727/10000000000 : ℝ)^2075 ≤ (1108959587021/2500000000000 : ℝ)^1563 := by
    have hnat : (5421049727 : ℕ)^2075*2500000000000^1563 ≤ 1108959587021^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421049727 10000000000 1108959587021 2500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312159277/1250000000 : ℝ)^2075 ≤ (15852257872021/100000000000000 : ℝ)^1563 := by
    have hnat : (312159277 : ℕ)^2075*100000000000000^1563 ≤ 15852257872021^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312159277 1250000000 15852257872021 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4994859093/10000000000 : ℝ)^2075 ≤ (19894679316083/50000000000000 : ℝ)^1563 := by
    have hnat : (4994859093 : ℕ)^2075*50000000000000^1563 ≤ 19894679316083^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4994859093 10000000000 19894679316083 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421049727/10000000000 : ℝ), (-312159277/1250000000 : ℝ), (4994859093/10000000000 : ℝ)] ![(1108959587021/2500000000000 : ℝ), (15852257872021/100000000000000 : ℝ), (19894679316083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421049727/10000000000 : ℝ)|^2075 ≤ (1108959587021/2500000000000 : ℝ)^1563
        have hw : |(5421049727/10000000000 : ℝ)|=(5421049727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-312159277/1250000000 : ℝ)|^2075 ≤ (15852257872021/100000000000000 : ℝ)^1563
        have hw : |(-312159277/1250000000 : ℝ)|=(312159277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4994859093/10000000000 : ℝ)|^2075 ≤ (19894679316083/50000000000000 : ℝ)^1563
        have hw : |(4994859093/10000000000 : ℝ)|=(4994859093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s1_2 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2710525473/5000000000 : ℝ)*x 0 + (1248714481/2500000000 : ℝ)*x 1 + (-2497274111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710525473/5000000000 : ℝ)^2075 ≤ (5544799590361/12500000000000 : ℝ)^1563 := by
    have hnat : (2710525473 : ℕ)^2075*12500000000000^1563 ≤ 5544799590361^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710525473 5000000000 5544799590361 12500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1248714481/2500000000 : ℝ)^2075 ≤ (39789346269353/100000000000000 : ℝ)^1563 := by
    have hnat : (1248714481 : ℕ)^2075*100000000000000^1563 ≤ 39789346269353^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248714481 2500000000 39789346269353 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2497274111/10000000000 : ℝ)^2075 ≤ (15852256987163/100000000000000 : ℝ)^1563 := by
    have hnat : (2497274111 : ℕ)^2075*100000000000000^1563 ≤ 15852256987163^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497274111 10000000000 15852256987163 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710525473/5000000000 : ℝ), (1248714481/2500000000 : ℝ), (-2497274111/10000000000 : ℝ)] ![(5544799590361/12500000000000 : ℝ), (39789346269353/100000000000000 : ℝ), (15852256987163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710525473/5000000000 : ℝ)|^2075 ≤ (5544799590361/12500000000000 : ℝ)^1563
        have hw : |(2710525473/5000000000 : ℝ)|=(2710525473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1248714481/2500000000 : ℝ)|^2075 ≤ (39789346269353/100000000000000 : ℝ)^1563
        have hw : |(1248714481/2500000000 : ℝ)|=(1248714481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2497274111/10000000000 : ℝ)|^2075 ≤ (15852256987163/100000000000000 : ℝ)^1563
        have hw : |(-2497274111/10000000000 : ℝ)|=(2497274111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s1_3 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1080096867/2500000000 : ℝ)*x 0 + (3670417921/10000000000 : ℝ)*x 1 + (5085324051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080096867/2500000000 : ℝ)^2075 ≤ (4102409358563/12500000000000 : ℝ)^1563 := by
    have hnat : (1080096867 : ℕ)^2075*12500000000000^1563 ≤ 4102409358563^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080096867 2500000000 4102409358563 12500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3670417921/10000000000 : ℝ)^2075 ≤ (26431823491573/100000000000000 : ℝ)^1563 := by
    have hnat : (3670417921 : ℕ)^2075*100000000000000^1563 ≤ 26431823491573^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3670417921 10000000000 26431823491573 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5085324051/10000000000 : ℝ)^2075 ≤ (5093612703639/12500000000000 : ℝ)^1563 := by
    have hnat : (5085324051 : ℕ)^2075*12500000000000^1563 ≤ 5093612703639^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085324051 10000000000 5093612703639 12500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080096867/2500000000 : ℝ), (3670417921/10000000000 : ℝ), (5085324051/10000000000 : ℝ)] ![(4102409358563/12500000000000 : ℝ), (26431823491573/100000000000000 : ℝ), (5093612703639/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080096867/2500000000 : ℝ)|^2075 ≤ (4102409358563/12500000000000 : ℝ)^1563
        have hw : |(1080096867/2500000000 : ℝ)|=(1080096867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3670417921/10000000000 : ℝ)|^2075 ≤ (26431823491573/100000000000000 : ℝ)^1563
        have hw : |(3670417921/10000000000 : ℝ)|=(3670417921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5085324051/10000000000 : ℝ)|^2075 ≤ (5093612703639/12500000000000 : ℝ)^1563
        have hw : |(5085324051/10000000000 : ℝ)|=(5085324051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s1_4 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-21109811/100000000 : ℝ)*x 0 + (312798031/625000000 : ℝ)*x 1 + (1140172157/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21109811/100000000 : ℝ)^2075 ≤ (12682421576269/100000000000000 : ℝ)^1563 := by
    have hnat : (21109811 : ℕ)^2075*100000000000000^1563 ≤ 12682421576269^1563*100000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21109811 100000000 12682421576269 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312798031/625000000 : ℝ)^2075 ≤ (9973547505659/25000000000000 : ℝ)^1563 := by
    have hnat : (312798031 : ℕ)^2075*25000000000000^1563 ≤ 9973547505659^1563*625000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312798031 625000000 9973547505659 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140172157/2000000000 : ℝ)^2075 ≤ (23711694192049/50000000000000 : ℝ)^1563 := by
    have hnat : (1140172157 : ℕ)^2075*50000000000000^1563 ≤ 23711694192049^1563*2000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140172157 2000000000 23711694192049 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21109811/100000000 : ℝ), (312798031/625000000 : ℝ), (1140172157/2000000000 : ℝ)] ![(12682421576269/100000000000000 : ℝ), (9973547505659/25000000000000 : ℝ), (23711694192049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21109811/100000000 : ℝ)|^2075 ≤ (12682421576269/100000000000000 : ℝ)^1563
        have hw : |(-21109811/100000000 : ℝ)|=(21109811/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312798031/625000000 : ℝ)|^2075 ≤ (9973547505659/25000000000000 : ℝ)^1563
        have hw : |(312798031/625000000 : ℝ)|=(312798031/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140172157/2000000000 : ℝ)|^2075 ≤ (23711694192049/50000000000000 : ℝ)^1563
        have hw : |(1140172157/2000000000 : ℝ)|=(1140172157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s1_5 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (261888853/500000000 : ℝ)*x 0 + (-223909023/1250000000 : ℝ)*x 1 + (2850430299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261888853/500000000 : ℝ)^2075 ≤ (10594648436543/25000000000000 : ℝ)^1563 := by
    have hnat : (261888853 : ℕ)^2075*25000000000000^1563 ≤ 10594648436543^1563*500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261888853 500000000 10594648436543 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223909023/1250000000 : ℝ)^2075 ≤ (10198019915667/100000000000000 : ℝ)^1563 := by
    have hnat : (223909023 : ℕ)^2075*100000000000000^1563 ≤ 10198019915667^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223909023 1250000000 10198019915667 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2850430299/5000000000 : ℝ)^2075 ≤ (23711693159471/50000000000000 : ℝ)^1563 := by
    have hnat : (2850430299 : ℕ)^2075*50000000000000^1563 ≤ 23711693159471^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850430299 5000000000 23711693159471 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261888853/500000000 : ℝ), (-223909023/1250000000 : ℝ), (2850430299/5000000000 : ℝ)] ![(10594648436543/25000000000000 : ℝ), (10198019915667/100000000000000 : ℝ), (23711693159471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261888853/500000000 : ℝ)|^2075 ≤ (10594648436543/25000000000000 : ℝ)^1563
        have hw : |(261888853/500000000 : ℝ)|=(261888853/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223909023/1250000000 : ℝ)|^2075 ≤ (10198019915667/100000000000000 : ℝ)^1563
        have hw : |(-223909023/1250000000 : ℝ)|=(223909023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2850430299/5000000000 : ℝ)|^2075 ≤ (23711693159471/50000000000000 : ℝ)^1563
        have hw : |(2850430299/5000000000 : ℝ)|=(2850430299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s1_6 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2618888543/5000000000 : ℝ)*x 0 + (89075949/156250000 : ℝ)*x 1 + (-895635973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2618888543/5000000000 : ℝ)^2075 ≤ (42378594025447/100000000000000 : ℝ)^1563 := by
    have hnat : (2618888543 : ℕ)^2075*100000000000000^1563 ≤ 42378594025447^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618888543 5000000000 42378594025447 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89075949/156250000 : ℝ)^2075 ≤ (47423387842961/100000000000000 : ℝ)^1563 := by
    have hnat : (89075949 : ℕ)^2075*100000000000000^1563 ≤ 47423387842961^1563*156250000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89075949 156250000 47423387842961 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895635973/5000000000 : ℝ)^2075 ≤ (2549504529209/25000000000000 : ℝ)^1563 := by
    have hnat : (895635973 : ℕ)^2075*25000000000000^1563 ≤ 2549504529209^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895635973 5000000000 2549504529209 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2618888543/5000000000 : ℝ), (89075949/156250000 : ℝ), (-895635973/5000000000 : ℝ)] ![(42378594025447/100000000000000 : ℝ), (47423387842961/100000000000000 : ℝ), (2549504529209/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2618888543/5000000000 : ℝ)|^2075 ≤ (42378594025447/100000000000000 : ℝ)^1563
        have hw : |(2618888543/5000000000 : ℝ)|=(2618888543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(89075949/156250000 : ℝ)|^2075 ≤ (47423387842961/100000000000000 : ℝ)^1563
        have hw : |(89075949/156250000 : ℝ)|=(89075949/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-895635973/5000000000 : ℝ)|^2075 ≤ (2549504529209/25000000000000 : ℝ)^1563
        have hw : |(-895635973/5000000000 : ℝ)|=(895635973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s1_7 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4322077847/10000000000 : ℝ)*x 0 + (506574549/1000000000 : ℝ)*x 1 + (1845194307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322077847/10000000000 : ℝ)^2075 ≤ (32836323021053/100000000000000 : ℝ)^1563 := by
    have hnat : (4322077847 : ℕ)^2075*100000000000000^1563 ≤ 32836323021053^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322077847 10000000000 32836323021053 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506574549/1000000000 : ℝ)^2075 ≤ (40540758066629/100000000000000 : ℝ)^1563 := by
    have hnat : (506574549 : ℕ)^2075*100000000000000^1563 ≤ 40540758066629^1563*1000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506574549 1000000000 40540758066629 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1845194307/5000000000 : ℝ)^2075 ≤ (26622918900373/100000000000000 : ℝ)^1563 := by
    have hnat : (1845194307 : ℕ)^2075*100000000000000^1563 ≤ 26622918900373^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845194307 5000000000 26622918900373 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322077847/10000000000 : ℝ), (506574549/1000000000 : ℝ), (1845194307/5000000000 : ℝ)] ![(32836323021053/100000000000000 : ℝ), (40540758066629/100000000000000 : ℝ), (26622918900373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322077847/10000000000 : ℝ)|^2075 ≤ (32836323021053/100000000000000 : ℝ)^1563
        have hw : |(4322077847/10000000000 : ℝ)|=(4322077847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506574549/1000000000 : ℝ)|^2075 ≤ (40540758066629/100000000000000 : ℝ)^1563
        have hw : |(506574549/1000000000 : ℝ)|=(506574549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1845194307/5000000000 : ℝ)|^2075 ≤ (26622918900373/100000000000000 : ℝ)^1563
        have hw : |(1845194307/5000000000 : ℝ)|=(1845194307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1107_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (559/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5451/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10299/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (559/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (559/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (559/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (559/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (559/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (559/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (269/100000 : ℝ) ^ (8299/2048 : ℝ) ≤ (3843471957/100000000000000000000 : ℝ) := by
    have hpowers : (269/100000 : ℝ)^8299 ≤ (3843471957/100000000000000000000 : ℝ)^2048 := by
      have hnat : (269 : ℕ)^8299*100000000000000000000^2048 ≤ 3843471957^2048*100000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        269 100000 3843471957 100000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (269/100000 : ℝ)) (X := (3843471957/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (559/2000 : ℝ) ^ (8299/2048 : ℝ) ≤ (570956289185786073/100000000000000000000 : ℝ) := by
    have hpowers : (559/2000 : ℝ)^8299 ≤ (570956289185786073/100000000000000000000 : ℝ)^2048 := by
      have hnat : (559 : ℕ)^8299*100000000000000000000^2048 ≤ 570956289185786073^2048*2000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        559 2000 570956289185786073 100000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (559/2000 : ℝ)) (X := (570956289185786073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000003843471957/50000000000000000000 : ℝ) ≤ (39062500000741/39062500000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (50000000003843471957/50000000000000000000 : ℝ)^2048 ≤ (39062500000741/39062500000000 : ℝ)^8299 := by
      have hnat : (50000000003843471957 : ℕ)^2048*39062500000000^8299 ≤ 39062500000741^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000003843471957 50000000000000000000 39062500000741 39062500000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39062500000741/39062500000000 : ℝ)) (X := (50000000003843471957/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10057095629302925803/10000000000000000000 : ℝ) ≤ (10014059675547427/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (10057095629302925803/10000000000000000000 : ℝ)^2048 ≤ (10014059675547427/10000000000000000 : ℝ)^8299 := by
      have hnat : (10057095629302925803 : ℕ)^2048*10000000000000000^8299 ≤ 10014059675547427^8299*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10057095629302925803 10000000000000000000 10014059675547427 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014059675547427/10000000000000000 : ℝ)) (X := (10057095629302925803/10000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50570956289185786073/50000000000000000000 : ℝ) ≤ (5014059675452579/5000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (50570956289185786073/50000000000000000000 : ℝ)^2048 ≤ (5014059675452579/5000000000000000 : ℝ)^8299 := by
      have hnat : (50570956289185786073 : ℕ)^2048*5000000000000000^8299 ≤ 5014059675452579^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50570956289185786073 50000000000000000000 5014059675452579 5000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014059675452579/5000000000000000 : ℝ)) (X := (50570956289185786073/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3843471957/100000000000000000000 : ℝ) ≤ ((46133739316651419283/46135000000000000000 : ℝ)+2*(4686558452577/922700000000000 : ℝ)*(269/100000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (46133739316651419283/46135000000000000000 : ℝ)+2*(4686558452577/922700000000000 : ℝ)*(269/100000 : ℝ)=(39062500000741/39062500000000 : ℝ) by norm_num, show 1+2*(3843471957/100000000000000000000 : ℝ)=(50000000003843471957/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(570956289185786073/100000000000000000000 : ℝ)+(3843471957/100000000000000000000 : ℝ) ≤ ((46133739316651419283/46135000000000000000 : ℝ)+(4686558452577/922700000000000 : ℝ)*((559/2000 : ℝ)+(269/100000 : ℝ)))^(8299/2048 : ℝ) := by
    rw [show (46133739316651419283/46135000000000000000 : ℝ)+(4686558452577/922700000000000 : ℝ)*((559/2000 : ℝ)+(269/100000 : ℝ))=(10014059675547427/10000000000000000 : ℝ) by norm_num, show 1+(570956289185786073/100000000000000000000 : ℝ)+(3843471957/100000000000000000000 : ℝ)=(10057095629302925803/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(570956289185786073/100000000000000000000 : ℝ) ≤ ((46133739316651419283/46135000000000000000 : ℝ)+2*(4686558452577/922700000000000 : ℝ)*(559/2000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (46133739316651419283/46135000000000000000 : ℝ)+2*(4686558452577/922700000000000 : ℝ)*(559/2000 : ℝ)=(5014059675452579/5000000000000000 : ℝ) by norm_num, show 1+2*(570956289185786073/100000000000000000000 : ℝ)=(50570956289185786073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46133739316651419283/46135000000000000000 : ℝ)*(X 1 0+X 2 0)+(4686558452577/922700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (269/100000 : ℝ)) (hi := (559/2000 : ℝ)) (c := (46133739316651419283/46135000000000000000 : ℝ)) (alpha := (4686558452577/922700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46133739316651419283/46135000000000000000 : ℝ)*(X 0 1+X 2 1)+(4686558452577/922700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (269/100000 : ℝ)) (hi := (559/2000 : ℝ)) (c := (46133739316651419283/46135000000000000000 : ℝ)) (alpha := (4686558452577/922700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46133739316651419283/46135000000000000000 : ℝ)*(X 0 2+X 1 2)+(4686558452577/922700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (269/100000 : ℝ)) (hi := (559/2000 : ℝ)) (c := (46133739316651419283/46135000000000000000 : ℝ)) (alpha := (4686558452577/922700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2110124843/10000000000 : ℝ)*X 0 0+(2855484361/5000000000 : ℝ)*X 0 1+(1248714767/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5421049727/10000000000 : ℝ)*X 1 0+(-312159277/1250000000 : ℝ)*X 1 1+(4994859093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2710525473/5000000000 : ℝ)*X 2 0+(1248714481/2500000000 : ℝ)*X 2 1+(-2497274111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1080096867/2500000000 : ℝ)*X 0 0+(3670417921/10000000000 : ℝ)*X 0 1+(5085324051/10000000000 : ℝ)*X 0 2+(1080096867/2500000000 : ℝ)*X 1 0+(3670417921/10000000000 : ℝ)*X 1 1+(5085324051/10000000000 : ℝ)*X 1 2+(1080096867/2500000000 : ℝ)*X 2 0+(3670417921/10000000000 : ℝ)*X 2 1+(5085324051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21109811/100000000 : ℝ)*X 0 0+(312798031/625000000 : ℝ)*X 0 1+(1140172157/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((261888853/500000000 : ℝ)*X 1 0+(-223909023/1250000000 : ℝ)*X 1 1+(2850430299/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2618888543/5000000000 : ℝ)*X 2 0+(89075949/156250000 : ℝ)*X 2 1+(-895635973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322077847/10000000000 : ℝ)*X 0 0+(506574549/1000000000 : ℝ)*X 0 1+(1845194307/5000000000 : ℝ)*X 0 2+(4322077847/10000000000 : ℝ)*X 1 0+(506574549/1000000000 : ℝ)*X 1 1+(1845194307/5000000000 : ℝ)*X 1 2+(4322077847/10000000000 : ℝ)*X 2 0+(506574549/1000000000 : ℝ)*X 2 1+(1845194307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9142573088011069962629447211/1153375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50069357/20000000000000 : ℝ)*(base1) + (38026951/2500000000000 : ℝ)*(base19) + (91754433/5000000000000 : ℝ)*(base23) + (92880223/100000000000000 : ℝ)*(upper3) + (106816233/50000000000000 : ℝ)*(upper5) + (1051607209723939/100000000000000 : ℝ)*(major0) + (1051607209723939/100000000000000 : ℝ)*(major1) + (1051607209723939/100000000000000 : ℝ)*(major2) + (174554992769837/12500000000000 : ℝ)*(sp0) + (139644591699261/10000000000000 : ℝ)*(sp1) + (1396445602981989/100000000000000 : ℝ)*(sp2) + (70676362490891/10000000000000 : ℝ)*(sp3) + (3873129369/50000000000000 : ℝ)*(sp4) + (710473713/25000000000000 : ℝ)*(sp7) + (44172919821909/6250000000000 : ℝ)*(f.failure) + (27928948761413/2000000000000 : ℝ)*(f.sum) + (210281908519657/46135000000000000000000000000 : ℝ)*base66 + (31904673055013534263/4613500000000000000000000000000000 : ℝ)*base68 + (8899160253234534263/4613500000000000000000000000000000 : ℝ)*base70 + (15625397805807534263/4613500000000000000000000000000000 : ℝ)*base72 + (301726222766247/46135000000000000000000000000 : ℝ)*base74 + (23357214468406534263/4613500000000000000000000000000000 : ℝ)*base76 + (10033347346881534263/4613500000000000000000000000000000 : ℝ)*base78 + (14403304240660465737/4613500000000000000000000000000000 : ℝ)*base79 + (94808461922831/23067500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (228241/25000000000000000000 : ℝ)*base90 + (228241/25000000000000000000 : ℝ)*base92 + (228241/25000000000000000000 : ℝ)*base94 + (3/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (861624896676207814460139477/115337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88051183/100000000000000 : ℝ)*(base1) + (832389967/50000000000000 : ℝ)*(base19) + (1688569721/100000000000000 : ℝ)*(base23) + (167129353/100000000000000 : ℝ)*(upper3) + (337829/200000000000 : ℝ)*(upper5) + (54091887046073/5000000000000 : ℝ)*(major0) + (54091887046073/5000000000000 : ℝ)*(major1) + (54091887046073/5000000000000 : ℝ)*(major2) + (6678763957/100000000000000 : ℝ)*(sp1) + (1430961467/20000000000000 : ℝ)*(sp2) + (1436591195198837/100000000000000 : ℝ)*(sp4) + (1436582763603763/100000000000000 : ℝ)*(sp5) + (1436582263770599/100000000000000 : ℝ)*(sp6) + (727084037628539/100000000000000 : ℝ)*(sp7) + (363542062839861/50000000000000 : ℝ)*(f.failure) + (718295553573827/50000000000000 : ℝ)*(f.sum) + (5648897303607/9227000000000000000000000000 : ℝ)*base66 + (958015793719174341/230675000000000000000000000000000 : ℝ)*base68 + (300320084593750659/230675000000000000000000000000000 : ℝ)*base69 + (99106881522575659/230675000000000000000000000000000 : ℝ)*base71 + (10809416820439/4613500000000000000000000000 : ℝ)*base74 + (37026931411499341/230675000000000000000000000000000 : ℝ)*base76 + (982485958038299341/230675000000000000000000000000000 : ℝ)*base78 + (772307252299274341/230675000000000000000000000000000 : ℝ)*base80 + (3202407257639/1845400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1560511/200000000000000000000 : ℝ)*base89 + (1560511/200000000000000000000 : ℝ)*base91 + (1560511/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1107_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (559/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10299/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1107_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1107_s2_0 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082630997/5000000000 : ℝ)*x 0 + (275880393/500000000 : ℝ)*x 1 + (206127809/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082630997/5000000000 : ℝ)^2075 ≤ (163964634661/1250000000000 : ℝ)^1563 := by
    have hnat : (1082630997 : ℕ)^2075*1250000000000^1563 ≤ 163964634661^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082630997 5000000000 163964634661 1250000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275880393/500000000 : ℝ)^2075 ≤ (22705173204187/50000000000000 : ℝ)^1563 := by
    have hnat : (275880393 : ℕ)^2075*50000000000000^1563 ≤ 22705173204187^1563*500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275880393 500000000 22705173204187 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206127809/400000000 : ℝ)^2075 ≤ (41472482816563/100000000000000 : ℝ)^1563 := by
    have hnat : (206127809 : ℕ)^2075*100000000000000^1563 ≤ 41472482816563^1563*400000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206127809 400000000 41472482816563 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082630997/5000000000 : ℝ), (275880393/500000000 : ℝ), (206127809/400000000 : ℝ)] ![(163964634661/1250000000000 : ℝ), (22705173204187/50000000000000 : ℝ), (41472482816563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082630997/5000000000 : ℝ)|^2075 ≤ (163964634661/1250000000000 : ℝ)^1563
        have hw : |(-1082630997/5000000000 : ℝ)|=(1082630997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(275880393/500000000 : ℝ)|^2075 ≤ (22705173204187/50000000000000 : ℝ)^1563
        have hw : |(275880393/500000000 : ℝ)|=(275880393/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206127809/400000000 : ℝ)|^2075 ≤ (41472482816563/100000000000000 : ℝ)^1563
        have hw : |(206127809/400000000 : ℝ)|=(206127809/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s2_1 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5375385013/10000000000 : ℝ)*x 0 + (-147186561/625000000 : ℝ)*x 1 + (2576598217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375385013/10000000000 : ℝ)^2075 ≤ (43863011490147/100000000000000 : ℝ)^1563 := by
    have hnat : (5375385013 : ℕ)^2075*100000000000000^1563 ≤ 43863011490147^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375385013 10000000000 43863011490147 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147186561/625000000 : ℝ)^2075 ≤ (1466449276291/10000000000000 : ℝ)^1563 := by
    have hnat : (147186561 : ℕ)^2075*10000000000000^1563 ≤ 1466449276291^1563*625000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147186561 625000000 1466449276291 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576598217/5000000000 : ℝ)^2075 ≤ (20736247866889/50000000000000 : ℝ)^1563 := by
    have hnat : (2576598217 : ℕ)^2075*50000000000000^1563 ≤ 20736247866889^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576598217 5000000000 20736247866889 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375385013/10000000000 : ℝ), (-147186561/625000000 : ℝ), (2576598217/5000000000 : ℝ)] ![(43863011490147/100000000000000 : ℝ), (1466449276291/10000000000000 : ℝ), (20736247866889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375385013/10000000000 : ℝ)|^2075 ≤ (43863011490147/100000000000000 : ℝ)^1563
        have hw : |(5375385013/10000000000 : ℝ)|=(5375385013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-147186561/625000000 : ℝ)|^2075 ≤ (1466449276291/10000000000000 : ℝ)^1563
        have hw : |(-147186561/625000000 : ℝ)|=(147186561/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576598217/5000000000 : ℝ)|^2075 ≤ (20736247866889/50000000000000 : ℝ)^1563
        have hw : |(2576598217/5000000000 : ℝ)|=(2576598217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s2_2 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5375384963/10000000000 : ℝ)*x 0 + (644149561/1250000000 : ℝ)*x 1 + (-2354984971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375384963/10000000000 : ℝ)^2075 ≤ (21931505474249/50000000000000 : ℝ)^1563 := by
    have hnat : (5375384963 : ℕ)^2075*50000000000000^1563 ≤ 21931505474249^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375384963 10000000000 21931505474249 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (644149561/1250000000 : ℝ)^2075 ≤ (20736248155363/50000000000000 : ℝ)^1563 := by
    have hnat : (644149561 : ℕ)^2075*50000000000000^1563 ≤ 20736248155363^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644149561 1250000000 20736248155363 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2354984971/10000000000 : ℝ)^2075 ≤ (1833061590197/12500000000000 : ℝ)^1563 := by
    have hnat : (2354984971 : ℕ)^2075*12500000000000^1563 ≤ 1833061590197^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2354984971 10000000000 1833061590197 12500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375384963/10000000000 : ℝ), (644149561/1250000000 : ℝ), (-2354984971/10000000000 : ℝ)] ![(21931505474249/50000000000000 : ℝ), (20736248155363/50000000000000 : ℝ), (1833061590197/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375384963/10000000000 : ℝ)|^2075 ≤ (21931505474249/50000000000000 : ℝ)^1563
        have hw : |(5375384963/10000000000 : ℝ)|=(5375384963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(644149561/1250000000 : ℝ)|^2075 ≤ (20736248155363/50000000000000 : ℝ)^1563
        have hw : |(644149561/1250000000 : ℝ)|=(644149561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2354984971/10000000000 : ℝ)|^2075 ≤ (1833061590197/12500000000000 : ℝ)^1563
        have hw : |(-2354984971/10000000000 : ℝ)|=(2354984971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s2_3 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4358119401/10000000000 : ℝ)*x 0 + (2006483743/5000000000 : ℝ)*x 1 + (236649033/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358119401/10000000000 : ℝ)^2075 ≤ (6640067091829/20000000000000 : ℝ)^1563 := by
    have hnat : (4358119401 : ℕ)^2075*20000000000000^1563 ≤ 6640067091829^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358119401 10000000000 6640067091829 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006483743/5000000000 : ℝ)^2075 ≤ (29755745022361/100000000000000 : ℝ)^1563 := by
    have hnat : (2006483743 : ℕ)^2075*100000000000000^1563 ≤ 29755745022361^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006483743 5000000000 29755745022361 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236649033/500000000 : ℝ)^2075 ≤ (1157622484519/3125000000000 : ℝ)^1563 := by
    have hnat : (236649033 : ℕ)^2075*3125000000000^1563 ≤ 1157622484519^1563*500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236649033 500000000 1157622484519 3125000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358119401/10000000000 : ℝ), (2006483743/5000000000 : ℝ), (236649033/500000000 : ℝ)] ![(6640067091829/20000000000000 : ℝ), (29755745022361/100000000000000 : ℝ), (1157622484519/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358119401/10000000000 : ℝ)|^2075 ≤ (6640067091829/20000000000000 : ℝ)^1563
        have hw : |(4358119401/10000000000 : ℝ)|=(4358119401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2006483743/5000000000 : ℝ)|^2075 ≤ (29755745022361/100000000000000 : ℝ)^1563
        have hw : |(2006483743/5000000000 : ℝ)|=(2006483743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(236649033/500000000 : ℝ)|^2075 ≤ (1157622484519/3125000000000 : ℝ)^1563
        have hw : |(236649033/500000000 : ℝ)|=(236649033/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s2_4 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-4330749/20000000 : ℝ)*x 0 + (2577885453/5000000000 : ℝ)*x 1 + (2757502983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330749/20000000 : ℝ)^2075 ≤ (2623615121089/20000000000000 : ℝ)^1563 := by
    have hnat : (4330749 : ℕ)^2075*20000000000000^1563 ≤ 2623615121089^1563*20000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330749 20000000 2623615121089 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2577885453/5000000000 : ℝ)^2075 ≤ (41500004195207/100000000000000 : ℝ)^1563 := by
    have hnat : (2577885453 : ℕ)^2075*100000000000000^1563 ≤ 41500004195207^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577885453 5000000000 41500004195207 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2757502983/5000000000 : ℝ)^2075 ≤ (11345480046357/25000000000000 : ℝ)^1563 := by
    have hnat : (2757502983 : ℕ)^2075*25000000000000^1563 ≤ 11345480046357^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757502983 5000000000 11345480046357 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4330749/20000000 : ℝ), (2577885453/5000000000 : ℝ), (2757502983/5000000000 : ℝ)] ![(2623615121089/20000000000000 : ℝ), (41500004195207/100000000000000 : ℝ), (11345480046357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4330749/20000000 : ℝ)|^2075 ≤ (2623615121089/20000000000000 : ℝ)^1563
        have hw : |(-4330749/20000000 : ℝ)|=(4330749/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2577885453/5000000000 : ℝ)|^2075 ≤ (41500004195207/100000000000000 : ℝ)^1563
        have hw : |(2577885453/5000000000 : ℝ)|=(2577885453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2757502983/5000000000 : ℝ)|^2075 ≤ (11345480046357/25000000000000 : ℝ)^1563
        have hw : |(2757502983/5000000000 : ℝ)|=(2757502983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s2_5 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5283141971/10000000000 : ℝ)*x 0 + (-996587429/5000000000 : ℝ)*x 1 + (5515006051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283141971/10000000000 : ℝ)^2075 ≤ (1339580118851/3125000000000 : ℝ)^1563 := by
    have hnat : (5283141971 : ℕ)^2075*3125000000000^1563 ≤ 1339580118851^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283141971 10000000000 1339580118851 3125000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (996587429/5000000000 : ℝ)^2075 ≤ (5875757531493/50000000000000 : ℝ)^1563 := by
    have hnat : (996587429 : ℕ)^2075*50000000000000^1563 ≤ 5875757531493^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996587429 5000000000 5875757531493 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5515006051/10000000000 : ℝ)^2075 ≤ (22690960556999/50000000000000 : ℝ)^1563 := by
    have hnat : (5515006051 : ℕ)^2075*50000000000000^1563 ≤ 22690960556999^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515006051 10000000000 22690960556999 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283141971/10000000000 : ℝ), (-996587429/5000000000 : ℝ), (5515006051/10000000000 : ℝ)] ![(1339580118851/3125000000000 : ℝ), (5875757531493/50000000000000 : ℝ), (22690960556999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283141971/10000000000 : ℝ)|^2075 ≤ (1339580118851/3125000000000 : ℝ)^1563
        have hw : |(5283141971/10000000000 : ℝ)|=(5283141971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-996587429/5000000000 : ℝ)|^2075 ≤ (5875757531493/50000000000000 : ℝ)^1563
        have hw : |(-996587429/5000000000 : ℝ)|=(996587429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5515006051/10000000000 : ℝ)|^2075 ≤ (22690960556999/50000000000000 : ℝ)^1563
        have hw : |(5515006051/10000000000 : ℝ)|=(5515006051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s2_6 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2641571057/5000000000 : ℝ)*x 0 + (689375749/1250000000 : ℝ)*x 1 + (-249146843/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641571057/5000000000 : ℝ)^2075 ≤ (42866565343589/100000000000000 : ℝ)^1563 := by
    have hnat : (2641571057 : ℕ)^2075*100000000000000^1563 ≤ 42866565343589^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641571057 5000000000 42866565343589 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (689375749/1250000000 : ℝ)^2075 ≤ (45381920469461/100000000000000 : ℝ)^1563 := by
    have hnat : (689375749 : ℕ)^2075*100000000000000^1563 ≤ 45381920469461^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689375749 1250000000 45381920469461 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249146843/1250000000 : ℝ)^2075 ≤ (5875757085341/50000000000000 : ℝ)^1563 := by
    have hnat : (249146843 : ℕ)^2075*50000000000000^1563 ≤ 5875757085341^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249146843 1250000000 5875757085341 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641571057/5000000000 : ℝ), (689375749/1250000000 : ℝ), (-249146843/1250000000 : ℝ)] ![(42866565343589/100000000000000 : ℝ), (45381920469461/100000000000000 : ℝ), (5875757085341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641571057/5000000000 : ℝ)|^2075 ≤ (42866565343589/100000000000000 : ℝ)^1563
        have hw : |(2641571057/5000000000 : ℝ)|=(2641571057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(689375749/1250000000 : ℝ)|^2075 ≤ (45381920469461/100000000000000 : ℝ)^1563
        have hw : |(689375749/1250000000 : ℝ)|=(689375749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249146843/1250000000 : ℝ)|^2075 ≤ (5875757085341/50000000000000 : ℝ)^1563
        have hw : |(-249146843/1250000000 : ℝ)|=(249146843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s2_7 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4358343023/10000000000 : ℝ)*x 0 + (1181973153/2500000000 : ℝ)*x 1 + (200905319/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358343023/10000000000 : ℝ)^2075 ≤ (8300649271103/25000000000000 : ℝ)^1563 := by
    have hnat : (4358343023 : ℕ)^2075*25000000000000^1563 ≤ 8300649271103^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358343023 10000000000 8300649271103 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1181973153/2500000000 : ℝ)^2075 ≤ (36991060858981/100000000000000 : ℝ)^1563 := by
    have hnat : (1181973153 : ℕ)^2075*100000000000000^1563 ≤ 36991060858981^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181973153 2500000000 36991060858981 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200905319/500000000 : ℝ)^2075 ≤ (29806342052283/100000000000000 : ℝ)^1563 := by
    have hnat : (200905319 : ℕ)^2075*100000000000000^1563 ≤ 29806342052283^1563*500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200905319 500000000 29806342052283 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358343023/10000000000 : ℝ), (1181973153/2500000000 : ℝ), (200905319/500000000 : ℝ)] ![(8300649271103/25000000000000 : ℝ), (36991060858981/100000000000000 : ℝ), (29806342052283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358343023/10000000000 : ℝ)|^2075 ≤ (8300649271103/25000000000000 : ℝ)^1563
        have hw : |(4358343023/10000000000 : ℝ)|=(4358343023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1181973153/2500000000 : ℝ)|^2075 ≤ (36991060858981/100000000000000 : ℝ)^1563
        have hw : |(1181973153/2500000000 : ℝ)|=(1181973153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200905319/500000000 : ℝ)|^2075 ≤ (29806342052283/100000000000000 : ℝ)^1563
        have hw : |(200905319/500000000 : ℝ)|=(200905319/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1107_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10299/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8909/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16609/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10299/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5451/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10299/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5451/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10299/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5451/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10299/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5451/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10299/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5451/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10299/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5451/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5451/100000 : ℝ) ^ (8299/2048 : ℝ) ≤ (189596603484939/25000000000000000000 : ℝ) := by
    have hpowers : (5451/100000 : ℝ)^8299 ≤ (189596603484939/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5451 : ℕ)^8299*25000000000000000000^2048 ≤ 189596603484939^2048*100000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5451 100000 189596603484939 25000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5451/100000 : ℝ)) (X := (189596603484939/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10299/50000 : ℝ) ^ (8299/2048 : ℝ) ≤ (8287437363137727/5000000000000000000 : ℝ) := by
    have hpowers : (10299/50000 : ℝ)^8299 ≤ (8287437363137727/5000000000000000000 : ℝ)^2048 := by
      have hnat : (10299 : ℕ)^8299*5000000000000000000^2048 ≤ 8287437363137727^2048*50000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10299 50000 8287437363137727 5000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10299/50000 : ℝ)) (X := (8287437363137727/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500189596603484939/12500000000000000000 : ℝ) ≤ (2000007486041709/2000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (12500189596603484939/12500000000000000000 : ℝ)^2048 ≤ (2000007486041709/2000000000000000 : ℝ)^8299 := by
      have hnat : (12500189596603484939 : ℕ)^2048*2000000000000000^8299 ≤ 2000007486041709^8299*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500189596603484939 12500000000000000000 2000007486041709 2000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000007486041709/2000000000000000 : ℝ)) (X := (12500189596603484939/12500000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12520813391709586787/12500000000000000000 : ℝ) ≤ (10004106434237877/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (12520813391709586787/12500000000000000000 : ℝ)^2048 ≤ (10004106434237877/10000000000000000 : ℝ)^8299 := by
      have hnat : (12520813391709586787 : ℕ)^2048*10000000000000000^8299 ≤ 10004106434237877^8299*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12520813391709586787 12500000000000000000 10004106434237877 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004106434237877/10000000000000000 : ℝ)) (X := (12520813391709586787/12500000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2508287437363137727/2500000000000000000 : ℝ) ≤ (10008175438267209/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (2508287437363137727/2500000000000000000 : ℝ)^2048 ≤ (10008175438267209/10000000000000000 : ℝ)^8299 := by
      have hnat : (2508287437363137727 : ℕ)^2048*10000000000000000^8299 ≤ 10008175438267209^8299*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2508287437363137727 2500000000000000000 10008175438267209 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008175438267209/10000000000000000 : ℝ)) (X := (2508287437363137727/2500000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(189596603484939/25000000000000000000 : ℝ) ≤ ((89973979009768897/90000000000000000 : ℝ)+2*(1813281653/675000000000 : ℝ)*(5451/100000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (89973979009768897/90000000000000000 : ℝ)+2*(1813281653/675000000000 : ℝ)*(5451/100000 : ℝ)=(2000007486041709/2000000000000000 : ℝ) by norm_num, show 1+2*(189596603484939/25000000000000000000 : ℝ)=(12500189596603484939/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8287437363137727/5000000000000000000 : ℝ)+(189596603484939/25000000000000000000 : ℝ) ≤ ((89973979009768897/90000000000000000 : ℝ)+(1813281653/675000000000 : ℝ)*((10299/50000 : ℝ)+(5451/100000 : ℝ)))^(8299/2048 : ℝ) := by
    rw [show (89973979009768897/90000000000000000 : ℝ)+(1813281653/675000000000 : ℝ)*((10299/50000 : ℝ)+(5451/100000 : ℝ))=(10004106434237877/10000000000000000 : ℝ) by norm_num, show 1+(8287437363137727/5000000000000000000 : ℝ)+(189596603484939/25000000000000000000 : ℝ)=(12520813391709586787/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8287437363137727/5000000000000000000 : ℝ) ≤ ((89973979009768897/90000000000000000 : ℝ)+2*(1813281653/675000000000 : ℝ)*(10299/50000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (89973979009768897/90000000000000000 : ℝ)+2*(1813281653/675000000000 : ℝ)*(10299/50000 : ℝ)=(10008175438267209/10000000000000000 : ℝ) by norm_num, show 1+2*(8287437363137727/5000000000000000000 : ℝ)=(2508287437363137727/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (89973979009768897/90000000000000000 : ℝ)*(X 1 0+X 2 0)+(1813281653/675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (5451/100000 : ℝ)) (hi := (10299/50000 : ℝ)) (c := (89973979009768897/90000000000000000 : ℝ)) (alpha := (1813281653/675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (89973979009768897/90000000000000000 : ℝ)*(X 0 1+X 2 1)+(1813281653/675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (5451/100000 : ℝ)) (hi := (10299/50000 : ℝ)) (c := (89973979009768897/90000000000000000 : ℝ)) (alpha := (1813281653/675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (89973979009768897/90000000000000000 : ℝ)*(X 0 2+X 1 2)+(1813281653/675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (5451/100000 : ℝ)) (hi := (10299/50000 : ℝ)) (c := (89973979009768897/90000000000000000 : ℝ)) (alpha := (1813281653/675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1082630997/5000000000 : ℝ)*X 0 0+(275880393/500000000 : ℝ)*X 0 1+(206127809/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5375385013/10000000000 : ℝ)*X 1 0+(-147186561/625000000 : ℝ)*X 1 1+(2576598217/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375384963/10000000000 : ℝ)*X 2 0+(644149561/1250000000 : ℝ)*X 2 1+(-2354984971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358119401/10000000000 : ℝ)*X 0 0+(2006483743/5000000000 : ℝ)*X 0 1+(236649033/500000000 : ℝ)*X 0 2+(4358119401/10000000000 : ℝ)*X 1 0+(2006483743/5000000000 : ℝ)*X 1 1+(236649033/500000000 : ℝ)*X 1 2+(4358119401/10000000000 : ℝ)*X 2 0+(2006483743/5000000000 : ℝ)*X 2 1+(236649033/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-4330749/20000000 : ℝ)*X 0 0+(2577885453/5000000000 : ℝ)*X 0 1+(2757502983/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5283141971/10000000000 : ℝ)*X 1 0+(-996587429/5000000000 : ℝ)*X 1 1+(5515006051/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2641571057/5000000000 : ℝ)*X 2 0+(689375749/1250000000 : ℝ)*X 2 1+(-249146843/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358343023/10000000000 : ℝ)*X 0 0+(1181973153/2500000000 : ℝ)*X 0 1+(200905319/500000000 : ℝ)*X 0 2+(4358343023/10000000000 : ℝ)*X 1 0+(1181973153/2500000000 : ℝ)*X 1 1+(200905319/500000000 : ℝ)*X 1 2+(4358343023/10000000000 : ℝ)*X 2 0+(1181973153/2500000000 : ℝ)*X 2 1+(200905319/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1112066978688459914157623/250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140429491/100000000000000 : ℝ)*(base19) + (4934667/100000000000000 : ℝ)*(base23) + (47922181/100000000000000 : ℝ)*(upper2) + (1743379/2000000000000 : ℝ)*(upper3) + (21407013/20000000000000 : ℝ)*(upper4) + (1033256994800841/50000000000000 : ℝ)*(major0) + (1033256994800841/50000000000000 : ℝ)*(major1) + (1033256994800841/50000000000000 : ℝ)*(major2) + (1372075734330001/50000000000000 : ℝ)*(sp0) + (1372079984929809/50000000000000 : ℝ)*(sp1) + (1372080052677221/50000000000000 : ℝ)*(sp2) + (694432593664299/50000000000000 : ℝ)*(sp3) + (4320814553/50000000000000 : ℝ)*(sp4) + (50666201/2000000000000 : ℝ)*(sp7) + (1388867720638647/100000000000000 : ℝ)*(f.failure) + (686040027572277/25000000000000 : ℝ)*(f.sum) + (1765857061/937500000000000000000000 : ℝ)*base65 + (7248167626547459/1500000000000000000000000000000 : ℝ)*base67 + (11087793313547459/1500000000000000000000000000000 : ℝ)*base69 + (7801075129547459/1500000000000000000000000000000 : ℝ)*base71 + (8921944631/3750000000000000000000000 : ℝ)*base74 + (2156695264547459/1500000000000000000000000000000 : ℝ)*base75 + (6299649211547459/1500000000000000000000000000000 : ℝ)*base77 + (15274376716547459/1500000000000000000000000000000 : ℝ)*base79 + (12074337547/7500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3943803/400000000000000000000 : ℝ)*base90 + (3943803/400000000000000000000 : ℝ)*base92 + (3943803/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1196723201810591749242353/500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (241981233/50000000000000 : ℝ)*(base19) + (155729717/25000000000000 : ℝ)*(base23) + (17270211/20000000000000 : ℝ)*(upper3) + (1863523/12500000000000 : ℝ)*(lower4) + (33250683/100000000000000 : ℝ)*(upper5) + (2096283734528751/100000000000000 : ℝ)*(major0) + (2096283734528751/100000000000000 : ℝ)*(major1) + (2096283734528751/100000000000000 : ℝ)*(major2) + (4266531163/100000000000000 : ℝ)*(sp1) + (6293544967/100000000000000 : ℝ)*(sp2) + (1391845973229661/50000000000000 : ℝ)*(sp4) + (695921798991423/25000000000000 : ℝ)*(sp5) + (1391842514997743/50000000000000 : ℝ)*(sp6) + (88054715176039/6250000000000 : ℝ)*(sp7) + (88054715176039/6250000000000 : ℝ)*(f.failure) + (1391845973229661/50000000000000 : ℝ)*(f.sum) + (22506647197/3750000000000000000000000 : ℝ)*base65 + (17172549284152549/3000000000000000000000000000000 : ℝ)*base67 + (209623628152549/3000000000000000000000000000000 : ℝ)*base69 + (32243751935152549/3000000000000000000000000000000 : ℝ)*base71 + (12299605777/3750000000000000000000000 : ℝ)*base73 + (43758943682152549/3000000000000000000000000000000 : ℝ)*base75 + (18672623213152549/3000000000000000000000000000000 : ℝ)*base77 + (35300522456152549/3000000000000000000000000000000 : ℝ)*base79 + (27045999617/15000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (59611/25000000000000000000 : ℝ)*base90 + (59611/25000000000000000000 : ℝ)*base92 + (59611/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1107_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10299/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8909/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16609/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1107_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1107_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8909/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16609/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1107_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1107_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1107_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8909/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16609/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1107_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
