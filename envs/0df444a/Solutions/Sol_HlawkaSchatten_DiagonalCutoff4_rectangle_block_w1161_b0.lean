-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1161_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:40:16.893543+00:00
-- url     : https://prove2.me/submissions/2921ca68-efcd-418d-aea1-81d4d42b020a

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
theorem support_rectangle_w1161_s0_0 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885811831/10000000000 : ℝ)*x 0 + (3024974621/5000000000 : ℝ)*x 1 + (4782870511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885811831/10000000000 : ℝ)^4177 ≤ (5484940462709/50000000000000 : ℝ)^3153 := by
    have hnat : (1885811831 : ℕ)^4177*50000000000000^3153 ≤ 5484940462709^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885811831 10000000000 5484940462709 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3024974621/5000000000 : ℝ)^4177 ≤ (12847281383289/25000000000000 : ℝ)^3153 := by
    have hnat : (3024974621 : ℕ)^4177*25000000000000^3153 ≤ 12847281383289^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3024974621 5000000000 12847281383289 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4782870511/10000000000 : ℝ)^4177 ≤ (37640993525099/100000000000000 : ℝ)^3153 := by
    have hnat : (4782870511 : ℕ)^4177*100000000000000^3153 ≤ 37640993525099^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4782870511 10000000000 37640993525099 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885811831/10000000000 : ℝ), (3024974621/5000000000 : ℝ), (4782870511/10000000000 : ℝ)] ![(5484940462709/50000000000000 : ℝ), (12847281383289/25000000000000 : ℝ), (37640993525099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885811831/10000000000 : ℝ)|^4177 ≤ (5484940462709/50000000000000 : ℝ)^3153
        have hw : |(-1885811831/10000000000 : ℝ)|=(1885811831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3024974621/5000000000 : ℝ)|^4177 ≤ (12847281383289/25000000000000 : ℝ)^3153
        have hw : |(3024974621/5000000000 : ℝ)|=(3024974621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4782870511/10000000000 : ℝ)|^4177 ≤ (37640993525099/100000000000000 : ℝ)^3153
        have hw : |(4782870511/10000000000 : ℝ)|=(4782870511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s0_1 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5515723259/10000000000 : ℝ)*x 0 + (-2612428441/10000000000 : ℝ)*x 1 + (4782870511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5515723259/10000000000 : ℝ)^4177 ≤ (45465574811841/100000000000000 : ℝ)^3153 := by
    have hnat : (5515723259 : ℕ)^4177*100000000000000^3153 ≤ 45465574811841^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515723259 10000000000 45465574811841 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612428441/10000000000 : ℝ)^4177 ≤ (16893431645223/100000000000000 : ℝ)^3153 := by
    have hnat : (2612428441 : ℕ)^4177*100000000000000^3153 ≤ 16893431645223^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612428441 10000000000 16893431645223 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4782870511/10000000000 : ℝ)^4177 ≤ (37640993525099/100000000000000 : ℝ)^3153 := by
    have hnat : (4782870511 : ℕ)^4177*100000000000000^3153 ≤ 37640993525099^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4782870511 10000000000 37640993525099 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5515723259/10000000000 : ℝ), (-2612428441/10000000000 : ℝ), (4782870511/10000000000 : ℝ)] ![(45465574811841/100000000000000 : ℝ), (16893431645223/100000000000000 : ℝ), (37640993525099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5515723259/10000000000 : ℝ)|^4177 ≤ (45465574811841/100000000000000 : ℝ)^3153
        have hw : |(5515723259/10000000000 : ℝ)|=(5515723259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2612428441/10000000000 : ℝ)|^4177 ≤ (16893431645223/100000000000000 : ℝ)^3153
        have hw : |(-2612428441/10000000000 : ℝ)|=(2612428441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4782870511/10000000000 : ℝ)|^4177 ≤ (37640993525099/100000000000000 : ℝ)^3153
        have hw : |(4782870511/10000000000 : ℝ)|=(4782870511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s0_2 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5515723259/10000000000 : ℝ)*x 0 + (4782870511/10000000000 : ℝ)*x 1 + (-1306214221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5515723259/10000000000 : ℝ)^4177 ≤ (45465574811841/100000000000000 : ℝ)^3153 := by
    have hnat : (5515723259 : ℕ)^4177*100000000000000^3153 ≤ 45465574811841^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515723259 10000000000 45465574811841 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4782870511/10000000000 : ℝ)^4177 ≤ (37640993525099/100000000000000 : ℝ)^3153 := by
    have hnat : (4782870511 : ℕ)^4177*100000000000000^3153 ≤ 37640993525099^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4782870511 10000000000 37640993525099 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306214221/5000000000 : ℝ)^4177 ≤ (16893431653789/100000000000000 : ℝ)^3153 := by
    have hnat : (1306214221 : ℕ)^4177*100000000000000^3153 ≤ 16893431653789^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306214221 5000000000 16893431653789 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5515723259/10000000000 : ℝ), (4782870511/10000000000 : ℝ), (-1306214221/5000000000 : ℝ)] ![(45465574811841/100000000000000 : ℝ), (37640993525099/100000000000000 : ℝ), (16893431653789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5515723259/10000000000 : ℝ)|^4177 ≤ (45465574811841/100000000000000 : ℝ)^3153
        have hw : |(5515723259/10000000000 : ℝ)|=(5515723259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4782870511/10000000000 : ℝ)|^4177 ≤ (37640993525099/100000000000000 : ℝ)^3153
        have hw : |(4782870511/10000000000 : ℝ)|=(4782870511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1306214221/5000000000 : ℝ)|^4177 ≤ (16893431653789/100000000000000 : ℝ)^3153
        have hw : |(-1306214221/5000000000 : ℝ)|=(1306214221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s0_3 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4199458481/10000000000 : ℝ)*x 0 + (3120214471/10000000000 : ℝ)*x 1 + (5650432737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199458481/10000000000 : ℝ)^4177 ≤ (3168237678521/10000000000000 : ℝ)^3153 := by
    have hnat : (4199458481 : ℕ)^4177*10000000000000^3153 ≤ 3168237678521^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199458481 10000000000 3168237678521 10000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3120214471/10000000000 : ℝ)^4177 ≤ (21375225200763/100000000000000 : ℝ)^3153 := by
    have hnat : (3120214471 : ℕ)^4177*100000000000000^3153 ≤ 21375225200763^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120214471 10000000000 21375225200763 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5650432737/10000000000 : ℝ)^4177 ≤ (5867799749767/12500000000000 : ℝ)^3153 := by
    have hnat : (5650432737 : ℕ)^4177*12500000000000^3153 ≤ 5867799749767^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5650432737 10000000000 5867799749767 12500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199458481/10000000000 : ℝ), (3120214471/10000000000 : ℝ), (5650432737/10000000000 : ℝ)] ![(3168237678521/10000000000000 : ℝ), (21375225200763/100000000000000 : ℝ), (5867799749767/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199458481/10000000000 : ℝ)|^4177 ≤ (3168237678521/10000000000000 : ℝ)^3153
        have hw : |(4199458481/10000000000 : ℝ)|=(4199458481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3120214471/10000000000 : ℝ)|^4177 ≤ (21375225200763/100000000000000 : ℝ)^3153
        have hw : |(3120214471/10000000000 : ℝ)|=(3120214471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5650432737/10000000000 : ℝ)|^4177 ≤ (5867799749767/12500000000000 : ℝ)^3153
        have hw : |(5650432737/10000000000 : ℝ)|=(5650432737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s0_4 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-945450869/5000000000 : ℝ)*x 0 + (4815547851/10000000000 : ℝ)*x 1 + (1504030403/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (945450869/5000000000 : ℝ)^4177 ≤ (5504561144819/50000000000000 : ℝ)^3153 := by
    have hnat : (945450869 : ℕ)^4177*50000000000000^3153 ≤ 5504561144819^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945450869 5000000000 5504561144819 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4815547851/10000000000 : ℝ)^4177 ≤ (18991030566433/50000000000000 : ℝ)^3153 := by
    have hnat : (4815547851 : ℕ)^4177*50000000000000^3153 ≤ 18991030566433^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815547851 10000000000 18991030566433 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1504030403/2500000000 : ℝ)^4177 ≤ (25504408279073/50000000000000 : ℝ)^3153 := by
    have hnat : (1504030403 : ℕ)^4177*50000000000000^3153 ≤ 25504408279073^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504030403 2500000000 25504408279073 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-945450869/5000000000 : ℝ), (4815547851/10000000000 : ℝ), (1504030403/2500000000 : ℝ)] ![(5504561144819/50000000000000 : ℝ), (18991030566433/50000000000000 : ℝ), (25504408279073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-945450869/5000000000 : ℝ)|^4177 ≤ (5504561144819/50000000000000 : ℝ)^3153
        have hw : |(-945450869/5000000000 : ℝ)|=(945450869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4815547851/10000000000 : ℝ)|^4177 ≤ (18991030566433/50000000000000 : ℝ)^3153
        have hw : |(4815547851/10000000000 : ℝ)|=(4815547851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1504030403/2500000000 : ℝ)|^4177 ≤ (25504408279073/50000000000000 : ℝ)^3153
        have hw : |(1504030403/2500000000 : ℝ)|=(1504030403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s0_5 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2585668839/5000000000 : ℝ)*x 0 + (-689588751/5000000000 : ℝ)*x 1 + (601612141/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585668839/5000000000 : ℝ)^4177 ≤ (20871790037823/50000000000000 : ℝ)^3153 := by
    have hnat : (2585668839 : ℕ)^4177*50000000000000^3153 ≤ 20871790037823^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585668839 5000000000 20871790037823 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (689588751/5000000000 : ℝ)^4177 ≤ (3623802808383/50000000000000 : ℝ)^3153 := by
    have hnat : (689588751 : ℕ)^4177*50000000000000^3153 ≤ 3623802808383^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689588751 5000000000 3623802808383 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (601612141/1000000000 : ℝ)^4177 ≤ (51008814289219/100000000000000 : ℝ)^3153 := by
    have hnat : (601612141 : ℕ)^4177*100000000000000^3153 ≤ 51008814289219^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601612141 1000000000 51008814289219 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585668839/5000000000 : ℝ), (-689588751/5000000000 : ℝ), (601612141/1000000000 : ℝ)] ![(20871790037823/50000000000000 : ℝ), (3623802808383/50000000000000 : ℝ), (51008814289219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585668839/5000000000 : ℝ)|^4177 ≤ (20871790037823/50000000000000 : ℝ)^3153
        have hw : |(2585668839/5000000000 : ℝ)|=(2585668839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-689588751/5000000000 : ℝ)|^4177 ≤ (3623802808383/50000000000000 : ℝ)^3153
        have hw : |(-689588751/5000000000 : ℝ)|=(689588751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(601612141/1000000000 : ℝ)|^4177 ≤ (51008814289219/100000000000000 : ℝ)^3153
        have hw : |(601612141/1000000000 : ℝ)|=(601612141/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s0_6 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5171337651/10000000000 : ℝ)*x 0 + (6016121487/10000000000 : ℝ)*x 1 + (-1379177419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171337651/10000000000 : ℝ)^4177 ≤ (41743579786917/100000000000000 : ℝ)^3153 := by
    have hnat : (5171337651 : ℕ)^4177*100000000000000^3153 ≤ 41743579786917^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171337651 10000000000 41743579786917 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6016121487/10000000000 : ℝ)^4177 ≤ (51008815154107/100000000000000 : ℝ)^3153 := by
    have hnat : (6016121487 : ℕ)^4177*100000000000000^3153 ≤ 51008815154107^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6016121487 10000000000 51008815154107 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379177419/10000000000 : ℝ)^4177 ≤ (3623802519473/50000000000000 : ℝ)^3153 := by
    have hnat : (1379177419 : ℕ)^4177*50000000000000^3153 ≤ 3623802519473^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379177419 10000000000 3623802519473 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171337651/10000000000 : ℝ), (6016121487/10000000000 : ℝ), (-1379177419/10000000000 : ℝ)] ![(41743579786917/100000000000000 : ℝ), (51008815154107/100000000000000 : ℝ), (3623802519473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171337651/10000000000 : ℝ)|^4177 ≤ (41743579786917/100000000000000 : ℝ)^3153
        have hw : |(5171337651/10000000000 : ℝ)|=(5171337651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6016121487/10000000000 : ℝ)|^4177 ≤ (51008815154107/100000000000000 : ℝ)^3153
        have hw : |(6016121487/10000000000 : ℝ)|=(6016121487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1379177419/10000000000 : ℝ)|^4177 ≤ (3623802519473/50000000000000 : ℝ)^3153
        have hw : |(-1379177419/10000000000 : ℝ)|=(1379177419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s0_7 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052405663/2500000000 : ℝ)*x 0 + (279258969/500000000 : ℝ)*x 1 + (1593882407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052405663/2500000000 : ℝ)^4177 ≤ (31784003408129/100000000000000 : ℝ)^3153 := by
    have hnat : (1052405663 : ℕ)^4177*100000000000000^3153 ≤ 31784003408129^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052405663 2500000000 31784003408129 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279258969/500000000 : ℝ)^4177 ≤ (46225578840023/100000000000000 : ℝ)^3153 := by
    have hnat : (279258969 : ℕ)^4177*100000000000000^3153 ≤ 46225578840023^3153*500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279258969 500000000 46225578840023 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1593882407/5000000000 : ℝ)^4177 ≤ (21990417740311/100000000000000 : ℝ)^3153 := by
    have hnat : (1593882407 : ℕ)^4177*100000000000000^3153 ≤ 21990417740311^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593882407 5000000000 21990417740311 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052405663/2500000000 : ℝ), (279258969/500000000 : ℝ), (1593882407/5000000000 : ℝ)] ![(31784003408129/100000000000000 : ℝ), (46225578840023/100000000000000 : ℝ), (21990417740311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052405663/2500000000 : ℝ)|^4177 ≤ (31784003408129/100000000000000 : ℝ)^3153
        have hw : |(1052405663/2500000000 : ℝ)|=(1052405663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(279258969/500000000 : ℝ)|^4177 ≤ (46225578840023/100000000000000 : ℝ)^3153
        have hw : |(279258969/500000000 : ℝ)|=(279258969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1593882407/5000000000 : ℝ)|^4177 ≤ (21990417740311/100000000000000 : ℝ)^3153
        have hw : |(1593882407/5000000000 : ℝ)|=(1593882407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1161_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (491/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13871/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8353/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8353 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8353*1^2048 ≤ 0^2048*1^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8353/2048 : ℝ) ≤ (2382081386104742763/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8353 ≤ (2382081386104742763/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8353*100000000000000000000^2048 ≤ 2382081386104742763^2048*5^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2382081386104742763 100000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2382081386104742763/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8353 := by
      have hnat : (1 : ℕ)^2048*1^8353 ≤ 1^8353*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102382081386104742763/100000000000000000000 : ℝ) ≤ (5028943165595703/5000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (102382081386104742763/100000000000000000000 : ℝ)^2048 ≤ (5028943165595703/5000000000000000 : ℝ)^8353 := by
      have hnat : (102382081386104742763 : ℕ)^2048*5000000000000000^8353 ≤ 5028943165595703^8353*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102382081386104742763 100000000000000000000 5028943165595703 5000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028943165595703/5000000000000000 : ℝ)) (X := (102382081386104742763/100000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52382081386104742763/50000000000000000000 : ℝ) ≤ (2528943165595703/2500000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (52382081386104742763/50000000000000000000 : ℝ)^2048 ≤ (2528943165595703/2500000000000000 : ℝ)^8353 := by
      have hnat : (52382081386104742763 : ℕ)^2048*2500000000000000^8353 ≤ 2528943165595703^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52382081386104742763 50000000000000000000 2528943165595703 2500000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528943165595703/2500000000000000 : ℝ)) (X := (52382081386104742763/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28943165595703/2000000000000000 : ℝ)*(0 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28943165595703/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2382081386104742763/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28943165595703/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8353/2048 : ℝ) := by
    rw [show (1 : ℝ)+(28943165595703/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028943165595703/5000000000000000 : ℝ) by norm_num, show 1+(2382081386104742763/100000000000000000000 : ℝ)+(0 : ℝ)=(102382081386104742763/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2382081386104742763/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28943165595703/2000000000000000 : ℝ)*(2/5 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28943165595703/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528943165595703/2500000000000000 : ℝ) by norm_num, show 1+2*(2382081386104742763/100000000000000000000 : ℝ)=(52382081386104742763/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28943165595703/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28943165595703/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28943165595703/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28943165595703/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28943165595703/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28943165595703/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1885811831/10000000000 : ℝ)*X 0 0+(3024974621/5000000000 : ℝ)*X 0 1+(4782870511/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5515723259/10000000000 : ℝ)*X 1 0+(-2612428441/10000000000 : ℝ)*X 1 1+(4782870511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5515723259/10000000000 : ℝ)*X 2 0+(4782870511/10000000000 : ℝ)*X 2 1+(-1306214221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4199458481/10000000000 : ℝ)*X 0 0+(3120214471/10000000000 : ℝ)*X 0 1+(5650432737/10000000000 : ℝ)*X 0 2+(4199458481/10000000000 : ℝ)*X 1 0+(3120214471/10000000000 : ℝ)*X 1 1+(5650432737/10000000000 : ℝ)*X 1 2+(4199458481/10000000000 : ℝ)*X 2 0+(3120214471/10000000000 : ℝ)*X 2 1+(5650432737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-945450869/5000000000 : ℝ)*X 0 0+(4815547851/10000000000 : ℝ)*X 0 1+(1504030403/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2585668839/5000000000 : ℝ)*X 1 0+(-689588751/5000000000 : ℝ)*X 1 1+(601612141/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5171337651/10000000000 : ℝ)*X 2 0+(6016121487/10000000000 : ℝ)*X 2 1+(-1379177419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052405663/2500000000 : ℝ)*X 0 0+(279258969/500000000 : ℝ)*X 0 1+(1593882407/5000000000 : ℝ)*X 0 2+(1052405663/2500000000 : ℝ)*X 1 0+(279258969/500000000 : ℝ)*X 1 1+(1593882407/5000000000 : ℝ)*X 1 2+(1052405663/2500000000 : ℝ)*X 2 0+(279258969/500000000 : ℝ)*X 2 1+(1593882407/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92580394938611475314733/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78621311/100000000000000 : ℝ)*(base1) + (1825752413/100000000000000 : ℝ)*(base19) + (1700265637/100000000000000 : ℝ)*(base23) + (15685847/12500000000000 : ℝ)*(base24) + (41842079/10000000000000 : ℝ)*(upper3) + (296113812636163/50000000000000 : ℝ)*(major0) + (296113812636163/50000000000000 : ℝ)*(major1) + (296113812636163/50000000000000 : ℝ)*(major2) + (789223067408431/100000000000000 : ℝ)*(sp0) + (394612594466419/50000000000000 : ℝ)*(sp1) + (394612594466419/50000000000000 : ℝ)*(sp2) + (395224702616149/100000000000000 : ℝ)*(sp3) + (402589813/10000000000000 : ℝ)*(sp4) + (1603870441/50000000000000 : ℝ)*(sp7) + (197613994489171/50000000000000 : ℝ)*(f.failure) + (3156908058741/400000000000 : ℝ)*(f.sum) + (52086113607589/50000000000000000000000000000 : ℝ)*base65 + (387526368107589/100000000000000000000000000000 : ℝ)*base67 + (302258739007589/100000000000000000000000000000 : ℝ)*base69 + (200729917707589/100000000000000000000000000000 : ℝ)*base71 + (148831706157589/50000000000000000000000000000 : ℝ)*base73 + (398108902692411/100000000000000000000000000000 : ℝ)*base76 + (200729917707589/100000000000000000000000000000 : ℝ)*base77 + (25519860492411/100000000000000000000000000000 : ℝ)*base80 + (221983826957589/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6174231/1250000000000000000000 : ℝ)*base90 + (6174231/1250000000000000000000 : ℝ)*base92 + (6174231/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222749428415353765760553/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35513201/100000000000000 : ℝ)*(base1) + (2792507/500000000000 : ℝ)*(base19) + (138546851/25000000000000 : ℝ)*(base23) + (328533/625000000000 : ℝ)*(upper3) + (70705861/100000000000000 : ℝ)*(upper5) + (625025613305561/100000000000000 : ℝ)*(major0) + (625025613305561/100000000000000 : ℝ)*(major1) + (625025613305561/100000000000000 : ℝ)*(major2) + (534134753/50000000000000 : ℝ)*(sp1) + (1068792381/100000000000000 : ℝ)*(sp2) + (832935191144161/100000000000000 : ℝ)*(sp4) + (832933528860053/100000000000000 : ℝ)*(sp5) + (33317341306047/4000000000000 : ℝ)*(sp6) + (52139495152143/12500000000000 : ℝ)*(sp7) + (208557998365173/50000000000000 : ℝ)*(f.failure) + (10411689445387/1250000000000 : ℝ)*(f.sum) + (17394120604383/100000000000000000000000000000 : ℝ)*base65 + (459155781404383/200000000000000000000000000000 : ℝ)*base67 + (1829067778004383/200000000000000000000000000000 : ℝ)*base69 + (1387210952404383/200000000000000000000000000000 : ℝ)*base71 + (263610769195617/100000000000000000000000000000 : ℝ)*base74 + (2270014825204383/200000000000000000000000000000 : ℝ)*base75 + (1295618429204383/200000000000000000000000000000 : ℝ)*base77 + (85829399595617/200000000000000000000000000000 : ℝ)*base80 + (102798178704383/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6012047/1250000000000000000000 : ℝ)*base89 + (6012047/1250000000000000000000 : ℝ)*base91 + (6012047/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1161_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13871/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1161_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1161_s1_0 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2089106207/10000000000 : ℝ)*x 0 + (5696453729/10000000000 : ℝ)*x 1 + (1251555887/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089106207/10000000000 : ℝ)^4177 ≤ (502532377083/4000000000000 : ℝ)^3153 := by
    have hnat : (2089106207 : ℕ)^4177*4000000000000^3153 ≤ 502532377083^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089106207 10000000000 502532377083 4000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5696453729/10000000000 : ℝ)^4177 ≤ (47449567350331/100000000000000 : ℝ)^3153 := by
    have hnat : (5696453729 : ℕ)^4177*100000000000000^3153 ≤ 47449567350331^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5696453729 10000000000 47449567350331 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251555887/2500000000 : ℝ)^4177 ≤ (7997424641361/20000000000000 : ℝ)^3153 := by
    have hnat : (1251555887 : ℕ)^4177*20000000000000^3153 ≤ 7997424641361^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251555887 2500000000 7997424641361 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2089106207/10000000000 : ℝ), (5696453729/10000000000 : ℝ), (1251555887/2500000000 : ℝ)] ![(502532377083/4000000000000 : ℝ), (47449567350331/100000000000000 : ℝ), (7997424641361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2089106207/10000000000 : ℝ)|^4177 ≤ (502532377083/4000000000000 : ℝ)^3153
        have hw : |(-2089106207/10000000000 : ℝ)|=(2089106207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5696453729/10000000000 : ℝ)|^4177 ≤ (47449567350331/100000000000000 : ℝ)^3153
        have hw : |(5696453729/10000000000 : ℝ)|=(5696453729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1251555887/2500000000 : ℝ)|^4177 ≤ (7997424641361/20000000000000 : ℝ)^3153
        have hw : |(1251555887/2500000000 : ℝ)|=(1251555887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s1_1 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1354519321/2500000000 : ℝ)*x 0 + (-492246693/2000000000 : ℝ)*x 1 + (2503111301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354519321/2500000000 : ℝ)^4177 ≤ (44402363073681/100000000000000 : ℝ)^3153 := by
    have hnat : (1354519321 : ℕ)^4177*100000000000000^3153 ≤ 44402363073681^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354519321 2500000000 44402363073681 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492246693/2000000000 : ℝ)^4177 ≤ (195131546439/1250000000000 : ℝ)^3153 := by
    have hnat : (492246693 : ℕ)^4177*1250000000000^3153 ≤ 195131546439^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492246693 2000000000 195131546439 1250000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2503111301/5000000000 : ℝ)^4177 ≤ (39987113196633/100000000000000 : ℝ)^3153 := by
    have hnat : (2503111301 : ℕ)^4177*100000000000000^3153 ≤ 39987113196633^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503111301 5000000000 39987113196633 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354519321/2500000000 : ℝ), (-492246693/2000000000 : ℝ), (2503111301/5000000000 : ℝ)] ![(44402363073681/100000000000000 : ℝ), (195131546439/1250000000000 : ℝ), (39987113196633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354519321/2500000000 : ℝ)|^4177 ≤ (44402363073681/100000000000000 : ℝ)^3153
        have hw : |(1354519321/2500000000 : ℝ)|=(1354519321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-492246693/2000000000 : ℝ)|^4177 ≤ (195131546439/1250000000000 : ℝ)^3153
        have hw : |(-492246693/2000000000 : ℝ)|=(492246693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2503111301/5000000000 : ℝ)|^4177 ≤ (39987113196633/100000000000000 : ℝ)^3153
        have hw : |(2503111301/5000000000 : ℝ)|=(2503111301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s1_2 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (169314981/312500000 : ℝ)*x 0 + (5006220687/10000000000 : ℝ)*x 1 + (-2461233153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169314981/312500000 : ℝ)^4177 ≤ (44402385959793/100000000000000 : ℝ)^3153 := by
    have hnat : (169314981 : ℕ)^4177*100000000000000^3153 ≤ 44402385959793^3153*312500000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169314981 312500000 44402385959793 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5006220687/10000000000 : ℝ)^4177 ≤ (19993546466457/50000000000000 : ℝ)^3153 := by
    have hnat : (5006220687 : ℕ)^4177*50000000000000^3153 ≤ 19993546466457^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5006220687 10000000000 19993546466457 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2461233153/10000000000 : ℝ)^4177 ≤ (15610521093561/100000000000000 : ℝ)^3153 := by
    have hnat : (2461233153 : ℕ)^4177*100000000000000^3153 ≤ 15610521093561^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2461233153 10000000000 15610521093561 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(169314981/312500000 : ℝ), (5006220687/10000000000 : ℝ), (-2461233153/10000000000 : ℝ)] ![(44402385959793/100000000000000 : ℝ), (19993546466457/50000000000000 : ℝ), (15610521093561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(169314981/312500000 : ℝ)|^4177 ≤ (44402385959793/100000000000000 : ℝ)^3153
        have hw : |(169314981/312500000 : ℝ)|=(169314981/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5006220687/10000000000 : ℝ)|^4177 ≤ (19993546466457/50000000000000 : ℝ)^3153
        have hw : |(5006220687/10000000000 : ℝ)|=(5006220687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2461233153/10000000000 : ℝ)|^4177 ≤ (15610521093561/100000000000000 : ℝ)^3153
        have hw : |(-2461233153/10000000000 : ℝ)|=(2461233153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s1_3 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2157913683/5000000000 : ℝ)*x 0 + (1840302113/5000000000 : ℝ)*x 1 + (2529457173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157913683/5000000000 : ℝ)^4177 ≤ (16425318629629/50000000000000 : ℝ)^3153 := by
    have hnat : (2157913683 : ℕ)^4177*50000000000000^3153 ≤ 16425318629629^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157913683 5000000000 16425318629629 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1840302113/5000000000 : ℝ)^4177 ≤ (831366783541/3125000000000 : ℝ)^3153 := by
    have hnat : (1840302113 : ℕ)^4177*3125000000000^3153 ≤ 831366783541^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840302113 5000000000 831366783541 3125000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2529457173/5000000000 : ℝ)^4177 ≤ (506820320657/1250000000000 : ℝ)^3153 := by
    have hnat : (2529457173 : ℕ)^4177*1250000000000^3153 ≤ 506820320657^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2529457173 5000000000 506820320657 1250000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157913683/5000000000 : ℝ), (1840302113/5000000000 : ℝ), (2529457173/5000000000 : ℝ)] ![(16425318629629/50000000000000 : ℝ), (831366783541/3125000000000 : ℝ), (506820320657/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157913683/5000000000 : ℝ)|^4177 ≤ (16425318629629/50000000000000 : ℝ)^3153
        have hw : |(2157913683/5000000000 : ℝ)|=(2157913683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1840302113/5000000000 : ℝ)|^4177 ≤ (831366783541/3125000000000 : ℝ)^3153
        have hw : |(1840302113/5000000000 : ℝ)|=(1840302113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2529457173/5000000000 : ℝ)|^4177 ≤ (506820320657/1250000000000 : ℝ)^3153
        have hw : |(2529457173/5000000000 : ℝ)|=(2529457173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s1_4 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-130618161/625000000 : ℝ)*x 0 + (5015579769/10000000000 : ℝ)*x 1 + (355431889/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130618161/625000000 : ℝ)^4177 ≤ (12569558720803/100000000000000 : ℝ)^3153 := by
    have hnat : (130618161 : ℕ)^4177*100000000000000^3153 ≤ 12569558720803^3153*625000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130618161 625000000 12569558720803 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5015579769/10000000000 : ℝ)^4177 ≤ (40086156820003/100000000000000 : ℝ)^3153 := by
    have hnat : (5015579769 : ℕ)^4177*100000000000000^3153 ≤ 40086156820003^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015579769 10000000000 40086156820003 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (355431889/625000000 : ℝ)^4177 ≤ (47344284439899/100000000000000 : ℝ)^3153 := by
    have hnat : (355431889 : ℕ)^4177*100000000000000^3153 ≤ 47344284439899^3153*625000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355431889 625000000 47344284439899 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130618161/625000000 : ℝ), (5015579769/10000000000 : ℝ), (355431889/625000000 : ℝ)] ![(12569558720803/100000000000000 : ℝ), (40086156820003/100000000000000 : ℝ), (47344284439899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130618161/625000000 : ℝ)|^4177 ≤ (12569558720803/100000000000000 : ℝ)^3153
        have hw : |(-130618161/625000000 : ℝ)|=(130618161/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5015579769/10000000000 : ℝ)|^4177 ≤ (40086156820003/100000000000000 : ℝ)^3153
        have hw : |(5015579769/10000000000 : ℝ)|=(5015579769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(355431889/625000000 : ℝ)|^4177 ≤ (47344284439899/100000000000000 : ℝ)^3153
        have hw : |(355431889/625000000 : ℝ)|=(355431889/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s1_5 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (655118409/1250000000 : ℝ)*x 0 + (-1780542231/10000000000 : ℝ)*x 1 + (5686913573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655118409/1250000000 : ℝ)^4177 ≤ (21244792587407/50000000000000 : ℝ)^3153 := by
    have hnat : (655118409 : ℕ)^4177*50000000000000^3153 ≤ 21244792587407^3153*1250000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655118409 1250000000 21244792587407 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1780542231/10000000000 : ℝ)^4177 ≤ (1270761680087/12500000000000 : ℝ)^3153 := by
    have hnat : (1780542231 : ℕ)^4177*12500000000000^3153 ≤ 1270761680087^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780542231 10000000000 1270761680087 12500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5686913573/10000000000 : ℝ)^4177 ≤ (9468864275129/20000000000000 : ℝ)^3153 := by
    have hnat : (5686913573 : ℕ)^4177*20000000000000^3153 ≤ 9468864275129^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5686913573 10000000000 9468864275129 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655118409/1250000000 : ℝ), (-1780542231/10000000000 : ℝ), (5686913573/10000000000 : ℝ)] ![(21244792587407/50000000000000 : ℝ), (1270761680087/12500000000000 : ℝ), (9468864275129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655118409/1250000000 : ℝ)|^4177 ≤ (21244792587407/50000000000000 : ℝ)^3153
        have hw : |(655118409/1250000000 : ℝ)|=(655118409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1780542231/10000000000 : ℝ)|^4177 ≤ (1270761680087/12500000000000 : ℝ)^3153
        have hw : |(-1780542231/10000000000 : ℝ)|=(1780542231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5686913573/10000000000 : ℝ)|^4177 ≤ (9468864275129/20000000000000 : ℝ)^3153
        have hw : |(5686913573/10000000000 : ℝ)|=(5686913573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s1_6 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (655118287/1250000000 : ℝ)*x 0 + (2843457529/5000000000 : ℝ)*x 1 + (-35610829/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655118287/1250000000 : ℝ)^4177 ≤ (42489574692359/100000000000000 : ℝ)^3153 := by
    have hnat : (655118287 : ℕ)^4177*100000000000000^3153 ≤ 42489574692359^3153*1250000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655118287 1250000000 42489574692359 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2843457529/5000000000 : ℝ)^4177 ≤ (23672168876773/50000000000000 : ℝ)^3153 := by
    have hnat : (2843457529 : ℕ)^4177*50000000000000^3153 ≤ 23672168876773^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2843457529 5000000000 23672168876773 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35610829/200000000 : ℝ)^4177 ≤ (5083043766669/50000000000000 : ℝ)^3153 := by
    have hnat : (35610829 : ℕ)^4177*50000000000000^3153 ≤ 5083043766669^3153*200000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35610829 200000000 5083043766669 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655118287/1250000000 : ℝ), (2843457529/5000000000 : ℝ), (-35610829/200000000 : ℝ)] ![(42489574692359/100000000000000 : ℝ), (23672168876773/50000000000000 : ℝ), (5083043766669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655118287/1250000000 : ℝ)|^4177 ≤ (42489574692359/100000000000000 : ℝ)^3153
        have hw : |(655118287/1250000000 : ℝ)|=(655118287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2843457529/5000000000 : ℝ)|^4177 ≤ (23672168876773/50000000000000 : ℝ)^3153
        have hw : |(2843457529/5000000000 : ℝ)|=(2843457529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35610829/200000000 : ℝ)|^4177 ≤ (5083043766669/50000000000000 : ℝ)^3153
        have hw : |(-35610829/200000000 : ℝ)|=(35610829/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s1_7 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158690983/5000000000 : ℝ)*x 0 + (1008046611/2000000000 : ℝ)*x 1 + (36996529/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158690983/5000000000 : ℝ)^4177 ≤ (8216578576943/25000000000000 : ℝ)^3153 := by
    have hnat : (2158690983 : ℕ)^4177*25000000000000^3153 ≤ 8216578576943^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158690983 5000000000 8216578576943 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008046611/2000000000 : ℝ)^4177 ≤ (39401751797/97656250000 : ℝ)^3153 := by
    have hnat : (1008046611 : ℕ)^4177*97656250000^3153 ≤ 39401751797^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008046611 2000000000 39401751797 97656250000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36996529/100000000 : ℝ)^4177 ≤ (6696572961233/25000000000000 : ℝ)^3153 := by
    have hnat : (36996529 : ℕ)^4177*25000000000000^3153 ≤ 6696572961233^3153*100000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36996529 100000000 6696572961233 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158690983/5000000000 : ℝ), (1008046611/2000000000 : ℝ), (36996529/100000000 : ℝ)] ![(8216578576943/25000000000000 : ℝ), (39401751797/97656250000 : ℝ), (6696572961233/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158690983/5000000000 : ℝ)|^4177 ≤ (8216578576943/25000000000000 : ℝ)^3153
        have hw : |(2158690983/5000000000 : ℝ)|=(2158690983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1008046611/2000000000 : ℝ)|^4177 ≤ (39401751797/97656250000 : ℝ)^3153
        have hw : |(1008046611/2000000000 : ℝ)|=(1008046611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36996529/100000000 : ℝ)|^4177 ≤ (6696572961233/25000000000000 : ℝ)^3153
        have hw : |(36996529/100000000 : ℝ)|=(36996529/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s1_8 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5549009/10000000000 : ℝ)*x 0 + (2745242333/5000000000 : ℝ)*x 1 + (3175548287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5549009/10000000000 : ℝ)^4177 ≤ (972442819/20000000000000 : ℝ)^3153 := by
    have hnat : (5549009 : ℕ)^4177*20000000000000^3153 ≤ 972442819^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5549009 10000000000 972442819 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745242333/5000000000 : ℝ)^4177 ≤ (45190175586687/100000000000000 : ℝ)^3153 := by
    have hnat : (2745242333 : ℕ)^4177*100000000000000^3153 ≤ 45190175586687^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745242333 5000000000 45190175586687 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3175548287/5000000000 : ℝ)^4177 ≤ (54804962186011/100000000000000 : ℝ)^3153 := by
    have hnat : (3175548287 : ℕ)^4177*100000000000000^3153 ≤ 54804962186011^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3175548287 5000000000 54804962186011 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5549009/10000000000 : ℝ), (2745242333/5000000000 : ℝ), (3175548287/5000000000 : ℝ)] ![(972442819/20000000000000 : ℝ), (45190175586687/100000000000000 : ℝ), (54804962186011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5549009/10000000000 : ℝ)|^4177 ≤ (972442819/20000000000000 : ℝ)^3153
        have hw : |(5549009/10000000000 : ℝ)|=(5549009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745242333/5000000000 : ℝ)|^4177 ≤ (45190175586687/100000000000000 : ℝ)^3153
        have hw : |(2745242333/5000000000 : ℝ)|=(2745242333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3175548287/5000000000 : ℝ)|^4177 ≤ (54804962186011/100000000000000 : ℝ)^3153
        have hw : |(3175548287/5000000000 : ℝ)|=(3175548287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s1_9 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (30743079/312500000 : ℝ)*x 0 + (-1099302723/2500000000 : ℝ)*x 1 + (6944859799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30743079/312500000 : ℝ)^4177 ≤ (4632554610001/100000000000000 : ℝ)^3153 := by
    have hnat : (30743079 : ℕ)^4177*100000000000000^3153 ≤ 4632554610001^3153*312500000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30743079 312500000 4632554610001 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099302723/2500000000 : ℝ)^4177 ≤ (8418446811761/25000000000000 : ℝ)^3153 := by
    have hnat : (1099302723 : ℕ)^4177*25000000000000^3153 ≤ 8418446811761^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099302723 2500000000 8418446811761 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6944859799/10000000000 : ℝ)^4177 ≤ (3855853632741/6250000000000 : ℝ)^3153 := by
    have hnat : (6944859799 : ℕ)^4177*6250000000000^3153 ≤ 3855853632741^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6944859799 10000000000 3855853632741 6250000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(30743079/312500000 : ℝ), (-1099302723/2500000000 : ℝ), (6944859799/10000000000 : ℝ)] ![(4632554610001/100000000000000 : ℝ), (8418446811761/25000000000000 : ℝ), (3855853632741/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(30743079/312500000 : ℝ)|^4177 ≤ (4632554610001/100000000000000 : ℝ)^3153
        have hw : |(30743079/312500000 : ℝ)|=(30743079/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1099302723/2500000000 : ℝ)|^4177 ≤ (8418446811761/25000000000000 : ℝ)^3153
        have hw : |(-1099302723/2500000000 : ℝ)|=(1099302723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6944859799/10000000000 : ℝ)|^4177 ≤ (3855853632741/6250000000000 : ℝ)^3153
        have hw : |(6944859799/10000000000 : ℝ)|=(6944859799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s1_10 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (983771517/10000000000 : ℝ)*x 0 + (6944842853/10000000000 : ℝ)*x 1 + (-4397234861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (983771517/10000000000 : ℝ)^4177 ≤ (4632510873587/100000000000000 : ℝ)^3153 := by
    have hnat : (983771517 : ℕ)^4177*100000000000000^3153 ≤ 4632510873587^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983771517 10000000000 4632510873587 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6944842853/10000000000 : ℝ)^4177 ≤ (15423364674143/25000000000000 : ℝ)^3153 := by
    have hnat : (6944842853 : ℕ)^4177*25000000000000^3153 ≤ 15423364674143^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6944842853 10000000000 15423364674143 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4397234861/10000000000 : ℝ)^4177 ≤ (2104626900907/6250000000000 : ℝ)^3153 := by
    have hnat : (4397234861 : ℕ)^4177*6250000000000^3153 ≤ 2104626900907^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4397234861 10000000000 2104626900907 6250000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(983771517/10000000000 : ℝ), (6944842853/10000000000 : ℝ), (-4397234861/10000000000 : ℝ)] ![(4632510873587/100000000000000 : ℝ), (15423364674143/25000000000000 : ℝ), (2104626900907/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(983771517/10000000000 : ℝ)|^4177 ≤ (4632510873587/100000000000000 : ℝ)^3153
        have hw : |(983771517/10000000000 : ℝ)|=(983771517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6944842853/10000000000 : ℝ)|^4177 ≤ (15423364674143/25000000000000 : ℝ)^3153
        have hw : |(6944842853/10000000000 : ℝ)|=(6944842853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4397234861/10000000000 : ℝ)|^4177 ≤ (2104626900907/6250000000000 : ℝ)^3153
        have hw : |(-4397234861/10000000000 : ℝ)|=(4397234861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s1_11 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (382735559/2000000000 : ℝ)*x 0 + (5807358819/10000000000 : ℝ)*x 1 + (502043927/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382735559/2000000000 : ℝ)^4177 ≤ (5592568530913/50000000000000 : ℝ)^3153 := by
    have hnat : (382735559 : ℕ)^4177*50000000000000^3153 ≤ 5592568530913^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382735559 2000000000 5592568530913 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5807358819/10000000000 : ℝ)^4177 ≤ (12169311407171/25000000000000 : ℝ)^3153 := by
    have hnat : (5807358819 : ℕ)^4177*25000000000000^3153 ≤ 12169311407171^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5807358819 10000000000 12169311407171 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502043927/1000000000 : ℝ)^4177 ≤ (40137617292281/100000000000000 : ℝ)^3153 := by
    have hnat : (502043927 : ℕ)^4177*100000000000000^3153 ≤ 40137617292281^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502043927 1000000000 40137617292281 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(382735559/2000000000 : ℝ), (5807358819/10000000000 : ℝ), (502043927/1000000000 : ℝ)] ![(5592568530913/50000000000000 : ℝ), (12169311407171/25000000000000 : ℝ), (40137617292281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(382735559/2000000000 : ℝ)|^4177 ≤ (5592568530913/50000000000000 : ℝ)^3153
        have hw : |(382735559/2000000000 : ℝ)|=(382735559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5807358819/10000000000 : ℝ)|^4177 ≤ (12169311407171/25000000000000 : ℝ)^3153
        have hw : |(5807358819/10000000000 : ℝ)|=(5807358819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502043927/1000000000 : ℝ)|^4177 ≤ (40137617292281/100000000000000 : ℝ)^3153
        have hw : |(502043927/1000000000 : ℝ)|=(502043927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1161_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13871/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1151/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20351/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13871/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (491/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13871/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (491/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13871/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (491/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13871/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (491/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13871/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (491/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13871/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (491/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (491/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (38266109371/100000000000000000000 : ℝ) := by
    have hpowers : (491/100000 : ℝ)^8353 ≤ (38266109371/100000000000000000000 : ℝ)^2048 := by
      have hnat : (491 : ℕ)^8353*100000000000000000000^2048 ≤ 38266109371^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        491 100000 38266109371 100000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (491/100000 : ℝ)) (X := (38266109371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13871/50000 : ℝ) ^ (8353/2048 : ℝ) ≤ (535518282640171611/100000000000000000000 : ℝ) := by
    have hpowers : (13871/50000 : ℝ)^8353 ≤ (535518282640171611/100000000000000000000 : ℝ)^2048 := by
      have hnat : (13871 : ℕ)^8353*100000000000000000000^2048 ≤ 535518282640171611^2048*50000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13871 50000 535518282640171611 100000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13871/50000 : ℝ)) (X := (535518282640171611/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000038266109371/50000000000000000000 : ℝ) ≤ (2500000000469107/2500000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (50000000038266109371/50000000000000000000 : ℝ)^2048 ≤ (2500000000469107/2500000000000000 : ℝ)^8353 := by
      have hnat : (50000000038266109371 : ℕ)^2048*2500000000000000^8353 ≤ 2500000000469107^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000038266109371 50000000000000000000 2500000000469107 2500000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000469107/2500000000000000 : ℝ)) (X := (50000000038266109371/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50267759160453140491/50000000000000000000 : ℝ) ≤ (2002620691534191/2000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (50267759160453140491/50000000000000000000 : ℝ)^2048 ≤ (2002620691534191/2000000000000000 : ℝ)^8353 := by
      have hnat : (50267759160453140491 : ℕ)^2048*2000000000000000^8353 ≤ 2002620691534191^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50267759160453140491 50000000000000000000 2002620691534191 2000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002620691534191/2000000000000000 : ℝ)) (X := (50267759160453140491/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50535518282640171611/50000000000000000000 : ℝ) ≤ (5013103456732741/5000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (50535518282640171611/50000000000000000000 : ℝ)^2048 ≤ (5013103456732741/5000000000000000 : ℝ)^8353 := by
      have hnat : (50535518282640171611 : ℕ)^2048*5000000000000000^8353 ≤ 5013103456732741^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50535518282640171611 50000000000000000000 5013103456732741 5000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013103456732741/5000000000000000 : ℝ)) (X := (50535518282640171611/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(38266109371/100000000000000000000 : ℝ) ≤ ((19464080889824593851/19465000000000000000 : ℝ)+2*(1871922256361/389300000000000 : ℝ)*(491/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (19464080889824593851/19465000000000000000 : ℝ)+2*(1871922256361/389300000000000 : ℝ)*(491/100000 : ℝ)=(2500000000469107/2500000000000000 : ℝ) by norm_num, show 1+2*(38266109371/100000000000000000000 : ℝ)=(50000000038266109371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(535518282640171611/100000000000000000000 : ℝ)+(38266109371/100000000000000000000 : ℝ) ≤ ((19464080889824593851/19465000000000000000 : ℝ)+(1871922256361/389300000000000 : ℝ)*((13871/50000 : ℝ)+(491/100000 : ℝ)))^(8353/2048 : ℝ) := by
    rw [show (19464080889824593851/19465000000000000000 : ℝ)+(1871922256361/389300000000000 : ℝ)*((13871/50000 : ℝ)+(491/100000 : ℝ))=(2002620691534191/2000000000000000 : ℝ) by norm_num, show 1+(535518282640171611/100000000000000000000 : ℝ)+(38266109371/100000000000000000000 : ℝ)=(50267759160453140491/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(535518282640171611/100000000000000000000 : ℝ) ≤ ((19464080889824593851/19465000000000000000 : ℝ)+2*(1871922256361/389300000000000 : ℝ)*(13871/50000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (19464080889824593851/19465000000000000000 : ℝ)+2*(1871922256361/389300000000000 : ℝ)*(13871/50000 : ℝ)=(5013103456732741/5000000000000000 : ℝ) by norm_num, show 1+2*(535518282640171611/100000000000000000000 : ℝ)=(50535518282640171611/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19464080889824593851/19465000000000000000 : ℝ)*(X 1 0+X 2 0)+(1871922256361/389300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (491/100000 : ℝ)) (hi := (13871/50000 : ℝ)) (c := (19464080889824593851/19465000000000000000 : ℝ)) (alpha := (1871922256361/389300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19464080889824593851/19465000000000000000 : ℝ)*(X 0 1+X 2 1)+(1871922256361/389300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (491/100000 : ℝ)) (hi := (13871/50000 : ℝ)) (c := (19464080889824593851/19465000000000000000 : ℝ)) (alpha := (1871922256361/389300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19464080889824593851/19465000000000000000 : ℝ)*(X 0 2+X 1 2)+(1871922256361/389300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (491/100000 : ℝ)) (hi := (13871/50000 : ℝ)) (c := (19464080889824593851/19465000000000000000 : ℝ)) (alpha := (1871922256361/389300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2089106207/10000000000 : ℝ)*X 0 0+(5696453729/10000000000 : ℝ)*X 0 1+(1251555887/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1354519321/2500000000 : ℝ)*X 1 0+(-492246693/2000000000 : ℝ)*X 1 1+(2503111301/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((169314981/312500000 : ℝ)*X 2 0+(5006220687/10000000000 : ℝ)*X 2 1+(-2461233153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157913683/5000000000 : ℝ)*X 0 0+(1840302113/5000000000 : ℝ)*X 0 1+(2529457173/5000000000 : ℝ)*X 0 2+(2157913683/5000000000 : ℝ)*X 1 0+(1840302113/5000000000 : ℝ)*X 1 1+(2529457173/5000000000 : ℝ)*X 1 2+(2157913683/5000000000 : ℝ)*X 2 0+(1840302113/5000000000 : ℝ)*X 2 1+(2529457173/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-130618161/625000000 : ℝ)*X 0 0+(5015579769/10000000000 : ℝ)*X 0 1+(355431889/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((655118409/1250000000 : ℝ)*X 1 0+(-1780542231/10000000000 : ℝ)*X 1 1+(5686913573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((655118287/1250000000 : ℝ)*X 2 0+(2843457529/5000000000 : ℝ)*X 2 1+(-35610829/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158690983/5000000000 : ℝ)*X 0 0+(1008046611/2000000000 : ℝ)*X 0 1+(36996529/100000000 : ℝ)*X 0 2+(2158690983/5000000000 : ℝ)*X 1 0+(1008046611/2000000000 : ℝ)*X 1 1+(36996529/100000000 : ℝ)*X 1 2+(2158690983/5000000000 : ℝ)*X 2 0+(1008046611/2000000000 : ℝ)*X 2 1+(36996529/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((5549009/10000000000 : ℝ)*X 0 0+(2745242333/5000000000 : ℝ)*X 0 1+(3175548287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((30743079/312500000 : ℝ)*X 1 0+(-1099302723/2500000000 : ℝ)*X 1 1+(6944859799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((983771517/10000000000 : ℝ)*X 2 0+(6944842853/10000000000 : ℝ)*X 2 1+(-4397234861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((382735559/2000000000 : ℝ)*X 0 0+(5807358819/10000000000 : ℝ)*X 0 1+(502043927/1000000000 : ℝ)*X 0 2+(382735559/2000000000 : ℝ)*X 1 0+(5807358819/10000000000 : ℝ)*X 1 1+(502043927/1000000000 : ℝ)*X 1 2+(382735559/2000000000 : ℝ)*X 2 0+(5807358819/10000000000 : ℝ)*X 2 1+(502043927/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6080530291647564545448576903/486625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49208027/100000000000000 : ℝ)*(lower2) + (543582778240951/50000000000000 : ℝ)*(major0) + (543582778240951/50000000000000 : ℝ)*(major1) + (543582778240951/50000000000000 : ℝ)*(major2) + (181099549589211/12500000000000 : ℝ)*(sp0) + (289759206778573/20000000000000 : ℝ)*(sp1) + (1448793820981273/100000000000000 : ℝ)*(sp2) + (362763422166459/50000000000000 : ℝ)*(sp3) + (2700662303/50000000000000 : ℝ)*(sp4) + (4870963813/100000000000000 : ℝ)*(sp5) + (3287074913/50000000000000 : ℝ)*(sp6) + (55823851/6250000000000 : ℝ)*(sp9) + (280581439/20000000000000 : ℝ)*(sp10) + (513520563/25000000000000 : ℝ)*(sp11) + (72552889841517/10000000000000 : ℝ)*(f.failure) + (724400899019147/50000000000000 : ℝ)*(f.sum) + (4261243714209/9732500000000000000000000000 : ℝ)*base66 + (1168025712454957699/973250000000000000000000000000000 : ℝ)*base68 + (1873966774080457699/973250000000000000000000000000000 : ℝ)*base70 + (6053727038292457699/973250000000000000000000000000000 : ℝ)*base72 + (26430540495459/9732500000000000000000000000 : ℝ)*base74 + (931497746964207699/973250000000000000000000000000000 : ℝ)*base76 + (1056888768527792301/973250000000000000000000000000000 : ℝ)*base77 + (613738850894042301/973250000000000000000000000000000 : ℝ)*base79 + (30930896651869/9732500000000000000000000000 : ℝ)*base82 + (1307863/250000000000000000000 : ℝ)*base89 + (1307863/250000000000000000000 : ℝ)*base91 + (1307863/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (528570767395165958972028519/243312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4561891/6250000000000 : ℝ)*(lower4) + (558881611004877/50000000000000 : ℝ)*(major0) + (558881611004877/50000000000000 : ℝ)*(major1) + (558881611004877/50000000000000 : ℝ)*(major2) + (2151317833/50000000000000 : ℝ)*(sp1) + (342177999/5000000000000 : ℝ)*(sp2) + (1348243513/100000000000000 : ℝ)*(sp3) + (744787322848617/50000000000000 : ℝ)*(sp4) + (372393375462051/25000000000000 : ℝ)*(sp5) + (1489571025246073/100000000000000 : ℝ)*(sp6) + (4662164165447/625000000000 : ℝ)*(sp7) + (1611554409/50000000000000 : ℝ)*(sp8) + (64322183/100000000000000 : ℝ)*(sp9) + (177617053/20000000000000 : ℝ)*(sp11) + (372974251400149/50000000000000 : ℝ)*(f.failure) + (372394467201513/25000000000000 : ℝ)*(f.sum) + (12537202052279/19465000000000000000000000000 : ℝ)*base65 + (3822996607097311327/973250000000000000000000000000000 : ℝ)*base67 + (4393431387028061327/973250000000000000000000000000000 : ℝ)*base69 + (6699293231125811327/973250000000000000000000000000000 : ℝ)*base71 + (2221709705001/19465000000000000000000000000 : ℝ)*base74 + (319343991234188673/973250000000000000000000000000000 : ℝ)*base76 + (54301835321811327/973250000000000000000000000000000 : ℝ)*base77 + (443551668177311327/973250000000000000000000000000000 : ℝ)*base79 + (53650059743/608281250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1309711/1250000000000000000000 : ℝ)*base89 + (1309711/1250000000000000000000 : ℝ)*base91 + (1309711/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1161_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13871/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1151/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20351/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1161_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1161_s2_0 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141324277/10000000000 : ℝ)*x 0 + (86050343/156250000 : ℝ)*x 1 + (5162232139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141324277/10000000000 : ℝ)^4177 ≤ (12980999606347/100000000000000 : ℝ)^3153 := by
    have hnat : (2141324277 : ℕ)^4177*100000000000000^3153 ≤ 12980999606347^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141324277 10000000000 12980999606347 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86050343/156250000 : ℝ)^4177 ≤ (22686382095809/50000000000000 : ℝ)^3153 := by
    have hnat : (86050343 : ℕ)^4177*50000000000000^3153 ≤ 22686382095809^3153*156250000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86050343 156250000 22686382095809 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5162232139/10000000000 : ℝ)^4177 ≤ (41646236181149/100000000000000 : ℝ)^3153 := by
    have hnat : (5162232139 : ℕ)^4177*100000000000000^3153 ≤ 41646236181149^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162232139 10000000000 41646236181149 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141324277/10000000000 : ℝ), (86050343/156250000 : ℝ), (5162232139/10000000000 : ℝ)] ![(12980999606347/100000000000000 : ℝ), (22686382095809/50000000000000 : ℝ), (41646236181149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141324277/10000000000 : ℝ)|^4177 ≤ (12980999606347/100000000000000 : ℝ)^3153
        have hw : |(-2141324277/10000000000 : ℝ)|=(2141324277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86050343/156250000 : ℝ)|^4177 ≤ (22686382095809/50000000000000 : ℝ)^3153
        have hw : |(86050343/156250000 : ℝ)|=(86050343/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5162232139/10000000000 : ℝ)|^4177 ≤ (41646236181149/100000000000000 : ℝ)^3153
        have hw : |(5162232139/10000000000 : ℝ)|=(5162232139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s2_1 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373048781/10000000000 : ℝ)*x 0 + (-2320552517/10000000000 : ℝ)*x 1 + (2581117347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373048781/10000000000 : ℝ)^4177 ≤ (21957079554067/50000000000000 : ℝ)^3153 := by
    have hnat : (5373048781 : ℕ)^4177*50000000000000^3153 ≤ 21957079554067^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373048781 10000000000 21957079554067 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2320552517/10000000000 : ℝ)^4177 ≤ (1804947173791/12500000000000 : ℝ)^3153 := by
    have hnat : (2320552517 : ℕ)^4177*12500000000000^3153 ≤ 1804947173791^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320552517 10000000000 1804947173791 12500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2581117347/5000000000 : ℝ)^4177 ≤ (20823131743939/50000000000000 : ℝ)^3153 := by
    have hnat : (2581117347 : ℕ)^4177*50000000000000^3153 ≤ 20823131743939^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581117347 5000000000 20823131743939 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373048781/10000000000 : ℝ), (-2320552517/10000000000 : ℝ), (2581117347/5000000000 : ℝ)] ![(21957079554067/50000000000000 : ℝ), (1804947173791/12500000000000 : ℝ), (20823131743939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373048781/10000000000 : ℝ)|^4177 ≤ (21957079554067/50000000000000 : ℝ)^3153
        have hw : |(5373048781/10000000000 : ℝ)|=(5373048781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2320552517/10000000000 : ℝ)|^4177 ≤ (1804947173791/12500000000000 : ℝ)^3153
        have hw : |(-2320552517/10000000000 : ℝ)|=(2320552517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2581117347/5000000000 : ℝ)|^4177 ≤ (20823131743939/50000000000000 : ℝ)^3153
        have hw : |(2581117347/5000000000 : ℝ)|=(2581117347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s2_2 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373049099/10000000000 : ℝ)*x 0 + (5162234073/10000000000 : ℝ)*x 1 + (-464110581/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373049099/10000000000 : ℝ)^4177 ≤ (2744635159453/6250000000000 : ℝ)^3153 := by
    have hnat : (5373049099 : ℕ)^4177*6250000000000^3153 ≤ 2744635159453^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373049099 10000000000 2744635159453 6250000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5162234073/10000000000 : ℝ)^4177 ≤ (41646256850899/100000000000000 : ℝ)^3153 := by
    have hnat : (5162234073 : ℕ)^4177*100000000000000^3153 ≤ 41646256850899^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162234073 10000000000 41646256850899 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464110581/2000000000 : ℝ)^4177 ≤ (14439580588747/100000000000000 : ℝ)^3153 := by
    have hnat : (464110581 : ℕ)^4177*100000000000000^3153 ≤ 14439580588747^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464110581 2000000000 14439580588747 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373049099/10000000000 : ℝ), (5162234073/10000000000 : ℝ), (-464110581/2000000000 : ℝ)] ![(2744635159453/6250000000000 : ℝ), (41646256850899/100000000000000 : ℝ), (14439580588747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373049099/10000000000 : ℝ)|^4177 ≤ (2744635159453/6250000000000 : ℝ)^3153
        have hw : |(5373049099/10000000000 : ℝ)|=(5373049099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5162234073/10000000000 : ℝ)|^4177 ≤ (41646256850899/100000000000000 : ℝ)^3153
        have hw : |(5162234073/10000000000 : ℝ)|=(5162234073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-464110581/2000000000 : ℝ)|^4177 ≤ (14439580588747/100000000000000 : ℝ)^3153
        have hw : |(-464110581/2000000000 : ℝ)|=(464110581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s2_3 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4351697063/10000000000 : ℝ)*x 0 + (2010348347/5000000000 : ℝ)*x 1 + (470959893/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351697063/10000000000 : ℝ)^4177 ≤ (33212824036087/100000000000000 : ℝ)^3153 := by
    have hnat : (4351697063 : ℕ)^4177*100000000000000^3153 ≤ 33212824036087^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351697063 10000000000 33212824036087 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010348347/5000000000 : ℝ)^4177 ≤ (14954098284351/50000000000000 : ℝ)^3153 := by
    have hnat : (2010348347 : ℕ)^4177*50000000000000^3153 ≤ 14954098284351^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010348347 5000000000 14954098284351 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470959893/1000000000 : ℝ)^4177 ≤ (36878979376057/100000000000000 : ℝ)^3153 := by
    have hnat : (470959893 : ℕ)^4177*100000000000000^3153 ≤ 36878979376057^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470959893 1000000000 36878979376057 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351697063/10000000000 : ℝ), (2010348347/5000000000 : ℝ), (470959893/1000000000 : ℝ)] ![(33212824036087/100000000000000 : ℝ), (14954098284351/50000000000000 : ℝ), (36878979376057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351697063/10000000000 : ℝ)|^4177 ≤ (33212824036087/100000000000000 : ℝ)^3153
        have hw : |(4351697063/10000000000 : ℝ)|=(4351697063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010348347/5000000000 : ℝ)|^4177 ≤ (14954098284351/50000000000000 : ℝ)^3153
        have hw : |(2010348347/5000000000 : ℝ)|=(2010348347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(470959893/1000000000 : ℝ)|^4177 ≤ (36878979376057/100000000000000 : ℝ)^3153
        have hw : |(470959893/1000000000 : ℝ)|=(470959893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s2_4 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-535355287/2500000000 : ℝ)*x 0 + (322786257/625000000 : ℝ)*x 1 + (5504851181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535355287/2500000000 : ℝ)^4177 ≤ (12981777576927/100000000000000 : ℝ)^3153 := by
    have hnat : (535355287 : ℕ)^4177*100000000000000^3153 ≤ 12981777576927^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535355287 2500000000 12981777576927 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322786257/625000000 : ℝ)^4177 ≤ (41671332146289/100000000000000 : ℝ)^3153 := by
    have hnat : (322786257 : ℕ)^4177*100000000000000^3153 ≤ 41671332146289^3153*625000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322786257 625000000 41671332146289 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5504851181/10000000000 : ℝ)^4177 ≤ (45346890261191/100000000000000 : ℝ)^3153 := by
    have hnat : (5504851181 : ℕ)^4177*100000000000000^3153 ≤ 45346890261191^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504851181 10000000000 45346890261191 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535355287/2500000000 : ℝ), (322786257/625000000 : ℝ), (5504851181/10000000000 : ℝ)] ![(12981777576927/100000000000000 : ℝ), (41671332146289/100000000000000 : ℝ), (45346890261191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535355287/2500000000 : ℝ)|^4177 ≤ (12981777576927/100000000000000 : ℝ)^3153
        have hw : |(-535355287/2500000000 : ℝ)|=(535355287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(322786257/625000000 : ℝ)|^4177 ≤ (41671332146289/100000000000000 : ℝ)^3153
        have hw : |(322786257/625000000 : ℝ)|=(322786257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5504851181/10000000000 : ℝ)|^4177 ≤ (45346890261191/100000000000000 : ℝ)^3153
        have hw : |(5504851181/10000000000 : ℝ)|=(5504851181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s2_5 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285405479/10000000000 : ℝ)*x 0 + (-1977934953/10000000000 : ℝ)*x 1 + (5504851173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285405479/10000000000 : ℝ)^4177 ≤ (42967732616531/100000000000000 : ℝ)^3153 := by
    have hnat : (5285405479 : ℕ)^4177*100000000000000^3153 ≤ 42967732616531^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285405479 10000000000 42967732616531 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1977934953/10000000000 : ℝ)^4177 ≤ (2337075439023/20000000000000 : ℝ)^3153 := by
    have hnat : (1977934953 : ℕ)^4177*20000000000000^3153 ≤ 2337075439023^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977934953 10000000000 2337075439023 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5504851173/10000000000 : ℝ)^4177 ≤ (708545158967/1562500000000 : ℝ)^3153 := by
    have hnat : (5504851173 : ℕ)^4177*1562500000000^3153 ≤ 708545158967^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504851173 10000000000 708545158967 1562500000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285405479/10000000000 : ℝ), (-1977934953/10000000000 : ℝ), (5504851173/10000000000 : ℝ)] ![(42967732616531/100000000000000 : ℝ), (2337075439023/20000000000000 : ℝ), (708545158967/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285405479/10000000000 : ℝ)|^4177 ≤ (42967732616531/100000000000000 : ℝ)^3153
        have hw : |(5285405479/10000000000 : ℝ)|=(5285405479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1977934953/10000000000 : ℝ)|^4177 ≤ (2337075439023/20000000000000 : ℝ)^3153
        have hw : |(-1977934953/10000000000 : ℝ)|=(1977934953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5504851173/10000000000 : ℝ)|^4177 ≤ (708545158967/1562500000000 : ℝ)^3153
        have hw : |(5504851173/10000000000 : ℝ)|=(5504851173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s2_6 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057081119/2000000000 : ℝ)*x 0 + (172026599/312500000 : ℝ)*x 1 + (-4944837/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057081119/2000000000 : ℝ)^4177 ≤ (42967733865819/100000000000000 : ℝ)^3153 := by
    have hnat : (1057081119 : ℕ)^4177*100000000000000^3153 ≤ 42967733865819^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057081119 2000000000 42967733865819 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172026599/312500000 : ℝ)^4177 ≤ (45346890119323/100000000000000 : ℝ)^3153 := by
    have hnat : (172026599 : ℕ)^4177*100000000000000^3153 ≤ 45346890119323^3153*312500000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172026599 312500000 45346890119323 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4944837/25000000 : ℝ)^4177 ≤ (11685375997651/100000000000000 : ℝ)^3153 := by
    have hnat : (4944837 : ℕ)^4177*100000000000000^3153 ≤ 11685375997651^3153*25000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4944837 25000000 11685375997651 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057081119/2000000000 : ℝ), (172026599/312500000 : ℝ), (-4944837/25000000 : ℝ)] ![(42967733865819/100000000000000 : ℝ), (45346890119323/100000000000000 : ℝ), (11685375997651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057081119/2000000000 : ℝ)|^4177 ≤ (42967733865819/100000000000000 : ℝ)^3153
        have hw : |(1057081119/2000000000 : ℝ)|=(1057081119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(172026599/312500000 : ℝ)|^4177 ≤ (45346890119323/100000000000000 : ℝ)^3153
        have hw : |(172026599/312500000 : ℝ)|=(172026599/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4944837/25000000 : ℝ)|^4177 ≤ (11685375997651/100000000000000 : ℝ)^3153
        have hw : |(-4944837/25000000 : ℝ)|=(4944837/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s2_7 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (870378419/2000000000 : ℝ)*x 0 + (2352456333/5000000000 : ℝ)*x 1 + (402542813/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870378419/2000000000 : ℝ)^4177 ≤ (1328591839587/4000000000000 : ℝ)^3153 := by
    have hnat : (870378419 : ℕ)^4177*4000000000000^3153 ≤ 1328591839587^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870378419 2000000000 1328591839587 4000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2352456333/5000000000 : ℝ)^4177 ≤ (7366074627147/20000000000000 : ℝ)^3153 := by
    have hnat : (2352456333 : ℕ)^4177*20000000000000^3153 ≤ 7366074627147^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2352456333 5000000000 7366074627147 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402542813/1000000000 : ℝ)^4177 ≤ (29954830856371/100000000000000 : ℝ)^3153 := by
    have hnat : (402542813 : ℕ)^4177*100000000000000^3153 ≤ 29954830856371^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402542813 1000000000 29954830856371 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870378419/2000000000 : ℝ), (2352456333/5000000000 : ℝ), (402542813/1000000000 : ℝ)] ![(1328591839587/4000000000000 : ℝ), (7366074627147/20000000000000 : ℝ), (29954830856371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870378419/2000000000 : ℝ)|^4177 ≤ (1328591839587/4000000000000 : ℝ)^3153
        have hw : |(870378419/2000000000 : ℝ)|=(870378419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2352456333/5000000000 : ℝ)|^4177 ≤ (7366074627147/20000000000000 : ℝ)^3153
        have hw : |(2352456333/5000000000 : ℝ)|=(2352456333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(402542813/1000000000 : ℝ)|^4177 ≤ (29954830856371/100000000000000 : ℝ)^3153
        have hw : |(402542813/1000000000 : ℝ)|=(402542813/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1161_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20351/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1151/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1831/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8223/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20351/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1151/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20351/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1151/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20351/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1151/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20351/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1151/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20351/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1151/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20351/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1151/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1151/20000 : ℝ) ^ (8353/2048 : ℝ) ≤ (876404111866539/100000000000000000000 : ℝ) := by
    have hpowers : (1151/20000 : ℝ)^8353 ≤ (876404111866539/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1151 : ℕ)^8353*100000000000000000000^2048 ≤ 876404111866539^2048*20000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1151 20000 876404111866539 100000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1151/20000 : ℝ)) (X := (876404111866539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20351/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (151352177875194009/100000000000000000000 : ℝ) := by
    have hpowers : (20351/100000 : ℝ)^8353 ≤ (151352177875194009/100000000000000000000 : ℝ)^2048 := by
      have hnat : (20351 : ℕ)^8353*100000000000000000000^2048 ≤ 151352177875194009^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20351 100000 151352177875194009 100000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20351/100000 : ℝ)) (X := (151352177875194009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000876404111866539/50000000000000000000 : ℝ) ≤ (10000042975308217/10000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (50000876404111866539/50000000000000000000 : ℝ)^2048 ≤ (10000042975308217/10000000000000000 : ℝ)^8353 := by
      have hnat : (50000876404111866539 : ℕ)^2048*10000000000000000^8353 ≤ 10000042975308217^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000876404111866539 50000000000000000000 10000042975308217 10000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000042975308217/10000000000000000 : ℝ)) (X := (50000876404111866539/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25038057145496765137/25000000000000000000 : ℝ) ≤ (2500932554707869/2500000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (25038057145496765137/25000000000000000000 : ℝ)^2048 ≤ (2500932554707869/2500000000000000 : ℝ)^8353 := by
      have hnat : (25038057145496765137 : ℕ)^2048*2500000000000000^8353 ≤ 2500932554707869^8353*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25038057145496765137 25000000000000000000 2500932554707869 2500000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500932554707869/2500000000000000 : ℝ)) (X := (25038057145496765137/25000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50151352177875194009/50000000000000000000 : ℝ) ≤ (2001483492470947/2000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (50151352177875194009/50000000000000000000 : ℝ)^2048 ≤ (2001483492470947/2000000000000000 : ℝ)^8353 := by
      have hnat : (50151352177875194009 : ℕ)^2048*2000000000000000^8353 ≤ 2001483492470947^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50151352177875194009 50000000000000000000 2001483492470947 2000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001483492470947/2000000000000000 : ℝ)) (X := (50151352177875194009/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(876404111866539/100000000000000000000 : ℝ) ≤ ((72959093547323012121/72980000000000000000 : ℝ)+2*(3687243523259/1459600000000000 : ℝ)*(1151/20000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (72959093547323012121/72980000000000000000 : ℝ)+2*(3687243523259/1459600000000000 : ℝ)*(1151/20000 : ℝ)=(10000042975308217/10000000000000000 : ℝ) by norm_num, show 1+2*(876404111866539/100000000000000000000 : ℝ)=(50000876404111866539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(151352177875194009/100000000000000000000 : ℝ)+(876404111866539/100000000000000000000 : ℝ) ≤ ((72959093547323012121/72980000000000000000 : ℝ)+(3687243523259/1459600000000000 : ℝ)*((20351/100000 : ℝ)+(1151/20000 : ℝ)))^(8353/2048 : ℝ) := by
    rw [show (72959093547323012121/72980000000000000000 : ℝ)+(3687243523259/1459600000000000 : ℝ)*((20351/100000 : ℝ)+(1151/20000 : ℝ))=(2500932554707869/2500000000000000 : ℝ) by norm_num, show 1+(151352177875194009/100000000000000000000 : ℝ)+(876404111866539/100000000000000000000 : ℝ)=(25038057145496765137/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(151352177875194009/100000000000000000000 : ℝ) ≤ ((72959093547323012121/72980000000000000000 : ℝ)+2*(3687243523259/1459600000000000 : ℝ)*(20351/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (72959093547323012121/72980000000000000000 : ℝ)+2*(3687243523259/1459600000000000 : ℝ)*(20351/100000 : ℝ)=(2001483492470947/2000000000000000 : ℝ) by norm_num, show 1+2*(151352177875194009/100000000000000000000 : ℝ)=(50151352177875194009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72959093547323012121/72980000000000000000 : ℝ)*(X 1 0+X 2 0)+(3687243523259/1459600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (1151/20000 : ℝ)) (hi := (20351/100000 : ℝ)) (c := (72959093547323012121/72980000000000000000 : ℝ)) (alpha := (3687243523259/1459600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72959093547323012121/72980000000000000000 : ℝ)*(X 0 1+X 2 1)+(3687243523259/1459600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (1151/20000 : ℝ)) (hi := (20351/100000 : ℝ)) (c := (72959093547323012121/72980000000000000000 : ℝ)) (alpha := (3687243523259/1459600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72959093547323012121/72980000000000000000 : ℝ)*(X 0 2+X 1 2)+(3687243523259/1459600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (1151/20000 : ℝ)) (hi := (20351/100000 : ℝ)) (c := (72959093547323012121/72980000000000000000 : ℝ)) (alpha := (3687243523259/1459600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2141324277/10000000000 : ℝ)*X 0 0+(86050343/156250000 : ℝ)*X 0 1+(5162232139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5373048781/10000000000 : ℝ)*X 1 0+(-2320552517/10000000000 : ℝ)*X 1 1+(2581117347/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5373049099/10000000000 : ℝ)*X 2 0+(5162234073/10000000000 : ℝ)*X 2 1+(-464110581/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351697063/10000000000 : ℝ)*X 0 0+(2010348347/5000000000 : ℝ)*X 0 1+(470959893/1000000000 : ℝ)*X 0 2+(4351697063/10000000000 : ℝ)*X 1 0+(2010348347/5000000000 : ℝ)*X 1 1+(470959893/1000000000 : ℝ)*X 1 2+(4351697063/10000000000 : ℝ)*X 2 0+(2010348347/5000000000 : ℝ)*X 2 1+(470959893/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-535355287/2500000000 : ℝ)*X 0 0+(322786257/625000000 : ℝ)*X 0 1+(5504851181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5285405479/10000000000 : ℝ)*X 1 0+(-1977934953/10000000000 : ℝ)*X 1 1+(5504851173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057081119/2000000000 : ℝ)*X 2 0+(172026599/312500000 : ℝ)*X 2 1+(-4944837/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870378419/2000000000 : ℝ)*X 0 0+(2352456333/5000000000 : ℝ)*X 0 1+(402542813/1000000000 : ℝ)*X 0 2+(870378419/2000000000 : ℝ)*X 1 0+(2352456333/5000000000 : ℝ)*X 1 1+(402542813/1000000000 : ℝ)*X 1 2+(870378419/2000000000 : ℝ)*X 2 0+(2352456333/5000000000 : ℝ)*X 2 1+(402542813/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (207098244960188108735541/18245000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37183967/2500000000000 : ℝ)*(base19) + (1303008433/100000000000000 : ℝ)*(base23) + (502518019/100000000000000 : ℝ)*(upper3) + (191230843/100000000000000 : ℝ)*(upper4) + (9244119/50000000000000 : ℝ)*(upper5) + (543788011598157/25000000000000 : ℝ)*(major0) + (543788011598157/25000000000000 : ℝ)*(major1) + (543788011598157/25000000000000 : ℝ)*(major2) + (724667527517453/25000000000000 : ℝ)*(sp0) + (1449348286769073/50000000000000 : ℝ)*(sp1) + (362337094736049/12500000000000 : ℝ)*(sp2) + (725796370870687/50000000000000 : ℝ)*(sp3) + (27950827013/100000000000000 : ℝ)*(sp4) + (12911781753/100000000000000 : ℝ)*(sp7) + (1451605653523127/100000000000000 : ℝ)*(f.failure) + (1449349030448413/50000000000000 : ℝ)*(f.sum) + (48816492070329/9122500000000000000000000000 : ℝ)*base65 + (10219893664192410997/1824500000000000000000000000000000 : ℝ)*base67 + (11171278509134089003/1824500000000000000000000000000000 : ℝ)*base70 + (6710928438061910997/1824500000000000000000000000000000 : ℝ)*base71 + (86551749782523/18245000000000000000000000000 : ℝ)*base73 + (22362391323557589003/1824500000000000000000000000000000 : ℝ)*base76 + (223264090302910997/1824500000000000000000000000000000 : ℝ)*base77 + (5329411482939589003/1824500000000000000000000000000000 : ℝ)*base80 + (101121344489087/18245000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (261653/2500000000000000000000 : ℝ)*base89 + (261653/2500000000000000000000 : ℝ)*base91 + (261653/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (249531500051079683271227649/91225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (741196907/100000000000000 : ℝ)*(base19) + (885884067/100000000000000 : ℝ)*(base23) + (11152323/50000000000000 : ℝ)*(upper2) + (47122709/50000000000000 : ℝ)*(upper3) + (7956863/12500000000000 : ℝ)*(upper5) + (110263432460123/5000000000000 : ℝ)*(major0) + (110263432460123/5000000000000 : ℝ)*(major1) + (110263432460123/5000000000000 : ℝ)*(major2) + (431573223/6250000000000 : ℝ)*(sp1) + (9196019241/100000000000000 : ℝ)*(sp2) + (2938832990490123/100000000000000 : ℝ)*(sp4) + (183676584007603/6250000000000 : ℝ)*(sp5) + (45919107946669/1562500000000 : ℝ)*(sp6) + (5886816866947/400000000000 : ℝ)*(sp7) + (5886816866947/400000000000 : ℝ)*(f.failure) + (2938832990490123/100000000000000 : ℝ)*(f.sum) + (13258888503003/3649000000000000000000000000 : ℝ)*base65 + (2261515444191399117/364900000000000000000000000000000 : ℝ)*base68 + (4850573441597699117/364900000000000000000000000000000 : ℝ)*base70 + (2424425039703999117/364900000000000000000000000000000 : ℝ)*base72 + (2857307717843/3649000000000000000000000000 : ℝ)*base74 + (2527652164839399117/364900000000000000000000000000000 : ℝ)*base76 + (38145895098900883/364900000000000000000000000000000 : ℝ)*base77 + (5458975742925899117/364900000000000000000000000000000 : ℝ)*base80 + (6479707842649/1824500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (72633/10000000000000000000 : ℝ)*base89 + (72633/10000000000000000000 : ℝ)*base91 + (72633/10000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1161_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20351/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1151/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8223/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1161_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1161_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8223/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1161_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1161_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1161_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8223/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1161_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
