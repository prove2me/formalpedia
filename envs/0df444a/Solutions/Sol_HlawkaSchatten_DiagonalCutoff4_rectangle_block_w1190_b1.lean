-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1190_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:53:07.700574+00:00
-- url     : https://prove2.me/submissions/5f4ca4f7-8f52-46f8-baf7-fb3fe4ed43fe

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
theorem support_rectangle_w1190_s3_0 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140831009/10000000000 : ℝ)*x 0 + (2712208973/5000000000 : ℝ)*x 1 + (654549071/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140831009/10000000000 : ℝ)^8383 ≤ (13006810725961/100000000000000 : ℝ)^6335 := by
    have hnat : (2140831009 : ℕ)^8383*100000000000000^6335 ≤ 13006810725961^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140831009 10000000000 13006810725961 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712208973/5000000000 : ℝ)^8383 ≤ (8902335045221/20000000000000 : ℝ)^6335 := by
    have hnat : (2712208973 : ℕ)^8383*20000000000000^6335 ≤ 8902335045221^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712208973 5000000000 8902335045221 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654549071/1250000000 : ℝ)^8383 ≤ (42481514025431/100000000000000 : ℝ)^6335 := by
    have hnat : (654549071 : ℕ)^8383*100000000000000^6335 ≤ 42481514025431^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654549071 1250000000 42481514025431 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140831009/10000000000 : ℝ), (2712208973/5000000000 : ℝ), (654549071/1250000000 : ℝ)] ![(13006810725961/100000000000000 : ℝ), (8902335045221/20000000000000 : ℝ), (42481514025431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140831009/10000000000 : ℝ)|^8383 ≤ (13006810725961/100000000000000 : ℝ)^6335
        have hw : |(-2140831009/10000000000 : ℝ)|=(2140831009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712208973/5000000000 : ℝ)|^8383 ≤ (8902335045221/20000000000000 : ℝ)^6335
        have hw : |(2712208973/5000000000 : ℝ)|=(2712208973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654549071/1250000000 : ℝ)|^8383 ≤ (42481514025431/100000000000000 : ℝ)^6335
        have hw : |(654549071/1250000000 : ℝ)|=(654549071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s3_1 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (669083/1250000 : ℝ)*x 0 + (-2236846089/10000000000 : ℝ)*x 1 + (1047278523/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669083/1250000 : ℝ)^8383 ≤ (43734199136079/100000000000000 : ℝ)^6335 := by
    have hnat : (669083 : ℕ)^8383*100000000000000^6335 ≤ 43734199136079^6335*1250000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669083 1250000 43734199136079 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236846089/10000000000 : ℝ)^8383 ≤ (1378428631647/10000000000000 : ℝ)^6335 := by
    have hnat : (2236846089 : ℕ)^8383*10000000000000^6335 ≤ 1378428631647^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236846089 10000000000 1378428631647 10000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047278523/2000000000 : ℝ)^8383 ≤ (21240757264999/50000000000000 : ℝ)^6335 := by
    have hnat : (1047278523 : ℕ)^8383*50000000000000^6335 ≤ 21240757264999^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047278523 2000000000 21240757264999 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669083/1250000 : ℝ), (-2236846089/10000000000 : ℝ), (1047278523/2000000000 : ℝ)] ![(43734199136079/100000000000000 : ℝ), (1378428631647/10000000000000 : ℝ), (21240757264999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669083/1250000 : ℝ)|^8383 ≤ (43734199136079/100000000000000 : ℝ)^6335
        have hw : |(669083/1250000 : ℝ)|=(669083/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2236846089/10000000000 : ℝ)|^8383 ≤ (1378428631647/10000000000000 : ℝ)^6335
        have hw : |(-2236846089/10000000000 : ℝ)|=(2236846089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047278523/2000000000 : ℝ)|^8383 ≤ (21240757264999/50000000000000 : ℝ)^6335
        have hw : |(1047278523/2000000000 : ℝ)|=(1047278523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s3_2 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352663967/10000000000 : ℝ)*x 0 + (2618196361/5000000000 : ℝ)*x 1 + (-2236845991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352663967/10000000000 : ℝ)^8383 ≤ (8746839755857/20000000000000 : ℝ)^6335 := by
    have hnat : (5352663967 : ℕ)^8383*20000000000000^6335 ≤ 8746839755857^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352663967 10000000000 8746839755857 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618196361/5000000000 : ℝ)^8383 ≤ (10620378919673/25000000000000 : ℝ)^6335 := by
    have hnat : (2618196361 : ℕ)^8383*25000000000000^6335 ≤ 10620378919673^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618196361 5000000000 10620378919673 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236845991/10000000000 : ℝ)^8383 ≤ (6892142758661/50000000000000 : ℝ)^6335 := by
    have hnat : (2236845991 : ℕ)^8383*50000000000000^6335 ≤ 6892142758661^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236845991 10000000000 6892142758661 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352663967/10000000000 : ℝ), (2618196361/5000000000 : ℝ), (-2236845991/10000000000 : ℝ)] ![(8746839755857/20000000000000 : ℝ), (10620378919673/25000000000000 : ℝ), (6892142758661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352663967/10000000000 : ℝ)|^8383 ≤ (8746839755857/20000000000000 : ℝ)^6335
        have hw : |(5352663967/10000000000 : ℝ)|=(5352663967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618196361/5000000000 : ℝ)|^8383 ≤ (10620378919673/25000000000000 : ℝ)^6335
        have hw : |(2618196361/5000000000 : ℝ)|=(2618196361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2236845991/10000000000 : ℝ)|^8383 ≤ (6892142758661/50000000000000 : ℝ)^6335
        have hw : |(-2236845991/10000000000 : ℝ)|=(2236845991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s3_3 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871196939/2000000000 : ℝ)*x 0 + (4171207733/10000000000 : ℝ)*x 1 + (4548804183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871196939/2000000000 : ℝ)^8383 ≤ (16648648161007/50000000000000 : ℝ)^6335 := by
    have hnat : (871196939 : ℕ)^8383*50000000000000^6335 ≤ 16648648161007^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871196939 2000000000 16648648161007 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171207733/10000000000 : ℝ)^8383 ≤ (31441176531553/100000000000000 : ℝ)^6335 := by
    have hnat : (4171207733 : ℕ)^8383*100000000000000^6335 ≤ 31441176531553^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171207733 10000000000 31441176531553 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4548804183/10000000000 : ℝ)^8383 ≤ (35261527137017/100000000000000 : ℝ)^6335 := by
    have hnat : (4548804183 : ℕ)^8383*100000000000000^6335 ≤ 35261527137017^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4548804183 10000000000 35261527137017 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871196939/2000000000 : ℝ), (4171207733/10000000000 : ℝ), (4548804183/10000000000 : ℝ)] ![(16648648161007/50000000000000 : ℝ), (31441176531553/100000000000000 : ℝ), (35261527137017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871196939/2000000000 : ℝ)|^8383 ≤ (16648648161007/50000000000000 : ℝ)^6335
        have hw : |(871196939/2000000000 : ℝ)|=(871196939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171207733/10000000000 : ℝ)|^8383 ≤ (31441176531553/100000000000000 : ℝ)^6335
        have hw : |(4171207733/10000000000 : ℝ)|=(4171207733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4548804183/10000000000 : ℝ)|^8383 ≤ (35261527137017/100000000000000 : ℝ)^6335
        have hw : |(4548804183/10000000000 : ℝ)|=(4548804183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s3_4 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140847023/10000000000 : ℝ)*x 0 + (654637373/1250000000 : ℝ)*x 1 + (2711853827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140847023/10000000000 : ℝ)^8383 ≤ (6503469737149/50000000000000 : ℝ)^6335 := by
    have hnat : (2140847023 : ℕ)^8383*50000000000000^6335 ≤ 6503469737149^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140847023 10000000000 6503469737149 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654637373/1250000000 : ℝ)^8383 ≤ (10622274472779/25000000000000 : ℝ)^6335 := by
    have hnat : (654637373 : ℕ)^8383*25000000000000^6335 ≤ 10622274472779^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654637373 1250000000 10622274472779 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711853827/5000000000 : ℝ)^8383 ≤ (5562995327009/12500000000000 : ℝ)^6335 := by
    have hnat : (2711853827 : ℕ)^8383*12500000000000^6335 ≤ 5562995327009^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711853827 5000000000 5562995327009 12500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140847023/10000000000 : ℝ), (654637373/1250000000 : ℝ), (2711853827/5000000000 : ℝ)] ![(6503469737149/50000000000000 : ℝ), (10622274472779/25000000000000 : ℝ), (5562995327009/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140847023/10000000000 : ℝ)|^8383 ≤ (6503469737149/50000000000000 : ℝ)^6335
        have hw : |(-2140847023/10000000000 : ℝ)|=(2140847023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654637373/1250000000 : ℝ)|^8383 ≤ (10622274472779/25000000000000 : ℝ)^6335
        have hw : |(654637373/1250000000 : ℝ)|=(654637373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711853827/5000000000 : ℝ)|^8383 ≤ (5562995327009/12500000000000 : ℝ)^6335
        have hw : |(2711853827/5000000000 : ℝ)|=(2711853827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s3_5 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1326216271/2500000000 : ℝ)*x 0 + (-512382679/2500000000 : ℝ)*x 1 + (5423707589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326216271/2500000000 : ℝ)^8383 ≤ (43218147111637/100000000000000 : ℝ)^6335 := by
    have hnat : (1326216271 : ℕ)^8383*100000000000000^6335 ≤ 43218147111637^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326216271 2500000000 43218147111637 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512382679/2500000000 : ℝ)^8383 ≤ (6138945485089/50000000000000 : ℝ)^6335 := by
    have hnat : (512382679 : ℕ)^8383*50000000000000^6335 ≤ 6138945485089^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512382679 2500000000 6138945485089 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423707589/10000000000 : ℝ)^8383 ≤ (44503961910293/100000000000000 : ℝ)^6335 := by
    have hnat : (5423707589 : ℕ)^8383*100000000000000^6335 ≤ 44503961910293^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423707589 10000000000 44503961910293 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326216271/2500000000 : ℝ), (-512382679/2500000000 : ℝ), (5423707589/10000000000 : ℝ)] ![(43218147111637/100000000000000 : ℝ), (6138945485089/50000000000000 : ℝ), (44503961910293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326216271/2500000000 : ℝ)|^8383 ≤ (43218147111637/100000000000000 : ℝ)^6335
        have hw : |(1326216271/2500000000 : ℝ)|=(1326216271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-512382679/2500000000 : ℝ)|^8383 ≤ (6138945485089/50000000000000 : ℝ)^6335
        have hw : |(-512382679/2500000000 : ℝ)|=(512382679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423707589/10000000000 : ℝ)|^8383 ≤ (44503961910293/100000000000000 : ℝ)^6335
        have hw : |(5423707589/10000000000 : ℝ)|=(5423707589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s3_6 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304864721/10000000000 : ℝ)*x 0 + (5423707983/10000000000 : ℝ)*x 1 + (-2049530669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304864721/10000000000 : ℝ)^8383 ≤ (43218143198263/100000000000000 : ℝ)^6335 := by
    have hnat : (5304864721 : ℕ)^8383*100000000000000^6335 ≤ 43218143198263^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304864721 10000000000 43218143198263 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423707983/10000000000 : ℝ)^8383 ≤ (22251983094199/50000000000000 : ℝ)^6335 := by
    have hnat : (5423707983 : ℕ)^8383*50000000000000^6335 ≤ 22251983094199^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423707983 10000000000 22251983094199 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2049530669/10000000000 : ℝ)^8383 ≤ (12277890597597/100000000000000 : ℝ)^6335 := by
    have hnat : (2049530669 : ℕ)^8383*100000000000000^6335 ≤ 12277890597597^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049530669 10000000000 12277890597597 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304864721/10000000000 : ℝ), (5423707983/10000000000 : ℝ), (-2049530669/10000000000 : ℝ)] ![(43218143198263/100000000000000 : ℝ), (22251983094199/50000000000000 : ℝ), (12277890597597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304864721/10000000000 : ℝ)|^8383 ≤ (43218143198263/100000000000000 : ℝ)^6335
        have hw : |(5304864721/10000000000 : ℝ)|=(5304864721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423707983/10000000000 : ℝ)|^8383 ≤ (22251983094199/50000000000000 : ℝ)^6335
        have hw : |(5423707983/10000000000 : ℝ)|=(5423707983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2049530669/10000000000 : ℝ)|^8383 ≤ (12277890597597/100000000000000 : ℝ)^6335
        have hw : |(-2049530669/10000000000 : ℝ)|=(2049530669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s3_7 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (544502137/1250000000 : ℝ)*x 0 + (2273692597/5000000000 : ℝ)*x 1 + (2086317013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544502137/1250000000 : ℝ)^8383 ≤ (33297624065757/100000000000000 : ℝ)^6335 := by
    have hnat : (544502137 : ℕ)^8383*100000000000000^6335 ≤ 33297624065757^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544502137 1250000000 33297624065757 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2273692597/5000000000 : ℝ)^8383 ≤ (17623486041017/50000000000000 : ℝ)^6335 := by
    have hnat : (2273692597 : ℕ)^8383*50000000000000^6335 ≤ 17623486041017^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273692597 5000000000 17623486041017 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086317013/5000000000 : ℝ)^8383 ≤ (491490684909/1562500000000 : ℝ)^6335 := by
    have hnat : (2086317013 : ℕ)^8383*1562500000000^6335 ≤ 491490684909^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086317013 5000000000 491490684909 1562500000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544502137/1250000000 : ℝ), (2273692597/5000000000 : ℝ), (2086317013/5000000000 : ℝ)] ![(33297624065757/100000000000000 : ℝ), (17623486041017/50000000000000 : ℝ), (491490684909/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544502137/1250000000 : ℝ)|^8383 ≤ (33297624065757/100000000000000 : ℝ)^6335
        have hw : |(544502137/1250000000 : ℝ)|=(544502137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2273692597/5000000000 : ℝ)|^8383 ≤ (17623486041017/50000000000000 : ℝ)^6335
        have hw : |(2273692597/5000000000 : ℝ)|=(2273692597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086317013/5000000000 : ℝ)|^8383 ≤ (491490684909/1562500000000 : ℝ)^6335
        have hw : |(2086317013/5000000000 : ℝ)|=(2086317013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1190_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4641/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10773/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (461/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4091/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4641/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4091/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4641/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4091/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4641/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4091/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4641/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4091/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4641/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4091/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4641/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4641/50000 : ℝ) ^ (4191/1024 : ℝ) ≤ (47630024235381/800000000000000000 : ℝ) := by
    have hpowers : (4641/50000 : ℝ)^4191 ≤ (47630024235381/800000000000000000 : ℝ)^1024 := by
      have hnat : (4641 : ℕ)^4191*800000000000000000^1024 ≤ 47630024235381^1024*50000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4641 50000 47630024235381 800000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4641/50000 : ℝ)) (X := (47630024235381/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4091/25000 : ℝ) ^ (4191/1024 : ℝ) ≤ (15155410910101993/25000000000000000000 : ℝ) := by
    have hpowers : (4091/25000 : ℝ)^4191 ≤ (15155410910101993/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4091 : ℕ)^4191*25000000000000000000^1024 ≤ 15155410910101993^1024*25000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4091 25000 15155410910101993 25000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4091/25000 : ℝ)) (X := (15155410910101993/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (400047630024235381/400000000000000000 : ℝ) ≤ (5000145463345979/5000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (400047630024235381/400000000000000000 : ℝ)^1024 ≤ (5000145463345979/5000000000000000 : ℝ)^4191 := by
      have hnat : (400047630024235381 : ℕ)^1024*5000000000000000^4191 ≤ 5000145463345979^4191*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400047630024235381 400000000000000000 5000145463345979 5000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000145463345979/5000000000000000 : ℝ)) (X := (400047630024235381/400000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100066575396669830597/100000000000000000000 : ℝ) ≤ (10001626248253377/10000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (100066575396669830597/100000000000000000000 : ℝ)^1024 ≤ (10001626248253377/10000000000000000 : ℝ)^4191 := by
      have hnat : (100066575396669830597 : ℕ)^1024*10000000000000000^4191 ≤ 10001626248253377^4191*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100066575396669830597 100000000000000000000 10001626248253377 10000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001626248253377/10000000000000000 : ℝ)) (X := (100066575396669830597/100000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12515155410910101993/12500000000000000000 : ℝ) ≤ (2500740392453699/2500000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (12515155410910101993/12500000000000000000 : ℝ)^1024 ≤ (2500740392453699/2500000000000000 : ℝ)^4191 := by
      have hnat : (12515155410910101993 : ℕ)^1024*2500000000000000^4191 ≤ 2500740392453699^4191*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12515155410910101993 12500000000000000000 2500740392453699 2500000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500740392453699/2500000000000000 : ℝ)) (X := (12515155410910101993/12500000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(47630024235381/800000000000000000 : ℝ) ≤ ((884965892917078303/885250000000000000 : ℝ)+2*(1335321561419/708200000000000 : ℝ)*(4641/50000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (884965892917078303/885250000000000000 : ℝ)+2*(1335321561419/708200000000000 : ℝ)*(4641/50000 : ℝ)=(5000145463345979/5000000000000000 : ℝ) by norm_num, show 1+2*(47630024235381/800000000000000000 : ℝ)=(400047630024235381/400000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15155410910101993/25000000000000000000 : ℝ)+(47630024235381/800000000000000000 : ℝ) ≤ ((884965892917078303/885250000000000000 : ℝ)+(1335321561419/708200000000000 : ℝ)*((4091/25000 : ℝ)+(4641/50000 : ℝ)))^(4191/1024 : ℝ) := by
    rw [show (884965892917078303/885250000000000000 : ℝ)+(1335321561419/708200000000000 : ℝ)*((4091/25000 : ℝ)+(4641/50000 : ℝ))=(10001626248253377/10000000000000000 : ℝ) by norm_num, show 1+(15155410910101993/25000000000000000000 : ℝ)+(47630024235381/800000000000000000 : ℝ)=(100066575396669830597/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15155410910101993/25000000000000000000 : ℝ) ≤ ((884965892917078303/885250000000000000 : ℝ)+2*(1335321561419/708200000000000 : ℝ)*(4091/25000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (884965892917078303/885250000000000000 : ℝ)+2*(1335321561419/708200000000000 : ℝ)*(4091/25000 : ℝ)=(2500740392453699/2500000000000000 : ℝ) by norm_num, show 1+2*(15155410910101993/25000000000000000000 : ℝ)=(12515155410910101993/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (884965892917078303/885250000000000000 : ℝ)*(X 1 0+X 2 0)+(1335321561419/708200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (4641/50000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (884965892917078303/885250000000000000 : ℝ)) (alpha := (1335321561419/708200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (884965892917078303/885250000000000000 : ℝ)*(X 0 1+X 2 1)+(1335321561419/708200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (4641/50000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (884965892917078303/885250000000000000 : ℝ)) (alpha := (1335321561419/708200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (884965892917078303/885250000000000000 : ℝ)*(X 0 2+X 1 2)+(1335321561419/708200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (4641/50000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (884965892917078303/885250000000000000 : ℝ)) (alpha := (1335321561419/708200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2140831009/10000000000 : ℝ)*X 0 0+(2712208973/5000000000 : ℝ)*X 0 1+(654549071/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669083/1250000 : ℝ)*X 1 0+(-2236846089/10000000000 : ℝ)*X 1 1+(1047278523/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352663967/10000000000 : ℝ)*X 2 0+(2618196361/5000000000 : ℝ)*X 2 1+(-2236845991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871196939/2000000000 : ℝ)*X 0 0+(4171207733/10000000000 : ℝ)*X 0 1+(4548804183/10000000000 : ℝ)*X 0 2+(871196939/2000000000 : ℝ)*X 1 0+(4171207733/10000000000 : ℝ)*X 1 1+(4548804183/10000000000 : ℝ)*X 1 2+(871196939/2000000000 : ℝ)*X 2 0+(4171207733/10000000000 : ℝ)*X 2 1+(4548804183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2140847023/10000000000 : ℝ)*X 0 0+(654637373/1250000000 : ℝ)*X 0 1+(2711853827/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326216271/2500000000 : ℝ)*X 1 0+(-512382679/2500000000 : ℝ)*X 1 1+(5423707589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304864721/10000000000 : ℝ)*X 2 0+(5423707983/10000000000 : ℝ)*X 2 1+(-2049530669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((544502137/1250000000 : ℝ)*X 0 0+(2273692597/5000000000 : ℝ)*X 0 1+(2086317013/5000000000 : ℝ)*X 0 2+(544502137/1250000000 : ℝ)*X 1 0+(2273692597/5000000000 : ℝ)*X 1 1+(2086317013/5000000000 : ℝ)*X 1 2+(544502137/1250000000 : ℝ)*X 2 0+(2273692597/5000000000 : ℝ)*X 2 1+(2086317013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47682078321600732243213/17705000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7667301/2000000000000 : ℝ)*(base19) + (137971467/50000000000000 : ℝ)*(base23) + (39948567/100000000000000 : ℝ)*(lower2) + (1330941/12500000000000 : ℝ)*(upper3) + (55527589/100000000000000 : ℝ)*(upper5) + (995848437254073/25000000000000 : ℝ)*(major0) + (995848437254073/25000000000000 : ℝ)*(major1) + (995848437254073/25000000000000 : ℝ)*(major2) + (664804919858281/12500000000000 : ℝ)*(sp0) + (2659224745449013/50000000000000 : ℝ)*(sp1) + (2659224799160071/50000000000000 : ℝ)*(sp2) + (2648333967348753/100000000000000 : ℝ)*(sp3) + (2628849207/25000000000000 : ℝ)*(sp4) + (3566649347/100000000000000 : ℝ)*(sp7) + (26483375339981/1000000000000 : ℝ)*(f.failure) + (5318449874263077/100000000000000 : ℝ)*(f.sum) + (12977153230619/17705000000000000000000000000 : ℝ)*base65 + (95200458982368119/22131250000000000000000000000000 : ℝ)*base67 + (67771776982444381/22131250000000000000000000000000 : ℝ)*base70 + (131336145154006881/22131250000000000000000000000000 : ℝ)*base72 + (28417496376309/17705000000000000000000000000 : ℝ)*base73 + (236304701610218119/22131250000000000000000000000000 : ℝ)*base75 + (170258364653030619/22131250000000000000000000000000 : ℝ)*base77 + (145018705128406881/22131250000000000000000000000000 : ℝ)*base80 + (95494649053621/17705000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (177801/20000000000000000000 : ℝ)*base89 + (177801/20000000000000000000 : ℝ)*base91 + (177801/20000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15329650683541305733096983/2213125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1003892653/50000000000000 : ℝ)*(base19) + (954650851/50000000000000 : ℝ)*(base23) + (67387791/50000000000000 : ℝ)*(upper3) + (134720311/100000000000000 : ℝ)*(lower4) + (253530263/100000000000000 : ℝ)*(upper5) + (802724059020499/20000000000000 : ℝ)*(major0) + (802724059020499/20000000000000 : ℝ)*(major1) + (802724059020499/20000000000000 : ℝ)*(major2) + (39997519831/100000000000000 : ℝ)*(sp1) + (8315775299/20000000000000 : ℝ)*(sp2) + (669850858946651/12500000000000 : ℝ)*(sp4) + (669845608283509/12500000000000 : ℝ)*(sp5) + (5358763383395011/100000000000000 : ℝ)*(sp6) + (266843348774181/10000000000000 : ℝ)*(sp7) + (266843348774181/10000000000000 : ℝ)*(f.failure) + (669850858946651/12500000000000 : ℝ)*(f.sum) + (48967850469951/7082000000000000000000000000 : ℝ)*base66 + (27592239743774447/17705000000000000000000000000000 : ℝ)*base67 + (22944545408625553/17705000000000000000000000000000 : ℝ)*base70 + (202717657905405553/17705000000000000000000000000000 : ℝ)*base72 + (3143299733503/7082000000000000000000000000 : ℝ)*base73 + (205807317176530553/17705000000000000000000000000000 : ℝ)*base76 + (42920836007745553/17705000000000000000000000000000 : ℝ)*base78 + (8871588962580553/17705000000000000000000000000000 : ℝ)*base80 + (25435987522711/7082000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1936001/200000000000000000000 : ℝ)*base89 + (1936001/200000000000000000000 : ℝ)*base91 + (1936001/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1190_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4641/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10773/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1190_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1190_s4_0 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071734363/5000000000 : ℝ)*x 0 + (674960749/1250000000 : ℝ)*x 1 + (5259397657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071734363/5000000000 : ℝ)^8383 ≤ (13028021471797/100000000000000 : ℝ)^6335 := by
    have hnat : (1071734363 : ℕ)^8383*100000000000000^6335 ≤ 13028021471797^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071734363 5000000000 13028021471797 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674960749/1250000000 : ℝ)^8383 ≤ (44243319074069/100000000000000 : ℝ)^6335 := by
    have hnat : (674960749 : ℕ)^8383*100000000000000^6335 ≤ 44243319074069^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674960749 1250000000 44243319074069 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259397657/10000000000 : ℝ)^8383 ≤ (42728659435749/100000000000000 : ℝ)^6335 := by
    have hnat : (5259397657 : ℕ)^8383*100000000000000^6335 ≤ 42728659435749^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259397657 10000000000 42728659435749 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071734363/5000000000 : ℝ), (674960749/1250000000 : ℝ), (5259397657/10000000000 : ℝ)] ![(13028021471797/100000000000000 : ℝ), (44243319074069/100000000000000 : ℝ), (42728659435749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071734363/5000000000 : ℝ)|^8383 ≤ (13028021471797/100000000000000 : ℝ)^6335
        have hw : |(-1071734363/5000000000 : ℝ)|=(1071734363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674960749/1250000000 : ℝ)|^8383 ≤ (44243319074069/100000000000000 : ℝ)^6335
        have hw : |(674960749/1250000000 : ℝ)|=(674960749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259397657/10000000000 : ℝ)|^8383 ≤ (42728659435749/100000000000000 : ℝ)^6335
        have hw : |(5259397657/10000000000 : ℝ)|=(5259397657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s4_1 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346459639/10000000000 : ℝ)*x 0 + (-2214728119/10000000000 : ℝ)*x 1 + (5259397411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346459639/10000000000 : ℝ)^8383 ≤ (10916782616187/25000000000000 : ℝ)^6335 := by
    have hnat : (5346459639 : ℕ)^8383*25000000000000^6335 ≤ 10916782616187^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346459639 10000000000 10916782616187 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2214728119/10000000000 : ℝ)^8383 ≤ (6802106359207/50000000000000 : ℝ)^6335 := by
    have hnat : (2214728119 : ℕ)^8383*50000000000000^6335 ≤ 6802106359207^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214728119 10000000000 6802106359207 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259397411/10000000000 : ℝ)^8383 ≤ (42728656791081/100000000000000 : ℝ)^6335 := by
    have hnat : (5259397411 : ℕ)^8383*100000000000000^6335 ≤ 42728656791081^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259397411 10000000000 42728656791081 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346459639/10000000000 : ℝ), (-2214728119/10000000000 : ℝ), (5259397411/10000000000 : ℝ)] ![(10916782616187/25000000000000 : ℝ), (6802106359207/50000000000000 : ℝ), (42728656791081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346459639/10000000000 : ℝ)|^8383 ≤ (10916782616187/25000000000000 : ℝ)^6335
        have hw : |(5346459639/10000000000 : ℝ)|=(5346459639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2214728119/10000000000 : ℝ)|^8383 ≤ (6802106359207/50000000000000 : ℝ)^6335
        have hw : |(-2214728119/10000000000 : ℝ)|=(2214728119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259397411/10000000000 : ℝ)|^8383 ≤ (42728656791081/100000000000000 : ℝ)^6335
        have hw : |(5259397411/10000000000 : ℝ)|=(5259397411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s4_2 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346458637/10000000000 : ℝ)*x 0 + (131484947/250000000 : ℝ)*x 1 + (-2214728833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346458637/10000000000 : ℝ)^8383 ≤ (10916779908809/25000000000000 : ℝ)^6335 := by
    have hnat : (5346458637 : ℕ)^8383*25000000000000^6335 ≤ 10916779908809^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346458637 10000000000 10916779908809 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131484947/250000000 : ℝ)^8383 ≤ (667635341143/1562500000000 : ℝ)^6335 := by
    have hnat : (131484947 : ℕ)^8383*1562500000000^6335 ≤ 667635341143^6335*250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131484947 250000000 667635341143 1562500000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214728833/10000000000 : ℝ)^8383 ≤ (6802109261051/50000000000000 : ℝ)^6335 := by
    have hnat : (2214728833 : ℕ)^8383*50000000000000^6335 ≤ 6802109261051^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214728833 10000000000 6802109261051 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346458637/10000000000 : ℝ), (131484947/250000000 : ℝ), (-2214728833/10000000000 : ℝ)] ![(10916779908809/25000000000000 : ℝ), (667635341143/1562500000000 : ℝ), (6802109261051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346458637/10000000000 : ℝ)|^8383 ≤ (10916779908809/25000000000000 : ℝ)^6335
        have hw : |(5346458637/10000000000 : ℝ)|=(5346458637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131484947/250000000 : ℝ)|^8383 ≤ (667635341143/1562500000000 : ℝ)^6335
        have hw : |(131484947/250000000 : ℝ)|=(131484947/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2214728833/10000000000 : ℝ)|^8383 ≤ (6802109261051/50000000000000 : ℝ)^6335
        have hw : |(-2214728833/10000000000 : ℝ)|=(2214728833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s4_3 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178781223/5000000000 : ℝ)*x 0 + (4218937631/10000000000 : ℝ)*x 1 + (2250334419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178781223/5000000000 : ℝ)^8383 ≤ (16656628279961/50000000000000 : ℝ)^6335 := by
    have hnat : (2178781223 : ℕ)^8383*50000000000000^6335 ≤ 16656628279961^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178781223 5000000000 16656628279961 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4218937631/10000000000 : ℝ)^8383 ≤ (15959067629763/50000000000000 : ℝ)^6335 := by
    have hnat : (4218937631 : ℕ)^8383*50000000000000^6335 ≤ 15959067629763^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218937631 10000000000 15959067629763 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250334419/5000000000 : ℝ)^8383 ≤ (34768608163621/100000000000000 : ℝ)^6335 := by
    have hnat : (2250334419 : ℕ)^8383*100000000000000^6335 ≤ 34768608163621^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250334419 5000000000 34768608163621 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178781223/5000000000 : ℝ), (4218937631/10000000000 : ℝ), (2250334419/5000000000 : ℝ)] ![(16656628279961/50000000000000 : ℝ), (15959067629763/50000000000000 : ℝ), (34768608163621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178781223/5000000000 : ℝ)|^8383 ≤ (16656628279961/50000000000000 : ℝ)^6335
        have hw : |(2178781223/5000000000 : ℝ)|=(2178781223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4218937631/10000000000 : ℝ)|^8383 ≤ (15959067629763/50000000000000 : ℝ)^6335
        have hw : |(4218937631/10000000000 : ℝ)|=(4218937631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250334419/5000000000 : ℝ)|^8383 ≤ (34768608163621/100000000000000 : ℝ)^6335
        have hw : |(2250334419/5000000000 : ℝ)|=(2250334419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s4_4 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-535868861/2500000000 : ℝ)*x 0 + (657474001/1250000000 : ℝ)*x 1 + (5399289991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535868861/2500000000 : ℝ)^8383 ≤ (3257018876053/25000000000000 : ℝ)^6335 := by
    have hnat : (535868861 : ℕ)^8383*25000000000000^6335 ≤ 3257018876053^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535868861 2500000000 3257018876053 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657474001/1250000000 : ℝ)^8383 ≤ (667701547347/1562500000000 : ℝ)^6335 := by
    have hnat : (657474001 : ℕ)^8383*1562500000000^6335 ≤ 667701547347^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657474001 1250000000 667701547347 1562500000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399289991/10000000000 : ℝ)^8383 ≤ (8847805091663/20000000000000 : ℝ)^6335 := by
    have hnat : (5399289991 : ℕ)^8383*20000000000000^6335 ≤ 8847805091663^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399289991 10000000000 8847805091663 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535868861/2500000000 : ℝ), (657474001/1250000000 : ℝ), (5399289991/10000000000 : ℝ)] ![(3257018876053/25000000000000 : ℝ), (667701547347/1562500000000 : ℝ), (8847805091663/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535868861/2500000000 : ℝ)|^8383 ≤ (3257018876053/25000000000000 : ℝ)^6335
        have hw : |(-535868861/2500000000 : ℝ)|=(535868861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657474001/1250000000 : ℝ)|^8383 ≤ (667701547347/1562500000000 : ℝ)^6335
        have hw : |(657474001/1250000000 : ℝ)|=(657474001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399289991/10000000000 : ℝ)|^8383 ≤ (8847805091663/20000000000000 : ℝ)^6335
        have hw : |(5399289991/10000000000 : ℝ)|=(5399289991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s4_5 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531079521/1000000000 : ℝ)*x 0 + (-2074835553/10000000000 : ℝ)*x 1 + (33745561/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531079521/1000000000 : ℝ)^8383 ≤ (43282089229359/100000000000000 : ℝ)^6335 := by
    have hnat : (531079521 : ℕ)^8383*100000000000000^6335 ≤ 43282089229359^6335*1000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531079521 1000000000 43282089229359 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074835553/10000000000 : ℝ)^8383 ≤ (12478887799943/100000000000000 : ℝ)^6335 := by
    have hnat : (2074835553 : ℕ)^8383*100000000000000^6335 ≤ 12478887799943^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074835553 10000000000 12478887799943 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33745561/62500000 : ℝ)^8383 ≤ (22119511476871/50000000000000 : ℝ)^6335 := by
    have hnat : (33745561 : ℕ)^8383*50000000000000^6335 ≤ 22119511476871^6335*62500000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33745561 62500000 22119511476871 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531079521/1000000000 : ℝ), (-2074835553/10000000000 : ℝ), (33745561/62500000 : ℝ)] ![(43282089229359/100000000000000 : ℝ), (12478887799943/100000000000000 : ℝ), (22119511476871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531079521/1000000000 : ℝ)|^8383 ≤ (43282089229359/100000000000000 : ℝ)^6335
        have hw : |(531079521/1000000000 : ℝ)|=(531079521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2074835553/10000000000 : ℝ)|^8383 ≤ (12478887799943/100000000000000 : ℝ)^6335
        have hw : |(-2074835553/10000000000 : ℝ)|=(2074835553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33745561/62500000 : ℝ)|^8383 ≤ (22119511476871/50000000000000 : ℝ)^6335
        have hw : |(33745561/62500000 : ℝ)|=(33745561/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s4_6 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663849153/1250000000 : ℝ)*x 0 + (5399291997/10000000000 : ℝ)*x 1 + (-2074835197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663849153/1250000000 : ℝ)^8383 ≤ (4328206781127/10000000000000 : ℝ)^6335 := by
    have hnat : (663849153 : ℕ)^8383*10000000000000^6335 ≤ 4328206781127^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663849153 1250000000 4328206781127 10000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399291997/10000000000 : ℝ)^8383 ≤ (22119523603993/50000000000000 : ℝ)^6335 := by
    have hnat : (5399291997 : ℕ)^8383*50000000000000^6335 ≤ 22119523603993^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399291997 10000000000 22119523603993 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074835197/10000000000 : ℝ)^8383 ≤ (12478884966627/100000000000000 : ℝ)^6335 := by
    have hnat : (2074835197 : ℕ)^8383*100000000000000^6335 ≤ 12478884966627^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074835197 10000000000 12478884966627 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663849153/1250000000 : ℝ), (5399291997/10000000000 : ℝ), (-2074835197/10000000000 : ℝ)] ![(4328206781127/10000000000000 : ℝ), (22119523603993/50000000000000 : ℝ), (12478884966627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663849153/1250000000 : ℝ)|^8383 ≤ (4328206781127/10000000000000 : ℝ)^6335
        have hw : |(663849153/1250000000 : ℝ)|=(663849153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399291997/10000000000 : ℝ)|^8383 ≤ (22119523603993/50000000000000 : ℝ)^6335
        have hw : |(5399291997/10000000000 : ℝ)|=(5399291997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2074835197/10000000000 : ℝ)|^8383 ≤ (12478884966627/100000000000000 : ℝ)^6335
        have hw : |(-2074835197/10000000000 : ℝ)|=(2074835197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s4_7 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357576467/10000000000 : ℝ)*x 0 + (449987793/1000000000 : ℝ)*x 1 + (2109865513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357576467/10000000000 : ℝ)^8383 ≤ (16656699201073/50000000000000 : ℝ)^6335 := by
    have hnat : (4357576467 : ℕ)^8383*50000000000000^6335 ≤ 16656699201073^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357576467 10000000000 16656699201073 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449987793/1000000000 : ℝ)^8383 ≤ (4345065403129/12500000000000 : ℝ)^6335 := by
    have hnat : (449987793 : ℕ)^8383*12500000000000^6335 ≤ 4345065403129^6335*1000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449987793 1000000000 4345065403129 12500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109865513/5000000000 : ℝ)^8383 ≤ (15963039178687/50000000000000 : ℝ)^6335 := by
    have hnat : (2109865513 : ℕ)^8383*50000000000000^6335 ≤ 15963039178687^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109865513 5000000000 15963039178687 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357576467/10000000000 : ℝ), (449987793/1000000000 : ℝ), (2109865513/5000000000 : ℝ)] ![(16656699201073/50000000000000 : ℝ), (4345065403129/12500000000000 : ℝ), (15963039178687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357576467/10000000000 : ℝ)|^8383 ≤ (16656699201073/50000000000000 : ℝ)^6335
        have hw : |(4357576467/10000000000 : ℝ)|=(4357576467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449987793/1000000000 : ℝ)|^8383 ≤ (4345065403129/12500000000000 : ℝ)^6335
        have hw : |(449987793/1000000000 : ℝ)|=(449987793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2109865513/5000000000 : ℝ)|^8383 ≤ (15963039178687/50000000000000 : ℝ)^6335
        have hw : |(2109865513/5000000000 : ℝ)|=(2109865513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1190_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10773/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11263/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10773/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10773/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10773/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10773/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10773/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10773/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (10773/100000 : ℝ) ^ (4191/1024 : ℝ) ≤ (5477005654655839/50000000000000000000 : ℝ) := by
    have hpowers : (10773/100000 : ℝ)^4191 ≤ (5477005654655839/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10773 : ℕ)^4191*50000000000000000000^1024 ≤ 5477005654655839^1024*100000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10773 100000 5477005654655839 50000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10773/100000 : ℝ)) (X := (5477005654655839/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (461/3125 : ℝ) ^ (4191/1024 : ℝ) ≤ (7930947075403527/20000000000000000000 : ℝ) := by
    have hpowers : (461/3125 : ℝ)^4191 ≤ (7930947075403527/20000000000000000000 : ℝ)^1024 := by
      have hnat : (461 : ℕ)^4191*20000000000000000000^1024 ≤ 7930947075403527^1024*3125^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        461 3125 7930947075403527 20000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (461/3125 : ℝ)) (X := (7930947075403527/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005477005654655839/25000000000000000000 : ℝ) ≤ (200010704823871/200000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (25005477005654655839/25000000000000000000 : ℝ)^1024 ≤ (200010704823871/200000000000000 : ℝ)^4191 := by
      have hnat : (25005477005654655839 : ℕ)^1024*200000000000000^4191 ≤ 200010704823871^4191*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005477005654655839 25000000000000000000 200010704823871 200000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200010704823871/200000000000000 : ℝ)) (X := (25005477005654655839/25000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050608746686329313/100000000000000000000 : ℝ) ≤ (2000247260558557/2000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (100050608746686329313/100000000000000000000 : ℝ)^1024 ≤ (2000247260558557/2000000000000000 : ℝ)^4191 := by
      have hnat : (100050608746686329313 : ℕ)^1024*2000000000000000^4191 ≤ 2000247260558557^4191*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050608746686329313 100000000000000000000 2000247260558557 2000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000247260558557/2000000000000000 : ℝ)) (X := (100050608746686329313/100000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007930947075403527/10000000000000000000 : ℝ) ≤ (500096868219601/500000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (10007930947075403527/10000000000000000000 : ℝ)^1024 ≤ (500096868219601/500000000000000 : ℝ)^4191 := by
      have hnat : (10007930947075403527 : ℕ)^1024*500000000000000^4191 ≤ 500096868219601^4191*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007930947075403527 10000000000000000000 500096868219601 500000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500096868219601/500000000000000 : ℝ)) (X := (10007930947075403527/10000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5477005654655839/50000000000000000000 : ℝ) ≤ ((1988851232574600907/1989500000000000000 : ℝ)+2*(140212319847/79580000000000 : ℝ)*(10773/100000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (1988851232574600907/1989500000000000000 : ℝ)+2*(140212319847/79580000000000 : ℝ)*(10773/100000 : ℝ)=(200010704823871/200000000000000 : ℝ) by norm_num, show 1+2*(5477005654655839/50000000000000000000 : ℝ)=(25005477005654655839/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7930947075403527/20000000000000000000 : ℝ)+(5477005654655839/50000000000000000000 : ℝ) ≤ ((1988851232574600907/1989500000000000000 : ℝ)+(140212319847/79580000000000 : ℝ)*((461/3125 : ℝ)+(10773/100000 : ℝ)))^(4191/1024 : ℝ) := by
    rw [show (1988851232574600907/1989500000000000000 : ℝ)+(140212319847/79580000000000 : ℝ)*((461/3125 : ℝ)+(10773/100000 : ℝ))=(2000247260558557/2000000000000000 : ℝ) by norm_num, show 1+(7930947075403527/20000000000000000000 : ℝ)+(5477005654655839/50000000000000000000 : ℝ)=(100050608746686329313/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7930947075403527/20000000000000000000 : ℝ) ≤ ((1988851232574600907/1989500000000000000 : ℝ)+2*(140212319847/79580000000000 : ℝ)*(461/3125 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (1988851232574600907/1989500000000000000 : ℝ)+2*(140212319847/79580000000000 : ℝ)*(461/3125 : ℝ)=(500096868219601/500000000000000 : ℝ) by norm_num, show 1+2*(7930947075403527/20000000000000000000 : ℝ)=(10007930947075403527/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1988851232574600907/1989500000000000000 : ℝ)*(X 1 0+X 2 0)+(140212319847/79580000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (10773/100000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (1988851232574600907/1989500000000000000 : ℝ)) (alpha := (140212319847/79580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1988851232574600907/1989500000000000000 : ℝ)*(X 0 1+X 2 1)+(140212319847/79580000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (10773/100000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (1988851232574600907/1989500000000000000 : ℝ)) (alpha := (140212319847/79580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1988851232574600907/1989500000000000000 : ℝ)*(X 0 2+X 1 2)+(140212319847/79580000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (10773/100000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (1988851232574600907/1989500000000000000 : ℝ)) (alpha := (140212319847/79580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1071734363/5000000000 : ℝ)*X 0 0+(674960749/1250000000 : ℝ)*X 0 1+(5259397657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346459639/10000000000 : ℝ)*X 1 0+(-2214728119/10000000000 : ℝ)*X 1 1+(5259397411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346458637/10000000000 : ℝ)*X 2 0+(131484947/250000000 : ℝ)*X 2 1+(-2214728833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178781223/5000000000 : ℝ)*X 0 0+(4218937631/10000000000 : ℝ)*X 0 1+(2250334419/5000000000 : ℝ)*X 0 2+(2178781223/5000000000 : ℝ)*X 1 0+(4218937631/10000000000 : ℝ)*X 1 1+(2250334419/5000000000 : ℝ)*X 1 2+(2178781223/5000000000 : ℝ)*X 2 0+(4218937631/10000000000 : ℝ)*X 2 1+(2250334419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-535868861/2500000000 : ℝ)*X 0 0+(657474001/1250000000 : ℝ)*X 0 1+(5399289991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531079521/1000000000 : ℝ)*X 1 0+(-2074835553/10000000000 : ℝ)*X 1 1+(33745561/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663849153/1250000000 : ℝ)*X 2 0+(5399291997/10000000000 : ℝ)*X 2 1+(-2074835197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357576467/10000000000 : ℝ)*X 0 0+(449987793/1000000000 : ℝ)*X 0 1+(2109865513/5000000000 : ℝ)*X 0 2+(4357576467/10000000000 : ℝ)*X 1 0+(449987793/1000000000 : ℝ)*X 1 1+(2109865513/5000000000 : ℝ)*X 1 2+(4357576467/10000000000 : ℝ)*X 2 0+(449987793/1000000000 : ℝ)*X 2 1+(2109865513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (246308490765984327134158329/19895000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1778755359/100000000000000 : ℝ)*(base19) + (643360663/100000000000000 : ℝ)*(base23) + (197452717/100000000000000 : ℝ)*(upper2) + (335018453/100000000000000 : ℝ)*(upper3) + (1067779595020049/20000000000000 : ℝ)*(major0) + (1067779595020049/20000000000000 : ℝ)*(major1) + (1067779595020049/20000000000000 : ℝ)*(major2) + (3564117321423001/50000000000000 : ℝ)*(sp0) + (3564128329180987/50000000000000 : ℝ)*(sp1) + (7128232493200773/100000000000000 : ℝ)*(sp2) + (3549511014687333/100000000000000 : ℝ)*(sp3) + (23794271331/100000000000000 : ℝ)*(sp4) + (12650277949/50000000000000 : ℝ)*(sp6) + (26085715091/100000000000000 : ℝ)*(sp7) + (443692137550303/12500000000000 : ℝ)*(f.failure) + (7128258437117333/100000000000000 : ℝ)*(f.sum) + (4934399254547/1989500000000000000000000000 : ℝ)*base65 + (198752660007990557/39790000000000000000000000000000 : ℝ)*base68 + (517677920420290557/39790000000000000000000000000000 : ℝ)*base70 + (365989554865369443/39790000000000000000000000000000 : ℝ)*base71 + (10036970722849/1989500000000000000000000000 : ℝ)*base74 + (605983229944700557/39790000000000000000000000000000 : ℝ)*base76 + (76748318960439443/39790000000000000000000000000000 : ℝ)*base77 + (463880708156050557/39790000000000000000000000000000 : ℝ)*base80 + (352093994639/198950000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (962963/250000000000000000000 : ℝ)*base89 + (962963/250000000000000000000 : ℝ)*base91 + (962963/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13366920674600217890037/3979000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9129001/12500000000000 : ℝ)*(base21) + (641752943/100000000000000 : ℝ)*(upper2) + (28363647/5000000000000 : ℝ)*(lower4) + (4830217/1562500000000 : ℝ)*(upper5) + (2684536440497071/50000000000000 : ℝ)*(major0) + (2684536440497071/50000000000000 : ℝ)*(major1) + (2684536440497071/50000000000000 : ℝ)*(major2) + (11837205763/100000000000000 : ℝ)*(sp0) + (50581587773/100000000000000 : ℝ)*(sp2) + (34694686177/100000000000000 : ℝ)*(sp3) + (3584267545678363/50000000000000 : ℝ)*(sp4) + (7168546928562489/100000000000000 : ℝ)*(sp5) + (1792124068485677/25000000000000 : ℝ)*(sp6) + (892391006690179/25000000000000 : ℝ)*(sp7) + (892399680361723/25000000000000 : ℝ)*(f.failure) + (7168546928562489/100000000000000 : ℝ)*(f.sum) + (16947608091973/1989500000000000000000000000 : ℝ)*base65 + (561251782323143397/99475000000000000000000000000000 : ℝ)*base67 + (439567329477156603/99475000000000000000000000000000 : ℝ)*base70 + (3363679911757968397/99475000000000000000000000000000 : ℝ)*base71 + (712664668447/497375000000000000000000000 : ℝ)*base74 + (611299565188581603/99475000000000000000000000000000 : ℝ)*base76 + (95381999932956603/99475000000000000000000000000000 : ℝ)*base78 + (252241507114443397/99475000000000000000000000000000 : ℝ)*base79 + (23417104226029/3979000000000000000000000000 : ℝ)*base82 + (1226783/500000000000000000000 : ℝ)*base89 + (1226783/500000000000000000000 : ℝ)*base91 + (1226783/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1190_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10773/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1190_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1190_s5_0 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-428802381/2000000000 : ℝ)*x 0 + (674210247/1250000000 : ℝ)*x 1 + (1316261133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428802381/2000000000 : ℝ)^8383 ≤ (13032390400129/100000000000000 : ℝ)^6335 := by
    have hnat : (428802381 : ℕ)^8383*100000000000000^6335 ≤ 13032390400129^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428802381 2000000000 13032390400129 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674210247/1250000000 : ℝ)^8383 ≤ (1767129273703/4000000000000 : ℝ)^6335 := by
    have hnat : (674210247 : ℕ)^8383*4000000000000^6335 ≤ 1767129273703^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674210247 1250000000 1767129273703 4000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316261133/2500000000 : ℝ)^8383 ≤ (42789377739063/100000000000000 : ℝ)^6335 := by
    have hnat : (1316261133 : ℕ)^8383*100000000000000^6335 ≤ 42789377739063^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316261133 2500000000 42789377739063 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428802381/2000000000 : ℝ), (674210247/1250000000 : ℝ), (1316261133/2500000000 : ℝ)] ![(13032390400129/100000000000000 : ℝ), (1767129273703/4000000000000 : ℝ), (42789377739063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428802381/2000000000 : ℝ)|^8383 ≤ (13032390400129/100000000000000 : ℝ)^6335
        have hw : |(-428802381/2000000000 : ℝ)|=(428802381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674210247/1250000000 : ℝ)|^8383 ≤ (1767129273703/4000000000000 : ℝ)^6335
        have hw : |(674210247/1250000000 : ℝ)|=(674210247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316261133/2500000000 : ℝ)|^8383 ≤ (42789377739063/100000000000000 : ℝ)^6335
        have hw : |(1316261133/2500000000 : ℝ)|=(1316261133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s5_1 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672472889/5000000000 : ℝ)*x 0 + (-2209268551/10000000000 : ℝ)*x 1 + (5265044523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672472889/5000000000 : ℝ)^8383 ≤ (43650769559487/100000000000000 : ℝ)^6335 := by
    have hnat : (2672472889 : ℕ)^8383*100000000000000^6335 ≤ 43650769559487^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672472889 5000000000 43650769559487 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209268551/10000000000 : ℝ)^8383 ≤ (2711970555919/20000000000000 : ℝ)^6335 := by
    have hnat : (2209268551 : ℕ)^8383*20000000000000^6335 ≤ 2711970555919^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209268551 10000000000 2711970555919 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265044523/10000000000 : ℝ)^8383 ≤ (21394688821137/50000000000000 : ℝ)^6335 := by
    have hnat : (5265044523 : ℕ)^8383*50000000000000^6335 ≤ 21394688821137^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265044523 10000000000 21394688821137 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672472889/5000000000 : ℝ), (-2209268551/10000000000 : ℝ), (5265044523/10000000000 : ℝ)] ![(43650769559487/100000000000000 : ℝ), (2711970555919/20000000000000 : ℝ), (21394688821137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672472889/5000000000 : ℝ)|^8383 ≤ (43650769559487/100000000000000 : ℝ)^6335
        have hw : |(2672472889/5000000000 : ℝ)|=(2672472889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2209268551/10000000000 : ℝ)|^8383 ≤ (2711970555919/20000000000000 : ℝ)^6335
        have hw : |(-2209268551/10000000000 : ℝ)|=(2209268551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265044523/10000000000 : ℝ)|^8383 ≤ (21394688821137/50000000000000 : ℝ)^6335
        have hw : |(5265044523/10000000000 : ℝ)|=(5265044523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s5_2 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344945783/10000000000 : ℝ)*x 0 + (1316261129/2500000000 : ℝ)*x 1 + (-441853711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344945783/10000000000 : ℝ)^8383 ≤ (21825384806761/50000000000000 : ℝ)^6335 := by
    have hnat : (5344945783 : ℕ)^8383*50000000000000^6335 ≤ 21825384806761^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344945783 10000000000 21825384806761 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316261129/2500000000 : ℝ)^8383 ≤ (42789377566993/100000000000000 : ℝ)^6335 := by
    have hnat : (1316261129 : ℕ)^8383*100000000000000^6335 ≤ 42789377566993^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316261129 2500000000 42789377566993 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441853711/2000000000 : ℝ)^8383 ≤ (6779926406041/50000000000000 : ℝ)^6335 := by
    have hnat : (441853711 : ℕ)^8383*50000000000000^6335 ≤ 6779926406041^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441853711 2000000000 6779926406041 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344945783/10000000000 : ℝ), (1316261129/2500000000 : ℝ), (-441853711/2000000000 : ℝ)] ![(21825384806761/50000000000000 : ℝ), (42789377566993/100000000000000 : ℝ), (6779926406041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344945783/10000000000 : ℝ)|^8383 ≤ (21825384806761/50000000000000 : ℝ)^6335
        have hw : |(5344945783/10000000000 : ℝ)|=(5344945783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316261129/2500000000 : ℝ)|^8383 ≤ (42789377566993/100000000000000 : ℝ)^6335
        have hw : |(1316261129/2500000000 : ℝ)|=(1316261129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441853711/2000000000 : ℝ)|^8383 ≤ (6779926406041/50000000000000 : ℝ)^6335
        have hw : |(-441853711/2000000000 : ℝ)|=(441853711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s5_3 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357878757/10000000000 : ℝ)*x 0 + (4230595991/10000000000 : ℝ)*x 1 + (1122232127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357878757/10000000000 : ℝ)^8383 ≤ (4164557066057/12500000000000 : ℝ)^6335 := by
    have hnat : (4357878757 : ℕ)^8383*12500000000000^6335 ≤ 4164557066057^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357878757 10000000000 4164557066057 12500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230595991/10000000000 : ℝ)^8383 ≤ (32034901833287/100000000000000 : ℝ)^6335 := by
    have hnat : (4230595991 : ℕ)^8383*100000000000000^6335 ≤ 32034901833287^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230595991 10000000000 32034901833287 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122232127/2500000000 : ℝ)^8383 ≤ (8662160406157/25000000000000 : ℝ)^6335 := by
    have hnat : (1122232127 : ℕ)^8383*25000000000000^6335 ≤ 8662160406157^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122232127 2500000000 8662160406157 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357878757/10000000000 : ℝ), (4230595991/10000000000 : ℝ), (1122232127/2500000000 : ℝ)] ![(4164557066057/12500000000000 : ℝ), (32034901833287/100000000000000 : ℝ), (8662160406157/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357878757/10000000000 : ℝ)|^8383 ≤ (4164557066057/12500000000000 : ℝ)^6335
        have hw : |(4357878757/10000000000 : ℝ)|=(4357878757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230595991/10000000000 : ℝ)|^8383 ≤ (32034901833287/100000000000000 : ℝ)^6335
        have hw : |(4230595991/10000000000 : ℝ)|=(4230595991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122232127/2500000000 : ℝ)|^8383 ≤ (8662160406157/25000000000000 : ℝ)^6335
        have hw : |(1122232127/2500000000 : ℝ)|=(1122232127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s5_4 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144017019/10000000000 : ℝ)*x 0 + (5265375899/10000000000 : ℝ)*x 1 + (5393349383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144017019/10000000000 : ℝ)^8383 ≤ (6516215767523/50000000000000 : ℝ)^6335 := by
    have hnat : (2144017019 : ℕ)^8383*50000000000000^6335 ≤ 6516215767523^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144017019 10000000000 6516215767523 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265375899/10000000000 : ℝ)^8383 ≤ (5349117679171/12500000000000 : ℝ)^6335 := by
    have hnat : (5265375899 : ℕ)^8383*12500000000000^6335 ≤ 5349117679171^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265375899 10000000000 5349117679171 12500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393349383/10000000000 : ℝ)^8383 ≤ (22087313507001/50000000000000 : ℝ)^6335 := by
    have hnat : (5393349383 : ℕ)^8383*50000000000000^6335 ≤ 22087313507001^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393349383 10000000000 22087313507001 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144017019/10000000000 : ℝ), (5265375899/10000000000 : ℝ), (5393349383/10000000000 : ℝ)] ![(6516215767523/50000000000000 : ℝ), (5349117679171/12500000000000 : ℝ), (22087313507001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144017019/10000000000 : ℝ)|^8383 ≤ (6516215767523/50000000000000 : ℝ)^6335
        have hw : |(-2144017019/10000000000 : ℝ)|=(2144017019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265375899/10000000000 : ℝ)|^8383 ≤ (5349117679171/12500000000000 : ℝ)^6335
        have hw : |(5265375899/10000000000 : ℝ)|=(5265375899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393349383/10000000000 : ℝ)|^8383 ≤ (22087313507001/50000000000000 : ℝ)^6335
        have hw : |(5393349383/10000000000 : ℝ)|=(5393349383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s5_5 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664030211/1250000000 : ℝ)*x 0 + (-2080963681/10000000000 : ℝ)*x 1 + (1078669879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664030211/1250000000 : ℝ)^8383 ≤ (43297689511729/100000000000000 : ℝ)^6335 := by
    have hnat : (664030211 : ℕ)^8383*100000000000000^6335 ≤ 43297689511729^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664030211 1250000000 43297689511729 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080963681/10000000000 : ℝ)^8383 ≤ (97872526003/781250000000 : ℝ)^6335 := by
    have hnat : (2080963681 : ℕ)^8383*781250000000^6335 ≤ 97872526003^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080963681 10000000000 97872526003 781250000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078669879/2000000000 : ℝ)^8383 ≤ (44174627144063/100000000000000 : ℝ)^6335 := by
    have hnat : (1078669879 : ℕ)^8383*100000000000000^6335 ≤ 44174627144063^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078669879 2000000000 44174627144063 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664030211/1250000000 : ℝ), (-2080963681/10000000000 : ℝ), (1078669879/2000000000 : ℝ)] ![(43297689511729/100000000000000 : ℝ), (97872526003/781250000000 : ℝ), (44174627144063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664030211/1250000000 : ℝ)|^8383 ≤ (43297689511729/100000000000000 : ℝ)^6335
        have hw : |(664030211/1250000000 : ℝ)|=(664030211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080963681/10000000000 : ℝ)|^8383 ≤ (97872526003/781250000000 : ℝ)^6335
        have hw : |(-2080963681/10000000000 : ℝ)|=(2080963681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078669879/2000000000 : ℝ)|^8383 ≤ (44174627144063/100000000000000 : ℝ)^6335
        have hw : |(1078669879/2000000000 : ℝ)|=(1078669879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s5_6 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656120859/5000000000 : ℝ)*x 0 + (5393349363/10000000000 : ℝ)*x 1 + (-520240921/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656120859/5000000000 : ℝ)^8383 ≤ (43297689835293/100000000000000 : ℝ)^6335 := by
    have hnat : (2656120859 : ℕ)^8383*100000000000000^6335 ≤ 43297689835293^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656120859 5000000000 43297689835293 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393349363/10000000000 : ℝ)^8383 ≤ (44174626797233/100000000000000 : ℝ)^6335 := by
    have hnat : (5393349363 : ℕ)^8383*100000000000000^6335 ≤ 44174626797233^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393349363 10000000000 44174626797233 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520240921/2500000000 : ℝ)^8383 ≤ (12527683352283/100000000000000 : ℝ)^6335 := by
    have hnat : (520240921 : ℕ)^8383*100000000000000^6335 ≤ 12527683352283^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520240921 2500000000 12527683352283 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656120859/5000000000 : ℝ), (5393349363/10000000000 : ℝ), (-520240921/2500000000 : ℝ)] ![(43297689835293/100000000000000 : ℝ), (44174626797233/100000000000000 : ℝ), (12527683352283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656120859/5000000000 : ℝ)|^8383 ≤ (43297689835293/100000000000000 : ℝ)^6335
        have hw : |(2656120859/5000000000 : ℝ)|=(2656120859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393349363/10000000000 : ℝ)|^8383 ≤ (44174626797233/100000000000000 : ℝ)^6335
        have hw : |(5393349363/10000000000 : ℝ)|=(5393349363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520240921/2500000000 : ℝ)|^8383 ≤ (12527683352283/100000000000000 : ℝ)^6335
        have hw : |(-520240921/2500000000 : ℝ)|=(520240921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s5_7 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178944517/5000000000 : ℝ)*x 0 + (4488263139/10000000000 : ℝ)*x 1 + (4231263823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178944517/5000000000 : ℝ)^8383 ≤ (4164570062157/12500000000000 : ℝ)^6335 := by
    have hnat : (2178944517 : ℕ)^8383*12500000000000^6335 ≤ 4164570062157^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178944517 5000000000 4164570062157 12500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488263139/10000000000 : ℝ)^8383 ≤ (6928369140079/20000000000000 : ℝ)^6335 := by
    have hnat : (4488263139 : ℕ)^8383*20000000000000^6335 ≤ 6928369140079^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488263139 10000000000 6928369140079 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231263823/10000000000 : ℝ)^8383 ≤ (32041593788057/100000000000000 : ℝ)^6335 := by
    have hnat : (4231263823 : ℕ)^8383*100000000000000^6335 ≤ 32041593788057^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231263823 10000000000 32041593788057 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178944517/5000000000 : ℝ), (4488263139/10000000000 : ℝ), (4231263823/10000000000 : ℝ)] ![(4164570062157/12500000000000 : ℝ), (6928369140079/20000000000000 : ℝ), (32041593788057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178944517/5000000000 : ℝ)|^8383 ≤ (4164570062157/12500000000000 : ℝ)^6335
        have hw : |(2178944517/5000000000 : ℝ)|=(2178944517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488263139/10000000000 : ℝ)|^8383 ≤ (6928369140079/20000000000000 : ℝ)^6335
        have hw : |(4488263139/10000000000 : ℝ)|=(4488263139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231263823/10000000000 : ℝ)|^8383 ≤ (32041593788057/100000000000000 : ℝ)^6335
        have hw : |(4231263823/10000000000 : ℝ)|=(4231263823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1190_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1423/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14109/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11263/100000 : ℝ) ^ (4191/1024 : ℝ) ≤ (3285300006716591/25000000000000000000 : ℝ) := by
    have hpowers : (11263/100000 : ℝ)^4191 ≤ (3285300006716591/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11263 : ℕ)^4191*25000000000000000000^1024 ≤ 3285300006716591^1024*100000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11263 100000 3285300006716591 25000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11263/100000 : ℝ)) (X := (3285300006716591/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (4191/1024 : ℝ) ≤ (42822211363257/125000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^4191 ≤ (42822211363257/125000000000000000 : ℝ)^1024 := by
      have hnat : (7117 : ℕ)^4191*125000000000000000^1024 ≤ 42822211363257^1024*50000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 42822211363257 125000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (42822211363257/125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503285300006716591/12500000000000000000 : ℝ) ≤ (625040131390909/625000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (12503285300006716591/12500000000000000000 : ℝ)^1024 ≤ (625040131390909/625000000000000 : ℝ)^4191 := by
      have hnat : (12503285300006716591 : ℕ)^1024*625000000000000^4191 ≤ 625040131390909^4191*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503285300006716591 12500000000000000000 625040131390909 625000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625040131390909/625000000000000 : ℝ)) (X := (12503285300006716591/12500000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011849742279367991/25000000000000000000 : ℝ) ≤ (10001157906333039/10000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (25011849742279367991/25000000000000000000 : ℝ)^1024 ≤ (10001157906333039/10000000000000000 : ℝ)^4191 := by
      have hnat : (25011849742279367991 : ℕ)^1024*10000000000000000^4191 ≤ 10001157906333039^4191*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011849742279367991 25000000000000000000 10001157906333039 10000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001157906333039/10000000000000000 : ℝ)) (X := (25011849742279367991/25000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (62542822211363257/62500000000000000 : ℝ) ≤ (5000836855205767/5000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (62542822211363257/62500000000000000 : ℝ)^1024 ≤ (5000836855205767/5000000000000000 : ℝ)^4191 := by
      have hnat : (62542822211363257 : ℕ)^1024*5000000000000000^4191 ≤ 5000836855205767^4191*62500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62542822211363257 62500000000000000 5000836855205767 5000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000836855205767/5000000000000000 : ℝ)) (X := (62542822211363257/62500000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3285300006716591/25000000000000000000 : ℝ) ≤ ((14850144341563035927/14855000000000000000 : ℝ)+2*(103160815699/59420000000000 : ℝ)*(11263/100000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (14850144341563035927/14855000000000000000 : ℝ)+2*(103160815699/59420000000000 : ℝ)*(11263/100000 : ℝ)=(625040131390909/625000000000000 : ℝ) by norm_num, show 1+2*(3285300006716591/25000000000000000000 : ℝ)=(12503285300006716591/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42822211363257/125000000000000000 : ℝ)+(3285300006716591/25000000000000000000 : ℝ) ≤ ((14850144341563035927/14855000000000000000 : ℝ)+(103160815699/59420000000000 : ℝ)*((7117/50000 : ℝ)+(11263/100000 : ℝ)))^(4191/1024 : ℝ) := by
    rw [show (14850144341563035927/14855000000000000000 : ℝ)+(103160815699/59420000000000 : ℝ)*((7117/50000 : ℝ)+(11263/100000 : ℝ))=(10001157906333039/10000000000000000 : ℝ) by norm_num, show 1+(42822211363257/125000000000000000 : ℝ)+(3285300006716591/25000000000000000000 : ℝ)=(25011849742279367991/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42822211363257/125000000000000000 : ℝ) ≤ ((14850144341563035927/14855000000000000000 : ℝ)+2*(103160815699/59420000000000 : ℝ)*(7117/50000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (14850144341563035927/14855000000000000000 : ℝ)+2*(103160815699/59420000000000 : ℝ)*(7117/50000 : ℝ)=(5000836855205767/5000000000000000 : ℝ) by norm_num, show 1+2*(42822211363257/125000000000000000 : ℝ)=(62542822211363257/62500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14850144341563035927/14855000000000000000 : ℝ)*(X 1 0+X 2 0)+(103160815699/59420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14850144341563035927/14855000000000000000 : ℝ)) (alpha := (103160815699/59420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14850144341563035927/14855000000000000000 : ℝ)*(X 0 1+X 2 1)+(103160815699/59420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14850144341563035927/14855000000000000000 : ℝ)) (alpha := (103160815699/59420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14850144341563035927/14855000000000000000 : ℝ)*(X 0 2+X 1 2)+(103160815699/59420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14850144341563035927/14855000000000000000 : ℝ)) (alpha := (103160815699/59420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-428802381/2000000000 : ℝ)*X 0 0+(674210247/1250000000 : ℝ)*X 0 1+(1316261133/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672472889/5000000000 : ℝ)*X 1 0+(-2209268551/10000000000 : ℝ)*X 1 1+(5265044523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344945783/10000000000 : ℝ)*X 2 0+(1316261129/2500000000 : ℝ)*X 2 1+(-441853711/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357878757/10000000000 : ℝ)*X 0 0+(4230595991/10000000000 : ℝ)*X 0 1+(1122232127/2500000000 : ℝ)*X 0 2+(4357878757/10000000000 : ℝ)*X 1 0+(4230595991/10000000000 : ℝ)*X 1 1+(1122232127/2500000000 : ℝ)*X 1 2+(4357878757/10000000000 : ℝ)*X 2 0+(4230595991/10000000000 : ℝ)*X 2 1+(1122232127/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2144017019/10000000000 : ℝ)*X 0 0+(5265375899/10000000000 : ℝ)*X 0 1+(5393349383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664030211/1250000000 : ℝ)*X 1 0+(-2080963681/10000000000 : ℝ)*X 1 1+(1078669879/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656120859/5000000000 : ℝ)*X 2 0+(5393349363/10000000000 : ℝ)*X 2 1+(-520240921/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178944517/5000000000 : ℝ)*X 0 0+(4488263139/10000000000 : ℝ)*X 0 1+(4231263823/10000000000 : ℝ)*X 0 2+(2178944517/5000000000 : ℝ)*X 1 0+(4488263139/10000000000 : ℝ)*X 1 1+(4231263823/10000000000 : ℝ)*X 1 2+(2178944517/5000000000 : ℝ)*X 2 0+(4488263139/10000000000 : ℝ)*X 2 1+(4231263823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (574784467315805168337689253/148550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (770321317/100000000000000 : ℝ)*(base19) + (175126267/25000000000000 : ℝ)*(base23) + (41203321/100000000000000 : ℝ)*(lower2) + (55866999/50000000000000 : ℝ)*(upper3) + (791349/1562500000000 : ℝ)*(upper5) + (1164482578139887/20000000000000 : ℝ)*(major0) + (1164482578139887/20000000000000 : ℝ)*(major1) + (1164482578139887/20000000000000 : ℝ)*(major2) + (3886903566204539/50000000000000 : ℝ)*(sp0) + (971728192026069/12500000000000 : ℝ)*(sp1) + (3886912803012401/50000000000000 : ℝ)*(sp2) + (120968400289003/3125000000000 : ℝ)*(sp3) + (19174120791/100000000000000 : ℝ)*(sp4) + (131708053/1250000000000 : ℝ)*(sp7) + (241937459118271/6250000000000 : ℝ)*(f.failure) + (777382630652987/10000000000000 : ℝ)*(f.sum) + (1974465301121/1485500000000000000000000000 : ℝ)*base65 + (579655584658329751/297100000000000000000000000000000 : ℝ)*base68 + (770638066453270249/297100000000000000000000000000000 : ℝ)*base69 + (1475412580751170249/297100000000000000000000000000000 : ℝ)*base71 + (11164719724041/2971000000000000000000000000 : ℝ)*base73 + (2519737673630429751/297100000000000000000000000000000 : ℝ)*base76 + (4831627535630170249/297100000000000000000000000000000 : ℝ)*base77 + (1376304762467170249/297100000000000000000000000000000 : ℝ)*base79 + (2239999622227/2971000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (390109/125000000000000000000 : ℝ)*base90 + (390109/125000000000000000000 : ℝ)*base92 + (390109/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3940055050470876855252714867/371375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1909072769/100000000000000 : ℝ)*(base19) + (2167664233/100000000000000 : ℝ)*(base23) + (238069677/100000000000000 : ℝ)*(upper3) + (18429429/20000000000000 : ℝ)*(lower4) + (39290801/20000000000000 : ℝ)*(upper5) + (5852588202266593/100000000000000 : ℝ)*(major0) + (5852588202266593/100000000000000 : ℝ)*(major1) + (5852588202266593/100000000000000 : ℝ)*(major2) + (3169941893/6250000000000 : ℝ)*(sp1) + (28689500419/50000000000000 : ℝ)*(sp2) + (1953528703560259/25000000000000 : ℝ)*(sp4) + (7814062186097979/100000000000000 : ℝ)*(sp5) + (1953513816893991/25000000000000 : ℝ)*(sp6) + (972765309161613/25000000000000 : ℝ)*(sp7) + (972765309161613/25000000000000 : ℝ)*(f.failure) + (1953528703560259/25000000000000 : ℝ)*(f.sum) + (12203054553657/2971000000000000000000000000 : ℝ)*base66 + (2482385428648363289/1485500000000000000000000000000000 : ℝ)*base68 + (23018951540935636711/1485500000000000000000000000000000 : ℝ)*base69 + (13922175582335636711/1485500000000000000000000000000000 : ℝ)*base71 + (964495551963/371375000000000000000000000 : ℝ)*base74 + (3985352135280136711/1485500000000000000000000000000000 : ℝ)*base75 + (10224410022840636711/1485500000000000000000000000000000 : ℝ)*base77 + (23166816155003636711/1485500000000000000000000000000000 : ℝ)*base79 + (4648606453877/2971000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1982473/500000000000000000000 : ℝ)*base89 + (1982473/500000000000000000000 : ℝ)*base91 + (1982473/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1190_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1190_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1190_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4641/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1190_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1190_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1190_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4641/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1190_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
