-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1760_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:25:26.817529+00:00
-- url     : https://prove2.me/submissions/07bd06bc-b247-4c7d-9f06-26297d48315c

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
theorem support_rectangle_w1760_s0_0 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-28271117/250000000 : ℝ)*x 0 + (5600866403/10000000000 : ℝ)*x 1 + (624019011/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28271117/250000000 : ℝ)^5935 ≤ (3589191166347/50000000000000 : ℝ)^4911 := by
    have hnat : (28271117 : ℕ)^5935*50000000000000^4911 ≤ 3589191166347^4911*250000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28271117 250000000 3589191166347 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5600866403/10000000000 : ℝ)^5935 ≤ (620402504543/1250000000000 : ℝ)^4911 := by
    have hnat : (5600866403 : ℕ)^5935*1250000000000^4911 ≤ 620402504543^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5600866403 10000000000 620402504543 1250000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624019011/1250000000 : ℝ)^5935 ≤ (43189417293693/100000000000000 : ℝ)^4911 := by
    have hnat : (624019011 : ℕ)^5935*100000000000000^4911 ≤ 43189417293693^4911*1250000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624019011 1250000000 43189417293693 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-28271117/250000000 : ℝ), (5600866403/10000000000 : ℝ), (624019011/1250000000 : ℝ)] ![(3589191166347/50000000000000 : ℝ), (620402504543/1250000000000 : ℝ), (43189417293693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-28271117/250000000 : ℝ)|^5935 ≤ (3589191166347/50000000000000 : ℝ)^4911
        have hw : |(-28271117/250000000 : ℝ)|=(28271117/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5600866403/10000000000 : ℝ)|^5935 ≤ (620402504543/1250000000000 : ℝ)^4911
        have hw : |(5600866403/10000000000 : ℝ)|=(5600866403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(624019011/1250000000 : ℝ)|^5935 ≤ (43189417293693/100000000000000 : ℝ)^4911
        have hw : |(624019011/1250000000 : ℝ)|=(624019011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s0_1 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360430791/10000000000 : ℝ)*x 0 + (-727943923/5000000000 : ℝ)*x 1 + (4992152741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360430791/10000000000 : ℝ)^5935 ≤ (2941810752733/6250000000000 : ℝ)^4911 := by
    have hnat : (5360430791 : ℕ)^5935*6250000000000^4911 ≤ 2941810752733^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360430791 10000000000 2941810752733 6250000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (727943923/5000000000 : ℝ)^5935 ≤ (76106279939/781250000000 : ℝ)^4911 := by
    have hnat : (727943923 : ℕ)^5935*781250000000^4911 ≤ 76106279939^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727943923 5000000000 76106279939 781250000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4992152741/10000000000 : ℝ)^5935 ≤ (5398678015133/12500000000000 : ℝ)^4911 := by
    have hnat : (4992152741 : ℕ)^5935*12500000000000^4911 ≤ 5398678015133^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992152741 10000000000 5398678015133 12500000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360430791/10000000000 : ℝ), (-727943923/5000000000 : ℝ), (4992152741/10000000000 : ℝ)] ![(2941810752733/6250000000000 : ℝ), (76106279939/781250000000 : ℝ), (5398678015133/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360430791/10000000000 : ℝ)|^5935 ≤ (2941810752733/6250000000000 : ℝ)^4911
        have hw : |(5360430791/10000000000 : ℝ)|=(5360430791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-727943923/5000000000 : ℝ)|^5935 ≤ (76106279939/781250000000 : ℝ)^4911
        have hw : |(-727943923/5000000000 : ℝ)|=(727943923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4992152741/10000000000 : ℝ)|^5935 ≤ (5398678015133/12500000000000 : ℝ)^4911
        have hw : |(4992152741/10000000000 : ℝ)|=(4992152741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s0_2 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340108679/2500000000 : ℝ)*x 0 + (312009417/625000000 : ℝ)*x 1 + (-1455885369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340108679/2500000000 : ℝ)^5935 ≤ (9413802738947/20000000000000 : ℝ)^4911 := by
    have hnat : (1340108679 : ℕ)^5935*20000000000000^4911 ≤ 9413802738947^4911*2500000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340108679 2500000000 9413802738947 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312009417/625000000 : ℝ)^5935 ≤ (21594701244429/50000000000000 : ℝ)^4911 := by
    have hnat : (312009417 : ℕ)^5935*50000000000000^4911 ≤ 21594701244429^4911*625000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312009417 625000000 21594701244429 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1455885369/10000000000 : ℝ)^5935 ≤ (974158380227/10000000000000 : ℝ)^4911 := by
    have hnat : (1455885369 : ℕ)^5935*10000000000000^4911 ≤ 974158380227^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1455885369 10000000000 974158380227 10000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340108679/2500000000 : ℝ), (312009417/625000000 : ℝ), (-1455885369/10000000000 : ℝ)] ![(9413802738947/20000000000000 : ℝ), (21594701244429/50000000000000 : ℝ), (974158380227/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340108679/2500000000 : ℝ)|^5935 ≤ (9413802738947/20000000000000 : ℝ)^4911
        have hw : |(1340108679/2500000000 : ℝ)|=(1340108679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312009417/625000000 : ℝ)|^5935 ≤ (21594701244429/50000000000000 : ℝ)^4911
        have hw : |(312009417/625000000 : ℝ)|=(312009417/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1455885369/10000000000 : ℝ)|^5935 ≤ (974158380227/10000000000000 : ℝ)^4911
        have hw : |(-1455885369/10000000000 : ℝ)|=(1455885369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s0_3 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (792598637/2000000000 : ℝ)*x 0 + (1496424897/5000000000 : ℝ)*x 1 + (1014925389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (792598637/2000000000 : ℝ)^5935 ≤ (16337160231661/50000000000000 : ℝ)^4911 := by
    have hnat : (792598637 : ℕ)^5935*50000000000000^4911 ≤ 16337160231661^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792598637 2000000000 16337160231661 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1496424897/5000000000 : ℝ)^5935 ≤ (23272476442739/100000000000000 : ℝ)^4911 := by
    have hnat : (1496424897 : ℕ)^5935*100000000000000^4911 ≤ 23272476442739^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496424897 5000000000 23272476442739 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1014925389/2000000000 : ℝ)^5935 ≤ (4405320307553/10000000000000 : ℝ)^4911 := by
    have hnat : (1014925389 : ℕ)^5935*10000000000000^4911 ≤ 4405320307553^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014925389 2000000000 4405320307553 10000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(792598637/2000000000 : ℝ), (1496424897/5000000000 : ℝ), (1014925389/2000000000 : ℝ)] ![(16337160231661/50000000000000 : ℝ), (23272476442739/100000000000000 : ℝ), (4405320307553/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(792598637/2000000000 : ℝ)|^5935 ≤ (16337160231661/50000000000000 : ℝ)^4911
        have hw : |(792598637/2000000000 : ℝ)|=(792598637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1496424897/5000000000 : ℝ)|^5935 ≤ (23272476442739/100000000000000 : ℝ)^4911
        have hw : |(1496424897/5000000000 : ℝ)|=(1496424897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1014925389/2000000000 : ℝ)|^5935 ≤ (4405320307553/10000000000000 : ℝ)^4911
        have hw : |(1014925389/2000000000 : ℝ)|=(1014925389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s0_4 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-566008119/5000000000 : ℝ)*x 0 + (1251853931/2500000000 : ℝ)*x 1 + (5585115901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (566008119/5000000000 : ℝ)^5935 ≤ (1437474157761/20000000000000 : ℝ)^4911 := by
    have hnat : (566008119 : ℕ)^5935*20000000000000^4911 ≤ 1437474157761^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566008119 5000000000 1437474157761 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1251853931/2500000000 : ℝ)^5935 ≤ (43349055423317/100000000000000 : ℝ)^4911 := by
    have hnat : (1251853931 : ℕ)^5935*100000000000000^4911 ≤ 43349055423317^4911*2500000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251853931 2500000000 43349055423317 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5585115901/10000000000 : ℝ)^5935 ≤ (3091473360689/6250000000000 : ℝ)^4911 := by
    have hnat : (5585115901 : ℕ)^5935*6250000000000^4911 ≤ 3091473360689^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585115901 10000000000 3091473360689 6250000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-566008119/5000000000 : ℝ), (1251853931/2500000000 : ℝ), (5585115901/10000000000 : ℝ)] ![(1437474157761/20000000000000 : ℝ), (43349055423317/100000000000000 : ℝ), (3091473360689/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-566008119/5000000000 : ℝ)|^5935 ≤ (1437474157761/20000000000000 : ℝ)^4911
        have hw : |(-566008119/5000000000 : ℝ)|=(566008119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1251853931/2500000000 : ℝ)|^5935 ≤ (43349055423317/100000000000000 : ℝ)^4911
        have hw : |(1251853931/2500000000 : ℝ)|=(1251853931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5585115901/10000000000 : ℝ)|^5935 ≤ (3091473360689/6250000000000 : ℝ)^4911
        have hw : |(5585115901/10000000000 : ℝ)|=(5585115901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s0_5 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259939187/500000000 : ℝ)*x 0 + (-862921929/10000000000 : ℝ)*x 1 + (5585115873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259939187/500000000 : ℝ)^5935 ≤ (45359055077981/100000000000000 : ℝ)^4911 := by
    have hnat : (259939187 : ℕ)^5935*100000000000000^4911 ≤ 45359055077981^4911*500000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259939187 500000000 45359055077981 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (862921929/10000000000 : ℝ)^5935 ≤ (1294342858411/25000000000000 : ℝ)^4911 := by
    have hnat : (862921929 : ℕ)^5935*25000000000000^4911 ≤ 1294342858411^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862921929 10000000000 1294342858411 25000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5585115873/10000000000 : ℝ)^5935 ≤ (49463573471341/100000000000000 : ℝ)^4911 := by
    have hnat : (5585115873 : ℕ)^5935*100000000000000^4911 ≤ 49463573471341^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585115873 10000000000 49463573471341 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259939187/500000000 : ℝ), (-862921929/10000000000 : ℝ), (5585115873/10000000000 : ℝ)] ![(45359055077981/100000000000000 : ℝ), (1294342858411/25000000000000 : ℝ), (49463573471341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259939187/500000000 : ℝ)|^5935 ≤ (45359055077981/100000000000000 : ℝ)^4911
        have hw : |(259939187/500000000 : ℝ)|=(259939187/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-862921929/10000000000 : ℝ)|^5935 ≤ (1294342858411/25000000000000 : ℝ)^4911
        have hw : |(-862921929/10000000000 : ℝ)|=(862921929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5585115873/10000000000 : ℝ)|^5935 ≤ (49463573471341/100000000000000 : ℝ)^4911
        have hw : |(5585115873/10000000000 : ℝ)|=(5585115873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s0_6 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599391463/5000000000 : ℝ)*x 0 + (1396279051/2500000000 : ℝ)*x 1 + (-6903381/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599391463/5000000000 : ℝ)^5935 ≤ (9071809299003/20000000000000 : ℝ)^4911 := by
    have hnat : (2599391463 : ℕ)^5935*20000000000000^4911 ≤ 9071809299003^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599391463 5000000000 9071809299003 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1396279051/2500000000 : ℝ)^5935 ≤ (24731788507011/50000000000000 : ℝ)^4911 := by
    have hnat : (1396279051 : ℕ)^5935*50000000000000^4911 ≤ 24731788507011^4911*2500000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396279051 2500000000 24731788507011 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6903381/80000000 : ℝ)^5935 ≤ (647172060029/12500000000000 : ℝ)^4911 := by
    have hnat : (6903381 : ℕ)^5935*12500000000000^4911 ≤ 647172060029^4911*80000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6903381 80000000 647172060029 12500000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599391463/5000000000 : ℝ), (1396279051/2500000000 : ℝ), (-6903381/80000000 : ℝ)] ![(9071809299003/20000000000000 : ℝ), (24731788507011/50000000000000 : ℝ), (647172060029/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599391463/5000000000 : ℝ)|^5935 ≤ (9071809299003/20000000000000 : ℝ)^4911
        have hw : |(2599391463/5000000000 : ℝ)|=(2599391463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1396279051/2500000000 : ℝ)|^5935 ≤ (24731788507011/50000000000000 : ℝ)^4911
        have hw : |(1396279051/2500000000 : ℝ)|=(1396279051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6903381/80000000 : ℝ)|^5935 ≤ (647172060029/12500000000000 : ℝ)^4911
        have hw : |(-6903381/80000000 : ℝ)|=(6903381/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s0_7 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1983500901/5000000000 : ℝ)*x 0 + (5022422451/10000000000 : ℝ)*x 1 + (609343261/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1983500901/5000000000 : ℝ)^5935 ≤ (32714266562517/100000000000000 : ℝ)^4911 := by
    have hnat : (1983500901 : ℕ)^5935*100000000000000^4911 ≤ 32714266562517^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983500901 5000000000 32714266562517 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5022422451/10000000000 : ℝ)^5935 ≤ (43506105562453/100000000000000 : ℝ)^4911 := by
    have hnat : (5022422451 : ℕ)^5935*100000000000000^4911 ≤ 43506105562453^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5022422451 10000000000 43506105562453 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (609343261/2000000000 : ℝ)^5935 ≤ (23779627862033/100000000000000 : ℝ)^4911 := by
    have hnat : (609343261 : ℕ)^5935*100000000000000^4911 ≤ 23779627862033^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609343261 2000000000 23779627862033 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1983500901/5000000000 : ℝ), (5022422451/10000000000 : ℝ), (609343261/2000000000 : ℝ)] ![(32714266562517/100000000000000 : ℝ), (43506105562453/100000000000000 : ℝ), (23779627862033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1983500901/5000000000 : ℝ)|^5935 ≤ (32714266562517/100000000000000 : ℝ)^4911
        have hw : |(1983500901/5000000000 : ℝ)|=(1983500901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5022422451/10000000000 : ℝ)|^5935 ≤ (43506105562453/100000000000000 : ℝ)^4911
        have hw : |(5022422451/10000000000 : ℝ)|=(5022422451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(609343261/2000000000 : ℝ)|^5935 ≤ (23779627862033/100000000000000 : ℝ)^4911
        have hw : |(609343261/2000000000 : ℝ)|=(609343261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1760_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3551/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4059/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5919/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5919 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5919*1^1024 ≤ 0^1024*1^5919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5919/1024 : ℝ) ≤ (100190820638144377/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5919 ≤ (100190820638144377/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5919*20000000000000000000^1024 ≤ 100190820638144377^1024*5^5919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 100190820638144377 20000000000000000000 5919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (100190820638144377/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5919 := by
      have hnat : (1 : ℕ)^1024*1^5919 ≤ 1^5919*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20100190820638144377/20000000000000000000 : ℝ) ≤ (10008648718214047/10000000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (20100190820638144377/20000000000000000000 : ℝ)^1024 ≤ (10008648718214047/10000000000000000 : ℝ)^5919 := by
      have hnat : (20100190820638144377 : ℕ)^1024*10000000000000000^5919 ≤ 10008648718214047^5919*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20100190820638144377 20000000000000000000 10008648718214047 10000000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008648718214047/10000000000000000 : ℝ)) (X := (20100190820638144377/20000000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10100190820638144377/10000000000000000000 : ℝ) ≤ (5008648718214047/5000000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (10100190820638144377/10000000000000000000 : ℝ)^1024 ≤ (5008648718214047/5000000000000000 : ℝ)^5919 := by
      have hnat : (10100190820638144377 : ℕ)^1024*5000000000000000^5919 ≤ 5008648718214047^5919*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10100190820638144377 10000000000000000000 5008648718214047 5000000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008648718214047/5000000000000000 : ℝ)) (X := (10100190820638144377/10000000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8648718214047/4000000000000000 : ℝ)*(0 : ℝ))^(5919/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8648718214047/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(100190820638144377/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8648718214047/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5919/1024 : ℝ) := by
    rw [show (1 : ℝ)+(8648718214047/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10008648718214047/10000000000000000 : ℝ) by norm_num, show 1+(100190820638144377/20000000000000000000 : ℝ)+(0 : ℝ)=(20100190820638144377/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(100190820638144377/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8648718214047/4000000000000000 : ℝ)*(2/5 : ℝ))^(5919/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8648718214047/4000000000000000 : ℝ)*(2/5 : ℝ)=(5008648718214047/5000000000000000 : ℝ) by norm_num, show 1+2*(100190820638144377/20000000000000000000 : ℝ)=(10100190820638144377/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8648718214047/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8648718214047/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8648718214047/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8648718214047/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8648718214047/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8648718214047/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-28271117/250000000 : ℝ)*X 0 0+(5600866403/10000000000 : ℝ)*X 0 1+(624019011/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5360430791/10000000000 : ℝ)*X 1 0+(-727943923/5000000000 : ℝ)*X 1 1+(4992152741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1340108679/2500000000 : ℝ)*X 2 0+(312009417/625000000 : ℝ)*X 2 1+(-1455885369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((792598637/2000000000 : ℝ)*X 0 0+(1496424897/5000000000 : ℝ)*X 0 1+(1014925389/2000000000 : ℝ)*X 0 2+(792598637/2000000000 : ℝ)*X 1 0+(1496424897/5000000000 : ℝ)*X 1 1+(1014925389/2000000000 : ℝ)*X 1 2+(792598637/2000000000 : ℝ)*X 2 0+(1496424897/5000000000 : ℝ)*X 2 1+(1014925389/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-566008119/5000000000 : ℝ)*X 0 0+(1251853931/2500000000 : ℝ)*X 0 1+(5585115901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((259939187/500000000 : ℝ)*X 1 0+(-862921929/10000000000 : ℝ)*X 1 1+(5585115873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2599391463/5000000000 : ℝ)*X 2 0+(1396279051/2500000000 : ℝ)*X 2 1+(-6903381/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1983500901/5000000000 : ℝ)*X 0 0+(5022422451/10000000000 : ℝ)*X 0 1+(609343261/2000000000 : ℝ)*X 0 2+(1983500901/5000000000 : ℝ)*X 1 0+(5022422451/10000000000 : ℝ)*X 1 1+(609343261/2000000000 : ℝ)*X 1 2+(1983500901/5000000000 : ℝ)*X 2 0+(5022422451/10000000000 : ℝ)*X 2 1+(609343261/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5340710385173806473/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (38585161/2500000000000 : ℝ)*(base19) + (229895443/10000000000000 : ℝ)*(base23) + (3869579/2000000000000 : ℝ)*(base24) + (136088599/100000000000000 : ℝ)*(upper4) + (579884303/100000000000000 : ℝ)*(upper5) + (265398910719297/25000000000000 : ℝ)*(major0) + (265398910719297/25000000000000 : ℝ)*(major1) + (265398910719297/25000000000000 : ℝ)*(major2) + (821405190122367/50000000000000 : ℝ)*(sp0) + (1642823680760279/100000000000000 : ℝ)*(sp1) + (1642822731733339/100000000000000 : ℝ)*(sp2) + (3842901851773/800000000000 : ℝ)*(sp3) + (2968784397/20000000000000 : ℝ)*(sp4) + (1487034333/50000000000000 : ℝ)*(sp7) + (120091426385073/25000000000000 : ℝ)*(f.failure) + (1642825224166719/100000000000000 : ℝ)*(f.sum) + (33571230985041/50000000000000000000000000000 : ℝ)*base66 + (394686023564959/100000000000000000000000000000 : ℝ)*base67 + (1113971696164959/100000000000000000000000000000 : ℝ)*base69 + (614457734764959/100000000000000000000000000000 : ℝ)*base71 + (27268349735041/50000000000000000000000000000 : ℝ)*base74 + (978203029964959/100000000000000000000000000000 : ℝ)*base75 + (475573131264959/100000000000000000000000000000 : ℝ)*base77 + (902977036964959/100000000000000000000000000000 : ℝ)*base79 + (451903835041/50000000000000000000000000000 : ℝ)*base82 + (1206129/312500000000000000000 : ℝ)*base89 + (1206129/312500000000000000000 : ℝ)*base91 + (1206129/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1325713486415219847/200000000000000000000000 : ℝ) := by norm_num
    linear_combination (35134401/2000000000000 : ℝ)*(base19) + (1562934233/100000000000000 : ℝ)*(base23) + (6153327/10000000000000 : ℝ)*(upper2) + (74441563/25000000000000 : ℝ)*(upper3) + (60596297/25000000000000 : ℝ)*(upper5) + (279643530167471/25000000000000 : ℝ)*(major0) + (279643530167471/25000000000000 : ℝ)*(major1) + (279643530167471/25000000000000 : ℝ)*(major2) + (3988093603/50000000000000 : ℝ)*(sp1) + (3326831491/50000000000000 : ℝ)*(sp2) + (346199978601947/20000000000000 : ℝ)*(sp4) + (1730990160102479/100000000000000 : ℝ)*(sp5) + (43274791910313/2500000000000 : ℝ)*(sp6) + (506148127377781/100000000000000 : ℝ)*(sp7) + (506148127377781/100000000000000 : ℝ)*(f.failure) + (346199978601947/20000000000000 : ℝ)*(f.sum) + (194330286934863/50000000000000000000000000000 : ℝ)*base66 + (630450497565137/100000000000000000000000000000 : ℝ)*base67 + (188217609334863/100000000000000000000000000000 : ℝ)*base70 + (306177342134863/100000000000000000000000000000 : ℝ)*base72 + (88128886465137/50000000000000000000000000000 : ℝ)*base73 + (211746067134863/100000000000000000000000000000 : ℝ)*base76 + (786573864734863/100000000000000000000000000000 : ℝ)*base78 + (413528013165137/100000000000000000000000000000 : ℝ)*base79 + (99381742315137/50000000000000000000000000000 : ℝ)*base81 + (2409387/1250000000000000000000 : ℝ)*base90 + (2409387/1250000000000000000000 : ℝ)*base92 + (2409387/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1760_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3551/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4059/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1760_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1760_s1_0 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1167956769/10000000000 : ℝ)*x 0 + (2743004997/5000000000 : ℝ)*x 1 + (158814183/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1167956769/10000000000 : ℝ)^5935 ≤ (7464049657823/100000000000000 : ℝ)^4911 := by
    have hnat : (1167956769 : ℕ)^5935*100000000000000^4911 ≤ 7464049657823^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167956769 10000000000 7464049657823 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743004997/5000000000 : ℝ)^5935 ≤ (48404818339107/100000000000000 : ℝ)^4911 := by
    have hnat : (2743004997 : ℕ)^5935*100000000000000^4911 ≤ 48404818339107^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743004997 5000000000 48404818339107 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158814183/312500000 : ℝ)^5935 ≤ (44131131987687/100000000000000 : ℝ)^4911 := by
    have hnat : (158814183 : ℕ)^5935*100000000000000^4911 ≤ 44131131987687^4911*312500000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158814183 312500000 44131131987687 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1167956769/10000000000 : ℝ), (2743004997/5000000000 : ℝ), (158814183/312500000 : ℝ)] ![(7464049657823/100000000000000 : ℝ), (48404818339107/100000000000000 : ℝ), (44131131987687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1167956769/10000000000 : ℝ)|^5935 ≤ (7464049657823/100000000000000 : ℝ)^4911
        have hw : |(-1167956769/10000000000 : ℝ)|=(1167956769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743004997/5000000000 : ℝ)|^5935 ≤ (48404818339107/100000000000000 : ℝ)^4911
        have hw : |(2743004997/5000000000 : ℝ)|=(2743004997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158814183/312500000 : ℝ)|^5935 ≤ (44131131987687/100000000000000 : ℝ)^4911
        have hw : |(158814183/312500000 : ℝ)|=(158814183/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s1_1 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166560433/312500000 : ℝ)*x 0 + (-1378999621/10000000000 : ℝ)*x 1 + (635256719/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166560433/312500000 : ℝ)^5935 ≤ (46745539331633/100000000000000 : ℝ)^4911 := by
    have hnat : (166560433 : ℕ)^5935*100000000000000^4911 ≤ 46745539331633^4911*312500000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166560433 312500000 46745539331633 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1378999621/10000000000 : ℝ)^5935 ≤ (9123329753839/100000000000000 : ℝ)^4911 := by
    have hnat : (1378999621 : ℕ)^5935*100000000000000^4911 ≤ 9123329753839^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378999621 10000000000 9123329753839 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635256719/1250000000 : ℝ)^5935 ≤ (2758195681017/6250000000000 : ℝ)^4911 := by
    have hnat : (635256719 : ℕ)^5935*6250000000000^4911 ≤ 2758195681017^4911*1250000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635256719 1250000000 2758195681017 6250000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166560433/312500000 : ℝ), (-1378999621/10000000000 : ℝ), (635256719/1250000000 : ℝ)] ![(46745539331633/100000000000000 : ℝ), (9123329753839/100000000000000 : ℝ), (2758195681017/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166560433/312500000 : ℝ)|^5935 ≤ (46745539331633/100000000000000 : ℝ)^4911
        have hw : |(166560433/312500000 : ℝ)|=(166560433/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1378999621/10000000000 : ℝ)|^5935 ≤ (9123329753839/100000000000000 : ℝ)^4911
        have hw : |(-1378999621/10000000000 : ℝ)|=(1378999621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(635256719/1250000000 : ℝ)|^5935 ≤ (2758195681017/6250000000000 : ℝ)^4911
        have hw : |(635256719/1250000000 : ℝ)|=(635256719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s1_2 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5329933111/10000000000 : ℝ)*x 0 + (101641093/200000000 : ℝ)*x 1 + (-1378999431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5329933111/10000000000 : ℝ)^5935 ≤ (467455314353/1000000000000 : ℝ)^4911 := by
    have hnat : (5329933111 : ℕ)^5935*1000000000000^4911 ≤ 467455314353^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5329933111 10000000000 467455314353 1000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101641093/200000000 : ℝ)^5935 ≤ (22065570160111/50000000000000 : ℝ)^4911 := by
    have hnat : (101641093 : ℕ)^5935*50000000000000^4911 ≤ 22065570160111^4911*200000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101641093 200000000 22065570160111 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378999431/10000000000 : ℝ)^5935 ≤ (4561664117357/50000000000000 : ℝ)^4911 := by
    have hnat : (1378999431 : ℕ)^5935*50000000000000^4911 ≤ 4561664117357^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378999431 10000000000 4561664117357 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5329933111/10000000000 : ℝ), (101641093/200000000 : ℝ), (-1378999431/10000000000 : ℝ)] ![(467455314353/1000000000000 : ℝ), (22065570160111/50000000000000 : ℝ), (4561664117357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5329933111/10000000000 : ℝ)|^5935 ≤ (467455314353/1000000000000 : ℝ)^4911
        have hw : |(5329933111/10000000000 : ℝ)|=(5329933111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(101641093/200000000 : ℝ)|^5935 ≤ (22065570160111/50000000000000 : ℝ)^4911
        have hw : |(101641093/200000000 : ℝ)|=(101641093/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1378999431/10000000000 : ℝ)|^5935 ≤ (4561664117357/50000000000000 : ℝ)^4911
        have hw : |(-1378999431/10000000000 : ℝ)|=(1378999431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s1_3 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (500010879/1250000000 : ℝ)*x 0 + (3340334739/10000000000 : ℝ)*x 1 + (2360920831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (500010879/1250000000 : ℝ)^5935 ≤ (16522141802279/50000000000000 : ℝ)^4911 := by
    have hnat : (500010879 : ℕ)^5935*50000000000000^4911 ≤ 16522141802279^4911*1250000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500010879 1250000000 16522141802279 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3340334739/10000000000 : ℝ)^5935 ≤ (13288156329477/50000000000000 : ℝ)^4911 := by
    have hnat : (3340334739 : ℕ)^5935*50000000000000^4911 ≤ 13288156329477^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3340334739 10000000000 13288156329477 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2360920831/5000000000 : ℝ)^5935 ≤ (8075880744511/20000000000000 : ℝ)^4911 := by
    have hnat : (2360920831 : ℕ)^5935*20000000000000^4911 ≤ 8075880744511^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2360920831 5000000000 8075880744511 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(500010879/1250000000 : ℝ), (3340334739/10000000000 : ℝ), (2360920831/5000000000 : ℝ)] ![(16522141802279/50000000000000 : ℝ), (13288156329477/50000000000000 : ℝ), (8075880744511/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(500010879/1250000000 : ℝ)|^5935 ≤ (16522141802279/50000000000000 : ℝ)^4911
        have hw : |(500010879/1250000000 : ℝ)|=(500010879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3340334739/10000000000 : ℝ)|^5935 ≤ (13288156329477/50000000000000 : ℝ)^4911
        have hw : |(3340334739/10000000000 : ℝ)|=(3340334739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2360920831/5000000000 : ℝ)|^5935 ≤ (8075880744511/20000000000000 : ℝ)^4911
        have hw : |(2360920831/5000000000 : ℝ)|=(2360920831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s1_4 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-584148543/5000000000 : ℝ)*x 0 + (2544397321/5000000000 : ℝ)*x 1 + (5479127543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (584148543/5000000000 : ℝ)^5935 ≤ (3733339040769/50000000000000 : ℝ)^4911 := by
    have hnat : (584148543 : ℕ)^5935*50000000000000^4911 ≤ 3733339040769^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584148543 5000000000 3733339040769 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544397321/5000000000 : ℝ)^5935 ≤ (11050470526241/25000000000000 : ℝ)^4911 := by
    have hnat : (2544397321 : ℕ)^5935*25000000000000^4911 ≤ 11050470526241^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544397321 5000000000 11050470526241 25000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479127543/10000000000 : ℝ)^5935 ≤ (48331439794799/100000000000000 : ℝ)^4911 := by
    have hnat : (5479127543 : ℕ)^5935*100000000000000^4911 ≤ 48331439794799^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479127543 10000000000 48331439794799 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-584148543/5000000000 : ℝ), (2544397321/5000000000 : ℝ), (5479127543/10000000000 : ℝ)] ![(3733339040769/50000000000000 : ℝ), (11050470526241/25000000000000 : ℝ), (48331439794799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-584148543/5000000000 : ℝ)|^5935 ≤ (3733339040769/50000000000000 : ℝ)^4911
        have hw : |(-584148543/5000000000 : ℝ)|=(584148543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2544397321/5000000000 : ℝ)|^5935 ≤ (11050470526241/25000000000000 : ℝ)^4911
        have hw : |(2544397321/5000000000 : ℝ)|=(2544397321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479127543/10000000000 : ℝ)|^5935 ≤ (48331439794799/100000000000000 : ℝ)^4911
        have hw : |(5479127543/10000000000 : ℝ)|=(5479127543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s1_5 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (652896473/1250000000 : ℝ)*x 0 + (-981925439/10000000000 : ℝ)*x 1 + (1095825497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (652896473/1250000000 : ℝ)^5935 ≤ (45616332748113/100000000000000 : ℝ)^4911 := by
    have hnat : (652896473 : ℕ)^5935*100000000000000^4911 ≤ 45616332748113^4911*1250000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652896473 1250000000 45616332748113 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (981925439/10000000000 : ℝ)^5935 ≤ (6052228067713/100000000000000 : ℝ)^4911 := by
    have hnat : (981925439 : ℕ)^5935*100000000000000^4911 ≤ 6052228067713^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981925439 10000000000 6052228067713 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095825497/2000000000 : ℝ)^5935 ≤ (24165719588251/50000000000000 : ℝ)^4911 := by
    have hnat : (1095825497 : ℕ)^5935*50000000000000^4911 ≤ 24165719588251^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095825497 2000000000 24165719588251 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(652896473/1250000000 : ℝ), (-981925439/10000000000 : ℝ), (1095825497/2000000000 : ℝ)] ![(45616332748113/100000000000000 : ℝ), (6052228067713/100000000000000 : ℝ), (24165719588251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(652896473/1250000000 : ℝ)|^5935 ≤ (45616332748113/100000000000000 : ℝ)^4911
        have hw : |(652896473/1250000000 : ℝ)|=(652896473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-981925439/10000000000 : ℝ)|^5935 ≤ (6052228067713/100000000000000 : ℝ)^4911
        have hw : |(-981925439/10000000000 : ℝ)|=(981925439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095825497/2000000000 : ℝ)|^5935 ≤ (24165719588251/50000000000000 : ℝ)^4911
        have hw : |(1095825497/2000000000 : ℝ)|=(1095825497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s1_6 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2611585927/5000000000 : ℝ)*x 0 + (5479127103/10000000000 : ℝ)*x 1 + (-490962943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2611585927/5000000000 : ℝ)^5935 ≤ (45616333486927/100000000000000 : ℝ)^4911 := by
    have hnat : (2611585927 : ℕ)^5935*100000000000000^4911 ≤ 45616333486927^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611585927 5000000000 45616333486927 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479127103/10000000000 : ℝ)^5935 ≤ (48331435104271/100000000000000 : ℝ)^4911 := by
    have hnat : (5479127103 : ℕ)^5935*100000000000000^4911 ≤ 48331435104271^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479127103 10000000000 48331435104271 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490962943/5000000000 : ℝ)^5935 ≤ (756528924667/12500000000000 : ℝ)^4911 := by
    have hnat : (490962943 : ℕ)^5935*12500000000000^4911 ≤ 756528924667^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490962943 5000000000 756528924667 12500000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2611585927/5000000000 : ℝ), (5479127103/10000000000 : ℝ), (-490962943/5000000000 : ℝ)] ![(45616333486927/100000000000000 : ℝ), (48331435104271/100000000000000 : ℝ), (756528924667/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2611585927/5000000000 : ℝ)|^5935 ≤ (45616333486927/100000000000000 : ℝ)^4911
        have hw : |(2611585927/5000000000 : ℝ)|=(2611585927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479127103/10000000000 : ℝ)|^5935 ≤ (48331435104271/100000000000000 : ℝ)^4911
        have hw : |(5479127103/10000000000 : ℝ)|=(5479127103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490962943/5000000000 : ℝ)|^5935 ≤ (756528924667/12500000000000 : ℝ)^4911
        have hw : |(-490962943/5000000000 : ℝ)|=(490962943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s1_7 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4001252927/10000000000 : ℝ)*x 0 + (4698790883/10000000000 : ℝ)*x 1 + (420483771/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4001252927/10000000000 : ℝ)^5935 ≤ (3305592353339/10000000000000 : ℝ)^4911 := by
    have hnat : (4001252927 : ℕ)^5935*10000000000000^4911 ≤ 3305592353339^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4001252927 10000000000 3305592353339 10000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4698790883/10000000000 : ℝ)^5935 ≤ (40141301470901/100000000000000 : ℝ)^4911 := by
    have hnat : (4698790883 : ℕ)^5935*100000000000000^4911 ≤ 40141301470901^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4698790883 10000000000 40141301470901 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420483771/1250000000 : ℝ)^5935 ≤ (26802774979651/100000000000000 : ℝ)^4911 := by
    have hnat : (420483771 : ℕ)^5935*100000000000000^4911 ≤ 26802774979651^4911*1250000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420483771 1250000000 26802774979651 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4001252927/10000000000 : ℝ), (4698790883/10000000000 : ℝ), (420483771/1250000000 : ℝ)] ![(3305592353339/10000000000000 : ℝ), (40141301470901/100000000000000 : ℝ), (26802774979651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4001252927/10000000000 : ℝ)|^5935 ≤ (3305592353339/10000000000000 : ℝ)^4911
        have hw : |(4001252927/10000000000 : ℝ)|=(4001252927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4698790883/10000000000 : ℝ)|^5935 ≤ (40141301470901/100000000000000 : ℝ)^4911
        have hw : |(4698790883/10000000000 : ℝ)|=(4698790883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(420483771/1250000000 : ℝ)|^5935 ≤ (26802774979651/100000000000000 : ℝ)^4911
        have hw : |(420483771/1250000000 : ℝ)|=(420483771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1760_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4059/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3551/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4559/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4457/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4059/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3551/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4059/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3551/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4059/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3551/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4059/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3551/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4059/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3551/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4059/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3551/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3551/50000 : ℝ) ^ (5919/1024 : ℝ) ≤ (5735961054203/25000000000000000000 : ℝ) := by
    have hpowers : (3551/50000 : ℝ)^5919 ≤ (5735961054203/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3551 : ℕ)^5919*25000000000000000000^1024 ≤ 5735961054203^1024*50000^5919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3551 50000 5735961054203 25000000000000000000 5919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3551/50000 : ℝ)) (X := (5735961054203/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4059/20000 : ℝ) ^ (5919/1024 : ℝ) ≤ (9920175510277849/100000000000000000000 : ℝ) := by
    have hpowers : (4059/20000 : ℝ)^5919 ≤ (9920175510277849/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4059 : ℕ)^5919*100000000000000000000^1024 ≤ 9920175510277849^1024*20000^5919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4059 20000 9920175510277849 100000000000000000000 5919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4059/20000 : ℝ)) (X := (9920175510277849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500005735961054203/12500000000000000000 : ℝ) ≤ (5000000396933469/5000000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (12500005735961054203/12500000000000000000 : ℝ)^1024 ≤ (5000000396933469/5000000000000000 : ℝ)^5919 := by
      have hnat : (12500005735961054203 : ℕ)^1024*5000000000000000^5919 ≤ 5000000396933469^5919*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500005735961054203 12500000000000000000 5000000396933469 5000000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000396933469/5000000000000000 : ℝ)) (X := (12500005735961054203/12500000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100009943119354494661/100000000000000000000 : ℝ) ≤ (10000172011076613/10000000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (100009943119354494661/100000000000000000000 : ℝ)^1024 ≤ (10000172011076613/10000000000000000 : ℝ)^5919 := by
      have hnat : (100009943119354494661 : ℕ)^1024*10000000000000000^5919 ≤ 10000172011076613^5919*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100009943119354494661 100000000000000000000 10000172011076613 10000000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000172011076613/10000000000000000 : ℝ)) (X := (100009943119354494661/100000000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009920175510277849/50000000000000000000 : ℝ) ≤ (625021451767893/625000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (50009920175510277849/50000000000000000000 : ℝ)^1024 ≤ (625021451767893/625000000000000 : ℝ)^5919 := by
      have hnat : (50009920175510277849 : ℕ)^1024*625000000000000^5919 ≤ 625021451767893^5919*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009920175510277849 50000000000000000000 625021451767893 625000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625021451767893/625000000000000 : ℝ)) (X := (50009920175510277849/50000000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5735961054203/25000000000000000000 : ℝ) ≤ ((65963789252120144667/65965000000000000000 : ℝ)+2*(6848688387/52772000000000 : ℝ)*(3551/50000 : ℝ))^(5919/1024 : ℝ) := by
    rw [show (65963789252120144667/65965000000000000000 : ℝ)+2*(6848688387/52772000000000 : ℝ)*(3551/50000 : ℝ)=(5000000396933469/5000000000000000 : ℝ) by norm_num, show 1+2*(5735961054203/25000000000000000000 : ℝ)=(12500005735961054203/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9920175510277849/100000000000000000000 : ℝ)+(5735961054203/25000000000000000000 : ℝ) ≤ ((65963789252120144667/65965000000000000000 : ℝ)+(6848688387/52772000000000 : ℝ)*((4059/20000 : ℝ)+(3551/50000 : ℝ)))^(5919/1024 : ℝ) := by
    rw [show (65963789252120144667/65965000000000000000 : ℝ)+(6848688387/52772000000000 : ℝ)*((4059/20000 : ℝ)+(3551/50000 : ℝ))=(10000172011076613/10000000000000000 : ℝ) by norm_num, show 1+(9920175510277849/100000000000000000000 : ℝ)+(5735961054203/25000000000000000000 : ℝ)=(100009943119354494661/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9920175510277849/100000000000000000000 : ℝ) ≤ ((65963789252120144667/65965000000000000000 : ℝ)+2*(6848688387/52772000000000 : ℝ)*(4059/20000 : ℝ))^(5919/1024 : ℝ) := by
    rw [show (65963789252120144667/65965000000000000000 : ℝ)+2*(6848688387/52772000000000 : ℝ)*(4059/20000 : ℝ)=(625021451767893/625000000000000 : ℝ) by norm_num, show 1+2*(9920175510277849/100000000000000000000 : ℝ)=(50009920175510277849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (65963789252120144667/65965000000000000000 : ℝ)*(X 1 0+X 2 0)+(6848688387/52772000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (3551/50000 : ℝ)) (hi := (4059/20000 : ℝ)) (c := (65963789252120144667/65965000000000000000 : ℝ)) (alpha := (6848688387/52772000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (65963789252120144667/65965000000000000000 : ℝ)*(X 0 1+X 2 1)+(6848688387/52772000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (3551/50000 : ℝ)) (hi := (4059/20000 : ℝ)) (c := (65963789252120144667/65965000000000000000 : ℝ)) (alpha := (6848688387/52772000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (65963789252120144667/65965000000000000000 : ℝ)*(X 0 2+X 1 2)+(6848688387/52772000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (3551/50000 : ℝ)) (hi := (4059/20000 : ℝ)) (c := (65963789252120144667/65965000000000000000 : ℝ)) (alpha := (6848688387/52772000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1167956769/10000000000 : ℝ)*X 0 0+(2743004997/5000000000 : ℝ)*X 0 1+(158814183/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((166560433/312500000 : ℝ)*X 1 0+(-1378999621/10000000000 : ℝ)*X 1 1+(635256719/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5329933111/10000000000 : ℝ)*X 2 0+(101641093/200000000 : ℝ)*X 2 1+(-1378999431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((500010879/1250000000 : ℝ)*X 0 0+(3340334739/10000000000 : ℝ)*X 0 1+(2360920831/5000000000 : ℝ)*X 0 2+(500010879/1250000000 : ℝ)*X 1 0+(3340334739/10000000000 : ℝ)*X 1 1+(2360920831/5000000000 : ℝ)*X 1 2+(500010879/1250000000 : ℝ)*X 2 0+(3340334739/10000000000 : ℝ)*X 2 1+(2360920831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-584148543/5000000000 : ℝ)*X 0 0+(2544397321/5000000000 : ℝ)*X 0 1+(5479127543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((652896473/1250000000 : ℝ)*X 1 0+(-981925439/10000000000 : ℝ)*X 1 1+(1095825497/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2611585927/5000000000 : ℝ)*X 2 0+(5479127103/10000000000 : ℝ)*X 2 1+(-490962943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4001252927/10000000000 : ℝ)*X 0 0+(4698790883/10000000000 : ℝ)*X 0 1+(420483771/1250000000 : ℝ)*X 0 2+(4001252927/10000000000 : ℝ)*X 1 0+(4698790883/10000000000 : ℝ)*X 1 1+(420483771/1250000000 : ℝ)*X 1 2+(4001252927/10000000000 : ℝ)*X 2 0+(4698790883/10000000000 : ℝ)*X 2 1+(420483771/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1780878894073463453554042869/131930000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1411967/78125000000 : ℝ)*(base19) + (692730401/50000000000000 : ℝ)*(base23) + (20209483/50000000000000 : ℝ)*(lower2) + (28579151/10000000000000 : ℝ)*(upper3) + (147016363/50000000000000 : ℝ)*(upper5) + (63988005486869/4000000000000 : ℝ)*(major0) + (63988005486869/4000000000000 : ℝ)*(major1) + (63988005486869/4000000000000 : ℝ)*(major2) + (618882625366871/25000000000000 : ℝ)*(sp0) + (618885808202739/25000000000000 : ℝ)*(sp1) + (1237771827333957/50000000000000 : ℝ)*(sp2) + (180962757156919/25000000000000 : ℝ)*(sp3) + (14538661233/100000000000000 : ℝ)*(sp4) + (1877815773/50000000000000 : ℝ)*(sp7) + (361927392129611/50000000000000 : ℝ)*(f.failure) + (618886260032179/25000000000000 : ℝ)*(f.sum) + (3418198274869/2638600000000000000000000000 : ℝ)*base66 + (990494927917412377/263860000000000000000000000000000 : ℝ)*base68 + (2826758859455552377/263860000000000000000000000000000 : ℝ)*base70 + (169541701836972377/263860000000000000000000000000000 : ℝ)*base72 + (31204393296717/13193000000000000000000000000 : ℝ)*base73 + (432163311780907623/263860000000000000000000000000000 : ℝ)*base75 + (197451260612452377/263860000000000000000000000000000 : ℝ)*base78 + (773158130929107623/263860000000000000000000000000000 : ℝ)*base79 + (49394497349183/13193000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3757797/625000000000000000000 : ℝ)*base90 + (3757797/625000000000000000000 : ℝ)*base92 + (3757797/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41155394087721318013111958877/3298250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (864228559/50000000000000 : ℝ)*(base19) + (269967109/12500000000000 : ℝ)*(base23) + (335507039/100000000000000 : ℝ)*(upper3) + (188063863/100000000000000 : ℝ)*(lower4) + (170221331/100000000000000 : ℝ)*(upper5) + (1655509791159123/100000000000000 : ℝ)*(major0) + (1655509791159123/100000000000000 : ℝ)*(major1) + (1655509791159123/100000000000000 : ℝ)*(major2) + (1085559861/10000000000000 : ℝ)*(sp1) + (12660418683/100000000000000 : ℝ)*(sp2) + (40029856970317/1562500000000 : ℝ)*(sp4) + (32023728275557/1250000000000 : ℝ)*(sp5) + (640474006486183/25000000000000 : ℝ)*(sp6) + (374554160143163/50000000000000 : ℝ)*(sp7) + (374554160143163/50000000000000 : ℝ)*(f.failure) + (40029856970317/1562500000000 : ℝ)*(f.sum) + (92917272202243/13193000000000000000000000000 : ℝ)*base65 + (21478001892632902959/6596500000000000000000000000000000 : ℝ)*base68 + (11793893956039902959/6596500000000000000000000000000000 : ℝ)*base70 + (52159462140835097041/6596500000000000000000000000000000 : ℝ)*base71 + (6996770382139/13193000000000000000000000000 : ℝ)*base74 + (21015883710136097041/6596500000000000000000000000000000 : ℝ)*base75 + (31984391827828597041/6596500000000000000000000000000000 : ℝ)*base77 + (51088508478942097041/6596500000000000000000000000000000 : ℝ)*base79 + (1843832320653/6596500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7689301/625000000000000000000 : ℝ)*base90 + (7689301/625000000000000000000 : ℝ)*base92 + (7689301/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1760_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4059/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3551/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4559/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4457/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1760_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1760_s2_0 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1168613103/10000000000 : ℝ)*x 0 + (5483896447/10000000000 : ℝ)*x 1 + (5083718187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1168613103/10000000000 : ℝ)^5935 ≤ (7469118968207/100000000000000 : ℝ)^4911 := by
    have hnat : (1168613103 : ℕ)^5935*100000000000000^4911 ≤ 7469118968207^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168613103 10000000000 7469118968207 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5483896447/10000000000 : ℝ)^5935 ≤ (24191141158673/50000000000000 : ℝ)^4911 := by
    have hnat : (5483896447 : ℕ)^5935*50000000000000^4911 ≤ 24191141158673^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483896447 10000000000 24191141158673 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5083718187/10000000000 : ℝ)^5935 ≤ (8829719739641/20000000000000 : ℝ)^4911 := by
    have hnat : (5083718187 : ℕ)^5935*20000000000000^4911 ≤ 8829719739641^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083718187 10000000000 8829719739641 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1168613103/10000000000 : ℝ), (5483896447/10000000000 : ℝ), (5083718187/10000000000 : ℝ)] ![(7469118968207/100000000000000 : ℝ), (24191141158673/50000000000000 : ℝ), (8829719739641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1168613103/10000000000 : ℝ)|^5935 ≤ (7469118968207/100000000000000 : ℝ)^4911
        have hw : |(-1168613103/10000000000 : ℝ)|=(1168613103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5483896447/10000000000 : ℝ)|^5935 ≤ (24191141158673/50000000000000 : ℝ)^4911
        have hw : |(5483896447/10000000000 : ℝ)|=(5483896447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5083718187/10000000000 : ℝ)|^5935 ≤ (8829719739641/20000000000000 : ℝ)^4911
        have hw : |(5083718187/10000000000 : ℝ)|=(5083718187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s2_1 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2664671613/5000000000 : ℝ)*x 0 + (-275519539/2000000000 : ℝ)*x 1 + (5083718191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2664671613/5000000000 : ℝ)^5935 ≤ (46739279255293/100000000000000 : ℝ)^4911 := by
    have hnat : (2664671613 : ℕ)^5935*100000000000000^4911 ≤ 46739279255293^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2664671613 5000000000 46739279255293 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275519539/2000000000 : ℝ)^5935 ≤ (9112121987721/100000000000000 : ℝ)^4911 := by
    have hnat : (275519539 : ℕ)^5935*100000000000000^4911 ≤ 9112121987721^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275519539 2000000000 9112121987721 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5083718191/10000000000 : ℝ)^5935 ≤ (8829719748037/20000000000000 : ℝ)^4911 := by
    have hnat : (5083718191 : ℕ)^5935*20000000000000^4911 ≤ 8829719748037^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083718191 10000000000 8829719748037 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2664671613/5000000000 : ℝ), (-275519539/2000000000 : ℝ), (5083718191/10000000000 : ℝ)] ![(46739279255293/100000000000000 : ℝ), (9112121987721/100000000000000 : ℝ), (8829719748037/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2664671613/5000000000 : ℝ)|^5935 ≤ (46739279255293/100000000000000 : ℝ)^4911
        have hw : |(2664671613/5000000000 : ℝ)|=(2664671613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-275519539/2000000000 : ℝ)|^5935 ≤ (9112121987721/100000000000000 : ℝ)^4911
        have hw : |(-275519539/2000000000 : ℝ)|=(275519539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5083718191/10000000000 : ℝ)|^5935 ≤ (8829719748037/20000000000000 : ℝ)^4911
        have hw : |(5083718191/10000000000 : ℝ)|=(5083718191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s2_2 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1332335807/2500000000 : ℝ)*x 0 + (5083718189/10000000000 : ℝ)*x 1 + (-688798847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1332335807/2500000000 : ℝ)^5935 ≤ (4673927927649/10000000000000 : ℝ)^4911 := by
    have hnat : (1332335807 : ℕ)^5935*10000000000000^4911 ≤ 4673927927649^4911*2500000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332335807 2500000000 4673927927649 10000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083718189/10000000000 : ℝ)^5935 ≤ (8829719743839/20000000000000 : ℝ)^4911 := by
    have hnat : (5083718189 : ℕ)^5935*20000000000000^4911 ≤ 8829719743839^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083718189 10000000000 8829719743839 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (688798847/5000000000 : ℝ)^5935 ≤ (9112121979727/100000000000000 : ℝ)^4911 := by
    have hnat : (688798847 : ℕ)^5935*100000000000000^4911 ≤ 9112121979727^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688798847 5000000000 9112121979727 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1332335807/2500000000 : ℝ), (5083718189/10000000000 : ℝ), (-688798847/5000000000 : ℝ)] ![(4673927927649/10000000000000 : ℝ), (8829719743839/20000000000000 : ℝ), (9112121979727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1332335807/2500000000 : ℝ)|^5935 ≤ (4673927927649/10000000000000 : ℝ)^4911
        have hw : |(1332335807/2500000000 : ℝ)|=(1332335807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083718189/10000000000 : ℝ)|^5935 ≤ (8829719743839/20000000000000 : ℝ)^4911
        have hw : |(5083718189/10000000000 : ℝ)|=(5083718189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-688798847/5000000000 : ℝ)|^5935 ≤ (9112121979727/100000000000000 : ℝ)^4911
        have hw : |(-688798847/5000000000 : ℝ)|=(688798847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s2_3 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (100015689/250000000 : ℝ)*x 0 + (167337761/500000000 : ℝ)*x 1 + (4715343943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100015689/250000000 : ℝ)^5935 ≤ (4131209997261/12500000000000 : ℝ)^4911 := by
    have hnat : (100015689 : ℕ)^5935*12500000000000^4911 ≤ 4131209997261^4911*250000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100015689 250000000 4131209997261 12500000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167337761/500000000 : ℝ)^5935 ≤ (6659514708661/25000000000000 : ℝ)^4911 := by
    have hnat : (167337761 : ℕ)^5935*25000000000000^4911 ≤ 6659514708661^4911*500000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167337761 500000000 6659514708661 25000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4715343943/10000000000 : ℝ)^5935 ≤ (40312261167621/100000000000000 : ℝ)^4911 := by
    have hnat : (4715343943 : ℕ)^5935*100000000000000^4911 ≤ 40312261167621^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4715343943 10000000000 40312261167621 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(100015689/250000000 : ℝ), (167337761/500000000 : ℝ), (4715343943/10000000000 : ℝ)] ![(4131209997261/12500000000000 : ℝ), (6659514708661/25000000000000 : ℝ), (40312261167621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(100015689/250000000 : ℝ)|^5935 ≤ (4131209997261/12500000000000 : ℝ)^4911
        have hw : |(100015689/250000000 : ℝ)|=(100015689/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(167337761/500000000 : ℝ)|^5935 ≤ (6659514708661/25000000000000 : ℝ)^4911
        have hw : |(167337761/500000000 : ℝ)|=(167337761/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4715343943/10000000000 : ℝ)|^5935 ≤ (40312261167621/100000000000000 : ℝ)^4911
        have hw : |(4715343943/10000000000 : ℝ)|=(4715343943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s2_4 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1168944443/10000000000 : ℝ)*x 0 + (5090332879/10000000000 : ℝ)*x 1 + (109542873/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1168944443/10000000000 : ℝ)^5935 ≤ (3735839178073/50000000000000 : ℝ)^4911 := by
    have hnat : (1168944443 : ℕ)^5935*50000000000000^4911 ≤ 3735839178073^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168944443 10000000000 3735839178073 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5090332879/10000000000 : ℝ)^5935 ≤ (22109014956249/50000000000000 : ℝ)^4911 := by
    have hnat : (5090332879 : ℕ)^5935*50000000000000^4911 ≤ 22109014956249^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5090332879 10000000000 22109014956249 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109542873/200000000 : ℝ)^5935 ≤ (24155145857/50000000000 : ℝ)^4911 := by
    have hnat : (109542873 : ℕ)^5935*50000000000^4911 ≤ 24155145857^4911*200000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109542873 200000000 24155145857 50000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1168944443/10000000000 : ℝ), (5090332879/10000000000 : ℝ), (109542873/200000000 : ℝ)] ![(3735839178073/50000000000000 : ℝ), (22109014956249/50000000000000 : ℝ), (24155145857/50000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1168944443/10000000000 : ℝ)|^5935 ≤ (3735839178073/50000000000000 : ℝ)^4911
        have hw : |(-1168944443/10000000000 : ℝ)|=(1168944443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5090332879/10000000000 : ℝ)|^5935 ≤ (22109014956249/50000000000000 : ℝ)^4911
        have hw : |(5090332879/10000000000 : ℝ)|=(5090332879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109542873/200000000 : ℝ)|^5935 ≤ (24155145857/50000000000 : ℝ)^4911
        have hw : |(109542873/200000000 : ℝ)|=(109542873/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s2_5 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (652948649/1250000000 : ℝ)*x 0 + (-492086147/5000000000 : ℝ)*x 1 + (5477143789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (652948649/1250000000 : ℝ)^5935 ≤ (4562073830927/10000000000000 : ℝ)^4911 := by
    have hnat : (652948649 : ℕ)^5935*10000000000000^4911 ≤ 4562073830927^4911*1250000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652948649 1250000000 4562073830927 10000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492086147/5000000000 : ℝ)^5935 ≤ (6068968479603/100000000000000 : ℝ)^4911 := by
    have hnat : (492086147 : ℕ)^5935*100000000000000^4911 ≤ 6068968479603^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492086147 5000000000 6068968479603 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477143789/10000000000 : ℝ)^5935 ≤ (12077573298917/25000000000000 : ℝ)^4911 := by
    have hnat : (5477143789 : ℕ)^5935*25000000000000^4911 ≤ 12077573298917^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477143789 10000000000 12077573298917 25000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(652948649/1250000000 : ℝ), (-492086147/5000000000 : ℝ), (5477143789/10000000000 : ℝ)] ![(4562073830927/10000000000000 : ℝ), (6068968479603/100000000000000 : ℝ), (12077573298917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(652948649/1250000000 : ℝ)|^5935 ≤ (4562073830927/10000000000000 : ℝ)^4911
        have hw : |(652948649/1250000000 : ℝ)|=(652948649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-492086147/5000000000 : ℝ)|^5935 ≤ (6068968479603/100000000000000 : ℝ)^4911
        have hw : |(-492086147/5000000000 : ℝ)|=(492086147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477143789/10000000000 : ℝ)|^5935 ≤ (12077573298917/25000000000000 : ℝ)^4911
        have hw : |(5477143789/10000000000 : ℝ)|=(5477143789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s2_6 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5223589417/10000000000 : ℝ)*x 0 + (5477143703/10000000000 : ℝ)*x 1 + (-492086049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5223589417/10000000000 : ℝ)^5935 ≤ (45620740684067/100000000000000 : ℝ)^4911 := by
    have hnat : (5223589417 : ℕ)^5935*100000000000000^4911 ≤ 45620740684067^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223589417 10000000000 45620740684067 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5477143703/10000000000 : ℝ)^5935 ≤ (48310292278953/100000000000000 : ℝ)^4911 := by
    have hnat : (5477143703 : ℕ)^5935*100000000000000^4911 ≤ 48310292278953^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477143703 10000000000 48310292278953 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492086049/5000000000 : ℝ)^5935 ≤ (3034483509469/50000000000000 : ℝ)^4911 := by
    have hnat : (492086049 : ℕ)^5935*50000000000000^4911 ≤ 3034483509469^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492086049 5000000000 3034483509469 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5223589417/10000000000 : ℝ), (5477143703/10000000000 : ℝ), (-492086049/5000000000 : ℝ)] ![(45620740684067/100000000000000 : ℝ), (48310292278953/100000000000000 : ℝ), (3034483509469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5223589417/10000000000 : ℝ)|^5935 ≤ (45620740684067/100000000000000 : ℝ)^4911
        have hw : |(5223589417/10000000000 : ℝ)|=(5223589417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5477143703/10000000000 : ℝ)|^5935 ≤ (48310292278953/100000000000000 : ℝ)^4911
        have hw : |(5477143703/10000000000 : ℝ)|=(5477143703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-492086049/5000000000 : ℝ)|^5935 ≤ (3034483509469/50000000000000 : ℝ)^4911
        have hw : |(-492086049/5000000000 : ℝ)|=(492086049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s2_7 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4001760087/10000000000 : ℝ)*x 0 + (938544363/2000000000 : ℝ)*x 1 + (1684924711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4001760087/10000000000 : ℝ)^5935 ≤ (33060987079993/100000000000000 : ℝ)^4911 := by
    have hnat : (4001760087 : ℕ)^5935*100000000000000^4911 ≤ 33060987079993^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4001760087 10000000000 33060987079993 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (938544363/2000000000 : ℝ)^5935 ≤ (20039325840507/50000000000000 : ℝ)^4911 := by
    have hnat : (938544363 : ℕ)^5935*50000000000000^4911 ≤ 20039325840507^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938544363 2000000000 20039325840507 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1684924711/5000000000 : ℝ)^5935 ≤ (13430180612443/50000000000000 : ℝ)^4911 := by
    have hnat : (1684924711 : ℕ)^5935*50000000000000^4911 ≤ 13430180612443^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684924711 5000000000 13430180612443 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4001760087/10000000000 : ℝ), (938544363/2000000000 : ℝ), (1684924711/5000000000 : ℝ)] ![(33060987079993/100000000000000 : ℝ), (20039325840507/50000000000000 : ℝ), (13430180612443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4001760087/10000000000 : ℝ)|^5935 ≤ (33060987079993/100000000000000 : ℝ)^4911
        have hw : |(4001760087/10000000000 : ℝ)|=(4001760087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(938544363/2000000000 : ℝ)|^5935 ≤ (20039325840507/50000000000000 : ℝ)^4911
        have hw : |(938544363/2000000000 : ℝ)|=(938544363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1684924711/5000000000 : ℝ)|^5935 ≤ (13430180612443/50000000000000 : ℝ)^4911
        have hw : |(1684924711/5000000000 : ℝ)|=(1684924711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1760_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4457/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1831/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17783/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4457/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4457/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4457/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4457/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4457/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4457/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4559/50000 : ℝ) ^ (5919/1024 : ℝ) ≤ (97260212791727/100000000000000000000 : ℝ) := by
    have hpowers : (4559/50000 : ℝ)^5919 ≤ (97260212791727/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4559 : ℕ)^5919*100000000000000000000^1024 ≤ 97260212791727^1024*50000^5919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4559 50000 97260212791727 100000000000000000000 5919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4559/50000 : ℝ)) (X := (97260212791727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4457/25000 : ℝ) ^ (5919/1024 : ℝ) ≤ (4689952004108517/100000000000000000000 : ℝ) := by
    have hpowers : (4457/25000 : ℝ)^5919 ≤ (4689952004108517/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4457 : ℕ)^5919*100000000000000000000^1024 ≤ 4689952004108517^1024*25000^5919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4457 25000 4689952004108517 100000000000000000000 5919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4457/25000 : ℝ)) (X := (4689952004108517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000097260212791727/50000000000000000000 : ℝ) ≤ (10000003365243379/10000000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (50000097260212791727/50000000000000000000 : ℝ)^1024 ≤ (10000003365243379/10000000000000000 : ℝ)^5919 := by
      have hnat : (50000097260212791727 : ℕ)^1024*10000000000000000^5919 ≤ 10000003365243379^5919*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000097260212791727 50000000000000000000 10000003365243379 10000000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000003365243379/10000000000000000 : ℝ)) (X := (50000097260212791727/50000000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25001196803054225061/25000000000000000000 : ℝ) ≤ (50000414090917/50000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (25001196803054225061/25000000000000000000 : ℝ)^1024 ≤ (50000414090917/50000000000000 : ℝ)^5919 := by
      have hnat : (25001196803054225061 : ℕ)^1024*50000000000000^5919 ≤ 50000414090917^5919*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001196803054225061 25000000000000000000 50000414090917 50000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50000414090917/50000000000000 : ℝ)) (X := (25001196803054225061/25000000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50004689952004108517/50000000000000000000 : ℝ) ≤ (10000162271123421/10000000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (50004689952004108517/50000000000000000000 : ℝ)^1024 ≤ (10000162271123421/10000000000000000 : ℝ)^5919 := by
      have hnat : (50004689952004108517 : ℕ)^1024*10000000000000000^5919 ≤ 10000162271123421^5919*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004689952004108517 50000000000000000000 10000162271123421 10000000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000162271123421/10000000000000000 : ℝ)) (X := (50004689952004108517/50000000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(97260212791727/100000000000000000000 : ℝ) ≤ ((3349945400286754159/3350000000000000000 : ℝ)+2*(6111764617/67000000000000 : ℝ)*(4559/50000 : ℝ))^(5919/1024 : ℝ) := by
    rw [show (3349945400286754159/3350000000000000000 : ℝ)+2*(6111764617/67000000000000 : ℝ)*(4559/50000 : ℝ)=(10000003365243379/10000000000000000 : ℝ) by norm_num, show 1+2*(97260212791727/100000000000000000000 : ℝ)=(50000097260212791727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4689952004108517/100000000000000000000 : ℝ)+(97260212791727/100000000000000000000 : ℝ) ≤ ((3349945400286754159/3350000000000000000 : ℝ)+(6111764617/67000000000000 : ℝ)*((4457/25000 : ℝ)+(4559/50000 : ℝ)))^(5919/1024 : ℝ) := by
    rw [show (3349945400286754159/3350000000000000000 : ℝ)+(6111764617/67000000000000 : ℝ)*((4457/25000 : ℝ)+(4559/50000 : ℝ))=(50000414090917/50000000000000 : ℝ) by norm_num, show 1+(4689952004108517/100000000000000000000 : ℝ)+(97260212791727/100000000000000000000 : ℝ)=(25001196803054225061/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4689952004108517/100000000000000000000 : ℝ) ≤ ((3349945400286754159/3350000000000000000 : ℝ)+2*(6111764617/67000000000000 : ℝ)*(4457/25000 : ℝ))^(5919/1024 : ℝ) := by
    rw [show (3349945400286754159/3350000000000000000 : ℝ)+2*(6111764617/67000000000000 : ℝ)*(4457/25000 : ℝ)=(10000162271123421/10000000000000000 : ℝ) by norm_num, show 1+2*(4689952004108517/100000000000000000000 : ℝ)=(50004689952004108517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3349945400286754159/3350000000000000000 : ℝ)*(X 1 0+X 2 0)+(6111764617/67000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (4559/50000 : ℝ)) (hi := (4457/25000 : ℝ)) (c := (3349945400286754159/3350000000000000000 : ℝ)) (alpha := (6111764617/67000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3349945400286754159/3350000000000000000 : ℝ)*(X 0 1+X 2 1)+(6111764617/67000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (4559/50000 : ℝ)) (hi := (4457/25000 : ℝ)) (c := (3349945400286754159/3350000000000000000 : ℝ)) (alpha := (6111764617/67000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3349945400286754159/3350000000000000000 : ℝ)*(X 0 2+X 1 2)+(6111764617/67000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (4559/50000 : ℝ)) (hi := (4457/25000 : ℝ)) (c := (3349945400286754159/3350000000000000000 : ℝ)) (alpha := (6111764617/67000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1168613103/10000000000 : ℝ)*X 0 0+(5483896447/10000000000 : ℝ)*X 0 1+(5083718187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2664671613/5000000000 : ℝ)*X 1 0+(-275519539/2000000000 : ℝ)*X 1 1+(5083718191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1332335807/2500000000 : ℝ)*X 2 0+(5083718189/10000000000 : ℝ)*X 2 1+(-688798847/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((100015689/250000000 : ℝ)*X 0 0+(167337761/500000000 : ℝ)*X 0 1+(4715343943/10000000000 : ℝ)*X 0 2+(100015689/250000000 : ℝ)*X 1 0+(167337761/500000000 : ℝ)*X 1 1+(4715343943/10000000000 : ℝ)*X 1 2+(100015689/250000000 : ℝ)*X 2 0+(167337761/500000000 : ℝ)*X 2 1+(4715343943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1168944443/10000000000 : ℝ)*X 0 0+(5090332879/10000000000 : ℝ)*X 0 1+(109542873/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((652948649/1250000000 : ℝ)*X 1 0+(-492086147/5000000000 : ℝ)*X 1 1+(5477143789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5223589417/10000000000 : ℝ)*X 2 0+(5477143703/10000000000 : ℝ)*X 2 1+(-492086049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4001760087/10000000000 : ℝ)*X 0 0+(938544363/2000000000 : ℝ)*X 0 1+(1684924711/5000000000 : ℝ)*X 0 2+(4001760087/10000000000 : ℝ)*X 1 0+(938544363/2000000000 : ℝ)*X 1 1+(1684924711/5000000000 : ℝ)*X 1 2+(4001760087/10000000000 : ℝ)*X 2 0+(938544363/2000000000 : ℝ)*X 2 1+(1684924711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (132650390447347168956440991/10468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (852034827/50000000000000 : ℝ)*(base19) + (1612722959/100000000000000 : ℝ)*(base23) + (12295393/25000000000000 : ℝ)*(lower2) + (30113099/10000000000000 : ℝ)*(upper3) + (14769883/6250000000000 : ℝ)*(upper5) + (100925062011533/6250000000000 : ℝ)*(major0) + (100925062011533/6250000000000 : ℝ)*(major1) + (100925062011533/6250000000000 : ℝ)*(major2) + (1249450032622637/50000000000000 : ℝ)*(sp0) + (39045500417471/1562500000000 : ℝ)*(sp1) + (62472802951621/2500000000000 : ℝ)*(sp2) + (146136700495633/20000000000000 : ℝ)*(sp3) + (3416385631/25000000000000 : ℝ)*(sp4) + (4328733687/100000000000000 : ℝ)*(sp7) + (182671957802963/25000000000000 : ℝ)*(f.failure) + (1249456865393899/50000000000000 : ℝ)*(f.sum) + (4369526607763/1675000000000000000000000000 : ℝ)*base65 + (34590367107703247/20937500000000000000000000000000 : ℝ)*base67 + (21305249746453247/20937500000000000000000000000000 : ℝ)*base69 + (26635686666671753/20937500000000000000000000000000 : ℝ)*base72 + (8724499288513/1675000000000000000000000000 : ℝ)*base73 + (10130033572921753/20937500000000000000000000000000 : ℝ)*base76 + (22054791476671753/20937500000000000000000000000000 : ℝ)*base78 + (112545541630421753/20937500000000000000000000000000 : ℝ)*base80 + (4949167503313/1675000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1306099/312500000000000000000 : ℝ)*base89 + (1306099/312500000000000000000 : ℝ)*base91 + (1306099/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48191196914055244204731/3350000000000000000000000000 : ℝ) := by norm_num
    linear_combination (453703759/25000000000000 : ℝ)*(base19) + (1970230291/100000000000000 : ℝ)*(base23) + (134263611/25000000000000 : ℝ)*(lower1) + (19980937/6250000000000 : ℝ)*(upper3) + (3783707/50000000000000 : ℝ)*(lower4) + (317747169/100000000000000 : ℝ)*(upper5) + (1670578518218777/100000000000000 : ℝ)*(major0) + (1670578518218777/100000000000000 : ℝ)*(major1) + (1670578518218777/100000000000000 : ℝ)*(major2) + (365176139/25000000000000 : ℝ)*(sp2) + (646307431847909/25000000000000 : ℝ)*(sp4) + (2585227912576601/100000000000000 : ℝ)*(sp5) + (258522629645679/10000000000000 : ℝ)*(sp6) + (75592682953151/10000000000000 : ℝ)*(sp7) + (75592682953151/10000000000000 : ℝ)*(f.failure) + (646307431847909/25000000000000 : ℝ)*(f.sum) + (13852741170291/3350000000000000000000000000 : ℝ)*base66 + (1641621389757093543/335000000000000000000000000000000 : ℝ)*base67 + (379640234547093543/335000000000000000000000000000000 : ℝ)*base69 + (4183585621977093543/335000000000000000000000000000000 : ℝ)*base71 + (2161359539191/3350000000000000000000000000 : ℝ)*base74 + (11336438644767906457/335000000000000000000000000000000 : ℝ)*base76 + (41917383032906457/335000000000000000000000000000000 : ℝ)*base78 + (707419517592906457/335000000000000000000000000000000 : ℝ)*base80 + (22974071972191/3350000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (555377/125000000000000000000 : ℝ)*base90 + (555377/125000000000000000000 : ℝ)*base92 + (555377/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1760_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4457/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17783/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1760_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1760_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17783/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1760_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1760_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1760_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17783/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1760_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
