-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1536_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:06:14.724849+00:00
-- url     : https://prove2.me/submissions/ee8ab082-d2b9-421c-b151-0936893432ca

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
theorem support_rectangle_w1536_s6_0 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350224287/10000000000 : ℝ)*x 0 + (1043752119/2000000000 : ℝ)*x 1 + (-388267247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350224287/10000000000 : ℝ)^4569 ≤ (11164780683039/25000000000000 : ℝ)^3545 := by
    have hnat : (5350224287 : ℕ)^4569*25000000000000^3545 ≤ 11164780683039^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350224287 10000000000 11164780683039 25000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043752119/2000000000 : ℝ)^4569 ≤ (2703115462473/6250000000000 : ℝ)^3545 := by
    have hnat : (1043752119 : ℕ)^4569*6250000000000^3545 ≤ 2703115462473^3545*2000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043752119 2000000000 2703115462473 6250000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (388267247/2000000000 : ℝ)^4569 ≤ (6045514928147/50000000000000 : ℝ)^3545 := by
    have hnat : (388267247 : ℕ)^4569*50000000000000^3545 ≤ 6045514928147^3545*2000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388267247 2000000000 6045514928147 50000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350224287/10000000000 : ℝ), (1043752119/2000000000 : ℝ), (-388267247/2000000000 : ℝ)] ![(11164780683039/25000000000000 : ℝ), (2703115462473/6250000000000 : ℝ), (6045514928147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350224287/10000000000 : ℝ)|^4569 ≤ (11164780683039/25000000000000 : ℝ)^3545
        have hw : |(5350224287/10000000000 : ℝ)|=(5350224287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043752119/2000000000 : ℝ)|^4569 ≤ (2703115462473/6250000000000 : ℝ)^3545
        have hw : |(1043752119/2000000000 : ℝ)|=(1043752119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-388267247/2000000000 : ℝ)|^4569 ≤ (6045514928147/50000000000000 : ℝ)^3545
        have hw : |(-388267247/2000000000 : ℝ)|=(388267247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_s6_1 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-458290899/2500000000 : ℝ)*x 0 + (2609926897/5000000000 : ℝ)*x 1 + (1357256543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (458290899/2500000000 : ℝ)^4569 ≤ (5614891161687/50000000000000 : ℝ)^3545 := by
    have hnat : (458290899 : ℕ)^4569*50000000000000^3545 ≤ 5614891161687^3545*2500000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458290899 2500000000 5614891161687 50000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609926897/5000000000 : ℝ)^4569 ≤ (21630762242903/50000000000000 : ℝ)^3545 := by
    have hnat : (2609926897 : ℕ)^4569*50000000000000^3545 ≤ 21630762242903^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609926897 5000000000 21630762242903 50000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357256543/2500000000 : ℝ)^4569 ≤ (45508693179149/100000000000000 : ℝ)^3545 := by
    have hnat : (1357256543 : ℕ)^4569*100000000000000^3545 ≤ 45508693179149^3545*2500000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357256543 2500000000 45508693179149 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-458290899/2500000000 : ℝ), (2609926897/5000000000 : ℝ), (1357256543/2500000000 : ℝ)] ![(5614891161687/50000000000000 : ℝ), (21630762242903/50000000000000 : ℝ), (45508693179149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-458290899/2500000000 : ℝ)|^4569 ≤ (5614891161687/50000000000000 : ℝ)^3545
        have hw : |(-458290899/2500000000 : ℝ)|=(458290899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609926897/5000000000 : ℝ)|^4569 ≤ (21630762242903/50000000000000 : ℝ)^3545
        have hw : |(2609926897/5000000000 : ℝ)|=(2609926897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357256543/2500000000 : ℝ)|^4569 ≤ (45508693179149/100000000000000 : ℝ)^3545
        have hw : |(1357256543/2500000000 : ℝ)|=(1357256543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_s6_2 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294545813/10000000000 : ℝ)*x 0 + (-1731070521/10000000000 : ℝ)*x 1 + (2714513093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294545813/10000000000 : ℝ)^4569 ≤ (44061020296621/100000000000000 : ℝ)^3545 := by
    have hnat : (5294545813 : ℕ)^4569*100000000000000^3545 ≤ 44061020296621^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294545813 10000000000 44061020296621 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1731070521/10000000000 : ℝ)^4569 ≤ (10430286354199/100000000000000 : ℝ)^3545 := by
    have hnat : (1731070521 : ℕ)^4569*100000000000000^3545 ≤ 10430286354199^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1731070521 10000000000 10430286354199 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714513093/5000000000 : ℝ)^4569 ≤ (22754346665201/50000000000000 : ℝ)^3545 := by
    have hnat : (2714513093 : ℕ)^4569*50000000000000^3545 ≤ 22754346665201^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714513093 5000000000 22754346665201 50000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294545813/10000000000 : ℝ), (-1731070521/10000000000 : ℝ), (2714513093/5000000000 : ℝ)] ![(44061020296621/100000000000000 : ℝ), (10430286354199/100000000000000 : ℝ), (22754346665201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294545813/10000000000 : ℝ)|^4569 ≤ (44061020296621/100000000000000 : ℝ)^3545
        have hw : |(5294545813/10000000000 : ℝ)|=(5294545813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1731070521/10000000000 : ℝ)|^4569 ≤ (10430286354199/100000000000000 : ℝ)^3545
        have hw : |(-1731070521/10000000000 : ℝ)|=(1731070521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714513093/5000000000 : ℝ)|^4569 ≤ (22754346665201/50000000000000 : ℝ)^3545
        have hw : |(2714513093/5000000000 : ℝ)|=(2714513093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_s6_3 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529454587/1000000000 : ℝ)*x 0 + (5429026131/10000000000 : ℝ)*x 1 + (-865535259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529454587/1000000000 : ℝ)^4569 ≤ (44061020907993/100000000000000 : ℝ)^3545 := by
    have hnat : (529454587 : ℕ)^4569*100000000000000^3545 ≤ 44061020907993^3545*1000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529454587 1000000000 44061020907993 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429026131/10000000000 : ℝ)^4569 ≤ (711073324003/1562500000000 : ℝ)^3545 := by
    have hnat : (5429026131 : ℕ)^4569*1562500000000^3545 ≤ 711073324003^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429026131 10000000000 711073324003 1562500000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (865535259/5000000000 : ℝ)^4569 ≤ (10430286330901/100000000000000 : ℝ)^3545 := by
    have hnat : (865535259 : ℕ)^4569*100000000000000^3545 ≤ 10430286330901^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865535259 5000000000 10430286330901 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529454587/1000000000 : ℝ), (5429026131/10000000000 : ℝ), (-865535259/5000000000 : ℝ)] ![(44061020907993/100000000000000 : ℝ), (711073324003/1562500000000 : ℝ), (10430286330901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529454587/1000000000 : ℝ)|^4569 ≤ (44061020907993/100000000000000 : ℝ)^3545
        have hw : |(529454587/1000000000 : ℝ)|=(529454587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429026131/10000000000 : ℝ)|^4569 ≤ (711073324003/1562500000000 : ℝ)^3545
        have hw : |(5429026131/10000000000 : ℝ)|=(5429026131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-865535259/5000000000 : ℝ)|^4569 ≤ (10430286330901/100000000000000 : ℝ)^3545
        have hw : |(-865535259/5000000000 : ℝ)|=(865535259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_s6_4 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170351583/400000000 : ℝ)*x 0 + (2252856483/5000000000 : ℝ)*x 1 + (2011682187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170351583/400000000 : ℝ)^4569 ≤ (16640742603231/50000000000000 : ℝ)^3545 := by
    have hnat : (170351583 : ℕ)^4569*50000000000000^3545 ≤ 16640742603231^3545*400000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170351583 400000000 16640742603231 50000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252856483/5000000000 : ℝ)^4569 ≤ (35789077355271/100000000000000 : ℝ)^3545 := by
    have hnat : (2252856483 : ℕ)^4569*100000000000000^3545 ≤ 35789077355271^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252856483 5000000000 35789077355271 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011682187/5000000000 : ℝ)^4569 ≤ (30929437423969/100000000000000 : ℝ)^3545 := by
    have hnat : (2011682187 : ℕ)^4569*100000000000000^3545 ≤ 30929437423969^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011682187 5000000000 30929437423969 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170351583/400000000 : ℝ), (2252856483/5000000000 : ℝ), (2011682187/5000000000 : ℝ)] ![(16640742603231/50000000000000 : ℝ), (35789077355271/100000000000000 : ℝ), (30929437423969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170351583/400000000 : ℝ)|^4569 ≤ (16640742603231/50000000000000 : ℝ)^3545
        have hw : |(170351583/400000000 : ℝ)|=(170351583/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252856483/5000000000 : ℝ)|^4569 ≤ (35789077355271/100000000000000 : ℝ)^3545
        have hw : |(2252856483/5000000000 : ℝ)|=(2252856483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2011682187/5000000000 : ℝ)|^4569 ≤ (30929437423969/100000000000000 : ℝ)^3545
        have hw : |(2011682187/5000000000 : ℝ)|=(2011682187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1536_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165299311/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2201/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2201/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2201/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2201/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2201/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2201/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2201/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2201/20000 : ℝ) ^ (4567/1024 : ℝ) ≤ (1328828872154409/25000000000000000000 : ℝ) := by
    have hpowers : (2201/20000 : ℝ)^4567 ≤ (1328828872154409/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2201 : ℕ)^4567*25000000000000000000^1024 ≤ 1328828872154409^1024*20000^4567 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2201 20000 1328828872154409 25000000000000000000 4567 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2201/20000 : ℝ)) (X := (1328828872154409/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4567 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4567/1024 : ℝ) ≤ (24380108796093553/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4567 ≤ (24380108796093553/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4567*100000000000000000000^1024 ≤ 24380108796093553^1024*20000^4567 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 24380108796093553 100000000000000000000 4567 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (24380108796093553/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4567 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501328828872154409/12500000000000000000 : ℝ) ≤ (10000238347214169/10000000000000000 : ℝ) ^ (4567/1024 : ℝ) := by
    have hpowers : (12501328828872154409/12500000000000000000 : ℝ)^1024 ≤ (10000238347214169/10000000000000000 : ℝ)^4567 := by
      have hnat : (12501328828872154409 : ℕ)^1024*10000000000000000^4567 ≤ 10000238347214169^4567*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501328828872154409 12500000000000000000 10000238347214169 10000000000000000 1024 4567 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000238347214169/10000000000000000 : ℝ)) (X := (12501328828872154409/12500000000000000000 : ℝ)) (by norm_num) 4567 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029695424284711189/100000000000000000000 : ℝ) ≤ (1250083218229949/1250000000000000 : ℝ) ^ (4567/1024 : ℝ) := by
    have hpowers : (100029695424284711189/100000000000000000000 : ℝ)^1024 ≤ (1250083218229949/1250000000000000 : ℝ)^4567 := by
      have hnat : (100029695424284711189 : ℕ)^1024*1250000000000000^4567 ≤ 1250083218229949^4567*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029695424284711189 100000000000000000000 1250083218229949 1250000000000000 1024 4567 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250083218229949/1250000000000000 : ℝ)) (X := (100029695424284711189/100000000000000000000 : ℝ)) (by norm_num) 4567 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024380108796093553/50000000000000000000 : ℝ) ≤ (2000218628893003/2000000000000000 : ℝ) ^ (4567/1024 : ℝ) := by
    have hpowers : (50024380108796093553/50000000000000000000 : ℝ)^1024 ≤ (2000218628893003/2000000000000000 : ℝ)^4567 := by
      have hnat : (50024380108796093553 : ℕ)^1024*2000000000000000^4567 ≤ 2000218628893003^4567*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024380108796093553 50000000000000000000 2000218628893003 2000000000000000 1024 4567 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000218628893003/2000000000000000 : ℝ)) (X := (50024380108796093553/50000000000000000000 : ℝ)) (by norm_num) 4567 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1328828872154409/25000000000000000000 : ℝ) ≤ ((639880867882484527/640000000000000000 : ℝ)+2*(61056946489/64000000000000 : ℝ)*(2201/20000 : ℝ))^(4567/1024 : ℝ) := by
    rw [show (639880867882484527/640000000000000000 : ℝ)+2*(61056946489/64000000000000 : ℝ)*(2201/20000 : ℝ)=(10000238347214169/10000000000000000 : ℝ) by norm_num, show 1+2*(1328828872154409/25000000000000000000 : ℝ)=(12501328828872154409/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24380108796093553/100000000000000000000 : ℝ)+(1328828872154409/25000000000000000000 : ℝ) ≤ ((639880867882484527/640000000000000000 : ℝ)+(61056946489/64000000000000 : ℝ)*((3097/20000 : ℝ)+(2201/20000 : ℝ)))^(4567/1024 : ℝ) := by
    rw [show (639880867882484527/640000000000000000 : ℝ)+(61056946489/64000000000000 : ℝ)*((3097/20000 : ℝ)+(2201/20000 : ℝ))=(1250083218229949/1250000000000000 : ℝ) by norm_num, show 1+(24380108796093553/100000000000000000000 : ℝ)+(1328828872154409/25000000000000000000 : ℝ)=(100029695424284711189/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24380108796093553/100000000000000000000 : ℝ) ≤ ((639880867882484527/640000000000000000 : ℝ)+2*(61056946489/64000000000000 : ℝ)*(3097/20000 : ℝ))^(4567/1024 : ℝ) := by
    rw [show (639880867882484527/640000000000000000 : ℝ)+2*(61056946489/64000000000000 : ℝ)*(3097/20000 : ℝ)=(2000218628893003/2000000000000000 : ℝ) by norm_num, show 1+2*(24380108796093553/100000000000000000000 : ℝ)=(50024380108796093553/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (639880867882484527/640000000000000000 : ℝ)*(X 1 0+X 2 0)+(61056946489/64000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4567/1024 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (639880867882484527/640000000000000000 : ℝ)) (alpha := (61056946489/64000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (639880867882484527/640000000000000000 : ℝ)*(X 0 1+X 2 1)+(61056946489/64000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4567/1024 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (639880867882484527/640000000000000000 : ℝ)) (alpha := (61056946489/64000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (639880867882484527/640000000000000000 : ℝ)*(X 0 2+X 1 2)+(61056946489/64000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4567/1024 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (639880867882484527/640000000000000000 : ℝ)) (alpha := (61056946489/64000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5350224287/10000000000 : ℝ)*X 2 0+(1043752119/2000000000 : ℝ)*X 2 1+(-388267247/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-458290899/2500000000 : ℝ)*X 0 0+(2609926897/5000000000 : ℝ)*X 0 1+(1357256543/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294545813/10000000000 : ℝ)*X 1 0+(-1731070521/10000000000 : ℝ)*X 1 1+(2714513093/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((529454587/1000000000 : ℝ)*X 2 0+(5429026131/10000000000 : ℝ)*X 2 1+(-865535259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((170351583/400000000 : ℝ)*X 0 0+(2252856483/5000000000 : ℝ)*X 0 1+(2011682187/5000000000 : ℝ)*X 0 2+(170351583/400000000 : ℝ)*X 1 0+(2252856483/5000000000 : ℝ)*X 1 1+(2011682187/5000000000 : ℝ)*X 1 2+(170351583/400000000 : ℝ)*X 2 0+(2252856483/5000000000 : ℝ)*X 2 1+(2011682187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140267055831952020298177617/32000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (197696767/25000000000000 : ℝ)*(base19) + (224029317/25000000000000 : ℝ)*(base23) + (267277011/100000000000000 : ℝ)*(lower1) + (20176543/20000000000000 : ℝ)*(upper3) + (23915527/100000000000000 : ℝ)*(lower4) + (105770283/100000000000000 : ℝ)*(upper5) + (3426958586366443/100000000000000 : ℝ)*(major0) + (3426958586366443/100000000000000 : ℝ)*(major1) + (3426958586366443/100000000000000 : ℝ)*(major2) + (165300997/20000000000000 : ℝ)*(sp0) + (4780733196855457/100000000000000 : ℝ)*(sp1) + (4780732406068389/100000000000000 : ℝ)*(sp2) + (956146294846641/20000000000000 : ℝ)*(sp3) + (1036591914882949/50000000000000 : ℝ)*(sp4) + (1036591914882949/50000000000000 : ℝ)*(f.failure) + (4780733196855457/100000000000000 : ℝ)*(f.sum) + (926172339027/3200000000000000000000000000 : ℝ)*base65 + (505921833921797461/64000000000000000000000000000000 : ℝ)*base67 + (1054561601797461/64000000000000000000000000000000 : ℝ)*base69 + (4050444968062202539/64000000000000000000000000000000 : ℝ)*base72 + (7298003311827/3200000000000000000000000000 : ℝ)*base73 + (958890481601797461/64000000000000000000000000000000 : ℝ)*base75 + (29453989505797461/64000000000000000000000000000000 : ℝ)*base77 + (411255258686202539/64000000000000000000000000000000 : ℝ)*base80 + (15307080470227/3200000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (34651861/5000000000000000000000 : ℝ)*base90 + (34651861/5000000000000000000000 : ℝ)*base92 + (34651861/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1536_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165299311/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1536_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1536_box_0 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-811852401/5000000000 : ℝ)*x 0 + (5400242599/10000000000 : ℝ)*x 1 + (2700121061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (811852401/5000000000 : ℝ)^4569 ≤ (4802043508943/50000000000000 : ℝ)^3545 := by
    have hnat : (811852401 : ℕ)^4569*50000000000000^3545 ≤ 4802043508943^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811852401 5000000000 4802043508943 50000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400242599/10000000000 : ℝ)^4569 ≤ (706218110207/1562500000000 : ℝ)^3545 := by
    have hnat : (5400242599 : ℕ)^4569*1562500000000^3545 ≤ 706218110207^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400242599 10000000000 706218110207 1562500000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700121061/5000000000 : ℝ)^4569 ≤ (45197953907733/100000000000000 : ℝ)^3545 := by
    have hnat : (2700121061 : ℕ)^4569*100000000000000^3545 ≤ 45197953907733^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700121061 5000000000 45197953907733 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-811852401/5000000000 : ℝ), (5400242599/10000000000 : ℝ), (2700121061/5000000000 : ℝ)] ![(4802043508943/50000000000000 : ℝ), (706218110207/1562500000000 : ℝ), (45197953907733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-811852401/5000000000 : ℝ)|^4569 ≤ (4802043508943/50000000000000 : ℝ)^3545
        have hw : |(-811852401/5000000000 : ℝ)|=(811852401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400242599/10000000000 : ℝ)|^4569 ≤ (706218110207/1562500000000 : ℝ)^3545
        have hw : |(5400242599/10000000000 : ℝ)|=(5400242599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700121061/5000000000 : ℝ)|^4569 ≤ (45197953907733/100000000000000 : ℝ)^3545
        have hw : |(2700121061/5000000000 : ℝ)|=(2700121061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_1 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271017837/10000000000 : ℝ)*x 0 + (-901564443/5000000000 : ℝ)*x 1 + (5400243189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271017837/10000000000 : ℝ)^4569 ≤ (5476103181407/12500000000000 : ℝ)^3545 := by
    have hnat : (5271017837 : ℕ)^4569*12500000000000^3545 ≤ 5476103181407^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271017837 10000000000 5476103181407 12500000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901564443/5000000000 : ℝ)^4569 ≤ (10993209124213/100000000000000 : ℝ)^3545 := by
    have hnat : (901564443 : ℕ)^4569*100000000000000^3545 ≤ 10993209124213^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901564443 5000000000 10993209124213 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400243189/10000000000 : ℝ)^4569 ≤ (45197965417721/100000000000000 : ℝ)^3545 := by
    have hnat : (5400243189 : ℕ)^4569*100000000000000^3545 ≤ 45197965417721^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400243189 10000000000 45197965417721 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271017837/10000000000 : ℝ), (-901564443/5000000000 : ℝ), (5400243189/10000000000 : ℝ)] ![(5476103181407/12500000000000 : ℝ), (10993209124213/100000000000000 : ℝ), (45197965417721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271017837/10000000000 : ℝ)|^4569 ≤ (5476103181407/12500000000000 : ℝ)^3545
        have hw : |(5271017837/10000000000 : ℝ)|=(5271017837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-901564443/5000000000 : ℝ)|^4569 ≤ (10993209124213/100000000000000 : ℝ)^3545
        have hw : |(-901564443/5000000000 : ℝ)|=(901564443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400243189/10000000000 : ℝ)|^4569 ≤ (45197965417721/100000000000000 : ℝ)^3545
        have hw : |(5400243189/10000000000 : ℝ)|=(5400243189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_2 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271018513/10000000000 : ℝ)*x 0 + (675030291/1250000000 : ℝ)*x 1 + (-901564573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271018513/10000000000 : ℝ)^4569 ≤ (2738052043287/6250000000000 : ℝ)^3545 := by
    have hnat : (5271018513 : ℕ)^4569*6250000000000^3545 ≤ 2738052043287^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271018513 10000000000 2738052043287 6250000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675030291/1250000000 : ℝ)^4569 ≤ (9039591225981/20000000000000 : ℝ)^3545 := by
    have hnat : (675030291 : ℕ)^4569*20000000000000^3545 ≤ 9039591225981^3545*1250000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675030291 1250000000 9039591225981 20000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901564573/5000000000 : ℝ)^4569 ≤ (10993211167249/100000000000000 : ℝ)^3545 := by
    have hnat : (901564573 : ℕ)^4569*100000000000000^3545 ≤ 10993211167249^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901564573 5000000000 10993211167249 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271018513/10000000000 : ℝ), (675030291/1250000000 : ℝ), (-901564573/5000000000 : ℝ)] ![(2738052043287/6250000000000 : ℝ), (9039591225981/20000000000000 : ℝ), (10993211167249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271018513/10000000000 : ℝ)|^4569 ≤ (2738052043287/6250000000000 : ℝ)^3545
        have hw : |(5271018513/10000000000 : ℝ)|=(5271018513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675030291/1250000000 : ℝ)|^4569 ≤ (9039591225981/20000000000000 : ℝ)^3545
        have hw : |(675030291/1250000000 : ℝ)|=(675030291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-901564573/5000000000 : ℝ)|^4569 ≤ (10993211167249/100000000000000 : ℝ)^3545
        have hw : |(-901564573/5000000000 : ℝ)|=(901564573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_3 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4460745109/10000000000 : ℝ)*x 0 + (832909211/2000000000 : ℝ)*x 1 + (4164547057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4460745109/10000000000 : ℝ)^4569 ≤ (35329386202003/100000000000000 : ℝ)^3545 := by
    have hnat : (4460745109 : ℕ)^4569*100000000000000^3545 ≤ 35329386202003^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460745109 10000000000 35329386202003 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (832909211/2000000000 : ℝ)^4569 ≤ (32335301877737/100000000000000 : ℝ)^3545 := by
    have hnat : (832909211 : ℕ)^4569*100000000000000^3545 ≤ 32335301877737^3545*2000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832909211 2000000000 32335301877737 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4164547057/10000000000 : ℝ)^4569 ≤ (8083827976247/25000000000000 : ℝ)^3545 := by
    have hnat : (4164547057 : ℕ)^4569*25000000000000^3545 ≤ 8083827976247^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164547057 10000000000 8083827976247 25000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4460745109/10000000000 : ℝ), (832909211/2000000000 : ℝ), (4164547057/10000000000 : ℝ)] ![(35329386202003/100000000000000 : ℝ), (32335301877737/100000000000000 : ℝ), (8083827976247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4460745109/10000000000 : ℝ)|^4569 ≤ (35329386202003/100000000000000 : ℝ)^3545
        have hw : |(4460745109/10000000000 : ℝ)|=(4460745109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(832909211/2000000000 : ℝ)|^4569 ≤ (32335301877737/100000000000000 : ℝ)^3545
        have hw : |(832909211/2000000000 : ℝ)|=(832909211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4164547057/10000000000 : ℝ)|^4569 ≤ (8083827976247/25000000000000 : ℝ)^3545
        have hw : |(4164547057/10000000000 : ℝ)|=(4164547057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_4 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2047989281/10000000000 : ℝ)*x 0 + (655540213/1250000000 : ℝ)*x 1 + (2622160929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2047989281/10000000000 : ℝ)^4569 ≤ (12953868462731/100000000000000 : ℝ)^3545 := by
    have hnat : (2047989281 : ℕ)^4569*100000000000000^3545 ≤ 12953868462731^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047989281 10000000000 12953868462731 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655540213/1250000000 : ℝ)^4569 ≤ (5440383117081/12500000000000 : ℝ)^3545 := by
    have hnat : (655540213 : ℕ)^4569*12500000000000^3545 ≤ 5440383117081^3545*1250000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655540213 1250000000 5440383117081 12500000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622160929/5000000000 : ℝ)^4569 ≤ (10880766645971/25000000000000 : ℝ)^3545 := by
    have hnat : (2622160929 : ℕ)^4569*25000000000000^3545 ≤ 10880766645971^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622160929 5000000000 10880766645971 25000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2047989281/10000000000 : ℝ), (655540213/1250000000 : ℝ), (2622160929/5000000000 : ℝ)] ![(12953868462731/100000000000000 : ℝ), (5440383117081/12500000000000 : ℝ), (10880766645971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2047989281/10000000000 : ℝ)|^4569 ≤ (12953868462731/100000000000000 : ℝ)^3545
        have hw : |(-2047989281/10000000000 : ℝ)|=(2047989281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655540213/1250000000 : ℝ)|^4569 ≤ (5440383117081/12500000000000 : ℝ)^3545
        have hw : |(655540213/1250000000 : ℝ)|=(655540213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622160929/5000000000 : ℝ)|^4569 ≤ (10880766645971/25000000000000 : ℝ)^3545
        have hw : |(2622160929/5000000000 : ℝ)|=(2622160929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_5 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379374863/10000000000 : ℝ)*x 0 + (-93389751/500000000 : ℝ)*x 1 + (26221609/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379374863/10000000000 : ℝ)^4569 ≤ (44972979456367/100000000000000 : ℝ)^3545 := by
    have hnat : (5379374863 : ℕ)^4569*100000000000000^3545 ≤ 44972979456367^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379374863 10000000000 44972979456367 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93389751/500000000 : ℝ)^4569 ≤ (11503954568217/100000000000000 : ℝ)^3545 := by
    have hnat : (93389751 : ℕ)^4569*100000000000000^3545 ≤ 11503954568217^3545*500000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93389751 500000000 11503954568217 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26221609/50000000 : ℝ)^4569 ≤ (5440383245437/12500000000000 : ℝ)^3545 := by
    have hnat : (26221609 : ℕ)^4569*12500000000000^3545 ≤ 5440383245437^3545*50000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26221609 50000000 5440383245437 12500000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379374863/10000000000 : ℝ), (-93389751/500000000 : ℝ), (26221609/50000000 : ℝ)] ![(44972979456367/100000000000000 : ℝ), (11503954568217/100000000000000 : ℝ), (5440383245437/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379374863/10000000000 : ℝ)|^4569 ≤ (44972979456367/100000000000000 : ℝ)^3545
        have hw : |(5379374863/10000000000 : ℝ)|=(5379374863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93389751/500000000 : ℝ)|^4569 ≤ (11503954568217/100000000000000 : ℝ)^3545
        have hw : |(-93389751/500000000 : ℝ)|=(93389751/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26221609/50000000 : ℝ)|^4569 ≤ (5440383245437/12500000000000 : ℝ)^3545
        have hw : |(26221609/50000000 : ℝ)|=(26221609/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_6 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537937473/1000000000 : ℝ)*x 0 + (2622160857/5000000000 : ℝ)*x 1 + (-1867795317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537937473/1000000000 : ℝ)^4569 ≤ (44972978023267/100000000000000 : ℝ)^3545 := by
    have hnat : (537937473 : ℕ)^4569*100000000000000^3545 ≤ 44972978023267^3545*1000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537937473 1000000000 44972978023267 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622160857/5000000000 : ℝ)^4569 ≤ (43523065043611/100000000000000 : ℝ)^3545 := by
    have hnat : (2622160857 : ℕ)^4569*100000000000000^3545 ≤ 43523065043611^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622160857 5000000000 43523065043611 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1867795317/10000000000 : ℝ)^4569 ≤ (11503956925867/100000000000000 : ℝ)^3545 := by
    have hnat : (1867795317 : ℕ)^4569*100000000000000^3545 ≤ 11503956925867^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867795317 10000000000 11503956925867 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537937473/1000000000 : ℝ), (2622160857/5000000000 : ℝ), (-1867795317/10000000000 : ℝ)] ![(44972978023267/100000000000000 : ℝ), (43523065043611/100000000000000 : ℝ), (11503956925867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537937473/1000000000 : ℝ)|^4569 ≤ (44972978023267/100000000000000 : ℝ)^3545
        have hw : |(537937473/1000000000 : ℝ)|=(537937473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622160857/5000000000 : ℝ)|^4569 ≤ (43523065043611/100000000000000 : ℝ)^3545
        have hw : |(2622160857/5000000000 : ℝ)|=(2622160857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1867795317/10000000000 : ℝ)|^4569 ≤ (11503956925867/100000000000000 : ℝ)^3545
        have hw : |(-1867795317/10000000000 : ℝ)|=(1867795317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_7 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (40541709/100000000 : ℝ)*x 0 + (873540543/2000000000 : ℝ)*x 1 + (4367702009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40541709/100000000 : ℝ)^4569 ≤ (1952187908093/6250000000000 : ℝ)^3545 := by
    have hnat : (40541709 : ℕ)^4569*6250000000000^3545 ≤ 1952187908093^3545*100000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40541709 100000000 1952187908093 6250000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873540543/2000000000 : ℝ)^4569 ≤ (34382500311679/100000000000000 : ℝ)^3545 := by
    have hnat : (873540543 : ℕ)^4569*100000000000000^3545 ≤ 34382500311679^3545*2000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873540543 2000000000 34382500311679 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4367702009/10000000000 : ℝ)^4569 ≤ (6876498629739/20000000000000 : ℝ)^3545 := by
    have hnat : (4367702009 : ℕ)^4569*20000000000000^3545 ≤ 6876498629739^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367702009 10000000000 6876498629739 20000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(40541709/100000000 : ℝ), (873540543/2000000000 : ℝ), (4367702009/10000000000 : ℝ)] ![(1952187908093/6250000000000 : ℝ), (34382500311679/100000000000000 : ℝ), (6876498629739/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(40541709/100000000 : ℝ)|^4569 ≤ (1952187908093/6250000000000 : ℝ)^3545
        have hw : |(40541709/100000000 : ℝ)|=(40541709/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(873540543/2000000000 : ℝ)|^4569 ≤ (34382500311679/100000000000000 : ℝ)^3545
        have hw : |(873540543/2000000000 : ℝ)|=(873540543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4367702009/10000000000 : ℝ)|^4569 ≤ (6876498629739/20000000000000 : ℝ)^3545
        have hw : |(4367702009/10000000000 : ℝ)|=(4367702009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_8 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-979103919/5000000000 : ℝ)*x 0 + (256741533/500000000 : ℝ)*x 1 + (5420621111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (979103919/5000000000 : ℝ)^4569 ≤ (2445326456599/20000000000000 : ℝ)^3545 := by
    have hnat : (979103919 : ℕ)^4569*20000000000000^3545 ≤ 2445326456599^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979103919 5000000000 2445326456599 20000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256741533/500000000 : ℝ)^4569 ≤ (42355460980067/100000000000000 : ℝ)^3545 := by
    have hnat : (256741533 : ℕ)^4569*100000000000000^3545 ≤ 42355460980067^3545*500000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256741533 500000000 42355460980067 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420621111/10000000000 : ℝ)^4569 ≤ (11354476680813/25000000000000 : ℝ)^3545 := by
    have hnat : (5420621111 : ℕ)^4569*25000000000000^3545 ≤ 11354476680813^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420621111 10000000000 11354476680813 25000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-979103919/5000000000 : ℝ), (256741533/500000000 : ℝ), (5420621111/10000000000 : ℝ)] ![(2445326456599/20000000000000 : ℝ), (42355460980067/100000000000000 : ℝ), (11354476680813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-979103919/5000000000 : ℝ)|^4569 ≤ (2445326456599/20000000000000 : ℝ)^3545
        have hw : |(-979103919/5000000000 : ℝ)|=(979103919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256741533/500000000 : ℝ)|^4569 ≤ (42355460980067/100000000000000 : ℝ)^3545
        have hw : |(256741533/500000000 : ℝ)|=(256741533/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420621111/10000000000 : ℝ)|^4569 ≤ (11354476680813/25000000000000 : ℝ)^3545
        have hw : |(5420621111/10000000000 : ℝ)|=(5420621111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_9 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628425593/5000000000 : ℝ)*x 0 + (-1794436079/10000000000 : ℝ)*x 1 + (271031113/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628425593/5000000000 : ℝ)^4569 ≤ (2728570669601/6250000000000 : ℝ)^3545 := by
    have hnat : (2628425593 : ℕ)^4569*6250000000000^3545 ≤ 2728570669601^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628425593 5000000000 2728570669601 6250000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1794436079/10000000000 : ℝ)^4569 ≤ (5462475069281/50000000000000 : ℝ)^3545 := by
    have hnat : (1794436079 : ℕ)^4569*50000000000000^3545 ≤ 5462475069281^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794436079 10000000000 5462475069281 50000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271031113/500000000 : ℝ)^4569 ≤ (5677239891411/12500000000000 : ℝ)^3545 := by
    have hnat : (271031113 : ℕ)^4569*12500000000000^3545 ≤ 5677239891411^3545*500000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271031113 500000000 5677239891411 12500000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628425593/5000000000 : ℝ), (-1794436079/10000000000 : ℝ), (271031113/500000000 : ℝ)] ![(2728570669601/6250000000000 : ℝ), (5462475069281/50000000000000 : ℝ), (5677239891411/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628425593/5000000000 : ℝ)|^4569 ≤ (2728570669601/6250000000000 : ℝ)^3545
        have hw : |(2628425593/5000000000 : ℝ)|=(2628425593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1794436079/10000000000 : ℝ)|^4569 ≤ (5462475069281/50000000000000 : ℝ)^3545
        have hw : |(-1794436079/10000000000 : ℝ)|=(1794436079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271031113/500000000 : ℝ)|^4569 ≤ (5677239891411/12500000000000 : ℝ)^3545
        have hw : |(271031113/500000000 : ℝ)|=(271031113/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_10 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314212479/2500000000 : ℝ)*x 0 + (108412459/200000000 : ℝ)*x 1 + (-1794436861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314212479/2500000000 : ℝ)^4569 ≤ (21828558559951/50000000000000 : ℝ)^3545 := by
    have hnat : (1314212479 : ℕ)^4569*50000000000000^3545 ≤ 21828558559951^3545*2500000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314212479 2500000000 21828558559951 50000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108412459/200000000 : ℝ)^4569 ≤ (45417926582589/100000000000000 : ℝ)^3545 := by
    have hnat : (108412459 : ℕ)^4569*100000000000000^3545 ≤ 45417926582589^3545*200000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108412459 200000000 45417926582589 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1794436861/10000000000 : ℝ)^4569 ≤ (5462478137407/50000000000000 : ℝ)^3545 := by
    have hnat : (1794436861 : ℕ)^4569*50000000000000^3545 ≤ 5462478137407^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794436861 10000000000 5462478137407 50000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314212479/2500000000 : ℝ), (108412459/200000000 : ℝ), (-1794436861/10000000000 : ℝ)] ![(21828558559951/50000000000000 : ℝ), (45417926582589/100000000000000 : ℝ), (5462478137407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314212479/2500000000 : ℝ)|^4569 ≤ (21828558559951/50000000000000 : ℝ)^3545
        have hw : |(1314212479/2500000000 : ℝ)|=(1314212479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108412459/200000000 : ℝ)|^4569 ≤ (45417926582589/100000000000000 : ℝ)^3545
        have hw : |(108412459/200000000 : ℝ)|=(108412459/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1794436861/10000000000 : ℝ)|^4569 ≤ (5462478137407/50000000000000 : ℝ)^3545
        have hw : |(-1794436861/10000000000 : ℝ)|=(1794436861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_11 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4512738451/10000000000 : ℝ)*x 0 + (51724503/125000000 : ℝ)*x 1 + (2068979587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4512738451/10000000000 : ℝ)^4569 ≤ (35861016615177/100000000000000 : ℝ)^3545 := by
    have hnat : (4512738451 : ℕ)^4569*100000000000000^3545 ≤ 35861016615177^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512738451 10000000000 35861016615177 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51724503/125000000 : ℝ)^4569 ≤ (6413899401957/20000000000000 : ℝ)^3545 := by
    have hnat : (51724503 : ℕ)^4569*20000000000000^3545 ≤ 6413899401957^3545*125000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51724503 125000000 6413899401957 20000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068979587/5000000000 : ℝ)^4569 ≤ (32069486361787/100000000000000 : ℝ)^3545 := by
    have hnat : (2068979587 : ℕ)^4569*100000000000000^3545 ≤ 32069486361787^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068979587 5000000000 32069486361787 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4512738451/10000000000 : ℝ), (51724503/125000000 : ℝ), (2068979587/5000000000 : ℝ)] ![(35861016615177/100000000000000 : ℝ), (6413899401957/20000000000000 : ℝ), (32069486361787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4512738451/10000000000 : ℝ)|^4569 ≤ (35861016615177/100000000000000 : ℝ)^3545
        have hw : |(4512738451/10000000000 : ℝ)|=(4512738451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51724503/125000000 : ℝ)|^4569 ≤ (6413899401957/20000000000000 : ℝ)^3545
        have hw : |(51724503/125000000 : ℝ)|=(51724503/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2068979587/5000000000 : ℝ)|^4569 ≤ (32069486361787/100000000000000 : ℝ)^3545
        have hw : |(2068979587/5000000000 : ℝ)|=(2068979587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_12 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-856655207/5000000000 : ℝ)*x 0 + (688286709/1250000000 : ℝ)*x 1 + (5229280207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856655207/5000000000 : ℝ)^4569 ≤ (10292569724461/100000000000000 : ℝ)^3545 := by
    have hnat : (856655207 : ℕ)^4569*100000000000000^3545 ≤ 10292569724461^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856655207 5000000000 10292569724461 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688286709/1250000000 : ℝ)^4569 ≤ (9269037509007/20000000000000 : ℝ)^3545 := by
    have hnat : (688286709 : ℕ)^4569*20000000000000^3545 ≤ 9269037509007^3545*1250000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688286709 1250000000 9269037509007 20000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229280207/10000000000 : ℝ)^4569 ≤ (43362242712919/100000000000000 : ℝ)^3545 := by
    have hnat : (5229280207 : ℕ)^4569*100000000000000^3545 ≤ 43362242712919^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229280207 10000000000 43362242712919 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-856655207/5000000000 : ℝ), (688286709/1250000000 : ℝ), (5229280207/10000000000 : ℝ)] ![(10292569724461/100000000000000 : ℝ), (9269037509007/20000000000000 : ℝ), (43362242712919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-856655207/5000000000 : ℝ)|^4569 ≤ (10292569724461/100000000000000 : ℝ)^3545
        have hw : |(-856655207/5000000000 : ℝ)|=(856655207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688286709/1250000000 : ℝ)|^4569 ≤ (9269037509007/20000000000000 : ℝ)^3545
        have hw : |(688286709/1250000000 : ℝ)|=(688286709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229280207/10000000000 : ℝ)|^4569 ≤ (43362242712919/100000000000000 : ℝ)^3545
        have hw : |(5229280207/10000000000 : ℝ)|=(5229280207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_13 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389828131/10000000000 : ℝ)*x 0 + (-1873858417/10000000000 : ℝ)*x 1 + (5229280267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389828131/10000000000 : ℝ)^4569 ≤ (1803425878369/4000000000000 : ℝ)^3545 := by
    have hnat : (5389828131 : ℕ)^4569*4000000000000^3545 ≤ 1803425878369^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389828131 10000000000 1803425878369 4000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1873858417/10000000000 : ℝ)^4569 ≤ (11552109667853/100000000000000 : ℝ)^3545 := by
    have hnat : (1873858417 : ℕ)^4569*100000000000000^3545 ≤ 11552109667853^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873858417 10000000000 11552109667853 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229280267/10000000000 : ℝ)^4569 ≤ (43362243354167/100000000000000 : ℝ)^3545 := by
    have hnat : (5229280267 : ℕ)^4569*100000000000000^3545 ≤ 43362243354167^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229280267 10000000000 43362243354167 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389828131/10000000000 : ℝ), (-1873858417/10000000000 : ℝ), (5229280267/10000000000 : ℝ)] ![(1803425878369/4000000000000 : ℝ), (11552109667853/100000000000000 : ℝ), (43362243354167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389828131/10000000000 : ℝ)|^4569 ≤ (1803425878369/4000000000000 : ℝ)^3545
        have hw : |(5389828131/10000000000 : ℝ)|=(5389828131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1873858417/10000000000 : ℝ)|^4569 ≤ (11552109667853/100000000000000 : ℝ)^3545
        have hw : |(-1873858417/10000000000 : ℝ)|=(1873858417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229280267/10000000000 : ℝ)|^4569 ≤ (43362243354167/100000000000000 : ℝ)^3545
        have hw : |(5229280267/10000000000 : ℝ)|=(5229280267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_14 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21559313/40000000 : ℝ)*x 0 + (326830011/625000000 : ℝ)*x 1 + (-1873858379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21559313/40000000 : ℝ)^4569 ≤ (2817853015137/6250000000000 : ℝ)^3545 := by
    have hnat : (21559313 : ℕ)^4569*6250000000000^3545 ≤ 2817853015137^3545*40000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21559313 40000000 2817853015137 6250000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326830011/625000000 : ℝ)^4569 ≤ (43362242381607/100000000000000 : ℝ)^3545 := by
    have hnat : (326830011 : ℕ)^4569*100000000000000^3545 ≤ 43362242381607^3545*625000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326830011 625000000 43362242381607 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873858379/10000000000 : ℝ)^4569 ≤ (11552109365919/100000000000000 : ℝ)^3545 := by
    have hnat : (1873858379 : ℕ)^4569*100000000000000^3545 ≤ 11552109365919^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873858379 10000000000 11552109365919 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21559313/40000000 : ℝ), (326830011/625000000 : ℝ), (-1873858379/10000000000 : ℝ)] ![(2817853015137/6250000000000 : ℝ), (43362242381607/100000000000000 : ℝ), (11552109365919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21559313/40000000 : ℝ)|^4569 ≤ (2817853015137/6250000000000 : ℝ)^3545
        have hw : |(21559313/40000000 : ℝ)|=(21559313/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326830011/625000000 : ℝ)|^4569 ≤ (43362242381607/100000000000000 : ℝ)^3545
        have hw : |(326830011/625000000 : ℝ)|=(326830011/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1873858379/10000000000 : ℝ)|^4569 ≤ (11552109365919/100000000000000 : ℝ)^3545
        have hw : |(-1873858379/10000000000 : ℝ)|=(1873858379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1536_box_15 (p : ℝ) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2007043409/5000000000 : ℝ)*x 0 + (4387277067/10000000000 : ℝ)*x 1 + (877455397/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2007043409/5000000000 : ℝ)^4569 ≤ (30837545696379/100000000000000 : ℝ)^3545 := by
    have hnat : (2007043409 : ℕ)^4569*100000000000000^3545 ≤ 30837545696379^3545*5000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007043409 5000000000 30837545696379 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4387277067/10000000000 : ℝ)^4569 ≤ (34581227558531/100000000000000 : ℝ)^3545 := by
    have hnat : (4387277067 : ℕ)^4569*100000000000000^3545 ≤ 34581227558531^3545*10000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387277067 10000000000 34581227558531 100000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (877455397/2000000000 : ℝ)^4569 ≤ (17290613362747/50000000000000 : ℝ)^3545 := by
    have hnat : (877455397 : ℕ)^4569*50000000000000^3545 ≤ 17290613362747^3545*2000000000^4569 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877455397 2000000000 17290613362747 50000000000000 4569 3545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4569/1024 : ℝ)) 4569 3545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2007043409/5000000000 : ℝ), (4387277067/10000000000 : ℝ), (877455397/2000000000 : ℝ)] ![(30837545696379/100000000000000 : ℝ), (34581227558531/100000000000000 : ℝ), (17290613362747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2007043409/5000000000 : ℝ)|^4569 ≤ (30837545696379/100000000000000 : ℝ)^3545
        have hw : |(2007043409/5000000000 : ℝ)|=(2007043409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4387277067/10000000000 : ℝ)|^4569 ≤ (34581227558531/100000000000000 : ℝ)^3545
        have hw : |(4387277067/10000000000 : ℝ)|=(4387277067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(877455397/2000000000 : ℝ)|^4569 ≤ (17290613362747/50000000000000 : ℝ)^3545
        have hw : |(877455397/2000000000 : ℝ)|=(877455397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1536_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165299311/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63773/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58741/100000 : ℝ) ∧ (80573/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17231/20000 : ℝ) := by
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
  have lower0 : (2201/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2201/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2201/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2201/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2201/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2201/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2201/20000 : ℝ) ^ (4567/1024 : ℝ) ≤ (1328828872154409/25000000000000000000 : ℝ) := by
    have hpowers : (2201/20000 : ℝ)^4567 ≤ (1328828872154409/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2201 : ℕ)^4567*25000000000000000000^1024 ≤ 1328828872154409^1024*20000^4567 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2201 20000 1328828872154409 25000000000000000000 4567 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2201/20000 : ℝ)) (X := (1328828872154409/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4567 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4567/1024 : ℝ) ≤ (24373087666887717/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4567 ≤ (24373087666887717/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4567*100000000000000000000^1024 ≤ 24373087666887717^1024*25000^4567 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 24373087666887717 100000000000000000000 4567 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (24373087666887717/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4567 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501328828872154409/12500000000000000000 : ℝ) ≤ (10000238347214169/10000000000000000 : ℝ) ^ (4567/1024 : ℝ) := by
    have hpowers : (12501328828872154409/12500000000000000000 : ℝ)^1024 ≤ (10000238347214169/10000000000000000 : ℝ)^4567 := by
      have hnat : (12501328828872154409 : ℕ)^1024*10000000000000000^4567 ≤ 10000238347214169^4567*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501328828872154409 12500000000000000000 10000238347214169 10000000000000000 1024 4567 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000238347214169/10000000000000000 : ℝ)) (X := (12501328828872154409/12500000000000000000 : ℝ)) (by norm_num) 4567 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029688403155505353/100000000000000000000 : ℝ) ≤ (2500166397112511/2500000000000000 : ℝ) ^ (4567/1024 : ℝ) := by
    have hpowers : (100029688403155505353/100000000000000000000 : ℝ)^1024 ≤ (2500166397112511/2500000000000000 : ℝ)^4567 := by
      have hnat : (100029688403155505353 : ℕ)^1024*2500000000000000^4567 ≤ 2500166397112511^4567*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029688403155505353 100000000000000000000 2500166397112511 2500000000000000 1024 4567 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500166397112511/2500000000000000 : ℝ)) (X := (100029688403155505353/100000000000000000000 : ℝ)) (by norm_num) 4567 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024373087666887717/50000000000000000000 : ℝ) ≤ (10001092829685919/10000000000000000 : ℝ) ^ (4567/1024 : ℝ) := by
    have hpowers : (50024373087666887717/50000000000000000000 : ℝ)^1024 ≤ (10001092829685919/10000000000000000 : ℝ)^4567 := by
      have hnat : (50024373087666887717 : ℕ)^1024*10000000000000000^4567 ≤ 10001092829685919^4567*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024373087666887717 50000000000000000000 10001092829685919 10000000000000000 1024 4567 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001092829685919/10000000000000000 : ℝ)) (X := (50024373087666887717/50000000000000000000 : ℝ)) (by norm_num) 4567 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1328828872154409/25000000000000000000 : ℝ) ≤ ((44781663977570654201/44790000000000000000 : ℝ)+2*(3417929887/3583200000000 : ℝ)*(2201/20000 : ℝ))^(4567/1024 : ℝ) := by
    rw [show (44781663977570654201/44790000000000000000 : ℝ)+2*(3417929887/3583200000000 : ℝ)*(2201/20000 : ℝ)=(10000238347214169/10000000000000000 : ℝ) by norm_num, show 1+2*(1328828872154409/25000000000000000000 : ℝ)=(12501328828872154409/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24373087666887717/100000000000000000000 : ℝ)+(1328828872154409/25000000000000000000 : ℝ) ≤ ((44781663977570654201/44790000000000000000 : ℝ)+(3417929887/3583200000000 : ℝ)*((3871/25000 : ℝ)+(2201/20000 : ℝ)))^(4567/1024 : ℝ) := by
    rw [show (44781663977570654201/44790000000000000000 : ℝ)+(3417929887/3583200000000 : ℝ)*((3871/25000 : ℝ)+(2201/20000 : ℝ))=(2500166397112511/2500000000000000 : ℝ) by norm_num, show 1+(24373087666887717/100000000000000000000 : ℝ)+(1328828872154409/25000000000000000000 : ℝ)=(100029688403155505353/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24373087666887717/100000000000000000000 : ℝ) ≤ ((44781663977570654201/44790000000000000000 : ℝ)+2*(3417929887/3583200000000 : ℝ)*(3871/25000 : ℝ))^(4567/1024 : ℝ) := by
    rw [show (44781663977570654201/44790000000000000000 : ℝ)+2*(3417929887/3583200000000 : ℝ)*(3871/25000 : ℝ)=(10001092829685919/10000000000000000 : ℝ) by norm_num, show 1+2*(24373087666887717/100000000000000000000 : ℝ)=(50024373087666887717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44781663977570654201/44790000000000000000 : ℝ)*(X 1 0+X 2 0)+(3417929887/3583200000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4567/1024 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (44781663977570654201/44790000000000000000 : ℝ)) (alpha := (3417929887/3583200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44781663977570654201/44790000000000000000 : ℝ)*(X 0 1+X 2 1)+(3417929887/3583200000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4567/1024 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (44781663977570654201/44790000000000000000 : ℝ)) (alpha := (3417929887/3583200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44781663977570654201/44790000000000000000 : ℝ)*(X 0 2+X 1 2)+(3417929887/3583200000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4567/1024 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (44781663977570654201/44790000000000000000 : ℝ)) (alpha := (3417929887/3583200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-811852401/5000000000 : ℝ)*X 0 0+(5400242599/10000000000 : ℝ)*X 0 1+(2700121061/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271017837/10000000000 : ℝ)*X 1 0+(-901564443/5000000000 : ℝ)*X 1 1+(5400243189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271018513/10000000000 : ℝ)*X 2 0+(675030291/1250000000 : ℝ)*X 2 1+(-901564573/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4460745109/10000000000 : ℝ)*X 0 0+(832909211/2000000000 : ℝ)*X 0 1+(4164547057/10000000000 : ℝ)*X 0 2+(4460745109/10000000000 : ℝ)*X 1 0+(832909211/2000000000 : ℝ)*X 1 1+(4164547057/10000000000 : ℝ)*X 1 2+(4460745109/10000000000 : ℝ)*X 2 0+(832909211/2000000000 : ℝ)*X 2 1+(4164547057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2047989281/10000000000 : ℝ)*X 0 0+(655540213/1250000000 : ℝ)*X 0 1+(2622160929/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5379374863/10000000000 : ℝ)*X 1 0+(-93389751/500000000 : ℝ)*X 1 1+(26221609/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((537937473/1000000000 : ℝ)*X 2 0+(2622160857/5000000000 : ℝ)*X 2 1+(-1867795317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((40541709/100000000 : ℝ)*X 0 0+(873540543/2000000000 : ℝ)*X 0 1+(4367702009/10000000000 : ℝ)*X 0 2+(40541709/100000000 : ℝ)*X 1 0+(873540543/2000000000 : ℝ)*X 1 1+(4367702009/10000000000 : ℝ)*X 1 2+(40541709/100000000 : ℝ)*X 2 0+(873540543/2000000000 : ℝ)*X 2 1+(4367702009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-979103919/5000000000 : ℝ)*X 0 0+(256741533/500000000 : ℝ)*X 0 1+(5420621111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628425593/5000000000 : ℝ)*X 1 0+(-1794436079/10000000000 : ℝ)*X 1 1+(271031113/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1314212479/2500000000 : ℝ)*X 2 0+(108412459/200000000 : ℝ)*X 2 1+(-1794436861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4512738451/10000000000 : ℝ)*X 0 0+(51724503/125000000 : ℝ)*X 0 1+(2068979587/5000000000 : ℝ)*X 0 2+(4512738451/10000000000 : ℝ)*X 1 0+(51724503/125000000 : ℝ)*X 1 1+(2068979587/5000000000 : ℝ)*X 1 2+(4512738451/10000000000 : ℝ)*X 2 0+(51724503/125000000 : ℝ)*X 2 1+(2068979587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-856655207/5000000000 : ℝ)*X 0 0+(688286709/1250000000 : ℝ)*X 0 1+(5229280207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5389828131/10000000000 : ℝ)*X 1 0+(-1873858417/10000000000 : ℝ)*X 1 1+(5229280267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((21559313/40000000 : ℝ)*X 2 0+(326830011/625000000 : ℝ)*X 2 1+(-1873858379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2007043409/5000000000 : ℝ)*X 0 0+(4387277067/10000000000 : ℝ)*X 0 1+(877455397/2000000000 : ℝ)*X 0 2+(2007043409/5000000000 : ℝ)*X 1 0+(4387277067/10000000000 : ℝ)*X 1 1+(877455397/2000000000 : ℝ)*X 1 2+(2007043409/5000000000 : ℝ)*X 2 0+(4387277067/10000000000 : ℝ)*X 2 1+(877455397/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1536_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63773/100000 : ℝ) ≤ (-119011805185871936670290212309641/186625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12839041/50000000000000 : ℝ)*(lower0) + (102070779/100000000000000 : ℝ)*(upper1) + (92544371/100000000000000 : ℝ)*(lower4) + (674409/2000000000000 : ℝ)*(lower5) + (564654495782441/25000000000000 : ℝ)*(major0) + (564654495782441/25000000000000 : ℝ)*(major1) + (564654495782441/25000000000000 : ℝ)*(major2) + (72896873/20000000000000 : ℝ)*(sp3) + (1586056029213863/50000000000000 : ℝ)*(sp4) + (198253526922977/6250000000000 : ℝ)*(sp5) + (63442092055077/2000000000000 : ℝ)*(sp6) + (1366380396249577/100000000000000 : ℝ)*(sp7) + (27813830047/50000000000000 : ℝ)*(sp13) + (1863918469/25000000000000 : ℝ)*(sp14) + (683190380366971/50000000000000 : ℝ)*(f.failure) + (1586056029213863/50000000000000 : ℝ)*(f.sum) + (7565093287859/4479000000000000000000000000 : ℝ)*base65 + (239845372070315359/1119750000000000000000000000000000 : ℝ)*base68 + (2033804570832684641/1119750000000000000000000000000000 : ℝ)*base69 + (3989033740229934641/1119750000000000000000000000000000 : ℝ)*base71 + (1290524409083/1119750000000000000000000000 : ℝ)*base73 + (4230645527019815359/1119750000000000000000000000000000 : ℝ)*base76 + (596338185022434641/1119750000000000000000000000000000 : ℝ)*base77 + (1257466443282684641/1119750000000000000000000000000000 : ℝ)*base79 + (8201718115969/1119750000000000000000000000 : ℝ)*base82 + (33456981/5000000000000000000000 : ℝ)*base89 + (33456981/5000000000000000000000 : ℝ)*base91 + (33456981/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58741/100000 : ℝ) ≤ (109629902706746815992658247985949/186625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87584269/50000000000000 : ℝ)*(upper0) + (209667/50000000000000 : ℝ)*(upper2) + (62664713/100000000000000 : ℝ)*(upper3) + (2626809/5000000000000 : ℝ)*(upper4) + (22248079/50000000000000 : ℝ)*(upper5) + (1168254730635149/50000000000000 : ℝ)*(major0) + (1168254730635149/50000000000000 : ℝ)*(major1) + (1168254730635149/50000000000000 : ℝ)*(major2) + (1619967772436843/50000000000000 : ℝ)*(sp0) + (647983478473343/20000000000000 : ℝ)*(sp1) + (161996639769473/5000000000000 : ℝ)*(sp2) + (88343889908527/6250000000000 : ℝ)*(sp3) + (18152506971/100000000000000 : ℝ)*(sp5) + (1374742113/50000000000000 : ℝ)*(sp6) + (88343889908527/6250000000000 : ℝ)*(f.failure) + (1619967772436843/50000000000000 : ℝ)*(f.sum) + (7570847562307/2239500000000000000000000000 : ℝ)*base66 + (4295575425710389051/2239500000000000000000000000000000 : ℝ)*base68 + (13979972125469389051/2239500000000000000000000000000000 : ℝ)*base70 + (6751988163630610949/2239500000000000000000000000000000 : ℝ)*base71 + (786538841/2239500000000000000000000 : ℝ)*base73 + (4192730609667889051/2239500000000000000000000000000000 : ℝ)*base76 + (11037069209783389051/2239500000000000000000000000000000 : ℝ)*base78 + (1245368206745389051/2239500000000000000000000000000000 : ℝ)*base80 + (2348604146147/1119750000000000000000000000 : ℝ)*base82 + (3624897/625000000000000000000 : ℝ)*base89 + (3624897/625000000000000000000 : ℝ)*base91 + (3624897/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80573/100000 : ℝ) ≤ (300748973035122005539317208171103/373250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (240425303/100000000000000 : ℝ)*(upper2) + (133994813/50000000000000 : ℝ)*(upper3) + (14686413/5000000000000 : ℝ)*(lower5) + (1263733031419501/50000000000000 : ℝ)*(major0) + (1263733031419501/50000000000000 : ℝ)*(major1) + (1263733031419501/50000000000000 : ℝ)*(major2) + (101148897/50000000000000 : ℝ)*(sp0) + (32990570299/50000000000000 : ℝ)*(sp1) + (209919989411/100000000000000 : ℝ)*(sp2) + (67948196423/100000000000000 : ℝ)*(sp3) + (874762346540607/25000000000000 : ℝ)*(sp8) + (437372950914953/12500000000000 : ℝ)*(sp9) + (874709917117703/25000000000000 : ℝ)*(sp10) + (1528956006923997/100000000000000 : ℝ)*(sp11) + (1529023955120419/100000000000000 : ℝ)*(f.failure) + (1749524794230111/50000000000000 : ℝ)*(f.sum) + (792268444327/1119750000000000000000000000 : ℝ)*base66 + (19536507008548026299/2239500000000000000000000000000000 : ℝ)*base68 + (28196121255541026299/2239500000000000000000000000000000 : ℝ)*base70 + (15645072783311526299/2239500000000000000000000000000000 : ℝ)*base72 + (2099680885691/4479000000000000000000000000 : ℝ)*base73 + (11963824129738026299/2239500000000000000000000000000000 : ℝ)*base76 + (12705274515589026299/2239500000000000000000000000000000 : ℝ)*base78 + (32188237804267026299/2239500000000000000000000000000000 : ℝ)*base80 + (26755779579679/4479000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (17268691/10000000000000000000000 : ℝ)*base90 + (17268691/10000000000000000000000 : ℝ)*base92 + (17268691/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-17231/20000 : ℝ) ≤ (-643125934134007926834517838348273/746500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32218671/100000000000000 : ℝ)*(lower2) + (2001177/25000000000000 : ℝ)*(upper3) + (7608113/50000000000000 : ℝ)*(upper5) + (2567111856876109/100000000000000 : ℝ)*(major0) + (2567111856876109/100000000000000 : ℝ)*(major1) + (2567111856876109/100000000000000 : ℝ)*(major2) + (7546211/781250000000 : ℝ)*(sp0) + (1900456643/100000000000000 : ℝ)*(sp5) + (12174013021/100000000000000 : ℝ)*(sp6) + (834817903/12500000000000 : ℝ)*(sp7) + (3609931935657179/100000000000000 : ℝ)*(sp12) + (451241375139443/12500000000000 : ℝ)*(sp13) + (1804960363779583/50000000000000 : ℝ)*(sp14) + (1553001522970761/100000000000000 : ℝ)*(sp15) + (310601640302797/20000000000000 : ℝ)*(f.failure) + (3609932901572187/100000000000000 : ℝ)*(f.sum) + (3049749778829/4479000000000000000000000000 : ℝ)*base66 + (7886209492358116091/4479000000000000000000000000000000 : ℝ)*base68 + (31220936850395116091/4479000000000000000000000000000000 : ℝ)*base70 + (17927030334434116091/4479000000000000000000000000000000 : ℝ)*base72 + (12837576397397/2239500000000000000000000000 : ℝ)*base73 + (12902564178896116091/4479000000000000000000000000000000 : ℝ)*base76 + (14807253012137116091/4479000000000000000000000000000000 : ℝ)*base78 + (39578870560628116091/4479000000000000000000000000000000 : ℝ)*base80 + (2490666053141/895800000000000000000000000 : ℝ)*base81 + (4527133/2000000000000000000000 : ℝ)*base90 + (4527133/2000000000000000000000 : ℝ)*base92 + (4527133/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1536_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165299311/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63773/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58741/100000 : ℝ) else (80573/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17231/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1536_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1536_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165299311/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63773/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58741/100000 : ℝ) else (80573/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17231/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1536_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1536_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4567/1024 : ℝ) ≤ p) (hpb : p ≤ (4569/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165299311/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63773/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58741/100000 : ℝ) else (80573/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17231/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1536_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
