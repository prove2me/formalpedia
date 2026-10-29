-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1609_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:02.111433+00:00
-- url     : https://prove2.me/submissions/4dcce06d-5ce1-492d-94e1-656bc2378cdf

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
theorem support_rectangle_w1609_s0_0 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1567411141/10000000000 : ℝ)*x 0 + (5838477173/10000000000 : ℝ)*x 1 + (489226129/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1567411141/10000000000 : ℝ)^4755 ≤ (4712648556733/50000000000000 : ℝ)^3731 := by
    have hnat : (1567411141 : ℕ)^4755*50000000000000^3731 ≤ 4712648556733^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1567411141 10000000000 4712648556733 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5838477173/10000000000 : ℝ)^4755 ≤ (10073695273131/20000000000000 : ℝ)^3731 := by
    have hnat : (5838477173 : ℕ)^4755*20000000000000^3731 ≤ 10073695273131^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5838477173 10000000000 10073695273131 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (489226129/1000000000 : ℝ)^4755 ≤ (10051556625081/25000000000000 : ℝ)^3731 := by
    have hnat : (489226129 : ℕ)^4755*25000000000000^3731 ≤ 10051556625081^3731*1000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489226129 1000000000 10051556625081 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1567411141/10000000000 : ℝ), (5838477173/10000000000 : ℝ), (489226129/1000000000 : ℝ)] ![(4712648556733/50000000000000 : ℝ), (10073695273131/20000000000000 : ℝ), (10051556625081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1567411141/10000000000 : ℝ)|^4755 ≤ (4712648556733/50000000000000 : ℝ)^3731
        have hw : |(-1567411141/10000000000 : ℝ)|=(1567411141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5838477173/10000000000 : ℝ)|^4755 ≤ (10073695273131/20000000000000 : ℝ)^3731
        have hw : |(5838477173/10000000000 : ℝ)|=(5838477173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(489226129/1000000000 : ℝ)|^4755 ≤ (10051556625081/25000000000000 : ℝ)^3731
        have hw : |(489226129/1000000000 : ℝ)|=(489226129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s0_1 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (681766271/1250000000 : ℝ)*x 0 + (-1045709393/5000000000 : ℝ)*x 1 + (4892261297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (681766271/1250000000 : ℝ)^4755 ≤ (11545371490309/25000000000000 : ℝ)^3731 := by
    have hnat : (681766271 : ℕ)^4755*25000000000000^3731 ≤ 11545371490309^3731*1250000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681766271 1250000000 11545371490309 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045709393/5000000000 : ℝ)^4755 ≤ (108898299629/800000000000 : ℝ)^3731 := by
    have hnat : (1045709393 : ℕ)^4755*800000000000^3731 ≤ 108898299629^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045709393 5000000000 108898299629 800000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4892261297/10000000000 : ℝ)^4755 ≤ (40206226573641/100000000000000 : ℝ)^3731 := by
    have hnat : (4892261297 : ℕ)^4755*100000000000000^3731 ≤ 40206226573641^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4892261297 10000000000 40206226573641 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(681766271/1250000000 : ℝ), (-1045709393/5000000000 : ℝ), (4892261297/10000000000 : ℝ)] ![(11545371490309/25000000000000 : ℝ), (108898299629/800000000000 : ℝ), (40206226573641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(681766271/1250000000 : ℝ)|^4755 ≤ (11545371490309/25000000000000 : ℝ)^3731
        have hw : |(681766271/1250000000 : ℝ)|=(681766271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1045709393/5000000000 : ℝ)|^4755 ≤ (108898299629/800000000000 : ℝ)^3731
        have hw : |(-1045709393/5000000000 : ℝ)|=(1045709393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4892261297/10000000000 : ℝ)|^4755 ≤ (40206226573641/100000000000000 : ℝ)^3731
        have hw : |(4892261297/10000000000 : ℝ)|=(4892261297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s0_2 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5454130303/10000000000 : ℝ)*x 0 + (2446130661/5000000000 : ℝ)*x 1 + (-2091418579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5454130303/10000000000 : ℝ)^4755 ≤ (46181487418041/100000000000000 : ℝ)^3731 := by
    have hnat : (5454130303 : ℕ)^4755*100000000000000^3731 ≤ 46181487418041^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454130303 10000000000 46181487418041 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2446130661/5000000000 : ℝ)^4755 ≤ (40206226835489/100000000000000 : ℝ)^3731 := by
    have hnat : (2446130661 : ℕ)^4755*100000000000000^3731 ≤ 40206226835489^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2446130661 5000000000 40206226835489 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091418579/10000000000 : ℝ)^4755 ≤ (3403071434141/25000000000000 : ℝ)^3731 := by
    have hnat : (2091418579 : ℕ)^4755*25000000000000^3731 ≤ 3403071434141^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091418579 10000000000 3403071434141 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5454130303/10000000000 : ℝ), (2446130661/5000000000 : ℝ), (-2091418579/10000000000 : ℝ)] ![(46181487418041/100000000000000 : ℝ), (40206226835489/100000000000000 : ℝ), (3403071434141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5454130303/10000000000 : ℝ)|^4755 ≤ (46181487418041/100000000000000 : ℝ)^3731
        have hw : |(5454130303/10000000000 : ℝ)|=(5454130303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2446130661/5000000000 : ℝ)|^4755 ≤ (40206226835489/100000000000000 : ℝ)^3731
        have hw : |(2446130661/5000000000 : ℝ)|=(2446130661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091418579/10000000000 : ℝ)|^4755 ≤ (3403071434141/25000000000000 : ℝ)^3731
        have hw : |(-2091418579/10000000000 : ℝ)|=(2091418579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s0_3 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2055135943/5000000000 : ℝ)*x 0 + (768531981/2500000000 : ℝ)*x 1 + (1079248273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055135943/5000000000 : ℝ)^4755 ≤ (201267911921/625000000000 : ℝ)^3731 := by
    have hnat : (2055135943 : ℕ)^4755*625000000000^3731 ≤ 201267911921^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055135943 5000000000 201267911921 625000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (768531981/2500000000 : ℝ)^4755 ≤ (11119711290329/50000000000000 : ℝ)^3731 := by
    have hnat : (768531981 : ℕ)^4755*50000000000000^3731 ≤ 11119711290329^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768531981 2500000000 11119711290329 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079248273/2000000000 : ℝ)^4755 ≤ (11389427872521/25000000000000 : ℝ)^3731 := by
    have hnat : (1079248273 : ℕ)^4755*25000000000000^3731 ≤ 11389427872521^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079248273 2000000000 11389427872521 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2055135943/5000000000 : ℝ), (768531981/2500000000 : ℝ), (1079248273/2000000000 : ℝ)] ![(201267911921/625000000000 : ℝ), (11119711290329/50000000000000 : ℝ), (11389427872521/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2055135943/5000000000 : ℝ)|^4755 ≤ (201267911921/625000000000 : ℝ)^3731
        have hw : |(2055135943/5000000000 : ℝ)|=(2055135943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(768531981/2500000000 : ℝ)|^4755 ≤ (11119711290329/50000000000000 : ℝ)^3731
        have hw : |(768531981/2500000000 : ℝ)|=(768531981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079248273/2000000000 : ℝ)|^4755 ≤ (11389427872521/25000000000000 : ℝ)^3731
        have hw : |(1079248273/2000000000 : ℝ)|=(1079248273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s0_4 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-196277221/1250000000 : ℝ)*x 0 + (614527923/1250000000 : ℝ)*x 1 + (90838493/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196277221/1250000000 : ℝ)^4755 ≤ (4723405744577/50000000000000 : ℝ)^3731 := by
    have hnat : (196277221 : ℕ)^4755*50000000000000^3731 ≤ 4723405744577^3731*1250000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196277221 1250000000 4723405744577 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (614527923/1250000000 : ℝ)^4755 ≤ (40457371869321/100000000000000 : ℝ)^3731 := by
    have hnat : (614527923 : ℕ)^4755*100000000000000^3731 ≤ 40457371869321^3731*1250000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614527923 1250000000 40457371869321 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90838493/156250000 : ℝ)^4755 ≤ (50095816624401/100000000000000 : ℝ)^3731 := by
    have hnat : (90838493 : ℕ)^4755*100000000000000^3731 ≤ 50095816624401^3731*156250000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90838493 156250000 50095816624401 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196277221/1250000000 : ℝ), (614527923/1250000000 : ℝ), (90838493/156250000 : ℝ)] ![(4723405744577/50000000000000 : ℝ), (40457371869321/100000000000000 : ℝ), (50095816624401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196277221/1250000000 : ℝ)|^4755 ≤ (4723405744577/50000000000000 : ℝ)^3731
        have hw : |(-196277221/1250000000 : ℝ)|=(196277221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(614527923/1250000000 : ℝ)|^4755 ≤ (40457371869321/100000000000000 : ℝ)^3731
        have hw : |(614527923/1250000000 : ℝ)|=(614527923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90838493/156250000 : ℝ)|^4755 ≤ (50095816624401/100000000000000 : ℝ)^3731
        have hw : |(90838493/156250000 : ℝ)|=(90838493/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s0_5 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597851687/5000000000 : ℝ)*x 0 + (-73126007/625000000 : ℝ)*x 1 + (5813663621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597851687/5000000000 : ℝ)^4755 ≤ (43411108827161/100000000000000 : ℝ)^3731 := by
    have hnat : (2597851687 : ℕ)^4755*100000000000000^3731 ≤ 43411108827161^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597851687 5000000000 43411108827161 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73126007/625000000 : ℝ)^4755 ≤ (64930737811/1000000000000 : ℝ)^3731 := by
    have hnat : (73126007 : ℕ)^4755*1000000000000^3731 ≤ 64930737811^3731*625000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73126007 625000000 64930737811 1000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5813663621/10000000000 : ℝ)^4755 ≤ (50095817382151/100000000000000 : ℝ)^3731 := by
    have hnat : (5813663621 : ℕ)^4755*100000000000000^3731 ≤ 50095817382151^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5813663621 10000000000 50095817382151 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597851687/5000000000 : ℝ), (-73126007/625000000 : ℝ), (5813663621/10000000000 : ℝ)] ![(43411108827161/100000000000000 : ℝ), (64930737811/1000000000000 : ℝ), (50095817382151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597851687/5000000000 : ℝ)|^4755 ≤ (43411108827161/100000000000000 : ℝ)^3731
        have hw : |(2597851687/5000000000 : ℝ)|=(2597851687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-73126007/625000000 : ℝ)|^4755 ≤ (64930737811/1000000000000 : ℝ)^3731
        have hw : |(-73126007/625000000 : ℝ)|=(73126007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5813663621/10000000000 : ℝ)|^4755 ≤ (50095817382151/100000000000000 : ℝ)^3731
        have hw : |(5813663621/10000000000 : ℝ)|=(5813663621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s0_6 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597851723/5000000000 : ℝ)*x 0 + (5813663323/10000000000 : ℝ)*x 1 + (-234003293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597851723/5000000000 : ℝ)^4755 ≤ (21705554796921/50000000000000 : ℝ)^3731 := by
    have hnat : (2597851723 : ℕ)^4755*50000000000000^3731 ≤ 21705554796921^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597851723 5000000000 21705554796921 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5813663323/10000000000 : ℝ)^4755 ≤ (1001916282191/2000000000000 : ℝ)^3731 := by
    have hnat : (5813663323 : ℕ)^4755*2000000000000^3731 ≤ 1001916282191^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5813663323 10000000000 1001916282191 2000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234003293/2000000000 : ℝ)^4755 ≤ (1298615255551/20000000000000 : ℝ)^3731 := by
    have hnat : (234003293 : ℕ)^4755*20000000000000^3731 ≤ 1298615255551^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234003293 2000000000 1298615255551 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597851723/5000000000 : ℝ), (5813663323/10000000000 : ℝ), (-234003293/2000000000 : ℝ)] ![(21705554796921/50000000000000 : ℝ), (1001916282191/2000000000000 : ℝ), (1298615255551/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597851723/5000000000 : ℝ)|^4755 ≤ (21705554796921/50000000000000 : ℝ)^3731
        have hw : |(2597851723/5000000000 : ℝ)|=(2597851723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5813663323/10000000000 : ℝ)|^4755 ≤ (1001916282191/2000000000000 : ℝ)^3731
        have hw : |(5813663323/10000000000 : ℝ)|=(5813663323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-234003293/2000000000 : ℝ)|^4755 ≤ (1298615255551/20000000000000 : ℝ)^3731
        have hw : |(-234003293/2000000000 : ℝ)|=(234003293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s0_7 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (514645077/1250000000 : ℝ)*x 0 + (2668718243/5000000000 : ℝ)*x 1 + (313502317/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514645077/1250000000 : ℝ)^4755 ≤ (32271665876109/100000000000000 : ℝ)^3731 := by
    have hnat : (514645077 : ℕ)^4755*100000000000000^3731 ≤ 32271665876109^3731*1250000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514645077 1250000000 32271665876109 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2668718243/5000000000 : ℝ)^4755 ≤ (22462971835699/50000000000000 : ℝ)^3731 := by
    have hnat : (2668718243 : ℕ)^4755*50000000000000^3731 ≤ 22462971835699^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2668718243 5000000000 22462971835699 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313502317/1000000000 : ℝ)^4755 ≤ (11401195222411/50000000000000 : ℝ)^3731 := by
    have hnat : (313502317 : ℕ)^4755*50000000000000^3731 ≤ 11401195222411^3731*1000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313502317 1000000000 11401195222411 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(514645077/1250000000 : ℝ), (2668718243/5000000000 : ℝ), (313502317/1000000000 : ℝ)] ![(32271665876109/100000000000000 : ℝ), (22462971835699/50000000000000 : ℝ), (11401195222411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(514645077/1250000000 : ℝ)|^4755 ≤ (32271665876109/100000000000000 : ℝ)^3731
        have hw : |(514645077/1250000000 : ℝ)|=(514645077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2668718243/5000000000 : ℝ)|^4755 ≤ (22462971835699/50000000000000 : ℝ)^3731
        have hw : |(2668718243/5000000000 : ℝ)|=(2668718243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(313502317/1000000000 : ℝ)|^4755 ≤ (11401195222411/50000000000000 : ℝ)^3731
        have hw : |(313502317/1000000000 : ℝ)|=(313502317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1609_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4001/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4853/20000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4751/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4751 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4751*1^1024 ≤ 0^1024*1^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4751/1024 : ℝ) ≤ (284923490573543419/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4751 ≤ (284923490573543419/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4751*20000000000000000000^1024 ≤ 284923490573543419^1024*5^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 284923490573543419 20000000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (284923490573543419/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4751 := by
      have hnat : (1 : ℕ)^1024*1^4751 ≤ 1^4751*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20284923490573543419/20000000000000000000 : ℝ) ≤ (5015267576380849/5000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (20284923490573543419/20000000000000000000 : ℝ)^1024 ≤ (5015267576380849/5000000000000000 : ℝ)^4751 := by
      have hnat : (20284923490573543419 : ℕ)^1024*5000000000000000^4751 ≤ 5015267576380849^4751*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20284923490573543419 20000000000000000000 5015267576380849 5000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015267576380849/5000000000000000 : ℝ)) (X := (20284923490573543419/20000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10284923490573543419/10000000000000000000 : ℝ) ≤ (2515267576380849/2500000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (10284923490573543419/10000000000000000000 : ℝ)^1024 ≤ (2515267576380849/2500000000000000 : ℝ)^4751 := by
      have hnat : (10284923490573543419 : ℕ)^1024*2500000000000000^4751 ≤ 2515267576380849^4751*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10284923490573543419 10000000000000000000 2515267576380849 2500000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515267576380849/2500000000000000 : ℝ)) (X := (10284923490573543419/10000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15267576380849/2000000000000000 : ℝ)*(0 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15267576380849/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(284923490573543419/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15267576380849/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4751/1024 : ℝ) := by
    rw [show (1 : ℝ)+(15267576380849/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5015267576380849/5000000000000000 : ℝ) by norm_num, show 1+(284923490573543419/20000000000000000000 : ℝ)+(0 : ℝ)=(20284923490573543419/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(284923490573543419/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15267576380849/2000000000000000 : ℝ)*(2/5 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15267576380849/2000000000000000 : ℝ)*(2/5 : ℝ)=(2515267576380849/2500000000000000 : ℝ) by norm_num, show 1+2*(284923490573543419/20000000000000000000 : ℝ)=(10284923490573543419/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15267576380849/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15267576380849/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15267576380849/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15267576380849/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15267576380849/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15267576380849/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1567411141/10000000000 : ℝ)*X 0 0+(5838477173/10000000000 : ℝ)*X 0 1+(489226129/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((681766271/1250000000 : ℝ)*X 1 0+(-1045709393/5000000000 : ℝ)*X 1 1+(4892261297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5454130303/10000000000 : ℝ)*X 2 0+(2446130661/5000000000 : ℝ)*X 2 1+(-2091418579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2055135943/5000000000 : ℝ)*X 0 0+(768531981/2500000000 : ℝ)*X 0 1+(1079248273/2000000000 : ℝ)*X 0 2+(2055135943/5000000000 : ℝ)*X 1 0+(768531981/2500000000 : ℝ)*X 1 1+(1079248273/2000000000 : ℝ)*X 1 2+(2055135943/5000000000 : ℝ)*X 2 0+(768531981/2500000000 : ℝ)*X 2 1+(1079248273/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-196277221/1250000000 : ℝ)*X 0 0+(614527923/1250000000 : ℝ)*X 0 1+(90838493/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2597851687/5000000000 : ℝ)*X 1 0+(-73126007/625000000 : ℝ)*X 1 1+(5813663621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2597851723/5000000000 : ℝ)*X 2 0+(5813663323/10000000000 : ℝ)*X 2 1+(-234003293/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((514645077/1250000000 : ℝ)*X 0 0+(2668718243/5000000000 : ℝ)*X 0 1+(313502317/1000000000 : ℝ)*X 0 2+(514645077/1250000000 : ℝ)*X 1 0+(2668718243/5000000000 : ℝ)*X 1 1+(313502317/1000000000 : ℝ)*X 1 2+(514645077/1250000000 : ℝ)*X 2 0+(2668718243/5000000000 : ℝ)*X 2 1+(313502317/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (241896156950163357873339/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33893877/100000000000000 : ℝ)*(base1) + (138666757/25000000000000 : ℝ)*(base19) + (580825929/100000000000000 : ℝ)*(base23) + (43877571/100000000000000 : ℝ)*(upper3) + (29032311/25000000000000 : ℝ)*(upper5) + (743744637994663/100000000000000 : ℝ)*(major0) + (743744637994663/100000000000000 : ℝ)*(major1) + (743744637994663/100000000000000 : ℝ)*(major2) + (528421490927843/50000000000000 : ℝ)*(sp0) + (1056844819920851/100000000000000 : ℝ)*(sp1) + (1056844793761951/100000000000000 : ℝ)*(sp2) + (21532153132849/5000000000000 : ℝ)*(sp3) + (242662607/10000000000000 : ℝ)*(sp4) + (181054633/25000000000000 : ℝ)*(sp7) + (430643820769389/100000000000000 : ℝ)*(f.failure) + (1056845374587879/100000000000000 : ℝ)*(f.sum) + (12096533191113/100000000000000000000000000000 : ℝ)*base66 + (39593591408887/200000000000000000000000000000 : ℝ)*base67 + (1062270573408887/200000000000000000000000000000 : ℝ)*base69 + (507635925408887/200000000000000000000000000000 : ℝ)*base71 + (150533601191113/100000000000000000000000000000 : ℝ)*base74 + (767388940008887/200000000000000000000000000000 : ℝ)*base75 + (206402288408887/200000000000000000000000000000 : ℝ)*base77 + (821062941391113/200000000000000000000000000000 : ℝ)*base80 + (144514866308887/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10695827/2000000000000000000000 : ℝ)*base90 + (10695827/2000000000000000000000 : ℝ)*base92 + (10695827/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31583526501175175707713/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (511521163/50000000000000 : ℝ)*(base19) + (520944629/50000000000000 : ℝ)*(base23) + (188672929/100000000000000 : ℝ)*(base32) + (180336013/100000000000000 : ℝ)*(upper3) + (55232451/100000000000000 : ℝ)*(upper5) + (784163311689347/100000000000000 : ℝ)*(major0) + (784163311689347/100000000000000 : ℝ)*(major1) + (196040827922337/25000000000000 : ℝ)*(major2) + (1387192317/50000000000000 : ℝ)*(sp1) + (710714017/25000000000000 : ℝ)*(sp2) + (1114279370219303/100000000000000 : ℝ)*(sp4) + (139284446599043/12500000000000 : ℝ)*(sp5) + (139284435684247/12500000000000 : ℝ)*(sp6) + (454046896040979/100000000000000 : ℝ)*(sp7) + (454047084713909/100000000000000 : ℝ)*(f.failure) + (1114279370219303/100000000000000 : ℝ)*(f.sum) + (28427800122411/40000000000000000000000000000 : ℝ)*base65 + (211391448824113/50000000000000000000000000000 : ℝ)*base67 + (2100320910915603/200000000000000000000000000000 : ℝ)*base69 + (310386005475887/50000000000000000000000000000 : ℝ)*base72 + (413048936842411/40000000000000000000000000000 : ℝ)*base73 + (197944177715603/200000000000000000000000000000 : ℝ)*base75 + (76079855315603/200000000000000000000000000000 : ℝ)*base77 + (1147337660515603/200000000000000000000000000000 : ℝ)*base79 + (392068326315603/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (19461813/2000000000000000000000 : ℝ)*base89 + (19461813/2000000000000000000000 : ℝ)*base91 + (538187/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1609_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4853/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1609_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1609_s1_0 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-84564117/500000000 : ℝ)*x 0 + (2765419151/5000000000 : ℝ)*x 1 + (2559897707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84564117/500000000 : ℝ)^4755 ≤ (10384711387697/100000000000000 : ℝ)^3731 := by
    have hnat : (84564117 : ℕ)^4755*100000000000000^3731 ≤ 10384711387697^3731*500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84564117 500000000 10384711387697 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2765419151/5000000000 : ℝ)^4755 ≤ (5876355880691/12500000000000 : ℝ)^3731 := by
    have hnat : (2765419151 : ℕ)^4755*12500000000000^3731 ≤ 5876355880691^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2765419151 5000000000 5876355880691 12500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2559897707/5000000000 : ℝ)^4755 ≤ (42604441551583/100000000000000 : ℝ)^3731 := by
    have hnat : (2559897707 : ℕ)^4755*100000000000000^3731 ≤ 42604441551583^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559897707 5000000000 42604441551583 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84564117/500000000 : ℝ), (2765419151/5000000000 : ℝ), (2559897707/5000000000 : ℝ)] ![(10384711387697/100000000000000 : ℝ), (5876355880691/12500000000000 : ℝ), (42604441551583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84564117/500000000 : ℝ)|^4755 ≤ (10384711387697/100000000000000 : ℝ)^3731
        have hw : |(-84564117/500000000 : ℝ)|=(84564117/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2765419151/5000000000 : ℝ)|^4755 ≤ (5876355880691/12500000000000 : ℝ)^3731
        have hw : |(2765419151/5000000000 : ℝ)|=(2765419151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2559897707/5000000000 : ℝ)|^4755 ≤ (42604441551583/100000000000000 : ℝ)^3731
        have hw : |(2559897707/5000000000 : ℝ)|=(2559897707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s1_1 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074452361/2000000000 : ℝ)*x 0 + (-381257613/2000000000 : ℝ)*x 1 + (5119795269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074452361/2000000000 : ℝ)^4755 ≤ (22649929356777/50000000000000 : ℝ)^3731 := by
    have hnat : (1074452361 : ℕ)^4755*50000000000000^3731 ≤ 22649929356777^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074452361 2000000000 22649929356777 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (381257613/2000000000 : ℝ)^4755 ≤ (12095701254641/100000000000000 : ℝ)^3731 := by
    have hnat : (381257613 : ℕ)^4755*100000000000000^3731 ≤ 12095701254641^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381257613 2000000000 12095701254641 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5119795269/10000000000 : ℝ)^4755 ≤ (21302220006899/50000000000000 : ℝ)^3731 := by
    have hnat : (5119795269 : ℕ)^4755*50000000000000^3731 ≤ 21302220006899^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5119795269 10000000000 21302220006899 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074452361/2000000000 : ℝ), (-381257613/2000000000 : ℝ), (5119795269/10000000000 : ℝ)] ![(22649929356777/50000000000000 : ℝ), (12095701254641/100000000000000 : ℝ), (21302220006899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074452361/2000000000 : ℝ)|^4755 ≤ (22649929356777/50000000000000 : ℝ)^3731
        have hw : |(1074452361/2000000000 : ℝ)|=(1074452361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-381257613/2000000000 : ℝ)|^4755 ≤ (12095701254641/100000000000000 : ℝ)^3731
        have hw : |(-381257613/2000000000 : ℝ)|=(381257613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5119795269/10000000000 : ℝ)|^4755 ≤ (21302220006899/50000000000000 : ℝ)^3731
        have hw : |(5119795269/10000000000 : ℝ)|=(5119795269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s1_2 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671532689/1250000000 : ℝ)*x 0 + (5119795503/10000000000 : ℝ)*x 1 + (-476572037/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671532689/1250000000 : ℝ)^4755 ≤ (9059971112969/20000000000000 : ℝ)^3731 := by
    have hnat : (671532689 : ℕ)^4755*20000000000000^3731 ≤ 9059971112969^3731*1250000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671532689 1250000000 9059971112969 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5119795503/10000000000 : ℝ)^4755 ≤ (5325555311933/12500000000000 : ℝ)^3731 := by
    have hnat : (5119795503 : ℕ)^4755*12500000000000^3731 ≤ 5325555311933^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5119795503 10000000000 5325555311933 12500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476572037/2500000000 : ℝ)^4755 ≤ (1511962740729/12500000000000 : ℝ)^3731 := by
    have hnat : (476572037 : ℕ)^4755*12500000000000^3731 ≤ 1511962740729^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476572037 2500000000 1511962740729 12500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671532689/1250000000 : ℝ), (5119795503/10000000000 : ℝ), (-476572037/2500000000 : ℝ)] ![(9059971112969/20000000000000 : ℝ), (5325555311933/12500000000000 : ℝ), (1511962740729/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671532689/1250000000 : ℝ)|^4755 ≤ (9059971112969/20000000000000 : ℝ)^3731
        have hw : |(671532689/1250000000 : ℝ)|=(671532689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5119795503/10000000000 : ℝ)|^4755 ≤ (5325555311933/12500000000000 : ℝ)^3731
        have hw : |(5119795503/10000000000 : ℝ)|=(5119795503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-476572037/2500000000 : ℝ)|^4755 ≤ (1511962740729/12500000000000 : ℝ)^3731
        have hw : |(-476572037/2500000000 : ℝ)|=(476572037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s1_3 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4202027093/10000000000 : ℝ)*x 0 + (744186247/2000000000 : ℝ)*x 1 + (945934851/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4202027093/10000000000 : ℝ)^4755 ≤ (16560917874979/50000000000000 : ℝ)^3731 := by
    have hnat : (4202027093 : ℕ)^4755*50000000000000^3731 ≤ 16560917874979^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202027093 10000000000 16560917874979 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744186247/2000000000 : ℝ)^4755 ≤ (14183515229191/50000000000000 : ℝ)^3731 := by
    have hnat : (744186247 : ℕ)^4755*50000000000000^3731 ≤ 14183515229191^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744186247 2000000000 14183515229191 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945934851/2000000000 : ℝ)^4755 ≤ (38511133778811/100000000000000 : ℝ)^3731 := by
    have hnat : (945934851 : ℕ)^4755*100000000000000^3731 ≤ 38511133778811^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945934851 2000000000 38511133778811 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4202027093/10000000000 : ℝ), (744186247/2000000000 : ℝ), (945934851/2000000000 : ℝ)] ![(16560917874979/50000000000000 : ℝ), (14183515229191/50000000000000 : ℝ), (38511133778811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4202027093/10000000000 : ℝ)|^4755 ≤ (16560917874979/50000000000000 : ℝ)^3731
        have hw : |(4202027093/10000000000 : ℝ)|=(4202027093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(744186247/2000000000 : ℝ)|^4755 ≤ (14183515229191/50000000000000 : ℝ)^3731
        have hw : |(744186247/2000000000 : ℝ)|=(744186247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(945934851/2000000000 : ℝ)|^4755 ≤ (38511133778811/100000000000000 : ℝ)^3731
        have hw : |(945934851/2000000000 : ℝ)|=(945934851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s1_4 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-422876803/2500000000 : ℝ)*x 0 + (5124276929/10000000000 : ℝ)*x 1 + (1105257457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422876803/2500000000 : ℝ)^4755 ≤ (2596617780293/25000000000000 : ℝ)^3731 := by
    have hnat : (422876803 : ℕ)^4755*25000000000000^3731 ≤ 2596617780293^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422876803 2500000000 2596617780293 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5124276929/10000000000 : ℝ)^4755 ≤ (42651975572193/100000000000000 : ℝ)^3731 := by
    have hnat : (5124276929 : ℕ)^4755*100000000000000^3731 ≤ 42651975572193^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124276929 10000000000 42651975572193 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105257457/2000000000 : ℝ)^4755 ≤ (4696155330297/10000000000000 : ℝ)^3731 := by
    have hnat : (1105257457 : ℕ)^4755*10000000000000^3731 ≤ 4696155330297^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105257457 2000000000 4696155330297 10000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422876803/2500000000 : ℝ), (5124276929/10000000000 : ℝ), (1105257457/2000000000 : ℝ)] ![(2596617780293/25000000000000 : ℝ), (42651975572193/100000000000000 : ℝ), (4696155330297/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422876803/2500000000 : ℝ)|^4755 ≤ (2596617780293/25000000000000 : ℝ)^3731
        have hw : |(-422876803/2500000000 : ℝ)|=(422876803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5124276929/10000000000 : ℝ)|^4755 ≤ (42651975572193/100000000000000 : ℝ)^3731
        have hw : |(5124276929/10000000000 : ℝ)|=(5124276929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105257457/2000000000 : ℝ)|^4755 ≤ (4696155330297/10000000000000 : ℝ)^3731
        have hw : |(1105257457/2000000000 : ℝ)|=(1105257457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s1_5 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315732519/2500000000 : ℝ)*x 0 + (-1499795763/10000000000 : ℝ)*x 1 + (5526287611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315732519/2500000000 : ℝ)^4755 ≤ (11032057133457/25000000000000 : ℝ)^3731 := by
    have hnat : (1315732519 : ℕ)^4755*25000000000000^3731 ≤ 11032057133457^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315732519 2500000000 11032057133457 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1499795763/10000000000 : ℝ)^4755 ≤ (1113776826279/12500000000000 : ℝ)^3731 := by
    have hnat : (1499795763 : ℕ)^4755*12500000000000^3731 ≤ 1113776826279^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499795763 10000000000 1113776826279 12500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5526287611/10000000000 : ℝ)^4755 ≤ (23480778416799/50000000000000 : ℝ)^3731 := by
    have hnat : (5526287611 : ℕ)^4755*50000000000000^3731 ≤ 23480778416799^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526287611 10000000000 23480778416799 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315732519/2500000000 : ℝ), (-1499795763/10000000000 : ℝ), (5526287611/10000000000 : ℝ)] ![(11032057133457/25000000000000 : ℝ), (1113776826279/12500000000000 : ℝ), (23480778416799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315732519/2500000000 : ℝ)|^4755 ≤ (11032057133457/25000000000000 : ℝ)^3731
        have hw : |(1315732519/2500000000 : ℝ)|=(1315732519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1499795763/10000000000 : ℝ)|^4755 ≤ (1113776826279/12500000000000 : ℝ)^3731
        have hw : |(-1499795763/10000000000 : ℝ)|=(1499795763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5526287611/10000000000 : ℝ)|^4755 ≤ (23480778416799/50000000000000 : ℝ)^3731
        have hw : |(5526287611/10000000000 : ℝ)|=(5526287611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s1_6 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5262929443/10000000000 : ℝ)*x 0 + (5526287851/10000000000 : ℝ)*x 1 + (-749898157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5262929443/10000000000 : ℝ)^4755 ≤ (22064110884803/50000000000000 : ℝ)^3731 := by
    have hnat : (5262929443 : ℕ)^4755*50000000000000^3731 ≤ 22064110884803^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262929443 10000000000 22064110884803 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5526287851/10000000000 : ℝ)^4755 ≤ (46961559432833/100000000000000 : ℝ)^3731 := by
    have hnat : (5526287851 : ℕ)^4755*100000000000000^3731 ≤ 46961559432833^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526287851 10000000000 46961559432833 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (749898157/5000000000 : ℝ)^4755 ≤ (8910218782123/100000000000000 : ℝ)^3731 := by
    have hnat : (749898157 : ℕ)^4755*100000000000000^3731 ≤ 8910218782123^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749898157 5000000000 8910218782123 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5262929443/10000000000 : ℝ), (5526287851/10000000000 : ℝ), (-749898157/5000000000 : ℝ)] ![(22064110884803/50000000000000 : ℝ), (46961559432833/100000000000000 : ℝ), (8910218782123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5262929443/10000000000 : ℝ)|^4755 ≤ (22064110884803/50000000000000 : ℝ)^3731
        have hw : |(5262929443/10000000000 : ℝ)|=(5262929443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5526287851/10000000000 : ℝ)|^4755 ≤ (46961559432833/100000000000000 : ℝ)^3731
        have hw : |(5526287851/10000000000 : ℝ)|=(5526287851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-749898157/5000000000 : ℝ)|^4755 ≤ (8910218782123/100000000000000 : ℝ)^3731
        have hw : |(-749898157/5000000000 : ℝ)|=(749898157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s1_7 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050644437/2500000000 : ℝ)*x 0 + (4718677319/10000000000 : ℝ)*x 1 + (3732098849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050644437/2500000000 : ℝ)^4755 ≤ (33127367572247/100000000000000 : ℝ)^3731 := by
    have hnat : (1050644437 : ℕ)^4755*100000000000000^3731 ≤ 33127367572247^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050644437 2500000000 33127367572247 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4718677319/10000000000 : ℝ)^4755 ≤ (38397052764643/100000000000000 : ℝ)^3731 := by
    have hnat : (4718677319 : ℕ)^4755*100000000000000^3731 ≤ 38397052764643^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4718677319 10000000000 38397052764643 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3732098849/10000000000 : ℝ)^4755 ≤ (14237789825969/50000000000000 : ℝ)^3731 := by
    have hnat : (3732098849 : ℕ)^4755*50000000000000^3731 ≤ 14237789825969^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732098849 10000000000 14237789825969 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050644437/2500000000 : ℝ), (4718677319/10000000000 : ℝ), (3732098849/10000000000 : ℝ)] ![(33127367572247/100000000000000 : ℝ), (38397052764643/100000000000000 : ℝ), (14237789825969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050644437/2500000000 : ℝ)|^4755 ≤ (33127367572247/100000000000000 : ℝ)^3731
        have hw : |(1050644437/2500000000 : ℝ)|=(1050644437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4718677319/10000000000 : ℝ)|^4755 ≤ (38397052764643/100000000000000 : ℝ)^3731
        have hw : |(4718677319/10000000000 : ℝ)|=(4718677319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3732098849/10000000000 : ℝ)|^4755 ≤ (14237789825969/50000000000000 : ℝ)^3731
        have hw : |(3732098849/10000000000 : ℝ)|=(3732098849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1609_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4853/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9113/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17823/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4853/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4853/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4853/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4853/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4853/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4853/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4001/100000 : ℝ) ^ (4751/1024 : ℝ) ≤ (32700433010951/100000000000000000000 : ℝ) := by
    have hpowers : (4001/100000 : ℝ)^4751 ≤ (32700433010951/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4001 : ℕ)^4751*100000000000000000000^1024 ≤ 32700433010951^1024*100000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001 100000 32700433010951 100000000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4001/100000 : ℝ)) (X := (32700433010951/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4853/20000 : ℝ) ^ (4751/1024 : ℝ) ≤ (140127956820426677/100000000000000000000 : ℝ) := by
    have hpowers : (4853/20000 : ℝ)^4751 ≤ (140127956820426677/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4853 : ℕ)^4751*100000000000000000000^1024 ≤ 140127956820426677^1024*20000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4853 20000 140127956820426677 100000000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4853/20000 : ℝ)) (X := (140127956820426677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000032700433010951/50000000000000000000 : ℝ) ≤ (2000000281921573/2000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (50000032700433010951/50000000000000000000 : ℝ)^1024 ≤ (2000000281921573/2000000000000000 : ℝ)^4751 := by
      have hnat : (50000032700433010951 : ℕ)^1024*2000000000000000^4751 ≤ 2000000281921573^4751*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000032700433010951 50000000000000000000 2000000281921573 2000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000281921573/2000000000000000 : ℝ)) (X := (50000032700433010951/50000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25035040164313359407/25000000000000000000 : ℝ) ≤ (5001509636657443/5000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (25035040164313359407/25000000000000000000 : ℝ)^1024 ≤ (5001509636657443/5000000000000000 : ℝ)^4751 := by
      have hnat : (25035040164313359407 : ℕ)^1024*5000000000000000^4751 ≤ 5001509636657443^4751*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25035040164313359407 25000000000000000000 5001509636657443 5000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001509636657443/5000000000000000 : ℝ)) (X := (25035040164313359407/25000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50140127956820426677/50000000000000000000 : ℝ) ≤ (10006037137021907/10000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (50140127956820426677/50000000000000000000 : ℝ)^1024 ≤ (10006037137021907/10000000000000000 : ℝ)^4751 := by
      have hnat : (50140127956820426677 : ℕ)^1024*10000000000000000^4751 ≤ 10006037137021907^4751*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50140127956820426677 50000000000000000000 10006037137021907 10000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006037137021907/10000000000000000 : ℝ)) (X := (50140127956820426677/50000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(32700433010951/100000000000000000000 : ℝ) ≤ ((101307939809455097159/101320000000000000000 : ℝ)+2*(3017863707021/2026400000000000 : ℝ)*(4001/100000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (101307939809455097159/101320000000000000000 : ℝ)+2*(3017863707021/2026400000000000 : ℝ)*(4001/100000 : ℝ)=(2000000281921573/2000000000000000 : ℝ) by norm_num, show 1+2*(32700433010951/100000000000000000000 : ℝ)=(50000032700433010951/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(140127956820426677/100000000000000000000 : ℝ)+(32700433010951/100000000000000000000 : ℝ) ≤ ((101307939809455097159/101320000000000000000 : ℝ)+(3017863707021/2026400000000000 : ℝ)*((4853/20000 : ℝ)+(4001/100000 : ℝ)))^(4751/1024 : ℝ) := by
    rw [show (101307939809455097159/101320000000000000000 : ℝ)+(3017863707021/2026400000000000 : ℝ)*((4853/20000 : ℝ)+(4001/100000 : ℝ))=(5001509636657443/5000000000000000 : ℝ) by norm_num, show 1+(140127956820426677/100000000000000000000 : ℝ)+(32700433010951/100000000000000000000 : ℝ)=(25035040164313359407/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(140127956820426677/100000000000000000000 : ℝ) ≤ ((101307939809455097159/101320000000000000000 : ℝ)+2*(3017863707021/2026400000000000 : ℝ)*(4853/20000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (101307939809455097159/101320000000000000000 : ℝ)+2*(3017863707021/2026400000000000 : ℝ)*(4853/20000 : ℝ)=(10006037137021907/10000000000000000 : ℝ) by norm_num, show 1+2*(140127956820426677/100000000000000000000 : ℝ)=(50140127956820426677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (101307939809455097159/101320000000000000000 : ℝ)*(X 1 0+X 2 0)+(3017863707021/2026400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (4001/100000 : ℝ)) (hi := (4853/20000 : ℝ)) (c := (101307939809455097159/101320000000000000000 : ℝ)) (alpha := (3017863707021/2026400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (101307939809455097159/101320000000000000000 : ℝ)*(X 0 1+X 2 1)+(3017863707021/2026400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (4001/100000 : ℝ)) (hi := (4853/20000 : ℝ)) (c := (101307939809455097159/101320000000000000000 : ℝ)) (alpha := (3017863707021/2026400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (101307939809455097159/101320000000000000000 : ℝ)*(X 0 2+X 1 2)+(3017863707021/2026400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (4001/100000 : ℝ)) (hi := (4853/20000 : ℝ)) (c := (101307939809455097159/101320000000000000000 : ℝ)) (alpha := (3017863707021/2026400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-84564117/500000000 : ℝ)*X 0 0+(2765419151/5000000000 : ℝ)*X 0 1+(2559897707/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074452361/2000000000 : ℝ)*X 1 0+(-381257613/2000000000 : ℝ)*X 1 1+(5119795269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671532689/1250000000 : ℝ)*X 2 0+(5119795503/10000000000 : ℝ)*X 2 1+(-476572037/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4202027093/10000000000 : ℝ)*X 0 0+(744186247/2000000000 : ℝ)*X 0 1+(945934851/2000000000 : ℝ)*X 0 2+(4202027093/10000000000 : ℝ)*X 1 0+(744186247/2000000000 : ℝ)*X 1 1+(945934851/2000000000 : ℝ)*X 1 2+(4202027093/10000000000 : ℝ)*X 2 0+(744186247/2000000000 : ℝ)*X 2 1+(945934851/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-422876803/2500000000 : ℝ)*X 0 0+(5124276929/10000000000 : ℝ)*X 0 1+(1105257457/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1315732519/2500000000 : ℝ)*X 1 0+(-1499795763/10000000000 : ℝ)*X 1 1+(5526287611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5262929443/10000000000 : ℝ)*X 2 0+(5526287851/10000000000 : ℝ)*X 2 1+(-749898157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1050644437/2500000000 : ℝ)*X 0 0+(4718677319/10000000000 : ℝ)*X 0 1+(3732098849/10000000000 : ℝ)*X 0 2+(1050644437/2500000000 : ℝ)*X 1 0+(4718677319/10000000000 : ℝ)*X 1 1+(3732098849/10000000000 : ℝ)*X 1 2+(1050644437/2500000000 : ℝ)*X 2 0+(4718677319/10000000000 : ℝ)*X 2 1+(3732098849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100204256915621347967729169/29800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (96673797/100000000000000 : ℝ)*(base1) + (447538653/50000000000000 : ℝ)*(base19) + (762391187/100000000000000 : ℝ)*(base23) + (115123611/100000000000000 : ℝ)*(upper3) + (44731679/100000000000000 : ℝ)*(upper5) + (171209381274817/10000000000000 : ℝ)*(major0) + (171209381274817/10000000000000 : ℝ)*(major1) + (171209381274817/10000000000000 : ℝ)*(major2) + (1216421689750043/50000000000000 : ℝ)*(sp0) + (12164241080917/500000000000 : ℝ)*(sp1) + (2432848348869519/100000000000000 : ℝ)*(sp2) + (991335376042329/100000000000000 : ℝ)*(sp3) + (5828434417/100000000000000 : ℝ)*(sp4) + (14647171/500000000000 : ℝ)*(sp7) + (123917300268791/12500000000000 : ℝ)*(f.failure) + (1216424555630353/50000000000000 : ℝ)*(f.sum) + (26307524859161/10132000000000000000000000000 : ℝ)*base65 + (12502572375186794903/1013200000000000000000000000000000 : ℝ)*base67 + (6266575962821994903/1013200000000000000000000000000000 : ℝ)*base69 + (7107664638322394903/1013200000000000000000000000000000 : ℝ)*base71 + (64689257604977/10132000000000000000000000000 : ℝ)*base73 + (7768704588628794903/1013200000000000000000000000000000 : ℝ)*base75 + (4130259182712794903/1013200000000000000000000000000000 : ℝ)*base77 + (6396812662452394903/1013200000000000000000000000000000 : ℝ)*base79 + (7903655395601/10132000000000000000000000000 : ℝ)*base81 + (252087/250000000000000000000 : ℝ)*base89 + (252087/250000000000000000000 : ℝ)*base91 + (252087/250000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (334738898478450394849036881/39578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (847433171/50000000000000 : ℝ)*(base19) + (721947829/50000000000000 : ℝ)*(base23) + (35578199/100000000000000 : ℝ)*(upper2) + (317542591/100000000000000 : ℝ)*(upper3) + (106238691/100000000000000 : ℝ)*(upper5) + (6838082757087/390625000000 : ℝ)*(major0) + (6838082757087/390625000000 : ℝ)*(major1) + (6838082757087/390625000000 : ℝ)*(major2) + (50141641/390625000000 : ℝ)*(sp1) + (11902908781/100000000000000 : ℝ)*(sp2) + (2487493216054229/100000000000000 : ℝ)*(sp4) + (248747868492779/10000000000000 : ℝ)*(sp5) + (2487479869249789/100000000000000 : ℝ)*(sp6) + (63350304603239/6250000000000 : ℝ)*(sp7) + (63350304603239/6250000000000 : ℝ)*(f.failure) + (2487493216054229/100000000000000 : ℝ)*(f.sum) + (10154871971951/3166250000000000000000000000 : ℝ)*base65 + (22755528551596901/4947265625000000000000000000000 : ℝ)*base67 + (56350850087365677/9894531250000000000000000000000 : ℝ)*base69 + (183892721772540833/39578125000000000000000000000000 : ℝ)*base71 + (20616310939563/6332500000000000000000000000 : ℝ)*base74 + (388951403603884583/39578125000000000000000000000000 : ℝ)*base75 + (226568798721371979/19789062500000000000000000000000 : ℝ)*base77 + (223979525969759583/39578125000000000000000000000000 : ℝ)*base79 + (22997162469733/6332500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (683623/125000000000000000000 : ℝ)*base89 + (683623/125000000000000000000 : ℝ)*base91 + (683623/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1609_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4853/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9113/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17823/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1609_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1609_s2_0 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-5329137/31250000 : ℝ)*x 0 + (5467160441/10000000000 : ℝ)*x 1 + (1034856483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5329137/31250000 : ℝ)^4755 ≤ (16397993641/156250000000 : ℝ)^3731 := by
    have hnat : (5329137 : ℕ)^4755*156250000000^3731 ≤ 16397993641^3731*31250000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5329137 31250000 16397993641 156250000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467160441/10000000000 : ℝ)^4755 ≤ (23161071823631/50000000000000 : ℝ)^3731 := by
    have hnat : (5467160441 : ℕ)^4755*50000000000000^3731 ≤ 23161071823631^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467160441 10000000000 23161071823631 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034856483/2000000000 : ℝ)^4755 ≤ (21591570204263/50000000000000 : ℝ)^3731 := by
    have hnat : (1034856483 : ℕ)^4755*50000000000000^3731 ≤ 21591570204263^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034856483 2000000000 21591570204263 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5329137/31250000 : ℝ), (5467160441/10000000000 : ℝ), (1034856483/2000000000 : ℝ)] ![(16397993641/156250000000 : ℝ), (23161071823631/50000000000000 : ℝ), (21591570204263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5329137/31250000 : ℝ)|^4755 ≤ (16397993641/156250000000 : ℝ)^3731
        have hw : |(-5329137/31250000 : ℝ)|=(5329137/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467160441/10000000000 : ℝ)|^4755 ≤ (23161071823631/50000000000000 : ℝ)^3731
        have hw : |(5467160441/10000000000 : ℝ)|=(5467160441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034856483/2000000000 : ℝ)|^4755 ≤ (21591570204263/50000000000000 : ℝ)^3731
        have hw : |(1034856483/2000000000 : ℝ)|=(1034856483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s2_1 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677837741/5000000000 : ℝ)*x 0 + (-1856579119/10000000000 : ℝ)*x 1 + (2587141139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677837741/5000000000 : ℝ)^4755 ≤ (45121690226967/100000000000000 : ℝ)^3731 := by
    have hnat : (2677837741 : ℕ)^4755*100000000000000^3731 ≤ 45121690226967^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677837741 5000000000 45121690226967 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1856579119/10000000000 : ℝ)^4755 ≤ (11695170814037/100000000000000 : ℝ)^3731 := by
    have hnat : (1856579119 : ℕ)^4755*100000000000000^3731 ≤ 11695170814037^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856579119 10000000000 11695170814037 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587141139/5000000000 : ℝ)^4755 ≤ (43183138951357/100000000000000 : ℝ)^3731 := by
    have hnat : (2587141139 : ℕ)^4755*100000000000000^3731 ≤ 43183138951357^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587141139 5000000000 43183138951357 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677837741/5000000000 : ℝ), (-1856579119/10000000000 : ℝ), (2587141139/5000000000 : ℝ)] ![(45121690226967/100000000000000 : ℝ), (11695170814037/100000000000000 : ℝ), (43183138951357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677837741/5000000000 : ℝ)|^4755 ≤ (45121690226967/100000000000000 : ℝ)^3731
        have hw : |(2677837741/5000000000 : ℝ)|=(2677837741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1856579119/10000000000 : ℝ)|^4755 ≤ (11695170814037/100000000000000 : ℝ)^3731
        have hw : |(-1856579119/10000000000 : ℝ)|=(1856579119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587141139/5000000000 : ℝ)|^4755 ≤ (43183138951357/100000000000000 : ℝ)^3731
        have hw : |(2587141139/5000000000 : ℝ)|=(2587141139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s2_2 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338918847/2500000000 : ℝ)*x 0 + (129357059/250000000 : ℝ)*x 1 + (-29009049/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338918847/2500000000 : ℝ)^4755 ≤ (45121689217657/100000000000000 : ℝ)^3731 := by
    have hnat : (1338918847 : ℕ)^4755*100000000000000^3731 ≤ 45121689217657^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338918847 2500000000 45121689217657 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129357059/250000000 : ℝ)^4755 ≤ (43183139823531/100000000000000 : ℝ)^3731 := by
    have hnat : (129357059 : ℕ)^4755*100000000000000^3731 ≤ 43183139823531^3731*250000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129357059 250000000 43183139823531 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29009049/156250000 : ℝ)^4755 ≤ (2923792737629/25000000000000 : ℝ)^3731 := by
    have hnat : (29009049 : ℕ)^4755*25000000000000^3731 ≤ 2923792737629^3731*156250000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29009049 156250000 2923792737629 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338918847/2500000000 : ℝ), (129357059/250000000 : ℝ), (-29009049/156250000 : ℝ)] ![(45121689217657/100000000000000 : ℝ), (43183139823531/100000000000000 : ℝ), (2923792737629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338918847/2500000000 : ℝ)|^4755 ≤ (45121689217657/100000000000000 : ℝ)^3731
        have hw : |(1338918847/2500000000 : ℝ)|=(1338918847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129357059/250000000 : ℝ)|^4755 ≤ (43183139823531/100000000000000 : ℝ)^3731
        have hw : |(129357059/250000000 : ℝ)|=(129357059/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29009049/156250000 : ℝ)|^4755 ≤ (2923792737629/25000000000000 : ℝ)^3731
        have hw : |(-29009049/156250000 : ℝ)|=(29009049/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s2_3 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4212385563/10000000000 : ℝ)*x 0 + (3864828627/10000000000 : ℝ)*x 1 + (4583582237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4212385563/10000000000 : ℝ)^4755 ≤ (16612964580279/50000000000000 : ℝ)^3731 := by
    have hnat : (4212385563 : ℕ)^4755*50000000000000^3731 ≤ 16612964580279^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212385563 10000000000 16612964580279 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3864828627/10000000000 : ℝ)^4755 ≤ (29772488949311/100000000000000 : ℝ)^3731 := by
    have hnat : (3864828627 : ℕ)^4755*100000000000000^3731 ≤ 29772488949311^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3864828627 10000000000 29772488949311 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4583582237/10000000000 : ℝ)^4755 ≤ (18500790939889/50000000000000 : ℝ)^3731 := by
    have hnat : (4583582237 : ℕ)^4755*50000000000000^3731 ≤ 18500790939889^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4583582237 10000000000 18500790939889 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4212385563/10000000000 : ℝ), (3864828627/10000000000 : ℝ), (4583582237/10000000000 : ℝ)] ![(16612964580279/50000000000000 : ℝ), (29772488949311/100000000000000 : ℝ), (18500790939889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4212385563/10000000000 : ℝ)|^4755 ≤ (16612964580279/50000000000000 : ℝ)^3731
        have hw : |(4212385563/10000000000 : ℝ)|=(4212385563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3864828627/10000000000 : ℝ)|^4755 ≤ (29772488949311/100000000000000 : ℝ)^3731
        have hw : |(3864828627/10000000000 : ℝ)|=(3864828627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4583582237/10000000000 : ℝ)|^4755 ≤ (18500790939889/50000000000000 : ℝ)^3731
        have hw : |(4583582237/10000000000 : ℝ)|=(4583582237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s2_4 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1705404917/10000000000 : ℝ)*x 0 + (5176564981/10000000000 : ℝ)*x 1 + (1366213237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1705404917/10000000000 : ℝ)^4755 ≤ (655959489461/6250000000000 : ℝ)^3731 := by
    have hnat : (1705404917 : ℕ)^4755*6250000000000^3731 ≤ 655959489461^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705404917 10000000000 655959489461 6250000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176564981/10000000000 : ℝ)^4755 ≤ (43207419867029/100000000000000 : ℝ)^3731 := by
    have hnat : (5176564981 : ℕ)^4755*100000000000000^3731 ≤ 43207419867029^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176564981 10000000000 43207419867029 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366213237/2500000000 : ℝ)^4755 ≤ (46297228277481/100000000000000 : ℝ)^3731 := by
    have hnat : (1366213237 : ℕ)^4755*100000000000000^3731 ≤ 46297228277481^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366213237 2500000000 46297228277481 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1705404917/10000000000 : ℝ), (5176564981/10000000000 : ℝ), (1366213237/2500000000 : ℝ)] ![(655959489461/6250000000000 : ℝ), (43207419867029/100000000000000 : ℝ), (46297228277481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1705404917/10000000000 : ℝ)|^4755 ≤ (655959489461/6250000000000 : ℝ)^3731
        have hw : |(-1705404917/10000000000 : ℝ)|=(1705404917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176564981/10000000000 : ℝ)|^4755 ≤ (43207419867029/100000000000000 : ℝ)^3731
        have hw : |(5176564981/10000000000 : ℝ)|=(5176564981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366213237/2500000000 : ℝ)|^4755 ≤ (46297228277481/100000000000000 : ℝ)^3731
        have hw : |(1366213237/2500000000 : ℝ)|=(1366213237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s2_5 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277896381/10000000000 : ℝ)*x 0 + (-783004293/5000000000 : ℝ)*x 1 + (5464853091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277896381/10000000000 : ℝ)^4755 ≤ (44288220467393/100000000000000 : ℝ)^3731 := by
    have hnat : (5277896381 : ℕ)^4755*100000000000000^3731 ≤ 44288220467393^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277896381 10000000000 44288220467393 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (783004293/5000000000 : ℝ)^4755 ≤ (9414549700203/100000000000000 : ℝ)^3731 := by
    have hnat : (783004293 : ℕ)^4755*100000000000000^3731 ≤ 9414549700203^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783004293 5000000000 9414549700203 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5464853091/10000000000 : ℝ)^4755 ≤ (5787153727681/12500000000000 : ℝ)^3731 := by
    have hnat : (5464853091 : ℕ)^4755*12500000000000^3731 ≤ 5787153727681^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464853091 10000000000 5787153727681 12500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277896381/10000000000 : ℝ), (-783004293/5000000000 : ℝ), (5464853091/10000000000 : ℝ)] ![(44288220467393/100000000000000 : ℝ), (9414549700203/100000000000000 : ℝ), (5787153727681/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277896381/10000000000 : ℝ)|^4755 ≤ (44288220467393/100000000000000 : ℝ)^3731
        have hw : |(5277896381/10000000000 : ℝ)|=(5277896381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-783004293/5000000000 : ℝ)|^4755 ≤ (9414549700203/100000000000000 : ℝ)^3731
        have hw : |(-783004293/5000000000 : ℝ)|=(783004293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5464853091/10000000000 : ℝ)|^4755 ≤ (5787153727681/12500000000000 : ℝ)^3731
        have hw : |(5464853091/10000000000 : ℝ)|=(5464853091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s2_6 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277896697/10000000000 : ℝ)*x 0 + (5464852497/10000000000 : ℝ)*x 1 + (-1566008981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277896697/10000000000 : ℝ)^4755 ≤ (22144111923397/50000000000000 : ℝ)^3731 := by
    have hnat : (5277896697 : ℕ)^4755*50000000000000^3731 ≤ 22144111923397^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277896697 10000000000 22144111923397 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464852497/10000000000 : ℝ)^4755 ≤ (46297223408049/100000000000000 : ℝ)^3731 := by
    have hnat : (5464852497 : ℕ)^4755*100000000000000^3731 ≤ 46297223408049^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464852497 10000000000 46297223408049 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1566008981/10000000000 : ℝ)^4755 ≤ (9414552726613/100000000000000 : ℝ)^3731 := by
    have hnat : (1566008981 : ℕ)^4755*100000000000000^3731 ≤ 9414552726613^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566008981 10000000000 9414552726613 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277896697/10000000000 : ℝ), (5464852497/10000000000 : ℝ), (-1566008981/10000000000 : ℝ)] ![(22144111923397/50000000000000 : ℝ), (46297223408049/100000000000000 : ℝ), (9414552726613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277896697/10000000000 : ℝ)|^4755 ≤ (22144111923397/50000000000000 : ℝ)^3731
        have hw : |(5277896697/10000000000 : ℝ)|=(5277896697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464852497/10000000000 : ℝ)|^4755 ≤ (46297223408049/100000000000000 : ℝ)^3731
        have hw : |(5464852497/10000000000 : ℝ)|=(5464852497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1566008981/10000000000 : ℝ)|^4755 ≤ (9414552726613/100000000000000 : ℝ)^3731
        have hw : |(-1566008981/10000000000 : ℝ)|=(1566008981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s2_7 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4212585349/10000000000 : ℝ)*x 0 + (2288990477/5000000000 : ℝ)*x 1 + (241905729/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4212585349/10000000000 : ℝ)^4755 ≤ (8306984380841/25000000000000 : ℝ)^3731 := by
    have hnat : (4212585349 : ℕ)^4755*25000000000000^3731 ≤ 8306984380841^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212585349 10000000000 8306984380841 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2288990477/5000000000 : ℝ)^4755 ≤ (36943964275893/100000000000000 : ℝ)^3731 := by
    have hnat : (2288990477 : ℕ)^4755*100000000000000^3731 ≤ 36943964275893^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288990477 5000000000 36943964275893 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241905729/625000000 : ℝ)^4755 ≤ (5965619635309/20000000000000 : ℝ)^3731 := by
    have hnat : (241905729 : ℕ)^4755*20000000000000^3731 ≤ 5965619635309^3731*625000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241905729 625000000 5965619635309 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4212585349/10000000000 : ℝ), (2288990477/5000000000 : ℝ), (241905729/625000000 : ℝ)] ![(8306984380841/25000000000000 : ℝ), (36943964275893/100000000000000 : ℝ), (5965619635309/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4212585349/10000000000 : ℝ)|^4755 ≤ (8306984380841/25000000000000 : ℝ)^3731
        have hw : |(4212585349/10000000000 : ℝ)|=(4212585349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2288990477/5000000000 : ℝ)|^4755 ≤ (36943964275893/100000000000000 : ℝ)^3731
        have hw : |(2288990477/5000000000 : ℝ)|=(2288990477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(241905729/625000000 : ℝ)|^4755 ≤ (5965619635309/20000000000000 : ℝ)^3731
        have hw : |(241905729/625000000 : ℝ)|=(241905729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1609_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17823/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9113/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10289/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8249/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17823/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9113/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17823/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9113/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17823/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9113/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17823/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9113/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17823/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9113/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17823/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9113/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9113/100000 : ℝ) ^ (4751/1024 : ℝ) ≤ (186253531111703/12500000000000000000 : ℝ) := by
    have hpowers : (9113/100000 : ℝ)^4751 ≤ (186253531111703/12500000000000000000 : ℝ)^1024 := by
      have hnat : (9113 : ℕ)^4751*12500000000000000000^1024 ≤ 186253531111703^1024*100000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9113 100000 186253531111703 12500000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9113/100000 : ℝ)) (X := (186253531111703/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17823/100000 : ℝ) ^ (4751/1024 : ℝ) ≤ (6696444405772911/20000000000000000000 : ℝ) := by
    have hpowers : (17823/100000 : ℝ)^4751 ≤ (6696444405772911/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17823 : ℕ)^4751*20000000000000000000^1024 ≤ 6696444405772911^1024*100000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17823 100000 6696444405772911 20000000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17823/100000 : ℝ)) (X := (6696444405772911/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250186253531111703/6250000000000000000 : ℝ) ≤ (10000064229471379/10000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (6250186253531111703/6250000000000000000 : ℝ)^1024 ≤ (10000064229471379/10000000000000000 : ℝ)^4751 := by
      have hnat : (6250186253531111703 : ℕ)^1024*10000000000000000^4751 ≤ 10000064229471379^4751*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250186253531111703 6250000000000000000 10000064229471379 10000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000064229471379/10000000000000000 : ℝ)) (X := (6250186253531111703/6250000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034972250277758179/100000000000000000000 : ℝ) ≤ (5000376833013381/5000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (100034972250277758179/100000000000000000000 : ℝ)^1024 ≤ (5000376833013381/5000000000000000 : ℝ)^4751 := by
      have hnat : (100034972250277758179 : ℕ)^1024*5000000000000000^4751 ≤ 5000376833013381^4751*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034972250277758179 100000000000000000000 5000376833013381 5000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000376833013381/5000000000000000 : ℝ)) (X := (100034972250277758179/100000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006696444405772911/10000000000000000000 : ℝ) ≤ (2000288620516429/2000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (10006696444405772911/10000000000000000000 : ℝ)^1024 ≤ (2000288620516429/2000000000000000 : ℝ)^4751 := by
      have hnat : (10006696444405772911 : ℕ)^1024*2000000000000000^4751 ≤ 2000288620516429^4751*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006696444405772911 10000000000000000000 2000288620516429 2000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000288620516429/2000000000000000 : ℝ)) (X := (10006696444405772911/10000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(186253531111703/12500000000000000000 : ℝ) ≤ ((1674769110923794241/1675000000000000000 : ℝ)+2*(689436555383/871000000000000 : ℝ)*(9113/100000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (1674769110923794241/1675000000000000000 : ℝ)+2*(689436555383/871000000000000 : ℝ)*(9113/100000 : ℝ)=(10000064229471379/10000000000000000 : ℝ) by norm_num, show 1+2*(186253531111703/12500000000000000000 : ℝ)=(6250186253531111703/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6696444405772911/20000000000000000000 : ℝ)+(186253531111703/12500000000000000000 : ℝ) ≤ ((1674769110923794241/1675000000000000000 : ℝ)+(689436555383/871000000000000 : ℝ)*((17823/100000 : ℝ)+(9113/100000 : ℝ)))^(4751/1024 : ℝ) := by
    rw [show (1674769110923794241/1675000000000000000 : ℝ)+(689436555383/871000000000000 : ℝ)*((17823/100000 : ℝ)+(9113/100000 : ℝ))=(5000376833013381/5000000000000000 : ℝ) by norm_num, show 1+(6696444405772911/20000000000000000000 : ℝ)+(186253531111703/12500000000000000000 : ℝ)=(100034972250277758179/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6696444405772911/20000000000000000000 : ℝ) ≤ ((1674769110923794241/1675000000000000000 : ℝ)+2*(689436555383/871000000000000 : ℝ)*(17823/100000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (1674769110923794241/1675000000000000000 : ℝ)+2*(689436555383/871000000000000 : ℝ)*(17823/100000 : ℝ)=(2000288620516429/2000000000000000 : ℝ) by norm_num, show 1+2*(6696444405772911/20000000000000000000 : ℝ)=(10006696444405772911/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1674769110923794241/1675000000000000000 : ℝ)*(X 1 0+X 2 0)+(689436555383/871000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (9113/100000 : ℝ)) (hi := (17823/100000 : ℝ)) (c := (1674769110923794241/1675000000000000000 : ℝ)) (alpha := (689436555383/871000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1674769110923794241/1675000000000000000 : ℝ)*(X 0 1+X 2 1)+(689436555383/871000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (9113/100000 : ℝ)) (hi := (17823/100000 : ℝ)) (c := (1674769110923794241/1675000000000000000 : ℝ)) (alpha := (689436555383/871000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1674769110923794241/1675000000000000000 : ℝ)*(X 0 2+X 1 2)+(689436555383/871000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (9113/100000 : ℝ)) (hi := (17823/100000 : ℝ)) (c := (1674769110923794241/1675000000000000000 : ℝ)) (alpha := (689436555383/871000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-5329137/31250000 : ℝ)*X 0 0+(5467160441/10000000000 : ℝ)*X 0 1+(1034856483/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677837741/5000000000 : ℝ)*X 1 0+(-1856579119/10000000000 : ℝ)*X 1 1+(2587141139/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338918847/2500000000 : ℝ)*X 2 0+(129357059/250000000 : ℝ)*X 2 1+(-29009049/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4212385563/10000000000 : ℝ)*X 0 0+(3864828627/10000000000 : ℝ)*X 0 1+(4583582237/10000000000 : ℝ)*X 0 2+(4212385563/10000000000 : ℝ)*X 1 0+(3864828627/10000000000 : ℝ)*X 1 1+(4583582237/10000000000 : ℝ)*X 1 2+(4212385563/10000000000 : ℝ)*X 2 0+(3864828627/10000000000 : ℝ)*X 2 1+(4583582237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1705404917/10000000000 : ℝ)*X 0 0+(5176564981/10000000000 : ℝ)*X 0 1+(1366213237/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277896381/10000000000 : ℝ)*X 1 0+(-783004293/5000000000 : ℝ)*X 1 1+(5464853091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277896697/10000000000 : ℝ)*X 2 0+(5464852497/10000000000 : ℝ)*X 2 1+(-1566008981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4212585349/10000000000 : ℝ)*X 0 0+(2288990477/5000000000 : ℝ)*X 0 1+(241905729/625000000 : ℝ)*X 0 2+(4212585349/10000000000 : ℝ)*X 1 0+(2288990477/5000000000 : ℝ)*X 1 1+(241905729/625000000 : ℝ)*X 1 2+(4212585349/10000000000 : ℝ)*X 2 0+(2288990477/5000000000 : ℝ)*X 2 1+(241905729/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49346876463434735234421/4355000000000000000000000000 : ℝ) := by norm_num
    linear_combination (417459789/20000000000000 : ℝ)*(base19) + (61448643/3125000000000 : ℝ)*(base23) + (3267711/10000000000000 : ℝ)*(lower2) + (7161899/2500000000000 : ℝ)*(upper3) + (218761657/100000000000000 : ℝ)*(upper5) + (240287754948793/10000000000000 : ℝ)*(major0) + (240287754948793/10000000000000 : ℝ)*(major1) + (240287754948793/10000000000000 : ℝ)*(major2) + (1707207390020681/50000000000000 : ℝ)*(sp0) + (1707217944549867/50000000000000 : ℝ)*(sp1) + (426804501255263/12500000000000 : ℝ)*(sp2) + (139130669918687/10000000000000 : ℝ)*(sp3) + (23196357317/100000000000000 : ℝ)*(sp4) + (5022843729/50000000000000 : ℝ)*(sp7) + (1391316744874327/100000000000000 : ℝ)*(f.failure) + (85360949409967/2500000000000 : ℝ)*(f.sum) + (1253285301373/2177500000000000000000000000 : ℝ)*base66 + (945317098706860531/217750000000000000000000000000000 : ℝ)*base68 + (68060924981110531/217750000000000000000000000000000 : ℝ)*base70 + (1045385323660889469/217750000000000000000000000000000 : ℝ)*base71 + (19842672368261/4355000000000000000000000000 : ℝ)*base74 + (373395777387389469/217750000000000000000000000000000 : ℝ)*base75 + (871182152349889469/217750000000000000000000000000000 : ℝ)*base77 + (2462818769479610531/217750000000000000000000000000000 : ℝ)*base80 + (14354013965371/4355000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (13256361/2000000000000000000000 : ℝ)*base90 + (13256361/2000000000000000000000 : ℝ)*base92 + (13256361/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4086445330937100550136014119/544375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (401127143/50000000000000 : ℝ)*(base19) + (1226464791/100000000000000 : ℝ)*(base23) + (122185479/100000000000000 : ℝ)*(upper3) + (125543447/100000000000000 : ℝ)*(lower4) + (108145263/100000000000000 : ℝ)*(upper5) + (1220550349300573/50000000000000 : ℝ)*(major0) + (1220550349300573/50000000000000 : ℝ)*(major1) + (1220550349300573/50000000000000 : ℝ)*(major2) + (10023435687/100000000000000 : ℝ)*(sp1) + (8575524457/100000000000000 : ℝ)*(sp2) + (693750478633429/20000000000000 : ℝ)*(sp4) + (3468741567477173/100000000000000 : ℝ)*(sp5) + (1734371295588949/50000000000000 : ℝ)*(sp6) + (353362188453171/25000000000000 : ℝ)*(sp7) + (353362188453171/25000000000000 : ℝ)*(f.failure) + (693750478633429/20000000000000 : ℝ)*(f.sum) + (19019229715717/10887500000000000000000000000 : ℝ)*base65 + (11421004169597926209/1088750000000000000000000000000000 : ℝ)*base67 + (10816758964966676209/1088750000000000000000000000000000 : ℝ)*base69 + (7115396421695426209/1088750000000000000000000000000000 : ℝ)*base71 + (5810680842573/2721875000000000000000000000 : ℝ)*base73 + (14684158718342926209/1088750000000000000000000000000000 : ℝ)*base75 + (7339646068664176209/1088750000000000000000000000000000 : ℝ)*base77 + (5788420737034176209/1088750000000000000000000000000000 : ℝ)*base79 + (23755794136809/21775000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8658253/500000000000000000000 : ℝ)*base90 + (8658253/500000000000000000000 : ℝ)*base92 + (8658253/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1609_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17823/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9113/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10289/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8249/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1609_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1609_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10289/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8249/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1609_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1609_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1609_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10289/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8249/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1609_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
