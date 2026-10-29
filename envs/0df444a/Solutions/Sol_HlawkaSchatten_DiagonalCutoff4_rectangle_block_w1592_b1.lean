-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1592_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:04.87416+00:00
-- url     : https://prove2.me/submissions/ca896870-bb22-4a7d-b842-4b66805b8b83

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
theorem support_rectangle_w1592_s3_0 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1750468029/10000000000 : ℝ)*x 0 + (5465982943/10000000000 : ℝ)*x 1 + (5178069013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1750468029/10000000000 : ℝ)^4687 ≤ (10754152970419/100000000000000 : ℝ)^3663 := by
    have hnat : (1750468029 : ℕ)^4687*100000000000000^3663 ≤ 10754152970419^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1750468029 10000000000 10754152970419 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465982943/10000000000 : ℝ)^4687 ≤ (180340335907/390625000000 : ℝ)^3663 := by
    have hnat : (5465982943 : ℕ)^4687*390625000000^3663 ≤ 180340335907^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465982943 10000000000 180340335907 390625000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178069013/10000000000 : ℝ)^4687 ≤ (43078721023389/100000000000000 : ℝ)^3663 := by
    have hnat : (5178069013 : ℕ)^4687*100000000000000^3663 ≤ 43078721023389^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178069013 10000000000 43078721023389 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1750468029/10000000000 : ℝ), (5465982943/10000000000 : ℝ), (5178069013/10000000000 : ℝ)] ![(10754152970419/100000000000000 : ℝ), (180340335907/390625000000 : ℝ), (43078721023389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1750468029/10000000000 : ℝ)|^4687 ≤ (10754152970419/100000000000000 : ℝ)^3663
        have hw : |(-1750468029/10000000000 : ℝ)|=(1750468029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465982943/10000000000 : ℝ)|^4687 ≤ (180340335907/390625000000 : ℝ)^3663
        have hw : |(5465982943/10000000000 : ℝ)|=(5465982943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178069013/10000000000 : ℝ)|^4687 ≤ (43078721023389/100000000000000 : ℝ)^3663
        have hw : |(5178069013/10000000000 : ℝ)|=(5178069013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s3_1 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356318657/10000000000 : ℝ)*x 0 + (-474770443/2500000000 : ℝ)*x 1 + (5178069029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356318657/10000000000 : ℝ)^4687 ≤ (5623159531727/12500000000000 : ℝ)^3663 := by
    have hnat : (5356318657 : ℕ)^4687*12500000000000^3663 ≤ 5623159531727^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356318657 10000000000 5623159531727 12500000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474770443/2500000000 : ℝ)^4687 ≤ (11936002534131/100000000000000 : ℝ)^3663 := by
    have hnat : (474770443 : ℕ)^4687*100000000000000^3663 ≤ 11936002534131^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474770443 2500000000 11936002534131 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178069029/10000000000 : ℝ)^4687 ≤ (2692420074607/6250000000000 : ℝ)^3663 := by
    have hnat : (5178069029 : ℕ)^4687*6250000000000^3663 ≤ 2692420074607^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178069029 10000000000 2692420074607 6250000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356318657/10000000000 : ℝ), (-474770443/2500000000 : ℝ), (5178069029/10000000000 : ℝ)] ![(5623159531727/12500000000000 : ℝ), (11936002534131/100000000000000 : ℝ), (2692420074607/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356318657/10000000000 : ℝ)|^4687 ≤ (5623159531727/12500000000000 : ℝ)^3663
        have hw : |(5356318657/10000000000 : ℝ)|=(5356318657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-474770443/2500000000 : ℝ)|^4687 ≤ (11936002534131/100000000000000 : ℝ)^3663
        have hw : |(-474770443/2500000000 : ℝ)|=(474770443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178069029/10000000000 : ℝ)|^4687 ≤ (2692420074607/6250000000000 : ℝ)^3663
        have hw : |(5178069029/10000000000 : ℝ)|=(5178069029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s3_2 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267815933/500000000 : ℝ)*x 0 + (1294517251/2500000000 : ℝ)*x 1 + (-1899081801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267815933/500000000 : ℝ)^4687 ≤ (5623159535757/12500000000000 : ℝ)^3663 := by
    have hnat : (267815933 : ℕ)^4687*12500000000000^3663 ≤ 5623159535757^3663*500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267815933 500000000 5623159535757 12500000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294517251/2500000000 : ℝ)^4687 ≤ (21539360463791/50000000000000 : ℝ)^3663 := by
    have hnat : (1294517251 : ℕ)^4687*50000000000000^3663 ≤ 21539360463791^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294517251 2500000000 21539360463791 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1899081801/10000000000 : ℝ)^4687 ≤ (5968001383677/50000000000000 : ℝ)^3663 := by
    have hnat : (1899081801 : ℕ)^4687*50000000000000^3663 ≤ 5968001383677^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899081801 10000000000 5968001383677 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267815933/500000000 : ℝ), (1294517251/2500000000 : ℝ), (-1899081801/10000000000 : ℝ)] ![(5623159535757/12500000000000 : ℝ), (21539360463791/50000000000000 : ℝ), (5968001383677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267815933/500000000 : ℝ)|^4687 ≤ (5623159535757/12500000000000 : ℝ)^3663
        have hw : |(267815933/500000000 : ℝ)|=(267815933/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294517251/2500000000 : ℝ)|^4687 ≤ (21539360463791/50000000000000 : ℝ)^3663
        have hw : |(1294517251/2500000000 : ℝ)|=(1294517251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1899081801/10000000000 : ℝ)|^4687 ≤ (5968001383677/50000000000000 : ℝ)^3663
        have hw : |(-1899081801/10000000000 : ℝ)|=(1899081801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s3_3 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2113756333/5000000000 : ℝ)*x 0 + (1946651759/5000000000 : ℝ)*x 1 + (1146016749/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113756333/5000000000 : ℝ)^4687 ≤ (4153996409143/12500000000000 : ℝ)^3663 := by
    have hnat : (2113756333 : ℕ)^4687*12500000000000^3663 ≤ 4153996409143^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113756333 5000000000 4153996409143 12500000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1946651759/5000000000 : ℝ)^4687 ≤ (14954117985593/50000000000000 : ℝ)^3663 := by
    have hnat : (1946651759 : ℕ)^4687*50000000000000^3663 ≤ 14954117985593^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946651759 5000000000 14954117985593 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146016749/2500000000 : ℝ)^4687 ≤ (36859792734473/100000000000000 : ℝ)^3663 := by
    have hnat : (1146016749 : ℕ)^4687*100000000000000^3663 ≤ 36859792734473^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146016749 2500000000 36859792734473 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2113756333/5000000000 : ℝ), (1946651759/5000000000 : ℝ), (1146016749/2500000000 : ℝ)] ![(4153996409143/12500000000000 : ℝ), (14954117985593/50000000000000 : ℝ), (36859792734473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2113756333/5000000000 : ℝ)|^4687 ≤ (4153996409143/12500000000000 : ℝ)^3663
        have hw : |(2113756333/5000000000 : ℝ)|=(2113756333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1946651759/5000000000 : ℝ)|^4687 ≤ (14954117985593/50000000000000 : ℝ)^3663
        have hw : |(1946651759/5000000000 : ℝ)|=(1946651759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1146016749/2500000000 : ℝ)|^4687 ≤ (36859792734473/100000000000000 : ℝ)^3663
        have hw : |(1146016749/2500000000 : ℝ)|=(1146016749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s3_4 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-875271487/5000000000 : ℝ)*x 0 + (5180204601/10000000000 : ℝ)*x 1 + (5463824663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875271487/5000000000 : ℝ)^4687 ≤ (5377371059831/50000000000000 : ℝ)^3663 := by
    have hnat : (875271487 : ℕ)^4687*50000000000000^3663 ≤ 5377371059831^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875271487 5000000000 5377371059831 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180204601/10000000000 : ℝ)^4687 ≤ (43101456052057/100000000000000 : ℝ)^3663 := by
    have hnat : (5180204601 : ℕ)^4687*100000000000000^3663 ≤ 43101456052057^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180204601 10000000000 43101456052057 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463824663/10000000000 : ℝ)^4687 ≤ (11535950452619/25000000000000 : ℝ)^3663 := by
    have hnat : (5463824663 : ℕ)^4687*25000000000000^3663 ≤ 11535950452619^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463824663 10000000000 11535950452619 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-875271487/5000000000 : ℝ), (5180204601/10000000000 : ℝ), (5463824663/10000000000 : ℝ)] ![(5377371059831/50000000000000 : ℝ), (43101456052057/100000000000000 : ℝ), (11535950452619/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-875271487/5000000000 : ℝ)|^4687 ≤ (5377371059831/50000000000000 : ℝ)^3663
        have hw : |(-875271487/5000000000 : ℝ)|=(875271487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180204601/10000000000 : ℝ)|^4687 ≤ (43101456052057/100000000000000 : ℝ)^3663
        have hw : |(5180204601/10000000000 : ℝ)|=(5180204601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463824663/10000000000 : ℝ)|^4687 ≤ (11535950452619/25000000000000 : ℝ)^3663
        have hw : |(5463824663/10000000000 : ℝ)|=(5463824663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s3_5 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280123587/10000000000 : ℝ)*x 0 + (-201665747/1250000000 : ℝ)*x 1 + (5463824619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280123587/10000000000 : ℝ)^4687 ≤ (2208404455229/5000000000000 : ℝ)^3663 := by
    have hnat : (5280123587 : ℕ)^4687*5000000000000^3663 ≤ 2208404455229^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280123587 10000000000 2208404455229 5000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201665747/1250000000 : ℝ)^4687 ≤ (9688109544747/100000000000000 : ℝ)^3663 := by
    have hnat : (201665747 : ℕ)^4687*100000000000000^3663 ≤ 9688109544747^3663*1250000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201665747 1250000000 9688109544747 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463824619/10000000000 : ℝ)^4687 ≤ (46143801335001/100000000000000 : ℝ)^3663 := by
    have hnat : (5463824619 : ℕ)^4687*100000000000000^3663 ≤ 46143801335001^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463824619 10000000000 46143801335001 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280123587/10000000000 : ℝ), (-201665747/1250000000 : ℝ), (5463824619/10000000000 : ℝ)] ![(2208404455229/5000000000000 : ℝ), (9688109544747/100000000000000 : ℝ), (46143801335001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280123587/10000000000 : ℝ)|^4687 ≤ (2208404455229/5000000000000 : ℝ)^3663
        have hw : |(5280123587/10000000000 : ℝ)|=(5280123587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201665747/1250000000 : ℝ)|^4687 ≤ (9688109544747/100000000000000 : ℝ)^3663
        have hw : |(-201665747/1250000000 : ℝ)|=(201665747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463824619/10000000000 : ℝ)|^4687 ≤ (46143801335001/100000000000000 : ℝ)^3663
        have hw : |(5463824619/10000000000 : ℝ)|=(5463824619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s3_6 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330007713/625000000 : ℝ)*x 0 + (218552979/400000000 : ℝ)*x 1 + (-403331607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330007713/625000000 : ℝ)^4687 ≤ (11042021797167/25000000000000 : ℝ)^3663 := by
    have hnat : (330007713 : ℕ)^4687*25000000000000^3663 ≤ 11042021797167^3663*625000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330007713 625000000 11042021797167 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218552979/400000000 : ℝ)^4687 ≤ (46143799778903/100000000000000 : ℝ)^3663 := by
    have hnat : (218552979 : ℕ)^4687*100000000000000^3663 ≤ 46143799778903^3663*400000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218552979 400000000 46143799778903 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403331607/2500000000 : ℝ)^4687 ≤ (1211014127227/12500000000000 : ℝ)^3663 := by
    have hnat : (403331607 : ℕ)^4687*12500000000000^3663 ≤ 1211014127227^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403331607 2500000000 1211014127227 12500000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330007713/625000000 : ℝ), (218552979/400000000 : ℝ), (-403331607/2500000000 : ℝ)] ![(11042021797167/25000000000000 : ℝ), (46143799778903/100000000000000 : ℝ), (1211014127227/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330007713/625000000 : ℝ)|^4687 ≤ (11042021797167/25000000000000 : ℝ)^3663
        have hw : |(330007713/625000000 : ℝ)|=(330007713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218552979/400000000 : ℝ)|^4687 ≤ (46143799778903/100000000000000 : ℝ)^3663
        have hw : |(218552979/400000000 : ℝ)|=(218552979/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403331607/2500000000 : ℝ)|^4687 ≤ (1211014127227/12500000000000 : ℝ)^3663
        have hw : |(-403331607/2500000000 : ℝ)|=(403331607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s3_7 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2113845859/5000000000 : ℝ)*x 0 + (2289471431/5000000000 : ℝ)*x 1 + (1949241007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113845859/5000000000 : ℝ)^4687 ≤ (33233772261763/100000000000000 : ℝ)^3663 := by
    have hnat : (2113845859 : ℕ)^4687*100000000000000^3663 ≤ 33233772261763^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113845859 5000000000 33233772261763 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2289471431/5000000000 : ℝ)^4687 ≤ (7361416072323/20000000000000 : ℝ)^3663 := by
    have hnat : (2289471431 : ℕ)^4687*20000000000000^3663 ≤ 7361416072323^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289471431 5000000000 7361416072323 20000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1949241007/5000000000 : ℝ)^4687 ≤ (5991829471561/20000000000000 : ℝ)^3663 := by
    have hnat : (1949241007 : ℕ)^4687*20000000000000^3663 ≤ 5991829471561^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949241007 5000000000 5991829471561 20000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2113845859/5000000000 : ℝ), (2289471431/5000000000 : ℝ), (1949241007/5000000000 : ℝ)] ![(33233772261763/100000000000000 : ℝ), (7361416072323/20000000000000 : ℝ), (5991829471561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2113845859/5000000000 : ℝ)|^4687 ≤ (33233772261763/100000000000000 : ℝ)^3663
        have hw : |(2113845859/5000000000 : ℝ)|=(2113845859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2289471431/5000000000 : ℝ)|^4687 ≤ (7361416072323/20000000000000 : ℝ)^3663
        have hw : |(2289471431/5000000000 : ℝ)|=(2289471431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1949241007/5000000000 : ℝ)|^4687 ≤ (5991829471561/20000000000000 : ℝ)^3663
        have hw : |(1949241007/5000000000 : ℝ)|=(1949241007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1592_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169960057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (518/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5063/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10293/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1639/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (518/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5063/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (518/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5063/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (518/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5063/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (518/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5063/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (518/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5063/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (518/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5063/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5063/50000 : ℝ) ^ (4683/1024 : ℝ) ≤ (1414479820224103/50000000000000000000 : ℝ) := by
    have hpowers : (5063/50000 : ℝ)^4683 ≤ (1414479820224103/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5063 : ℕ)^4683*50000000000000000000^1024 ≤ 1414479820224103^1024*50000^4683 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5063 50000 1414479820224103 50000000000000000000 4683 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5063/50000 : ℝ)) (X := (1414479820224103/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (518/3125 : ℝ) ^ (4683/1024 : ℝ) ≤ (13472922582213867/50000000000000000000 : ℝ) := by
    have hpowers : (518/3125 : ℝ)^4683 ≤ (13472922582213867/50000000000000000000 : ℝ)^1024 := by
      have hnat : (518 : ℕ)^4683*50000000000000000000^1024 ≤ 13472922582213867^1024*3125^4683 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        518 3125 13472922582213867 50000000000000000000 4683 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (518/3125 : ℝ)) (X := (13472922582213867/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001414479820224103/25000000000000000000 : ℝ) ≤ (10000123715167319/10000000000000000 : ℝ) ^ (4683/1024 : ℝ) := by
    have hpowers : (25001414479820224103/25000000000000000000 : ℝ)^1024 ≤ (10000123715167319/10000000000000000 : ℝ)^4683 := by
      have hnat : (25001414479820224103 : ℕ)^1024*10000000000000000^4683 ≤ 10000123715167319^4683*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001414479820224103 25000000000000000000 10000123715167319 10000000000000000 1024 4683 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000123715167319/10000000000000000 : ℝ)) (X := (25001414479820224103/25000000000000000000 : ℝ)) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001488740240243797/5000000000000000000 : ℝ) ≤ (10000650989839789/10000000000000000 : ℝ) ^ (4683/1024 : ℝ) := by
    have hpowers : (5001488740240243797/5000000000000000000 : ℝ)^1024 ≤ (10000650989839789/10000000000000000 : ℝ)^4683 := by
      have hnat : (5001488740240243797 : ℕ)^1024*10000000000000000^4683 ≤ 10000650989839789^4683*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001488740240243797 5000000000000000000 10000650989839789 10000000000000000 1024 4683 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000650989839789/10000000000000000 : ℝ)) (X := (5001488740240243797/5000000000000000000 : ℝ)) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013472922582213867/25000000000000000000 : ℝ) ≤ (10001178264512259/10000000000000000 : ℝ) ^ (4683/1024 : ℝ) := by
    have hpowers : (25013472922582213867/25000000000000000000 : ℝ)^1024 ≤ (10001178264512259/10000000000000000 : ℝ)^4683 := by
      have hnat : (25013472922582213867 : ℕ)^1024*10000000000000000^4683 ≤ 10001178264512259^4683*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013472922582213867 25000000000000000000 10001178264512259 10000000000000000 1024 4683 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001178264512259/10000000000000000 : ℝ)) (X := (25013472922582213867/25000000000000000000 : ℝ)) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1414479820224103/50000000000000000000 : ℝ) ≤ ((6449011959616234511/6450000000000000000 : ℝ)+2*(52727467247/64500000000000 : ℝ)*(5063/50000 : ℝ))^(4683/1024 : ℝ) := by
    rw [show (6449011959616234511/6450000000000000000 : ℝ)+2*(52727467247/64500000000000 : ℝ)*(5063/50000 : ℝ)=(10000123715167319/10000000000000000 : ℝ) by norm_num, show 1+2*(1414479820224103/50000000000000000000 : ℝ)=(25001414479820224103/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13472922582213867/50000000000000000000 : ℝ)+(1414479820224103/50000000000000000000 : ℝ) ≤ ((6449011959616234511/6450000000000000000 : ℝ)+(52727467247/64500000000000 : ℝ)*((518/3125 : ℝ)+(5063/50000 : ℝ)))^(4683/1024 : ℝ) := by
    rw [show (6449011959616234511/6450000000000000000 : ℝ)+(52727467247/64500000000000 : ℝ)*((518/3125 : ℝ)+(5063/50000 : ℝ))=(10000650989839789/10000000000000000 : ℝ) by norm_num, show 1+(13472922582213867/50000000000000000000 : ℝ)+(1414479820224103/50000000000000000000 : ℝ)=(5001488740240243797/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13472922582213867/50000000000000000000 : ℝ) ≤ ((6449011959616234511/6450000000000000000 : ℝ)+2*(52727467247/64500000000000 : ℝ)*(518/3125 : ℝ))^(4683/1024 : ℝ) := by
    rw [show (6449011959616234511/6450000000000000000 : ℝ)+2*(52727467247/64500000000000 : ℝ)*(518/3125 : ℝ)=(10001178264512259/10000000000000000 : ℝ) by norm_num, show 1+2*(13472922582213867/50000000000000000000 : ℝ)=(25013472922582213867/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6449011959616234511/6450000000000000000 : ℝ)*(X 1 0+X 2 0)+(52727467247/64500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4683/1024 : ℝ)) (lo := (5063/50000 : ℝ)) (hi := (518/3125 : ℝ)) (c := (6449011959616234511/6450000000000000000 : ℝ)) (alpha := (52727467247/64500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6449011959616234511/6450000000000000000 : ℝ)*(X 0 1+X 2 1)+(52727467247/64500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4683/1024 : ℝ)) (lo := (5063/50000 : ℝ)) (hi := (518/3125 : ℝ)) (c := (6449011959616234511/6450000000000000000 : ℝ)) (alpha := (52727467247/64500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6449011959616234511/6450000000000000000 : ℝ)*(X 0 2+X 1 2)+(52727467247/64500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4683/1024 : ℝ)) (lo := (5063/50000 : ℝ)) (hi := (518/3125 : ℝ)) (c := (6449011959616234511/6450000000000000000 : ℝ)) (alpha := (52727467247/64500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1750468029/10000000000 : ℝ)*X 0 0+(5465982943/10000000000 : ℝ)*X 0 1+(5178069013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356318657/10000000000 : ℝ)*X 1 0+(-474770443/2500000000 : ℝ)*X 1 1+(5178069029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267815933/500000000 : ℝ)*X 2 0+(1294517251/2500000000 : ℝ)*X 2 1+(-1899081801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2113756333/5000000000 : ℝ)*X 0 0+(1946651759/5000000000 : ℝ)*X 0 1+(1146016749/2500000000 : ℝ)*X 0 2+(2113756333/5000000000 : ℝ)*X 1 0+(1946651759/5000000000 : ℝ)*X 1 1+(1146016749/2500000000 : ℝ)*X 1 2+(2113756333/5000000000 : ℝ)*X 2 0+(1946651759/5000000000 : ℝ)*X 2 1+(1146016749/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-875271487/5000000000 : ℝ)*X 0 0+(5180204601/10000000000 : ℝ)*X 0 1+(5463824663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280123587/10000000000 : ℝ)*X 1 0+(-201665747/1250000000 : ℝ)*X 1 1+(5463824619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330007713/625000000 : ℝ)*X 2 0+(218552979/400000000 : ℝ)*X 2 1+(-403331607/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2113845859/5000000000 : ℝ)*X 0 0+(2289471431/5000000000 : ℝ)*X 0 1+(1949241007/5000000000 : ℝ)*X 0 2+(2113845859/5000000000 : ℝ)*X 1 0+(2289471431/5000000000 : ℝ)*X 1 1+(1949241007/5000000000 : ℝ)*X 1 2+(2113845859/5000000000 : ℝ)*X 2 0+(2289471431/5000000000 : ℝ)*X 2 1+(1949241007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21260853765331730773577697/6718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (546862183/100000000000000 : ℝ)*(base19) + (519189581/100000000000000 : ℝ)*(base23) + (15864309/100000000000000 : ℝ)*(lower2) + (570731/625000000000 : ℝ)*(upper3) + (4846593/10000000000000 : ℝ)*(upper5) + (153779766754809/6250000000000 : ℝ)*(major0) + (153779766754809/6250000000000 : ℝ)*(major1) + (153779766754809/6250000000000 : ℝ)*(major2) + (27134899044519/781250000000 : ℝ)*(sp0) + (1736636378802709/50000000000000 : ℝ)*(sp1) + (173663639263901/5000000000000 : ℝ)*(sp2) + (1447676104469301/100000000000000 : ℝ)*(sp3) + (622676917/10000000000000 : ℝ)*(sp4) + (3021736773/100000000000000 : ℝ)*(sp7) + (723839563103037/50000000000000 : ℝ)*(f.failure) + (3473273304467601/100000000000000 : ℝ)*(f.sum) + (600852825289/268750000000000000000000000 : ℝ)*base65 + (233777582765353867/13437500000000000000000000000000 : ℝ)*base68 + (151706118584728867/13437500000000000000000000000000 : ℝ)*base70 + (93594012636603867/13437500000000000000000000000000 : ℝ)*base72 + (1010102984511/268750000000000000000000000 : ℝ)*base74 + (60283708343478867/13437500000000000000000000000000 : ℝ)*base76 + (130361291287228867/13437500000000000000000000000000 : ℝ)*base78 + (19794741503478867/13437500000000000000000000000000 : ℝ)*base80 + (1258784804103/537500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (65393109/5000000000000000000000 : ℝ)*base89 + (65393109/5000000000000000000000 : ℝ)*base91 + (65393109/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117614380141435243055189421/53750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (544858867/100000000000000 : ℝ)*(base19) + (535956143/100000000000000 : ℝ)*(base23) + (25249583/25000000000000 : ℝ)*(upper2) + (1510451/10000000000000 : ℝ)*(upper3) + (23894897/20000000000000 : ℝ)*(upper5) + (2497717219991811/100000000000000 : ℝ)*(major0) + (2497717219991811/100000000000000 : ℝ)*(major1) + (2497717219991811/100000000000000 : ℝ)*(major2) + (3788890279/50000000000000 : ℝ)*(sp1) + (1988636187/100000000000000 : ℝ)*(sp2) + (440730456276747/12500000000000 : ℝ)*(sp4) + (3525835527574551/100000000000000 : ℝ)*(sp5) + (1762920562810823/50000000000000 : ℝ)*(sp6) + (1469590716830491/100000000000000 : ℝ)*(sp7) + (1469590716830491/100000000000000 : ℝ)*(f.failure) + (440730456276747/12500000000000 : ℝ)*(f.sum) + (3079003011111/1075000000000000000000000000 : ℝ)*base66 + (895820188632429807/215000000000000000000000000000000 : ℝ)*base67 + (173045892327570193/215000000000000000000000000000000 : ℝ)*base70 + (2302298310412570193/215000000000000000000000000000000 : ℝ)*base72 + (5539690404689/1075000000000000000000000000 : ℝ)*base73 + (980095512372570193/215000000000000000000000000000000 : ℝ)*base76 + (2489807108587570193/215000000000000000000000000000000 : ℝ)*base78 + (401130766097570193/215000000000000000000000000000000 : ℝ)*base80 + (1384107901257/537500000000000000000000000 : ℝ)*base81 + (9697987/10000000000000000000000 : ℝ)*base89 + (9697987/10000000000000000000000 : ℝ)*base91 + (9697987/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1592_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169960057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (518/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5063/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10293/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1639/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1592_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1592_s4_0 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-87532271/500000000 : ℝ)*x 0 + (5465102337/10000000000 : ℝ)*x 1 + (5178832007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87532271/500000000 : ℝ)^4687 ≤ (2151109493619/20000000000000 : ℝ)^3663 := by
    have hnat : (87532271 : ℕ)^4687*20000000000000^3663 ≤ 2151109493619^3663*500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87532271 500000000 2151109493619 20000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465102337/10000000000 : ℝ)^4687 ≤ (5769701139383/12500000000000 : ℝ)^3663 := by
    have hnat : (5465102337 : ℕ)^4687*12500000000000^3663 ≤ 5769701139383^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465102337 10000000000 5769701139383 12500000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178832007/10000000000 : ℝ)^4687 ≤ (43086843398989/100000000000000 : ℝ)^3663 := by
    have hnat : (5178832007 : ℕ)^4687*100000000000000^3663 ≤ 43086843398989^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178832007 10000000000 43086843398989 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87532271/500000000 : ℝ), (5465102337/10000000000 : ℝ), (5178832007/10000000000 : ℝ)] ![(2151109493619/20000000000000 : ℝ), (5769701139383/12500000000000 : ℝ), (43086843398989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87532271/500000000 : ℝ)|^4687 ≤ (2151109493619/20000000000000 : ℝ)^3663
        have hw : |(-87532271/500000000 : ℝ)|=(87532271/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465102337/10000000000 : ℝ)|^4687 ≤ (5769701139383/12500000000000 : ℝ)^3663
        have hw : |(5465102337/10000000000 : ℝ)|=(5465102337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178832007/10000000000 : ℝ)|^4687 ≤ (43086843398989/100000000000000 : ℝ)^3663
        have hw : |(5178832007/10000000000 : ℝ)|=(5178832007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s4_1 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356084697/10000000000 : ℝ)*x 0 + (-1898384337/10000000000 : ℝ)*x 1 + (1035766413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356084697/10000000000 : ℝ)^4687 ≤ (44982762047103/100000000000000 : ℝ)^3663 := by
    have hnat : (5356084697 : ℕ)^4687*100000000000000^3663 ≤ 44982762047103^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356084697 10000000000 44982762047103 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1898384337/10000000000 : ℝ)^4687 ≤ (11930393930949/100000000000000 : ℝ)^3663 := by
    have hnat : (1898384337 : ℕ)^4687*100000000000000^3663 ≤ 11930393930949^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898384337 10000000000 11930393930949 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035766413/2000000000 : ℝ)^4687 ≤ (8617368803287/20000000000000 : ℝ)^3663 := by
    have hnat : (1035766413 : ℕ)^4687*20000000000000^3663 ≤ 8617368803287^3663*2000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035766413 2000000000 8617368803287 20000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356084697/10000000000 : ℝ), (-1898384337/10000000000 : ℝ), (1035766413/2000000000 : ℝ)] ![(44982762047103/100000000000000 : ℝ), (11930393930949/100000000000000 : ℝ), (8617368803287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356084697/10000000000 : ℝ)|^4687 ≤ (44982762047103/100000000000000 : ℝ)^3663
        have hw : |(5356084697/10000000000 : ℝ)|=(5356084697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1898384337/10000000000 : ℝ)|^4687 ≤ (11930393930949/100000000000000 : ℝ)^3663
        have hw : |(-1898384337/10000000000 : ℝ)|=(1898384337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035766413/2000000000 : ℝ)|^4687 ≤ (8617368803287/20000000000000 : ℝ)^3663
        have hw : |(1035766413/2000000000 : ℝ)|=(1035766413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s4_2 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678042349/5000000000 : ℝ)*x 0 + (5178832053/10000000000 : ℝ)*x 1 + (-37967687/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678042349/5000000000 : ℝ)^4687 ≤ (44982762057849/100000000000000 : ℝ)^3663 := by
    have hnat : (2678042349 : ℕ)^4687*100000000000000^3663 ≤ 44982762057849^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678042349 5000000000 44982762057849 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178832053/10000000000 : ℝ)^4687 ≤ (2692927743043/6250000000000 : ℝ)^3663 := by
    have hnat : (5178832053 : ℕ)^4687*6250000000000^3663 ≤ 2692927743043^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178832053 10000000000 2692927743043 6250000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37967687/200000000 : ℝ)^4687 ≤ (11930394035487/100000000000000 : ℝ)^3663 := by
    have hnat : (37967687 : ℕ)^4687*100000000000000^3663 ≤ 11930394035487^3663*200000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37967687 200000000 11930394035487 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678042349/5000000000 : ℝ), (5178832053/10000000000 : ℝ), (-37967687/200000000 : ℝ)] ![(44982762057849/100000000000000 : ℝ), (2692927743043/6250000000000 : ℝ), (11930394035487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678042349/5000000000 : ℝ)|^4687 ≤ (44982762057849/100000000000000 : ℝ)^3663
        have hw : |(2678042349/5000000000 : ℝ)|=(2678042349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178832053/10000000000 : ℝ)|^4687 ≤ (2692927743043/6250000000000 : ℝ)^3663
        have hw : |(5178832053/10000000000 : ℝ)|=(5178832053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37967687/200000000 : ℝ)|^4687 ≤ (11930394035487/100000000000000 : ℝ)^3663
        have hw : |(-37967687/200000000 : ℝ)|=(37967687/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s4_3 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4227627277/10000000000 : ℝ)*x 0 + (973815687/2500000000 : ℝ)*x 1 + (4582082913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227627277/10000000000 : ℝ)^4687 ≤ (830828102041/2500000000000 : ℝ)^3663 := by
    have hnat : (4227627277 : ℕ)^4687*2500000000000^3663 ≤ 830828102041^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227627277 10000000000 830828102041 2500000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973815687/2500000000 : ℝ)^4687 ≤ (7481873884743/25000000000000 : ℝ)^3663 := by
    have hnat : (973815687 : ℕ)^4687*25000000000000^3663 ≤ 7481873884743^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973815687 2500000000 7481873884743 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4582082913/10000000000 : ℝ)^4687 ≤ (36839380360051/100000000000000 : ℝ)^3663 := by
    have hnat : (4582082913 : ℕ)^4687*100000000000000^3663 ≤ 36839380360051^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582082913 10000000000 36839380360051 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227627277/10000000000 : ℝ), (973815687/2500000000 : ℝ), (4582082913/10000000000 : ℝ)] ![(830828102041/2500000000000 : ℝ), (7481873884743/25000000000000 : ℝ), (36839380360051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227627277/10000000000 : ℝ)|^4687 ≤ (830828102041/2500000000000 : ℝ)^3663
        have hw : |(4227627277/10000000000 : ℝ)|=(4227627277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(973815687/2500000000 : ℝ)|^4687 ≤ (7481873884743/25000000000000 : ℝ)^3663
        have hw : |(973815687/2500000000 : ℝ)|=(973815687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4582082913/10000000000 : ℝ)|^4687 ≤ (36839380360051/100000000000000 : ℝ)^3663
        have hw : |(4582082913/10000000000 : ℝ)|=(4582082913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s4_4 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-175071889/1000000000 : ℝ)*x 0 + (2590471813/5000000000 : ℝ)*x 1 + (2731484281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175071889/1000000000 : ℝ)^4687 ≤ (10756125038527/100000000000000 : ℝ)^3663 := by
    have hnat : (175071889 : ℕ)^4687*100000000000000^3663 ≤ 10756125038527^3663*1000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175071889 1000000000 10756125038527 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590471813/5000000000 : ℝ)^4687 ≤ (43109324169853/100000000000000 : ℝ)^3663 := by
    have hnat : (2590471813 : ℕ)^4687*100000000000000^3663 ≤ 43109324169853^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590471813 5000000000 43109324169853 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731484281/5000000000 : ℝ)^4687 ≤ (46134550779257/100000000000000 : ℝ)^3663 := by
    have hnat : (2731484281 : ℕ)^4687*100000000000000^3663 ≤ 46134550779257^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731484281 5000000000 46134550779257 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-175071889/1000000000 : ℝ), (2590471813/5000000000 : ℝ), (2731484281/5000000000 : ℝ)] ![(10756125038527/100000000000000 : ℝ), (43109324169853/100000000000000 : ℝ), (46134550779257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-175071889/1000000000 : ℝ)|^4687 ≤ (10756125038527/100000000000000 : ℝ)^3663
        have hw : |(-175071889/1000000000 : ℝ)|=(175071889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590471813/5000000000 : ℝ)|^4687 ≤ (43109324169853/100000000000000 : ℝ)^3663
        have hw : |(2590471813/5000000000 : ℝ)|=(2590471813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731484281/5000000000 : ℝ)|^4687 ≤ (46134550779257/100000000000000 : ℝ)^3663
        have hw : |(2731484281/5000000000 : ℝ)|=(2731484281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s4_5 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280325999/10000000000 : ℝ)*x 0 + (-1614247853/10000000000 : ℝ)*x 1 + (68287107/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280325999/10000000000 : ℝ)^4687 ≤ (11042563904197/25000000000000 : ℝ)^3663 := by
    have hnat : (5280325999 : ℕ)^4687*25000000000000^3663 ≤ 11042563904197^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280325999 10000000000 11042563904197 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1614247853/10000000000 : ℝ)^4687 ≤ (9695193610933/100000000000000 : ℝ)^3663 := by
    have hnat : (1614247853 : ℕ)^4687*100000000000000^3663 ≤ 9695193610933^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614247853 10000000000 9695193610933 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68287107/125000000 : ℝ)^4687 ≤ (9226910151529/20000000000000 : ℝ)^3663 := by
    have hnat : (68287107 : ℕ)^4687*20000000000000^3663 ≤ 9226910151529^3663*125000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68287107 125000000 9226910151529 20000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280325999/10000000000 : ℝ), (-1614247853/10000000000 : ℝ), (68287107/125000000 : ℝ)] ![(11042563904197/25000000000000 : ℝ), (9695193610933/100000000000000 : ℝ), (9226910151529/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280325999/10000000000 : ℝ)|^4687 ≤ (11042563904197/25000000000000 : ℝ)^3663
        have hw : |(5280325999/10000000000 : ℝ)|=(5280325999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1614247853/10000000000 : ℝ)|^4687 ≤ (9695193610933/100000000000000 : ℝ)^3663
        have hw : |(-1614247853/10000000000 : ℝ)|=(1614247853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68287107/125000000 : ℝ)|^4687 ≤ (9226910151529/20000000000000 : ℝ)^3663
        have hw : |(68287107/125000000 : ℝ)|=(68287107/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s4_6 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280325997/10000000000 : ℝ)*x 0 + (2731484281/5000000000 : ℝ)*x 1 + (-1614247853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280325997/10000000000 : ℝ)^4687 ≤ (44170255595381/100000000000000 : ℝ)^3663 := by
    have hnat : (5280325997 : ℕ)^4687*100000000000000^3663 ≤ 44170255595381^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280325997 10000000000 44170255595381 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731484281/5000000000 : ℝ)^4687 ≤ (46134550779257/100000000000000 : ℝ)^3663 := by
    have hnat : (2731484281 : ℕ)^4687*100000000000000^3663 ≤ 46134550779257^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731484281 5000000000 46134550779257 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1614247853/10000000000 : ℝ)^4687 ≤ (9695193610933/100000000000000 : ℝ)^3663 := by
    have hnat : (1614247853 : ℕ)^4687*100000000000000^3663 ≤ 9695193610933^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614247853 10000000000 9695193610933 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280325997/10000000000 : ℝ), (2731484281/5000000000 : ℝ), (-1614247853/10000000000 : ℝ)] ![(44170255595381/100000000000000 : ℝ), (46134550779257/100000000000000 : ℝ), (9695193610933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280325997/10000000000 : ℝ)|^4687 ≤ (44170255595381/100000000000000 : ℝ)^3663
        have hw : |(5280325997/10000000000 : ℝ)|=(5280325997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731484281/5000000000 : ℝ)|^4687 ≤ (46134550779257/100000000000000 : ℝ)^3663
        have hw : |(2731484281/5000000000 : ℝ)|=(2731484281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1614247853/10000000000 : ℝ)|^4687 ≤ (9695193610933/100000000000000 : ℝ)^3663
        have hw : |(-1614247853/10000000000 : ℝ)|=(1614247853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s4_7 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1056950899/2500000000 : ℝ)*x 0 + (457701667/1000000000 : ℝ)*x 1 + (3900382123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056950899/2500000000 : ℝ)^4687 ≤ (1063516723/3200000000 : ℝ)^3663 := by
    have hnat : (1056950899 : ℕ)^4687*3200000000^3663 ≤ 1063516723^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056950899 2500000000 1063516723 3200000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457701667/1000000000 : ℝ)^4687 ≤ (36787269734867/100000000000000 : ℝ)^3663 := by
    have hnat : (457701667 : ℕ)^4687*100000000000000^3663 ≤ 36787269734867^3663*1000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457701667 1000000000 36787269734867 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3900382123/10000000000 : ℝ)^4687 ≤ (29977832656581/100000000000000 : ℝ)^3663 := by
    have hnat : (3900382123 : ℕ)^4687*100000000000000^3663 ≤ 29977832656581^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3900382123 10000000000 29977832656581 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056950899/2500000000 : ℝ), (457701667/1000000000 : ℝ), (3900382123/10000000000 : ℝ)] ![(1063516723/3200000000 : ℝ), (36787269734867/100000000000000 : ℝ), (29977832656581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056950899/2500000000 : ℝ)|^4687 ≤ (1063516723/3200000000 : ℝ)^3663
        have hw : |(1056950899/2500000000 : ℝ)|=(1056950899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(457701667/1000000000 : ℝ)|^4687 ≤ (36787269734867/100000000000000 : ℝ)^3663
        have hw : |(457701667/1000000000 : ℝ)|=(457701667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3900382123/10000000000 : ℝ)|^4687 ≤ (29977832656581/100000000000000 : ℝ)^3663
        have hw : |(3900382123/10000000000 : ℝ)|=(3900382123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1592_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169960057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1639/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10309/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4093/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1639/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1639/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1639/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1639/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1639/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1639/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10293/100000 : ℝ) ^ (4683/1024 : ℝ) ≤ (121948168688179/4000000000000000000 : ℝ) := by
    have hpowers : (10293/100000 : ℝ)^4683 ≤ (121948168688179/4000000000000000000 : ℝ)^1024 := by
      have hnat : (10293 : ℕ)^4683*4000000000000000000^1024 ≤ 121948168688179^1024*100000^4683 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10293 100000 121948168688179 4000000000000000000 4683 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10293/100000 : ℝ)) (X := (121948168688179/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1639/10000 : ℝ) ^ (4683/1024 : ℝ) ≤ (204724265906759/800000000000000000 : ℝ) := by
    have hpowers : (1639/10000 : ℝ)^4683 ≤ (204724265906759/800000000000000000 : ℝ)^1024 := by
      have hnat : (1639 : ℕ)^4683*800000000000000000^1024 ≤ 204724265906759^1024*10000^4683 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1639 10000 204724265906759 800000000000000000 4683 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1639/10000 : ℝ)) (X := (204724265906759/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000121948168688179/2000000000000000000 : ℝ) ≤ (400005332989547/400000000000000 : ℝ) ^ (4683/1024 : ℝ) := by
    have hpowers : (2000121948168688179/2000000000000000000 : ℝ)^1024 ≤ (400005332989547/400000000000000 : ℝ)^4683 := by
      have hnat : (2000121948168688179 : ℕ)^1024*400000000000000^4683 ≤ 400005332989547^4683*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000121948168688179 2000000000000000000 400005332989547 400000000000000 1024 4683 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400005332989547/400000000000000 : ℝ)) (X := (2000121948168688179/2000000000000000000 : ℝ)) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000572784749110987/2000000000000000000 : ℝ) ≤ (10000626164820081/10000000000000000 : ℝ) ^ (4683/1024 : ℝ) := by
    have hpowers : (2000572784749110987/2000000000000000000 : ℝ)^1024 ≤ (10000626164820081/10000000000000000 : ℝ)^4683 := by
      have hnat : (2000572784749110987 : ℕ)^1024*10000000000000000^4683 ≤ 10000626164820081^4683*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000572784749110987 2000000000000000000 10000626164820081 10000000000000000 1024 4683 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000626164820081/10000000000000000 : ℝ)) (X := (2000572784749110987/2000000000000000000 : ℝ)) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (400204724265906759/400000000000000000 : ℝ) ≤ (10001119004901487/10000000000000000 : ℝ) ^ (4683/1024 : ℝ) := by
    have hpowers : (400204724265906759/400000000000000000 : ℝ)^1024 ≤ (10001119004901487/10000000000000000 : ℝ)^4683 := by
      have hnat : (400204724265906759 : ℕ)^1024*10000000000000000^4683 ≤ 10001119004901487^4683*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400204724265906759 400000000000000000 10001119004901487 10000000000000000 1024 4683 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001119004901487/10000000000000000 : ℝ)) (X := (400204724265906759/400000000000000000 : ℝ)) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(121948168688179/4000000000000000000 : ℝ) ≤ ((60960667275015877559/60970000000000000000 : ℝ)+2*(246420040703/304850000000000 : ℝ)*(10293/100000 : ℝ))^(4683/1024 : ℝ) := by
    rw [show (60960667275015877559/60970000000000000000 : ℝ)+2*(246420040703/304850000000000 : ℝ)*(10293/100000 : ℝ)=(400005332989547/400000000000000 : ℝ) by norm_num, show 1+2*(121948168688179/4000000000000000000 : ℝ)=(2000121948168688179/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(204724265906759/800000000000000000 : ℝ)+(121948168688179/4000000000000000000 : ℝ) ≤ ((60960667275015877559/60970000000000000000 : ℝ)+(246420040703/304850000000000 : ℝ)*((1639/10000 : ℝ)+(10293/100000 : ℝ)))^(4683/1024 : ℝ) := by
    rw [show (60960667275015877559/60970000000000000000 : ℝ)+(246420040703/304850000000000 : ℝ)*((1639/10000 : ℝ)+(10293/100000 : ℝ))=(10000626164820081/10000000000000000 : ℝ) by norm_num, show 1+(204724265906759/800000000000000000 : ℝ)+(121948168688179/4000000000000000000 : ℝ)=(2000572784749110987/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(204724265906759/800000000000000000 : ℝ) ≤ ((60960667275015877559/60970000000000000000 : ℝ)+2*(246420040703/304850000000000 : ℝ)*(1639/10000 : ℝ))^(4683/1024 : ℝ) := by
    rw [show (60960667275015877559/60970000000000000000 : ℝ)+2*(246420040703/304850000000000 : ℝ)*(1639/10000 : ℝ)=(10001119004901487/10000000000000000 : ℝ) by norm_num, show 1+2*(204724265906759/800000000000000000 : ℝ)=(400204724265906759/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60960667275015877559/60970000000000000000 : ℝ)*(X 1 0+X 2 0)+(246420040703/304850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4683/1024 : ℝ)) (lo := (10293/100000 : ℝ)) (hi := (1639/10000 : ℝ)) (c := (60960667275015877559/60970000000000000000 : ℝ)) (alpha := (246420040703/304850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60960667275015877559/60970000000000000000 : ℝ)*(X 0 1+X 2 1)+(246420040703/304850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4683/1024 : ℝ)) (lo := (10293/100000 : ℝ)) (hi := (1639/10000 : ℝ)) (c := (60960667275015877559/60970000000000000000 : ℝ)) (alpha := (246420040703/304850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60960667275015877559/60970000000000000000 : ℝ)*(X 0 2+X 1 2)+(246420040703/304850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4683/1024 : ℝ)) (lo := (10293/100000 : ℝ)) (hi := (1639/10000 : ℝ)) (c := (60960667275015877559/60970000000000000000 : ℝ)) (alpha := (246420040703/304850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87532271/500000000 : ℝ)*X 0 0+(5465102337/10000000000 : ℝ)*X 0 1+(5178832007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356084697/10000000000 : ℝ)*X 1 0+(-1898384337/10000000000 : ℝ)*X 1 1+(1035766413/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678042349/5000000000 : ℝ)*X 2 0+(5178832053/10000000000 : ℝ)*X 2 1+(-37967687/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4227627277/10000000000 : ℝ)*X 0 0+(973815687/2500000000 : ℝ)*X 0 1+(4582082913/10000000000 : ℝ)*X 0 2+(4227627277/10000000000 : ℝ)*X 1 0+(973815687/2500000000 : ℝ)*X 1 1+(4582082913/10000000000 : ℝ)*X 1 2+(4227627277/10000000000 : ℝ)*X 2 0+(973815687/2500000000 : ℝ)*X 2 1+(4582082913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-175071889/1000000000 : ℝ)*X 0 0+(2590471813/5000000000 : ℝ)*X 0 1+(2731484281/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280325999/10000000000 : ℝ)*X 1 0+(-1614247853/10000000000 : ℝ)*X 1 1+(68287107/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280325997/10000000000 : ℝ)*X 2 0+(2731484281/5000000000 : ℝ)*X 2 1+(-1614247853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1056950899/2500000000 : ℝ)*X 0 0+(457701667/1000000000 : ℝ)*X 0 1+(3900382123/10000000000 : ℝ)*X 0 2+(1056950899/2500000000 : ℝ)*X 1 0+(457701667/1000000000 : ℝ)*X 1 1+(3900382123/10000000000 : ℝ)*X 1 2+(1056950899/2500000000 : ℝ)*X 2 0+(457701667/1000000000 : ℝ)*X 2 1+(3900382123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127084989341781395356813473/16750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79984737/6250000000000 : ℝ)*(base19) + (1209783721/100000000000000 : ℝ)*(base23) + (37826957/100000000000000 : ℝ)*(lower2) + (93843081/50000000000000 : ℝ)*(upper3) + (7853931/6250000000000 : ℝ)*(upper5) + (1237308270171547/50000000000000 : ℝ)*(major0) + (1237308270171547/50000000000000 : ℝ)*(major1) + (1237308270171547/50000000000000 : ℝ)*(major2) + (873304529341077/25000000000000 : ℝ)*(sp0) + (698646531960397/20000000000000 : ℝ)*(sp1) + (436654091221757/12500000000000 : ℝ)*(sp2) + (1455991672262081/100000000000000 : ℝ)*(sp3) + (3955548367/25000000000000 : ℝ)*(sp4) + (721596087/10000000000000 : ℝ)*(sp7) + (1455998888222951/100000000000000 : ℝ)*(f.failure) + (3493233939557777/100000000000000 : ℝ)*(f.sum) + (4885698793883/4355000000000000000000000000 : ℝ)*base66 + (5449178544994830539/435500000000000000000000000000000 : ℝ)*base67 + (4970858493948330539/435500000000000000000000000000000 : ℝ)*base69 + (2870273295619830539/435500000000000000000000000000000 : ℝ)*base71 + (19290384876687/4355000000000000000000000000 : ℝ)*base73 + (5775187862966830539/435500000000000000000000000000000 : ℝ)*base75 + (2247390038643330539/435500000000000000000000000000000 : ℝ)*base77 + (4858643069152830539/435500000000000000000000000000000 : ℝ)*base79 + (1842569754413/4355000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (19331793/10000000000000000000000 : ℝ)*base90 + (19331793/10000000000000000000000 : ℝ)*base92 + (19331793/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1331866019731150463397/217750000000000000000000000 : ℝ) := by norm_num
    linear_combination (957387143/100000000000000 : ℝ)*(base19) + (103707839/10000000000000 : ℝ)*(base23) + (305155897/100000000000000 : ℝ)*(lower1) + (128504507/100000000000000 : ℝ)*(upper3) + (36482247/100000000000000 : ℝ)*(lower4) + (63456193/50000000000000 : ℝ)*(upper5) + (15698976969921/625000000000 : ℝ)*(major0) + (15698976969921/625000000000 : ℝ)*(major1) + (15698976969921/625000000000 : ℝ)*(major2) + (208110881/25000000000000 : ℝ)*(sp2) + (1772887203836121/50000000000000 : ℝ)*(sp4) + (35457734502851/1000000000000 : ℝ)*(sp5) + (3545772538150329/100000000000000 : ℝ)*(sp6) + (738949009409711/50000000000000 : ℝ)*(sp7) + (738949009409711/50000000000000 : ℝ)*(f.failure) + (1772887203836121/50000000000000 : ℝ)*(f.sum) + (772343813899/217750000000000000000000000 : ℝ)*base66 + (6053419214478977/5443750000000000000000000000000 : ℝ)*base67 + (16748457186116477/5443750000000000000000000000000 : ℝ)*base69 + (1311224277896023/5443750000000000000000000000000 : ℝ)*base72 + (418037910983/108875000000000000000000000 : ℝ)*base74 + (100090092207891477/5443750000000000000000000000000 : ℝ)*base75 + (582218317989773/5443750000000000000000000000000 : ℝ)*base78 + (46606163892008523/5443750000000000000000000000000 : ℝ)*base80 + (3721599086523/871000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (17913527/5000000000000000000000 : ℝ)*base89 + (17913527/5000000000000000000000 : ℝ)*base91 + (17913527/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1592_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169960057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1639/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10309/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1592_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1592_s5_0 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1750662371/10000000000 : ℝ)*x 0 + (2732509907/5000000000 : ℝ)*x 1 + (5178903263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1750662371/10000000000 : ℝ)^4687 ≤ (2688920181139/25000000000000 : ℝ)^3663 := by
    have hnat : (1750662371 : ℕ)^4687*25000000000000^3663 ≤ 2688920181139^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1750662371 10000000000 2688920181139 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732509907/5000000000 : ℝ)^4687 ≤ (46156717295219/100000000000000 : ℝ)^3663 := by
    have hnat : (2732509907 : ℕ)^4687*100000000000000^3663 ≤ 46156717295219^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732509907 5000000000 46156717295219 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178903263/10000000000 : ℝ)^4687 ≤ (2692975122789/6250000000000 : ℝ)^3663 := by
    have hnat : (5178903263 : ℕ)^4687*6250000000000^3663 ≤ 2692975122789^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178903263 10000000000 2692975122789 6250000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1750662371/10000000000 : ℝ), (2732509907/5000000000 : ℝ), (5178903263/10000000000 : ℝ)] ![(2688920181139/25000000000000 : ℝ), (46156717295219/100000000000000 : ℝ), (2692975122789/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1750662371/10000000000 : ℝ)|^4687 ≤ (2688920181139/25000000000000 : ℝ)^3663
        have hw : |(-1750662371/10000000000 : ℝ)|=(1750662371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732509907/5000000000 : ℝ)|^4687 ≤ (46156717295219/100000000000000 : ℝ)^3663
        have hw : |(2732509907/5000000000 : ℝ)|=(2732509907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178903263/10000000000 : ℝ)|^4687 ≤ (2692975122789/6250000000000 : ℝ)^3663
        have hw : |(5178903263/10000000000 : ℝ)|=(5178903263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_1 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339015703/2500000000 : ℝ)*x 0 + (-949159871/5000000000 : ℝ)*x 1 + (5178902949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339015703/2500000000 : ℝ)^4687 ≤ (11245631716419/25000000000000 : ℝ)^3663 := by
    have hnat : (1339015703 : ℕ)^4687*25000000000000^3663 ≤ 11245631716419^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339015703 2500000000 11245631716419 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (949159871/5000000000 : ℝ)^4687 ≤ (11929874502761/100000000000000 : ℝ)^3663 := by
    have hnat : (949159871 : ℕ)^4687*100000000000000^3663 ≤ 11929874502761^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949159871 5000000000 11929874502761 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178902949/10000000000 : ℝ)^4687 ≤ (43087598621887/100000000000000 : ℝ)^3663 := by
    have hnat : (5178902949 : ℕ)^4687*100000000000000^3663 ≤ 43087598621887^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178902949 10000000000 43087598621887 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339015703/2500000000 : ℝ), (-949159871/5000000000 : ℝ), (5178902949/10000000000 : ℝ)] ![(11245631716419/25000000000000 : ℝ), (11929874502761/100000000000000 : ℝ), (43087598621887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339015703/2500000000 : ℝ)|^4687 ≤ (11245631716419/25000000000000 : ℝ)^3663
        have hw : |(1339015703/2500000000 : ℝ)|=(1339015703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-949159871/5000000000 : ℝ)|^4687 ≤ (11929874502761/100000000000000 : ℝ)^3663
        have hw : |(-949159871/5000000000 : ℝ)|=(949159871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178902949/10000000000 : ℝ)|^4687 ≤ (43087598621887/100000000000000 : ℝ)^3663
        have hw : |(5178902949/10000000000 : ℝ)|=(5178902949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_2 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356062727/10000000000 : ℝ)*x 0 + (5178903223/10000000000 : ℝ)*x 1 + (-474579873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356062727/10000000000 : ℝ)^4687 ≤ (22491262976123/50000000000000 : ℝ)^3663 := by
    have hnat : (5356062727 : ℕ)^4687*50000000000000^3663 ≤ 22491262976123^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356062727 10000000000 22491262976123 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178903223/10000000000 : ℝ)^4687 ≤ (21543800769399/50000000000000 : ℝ)^3663 := by
    have hnat : (5178903223 : ℕ)^4687*50000000000000^3663 ≤ 21543800769399^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178903223 10000000000 21543800769399 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474579873/2500000000 : ℝ)^4687 ≤ (2982468123111/25000000000000 : ℝ)^3663 := by
    have hnat : (474579873 : ℕ)^4687*25000000000000^3663 ≤ 2982468123111^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474579873 2500000000 2982468123111 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356062727/10000000000 : ℝ), (5178903223/10000000000 : ℝ), (-474579873/2500000000 : ℝ)] ![(22491262976123/50000000000000 : ℝ), (21543800769399/50000000000000 : ℝ), (2982468123111/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356062727/10000000000 : ℝ)|^4687 ≤ (22491262976123/50000000000000 : ℝ)^3663
        have hw : |(5356062727/10000000000 : ℝ)|=(5356062727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178903223/10000000000 : ℝ)|^4687 ≤ (21543800769399/50000000000000 : ℝ)^3663
        have hw : |(5178903223/10000000000 : ℝ)|=(5178903223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-474579873/2500000000 : ℝ)|^4687 ≤ (2982468123111/25000000000000 : ℝ)^3663
        have hw : |(-474579873/2500000000 : ℝ)|=(474579873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_3 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (845527533/2000000000 : ℝ)*x 0 + (389544623/1000000000 : ℝ)*x 1 + (572737177/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845527533/2000000000 : ℝ)^4687 ≤ (8308307142301/25000000000000 : ℝ)^3663 := by
    have hnat : (845527533 : ℕ)^4687*25000000000000^3663 ≤ 8308307142301^3663*2000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845527533 2000000000 8308307142301 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389544623/1000000000 : ℝ)^4687 ≤ (14964649668643/50000000000000 : ℝ)^3663 := by
    have hnat : (389544623 : ℕ)^4687*50000000000000^3663 ≤ 14964649668643^3663*1000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389544623 1000000000 14964649668643 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572737177/1250000000 : ℝ)^4687 ≤ (1151171002537/3125000000000 : ℝ)^3663 := by
    have hnat : (572737177 : ℕ)^4687*3125000000000^3663 ≤ 1151171002537^3663*1250000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572737177 1250000000 1151171002537 3125000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(845527533/2000000000 : ℝ), (389544623/1000000000 : ℝ), (572737177/1250000000 : ℝ)] ![(8308307142301/25000000000000 : ℝ), (14964649668643/50000000000000 : ℝ), (1151171002537/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(845527533/2000000000 : ℝ)|^4687 ≤ (8308307142301/25000000000000 : ℝ)^3663
        have hw : |(845527533/2000000000 : ℝ)|=(845527533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(389544623/1000000000 : ℝ)|^4687 ≤ (14964649668643/50000000000000 : ℝ)^3663
        have hw : |(389544623/1000000000 : ℝ)|=(389544623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(572737177/1250000000 : ℝ)|^4687 ≤ (1151171002537/3125000000000 : ℝ)^3663
        have hw : |(572737177/1250000000 : ℝ)|=(572737177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_4 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-109421449/625000000 : ℝ)*x 0 + (5180999699/10000000000 : ℝ)*x 1 + (5462895639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109421449/625000000 : ℝ)^4687 ≤ (5378158011339/50000000000000 : ℝ)^3663 := by
    have hnat : (109421449 : ℕ)^4687*50000000000000^3663 ≤ 5378158011339^3663*625000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109421449 625000000 5378158011339 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180999699/10000000000 : ℝ)^4687 ≤ (43109921170541/100000000000000 : ℝ)^3663 := by
    have hnat : (5180999699 : ℕ)^4687*100000000000000^3663 ≤ 43109921170541^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180999699 10000000000 43109921170541 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462895639/10000000000 : ℝ)^4687 ≤ (11533440697931/25000000000000 : ℝ)^3663 := by
    have hnat : (5462895639 : ℕ)^4687*25000000000000^3663 ≤ 11533440697931^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462895639 10000000000 11533440697931 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109421449/625000000 : ℝ), (5180999699/10000000000 : ℝ), (5462895639/10000000000 : ℝ)] ![(5378158011339/50000000000000 : ℝ), (43109921170541/100000000000000 : ℝ), (11533440697931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109421449/625000000 : ℝ)|^4687 ≤ (5378158011339/50000000000000 : ℝ)^3663
        have hw : |(-109421449/625000000 : ℝ)|=(109421449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180999699/10000000000 : ℝ)|^4687 ≤ (43109921170541/100000000000000 : ℝ)^3663
        have hw : |(5180999699/10000000000 : ℝ)|=(5180999699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462895639/10000000000 : ℝ)|^4687 ≤ (11533440697931/25000000000000 : ℝ)^3663
        have hw : |(5462895639/10000000000 : ℝ)|=(5462895639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_5 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41252593/78125000 : ℝ)*x 0 + (-403585647/2500000000 : ℝ)*x 1 + (1092579067/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41252593/78125000 : ℝ)^4687 ≤ (44170318821169/100000000000000 : ℝ)^3663 := by
    have hnat : (41252593 : ℕ)^4687*100000000000000^3663 ≤ 44170318821169^3663*78125000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41252593 78125000 44170318821169 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403585647/2500000000 : ℝ)^4687 ≤ (1211990207013/12500000000000 : ℝ)^3663 := by
    have hnat : (403585647 : ℕ)^4687*12500000000000^3663 ≤ 1211990207013^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403585647 2500000000 1211990207013 12500000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092579067/2000000000 : ℝ)^4687 ≤ (46133759506783/100000000000000 : ℝ)^3663 := by
    have hnat : (1092579067 : ℕ)^4687*100000000000000^3663 ≤ 46133759506783^3663*2000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092579067 2000000000 46133759506783 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41252593/78125000 : ℝ), (-403585647/2500000000 : ℝ), (1092579067/2000000000 : ℝ)] ![(44170318821169/100000000000000 : ℝ), (1211990207013/12500000000000 : ℝ), (46133759506783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41252593/78125000 : ℝ)|^4687 ≤ (44170318821169/100000000000000 : ℝ)^3663
        have hw : |(41252593/78125000 : ℝ)|=(41252593/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-403585647/2500000000 : ℝ)|^4687 ≤ (1211990207013/12500000000000 : ℝ)^3663
        have hw : |(-403585647/2500000000 : ℝ)|=(403585647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092579067/2000000000 : ℝ)|^4687 ≤ (46133759506783/100000000000000 : ℝ)^3663
        have hw : |(1092579067/2000000000 : ℝ)|=(1092579067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_6 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1056072061/2000000000 : ℝ)*x 0 + (5462870353/10000000000 : ℝ)*x 1 + (-807169079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056072061/2000000000 : ℝ)^4687 ≤ (22085311406287/50000000000000 : ℝ)^3663 := by
    have hnat : (1056072061 : ℕ)^4687*50000000000000^3663 ≤ 22085311406287^3663*2000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056072061 2000000000 22085311406287 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462870353/10000000000 : ℝ)^4687 ≤ (46133489558277/100000000000000 : ℝ)^3663 := by
    have hnat : (5462870353 : ℕ)^4687*100000000000000^3663 ≤ 46133489558277^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462870353 10000000000 46133489558277 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (807169079/5000000000 : ℝ)^4687 ≤ (4847943805487/50000000000000 : ℝ)^3663 := by
    have hnat : (807169079 : ℕ)^4687*50000000000000^3663 ≤ 4847943805487^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807169079 5000000000 4847943805487 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056072061/2000000000 : ℝ), (5462870353/10000000000 : ℝ), (-807169079/5000000000 : ℝ)] ![(22085311406287/50000000000000 : ℝ), (46133489558277/100000000000000 : ℝ), (4847943805487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056072061/2000000000 : ℝ)|^4687 ≤ (22085311406287/50000000000000 : ℝ)^3663
        have hw : |(1056072061/2000000000 : ℝ)|=(1056072061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462870353/10000000000 : ℝ)|^4687 ≤ (46133489558277/100000000000000 : ℝ)^3663
        have hw : |(5462870353/10000000000 : ℝ)|=(5462870353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-807169079/5000000000 : ℝ)|^4687 ≤ (4847943805487/50000000000000 : ℝ)^3663
        have hw : |(-807169079/5000000000 : ℝ)|=(807169079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_7 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16911267/40000000 : ℝ)*x 0 + (4576841987/10000000000 : ℝ)*x 1 + (3900551339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16911267/40000000 : ℝ)^4687 ≤ (8308757476161/25000000000000 : ℝ)^3663 := by
    have hnat : (16911267 : ℕ)^4687*25000000000000^3663 ≤ 8308757476161^3663*40000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16911267 40000000 8308757476161 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4576841987/10000000000 : ℝ)^4687 ≤ (7357094651771/20000000000000 : ℝ)^3663 := by
    have hnat : (4576841987 : ℕ)^4687*20000000000000^3663 ≤ 7357094651771^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4576841987 10000000000 7357094651771 20000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3900551339/10000000000 : ℝ)^4687 ≤ (14989748408459/50000000000000 : ℝ)^3663 := by
    have hnat : (3900551339 : ℕ)^4687*50000000000000^3663 ≤ 14989748408459^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3900551339 10000000000 14989748408459 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16911267/40000000 : ℝ), (4576841987/10000000000 : ℝ), (3900551339/10000000000 : ℝ)] ![(8308757476161/25000000000000 : ℝ), (7357094651771/20000000000000 : ℝ), (14989748408459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16911267/40000000 : ℝ)|^4687 ≤ (8308757476161/25000000000000 : ℝ)^3663
        have hw : |(16911267/40000000 : ℝ)|=(16911267/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4576841987/10000000000 : ℝ)|^4687 ≤ (7357094651771/20000000000000 : ℝ)^3663
        have hw : |(4576841987/10000000000 : ℝ)|=(4576841987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3900551339/10000000000 : ℝ)|^4687 ≤ (14989748408459/50000000000000 : ℝ)^3663
        have hw : |(3900551339/10000000000 : ℝ)|=(3900551339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_8 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4826172647/10000000000 : ℝ)*x 0 + (-984296203/5000000000 : ℝ)*x 1 + (5647073573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4826172647/10000000000 : ℝ)^4687 ≤ (39368902724113/100000000000000 : ℝ)^3663 := by
    have hnat : (4826172647 : ℕ)^4687*100000000000000^3663 ≤ 39368902724113^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826172647 10000000000 39368902724113 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984296203/5000000000 : ℝ)^4687 ≤ (12497854141629/100000000000000 : ℝ)^3663 := by
    have hnat : (984296203 : ℕ)^4687*100000000000000^3663 ≤ 12497854141629^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984296203 5000000000 12497854141629 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5647073573/10000000000 : ℝ)^4687 ≤ (48133243124397/100000000000000 : ℝ)^3663 := by
    have hnat : (5647073573 : ℕ)^4687*100000000000000^3663 ≤ 48133243124397^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5647073573 10000000000 48133243124397 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4826172647/10000000000 : ℝ), (-984296203/5000000000 : ℝ), (5647073573/10000000000 : ℝ)] ![(39368902724113/100000000000000 : ℝ), (12497854141629/100000000000000 : ℝ), (48133243124397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4826172647/10000000000 : ℝ)|^4687 ≤ (39368902724113/100000000000000 : ℝ)^3663
        have hw : |(4826172647/10000000000 : ℝ)|=(4826172647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-984296203/5000000000 : ℝ)|^4687 ≤ (12497854141629/100000000000000 : ℝ)^3663
        have hw : |(-984296203/5000000000 : ℝ)|=(984296203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5647073573/10000000000 : ℝ)|^4687 ≤ (48133243124397/100000000000000 : ℝ)^3663
        have hw : |(5647073573/10000000000 : ℝ)|=(5647073573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_9 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1508987867/10000000000 : ℝ)*x 0 + (5410068237/10000000000 : ℝ)*x 1 + (5408104887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1508987867/10000000000 : ℝ)^4687 ≤ (2223440361909/25000000000000 : ℝ)^3663 := by
    have hnat : (1508987867 : ℕ)^4687*25000000000000^3663 ≤ 2223440361909^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508987867 10000000000 2223440361909 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410068237/10000000000 : ℝ)^4687 ≤ (2278184883317/5000000000000 : ℝ)^3663 := by
    have hnat : (5410068237 : ℕ)^4687*5000000000000^3663 ≤ 2278184883317^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410068237 10000000000 2278184883317 5000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408104887/10000000000 : ℝ)^4687 ≤ (9108508173587/20000000000000 : ℝ)^3663 := by
    have hnat : (5408104887 : ℕ)^4687*20000000000000^3663 ≤ 9108508173587^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408104887 10000000000 9108508173587 20000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1508987867/10000000000 : ℝ), (5410068237/10000000000 : ℝ), (5408104887/10000000000 : ℝ)] ![(2223440361909/25000000000000 : ℝ), (2278184883317/5000000000000 : ℝ), (9108508173587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1508987867/10000000000 : ℝ)|^4687 ≤ (2223440361909/25000000000000 : ℝ)^3663
        have hw : |(-1508987867/10000000000 : ℝ)|=(1508987867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410068237/10000000000 : ℝ)|^4687 ≤ (2278184883317/5000000000000 : ℝ)^3663
        have hw : |(5410068237/10000000000 : ℝ)|=(5410068237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408104887/10000000000 : ℝ)|^4687 ≤ (9108508173587/20000000000000 : ℝ)^3663
        have hw : |(5408104887/10000000000 : ℝ)|=(5408104887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_10 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5891534337/10000000000 : ℝ)*x 0 + (-756303791/5000000000 : ℝ)*x 1 + (4911673557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5891534337/10000000000 : ℝ)^4687 ≤ (50815387570447/100000000000000 : ℝ)^3663 := by
    have hnat : (5891534337 : ℕ)^4687*100000000000000^3663 ≤ 50815387570447^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5891534337 10000000000 50815387570447 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (756303791/5000000000 : ℝ)^4687 ≤ (8921068677601/100000000000000 : ℝ)^3663 := by
    have hnat : (756303791 : ℕ)^4687*100000000000000^3663 ≤ 8921068677601^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756303791 5000000000 8921068677601 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4911673557/10000000000 : ℝ)^4687 ≤ (10065885936011/25000000000000 : ℝ)^3663 := by
    have hnat : (4911673557 : ℕ)^4687*25000000000000^3663 ≤ 10065885936011^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4911673557 10000000000 10065885936011 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5891534337/10000000000 : ℝ), (-756303791/5000000000 : ℝ), (4911673557/10000000000 : ℝ)] ![(50815387570447/100000000000000 : ℝ), (8921068677601/100000000000000 : ℝ), (10065885936011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5891534337/10000000000 : ℝ)|^4687 ≤ (50815387570447/100000000000000 : ℝ)^3663
        have hw : |(5891534337/10000000000 : ℝ)|=(5891534337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-756303791/5000000000 : ℝ)|^4687 ≤ (8921068677601/100000000000000 : ℝ)^3663
        have hw : |(-756303791/5000000000 : ℝ)|=(756303791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4911673557/10000000000 : ℝ)|^4687 ≤ (10065885936011/25000000000000 : ℝ)^3663
        have hw : |(4911673557/10000000000 : ℝ)|=(4911673557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_11 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1661338527/10000000000 : ℝ)*x 0 + (1338998453/2500000000 : ℝ)*x 1 + (2676967557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1661338527/10000000000 : ℝ)^4687 ≤ (5029275609331/50000000000000 : ℝ)^3663 := by
    have hnat : (1661338527 : ℕ)^4687*50000000000000^3663 ≤ 5029275609331^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1661338527 10000000000 5029275609331 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1338998453/2500000000 : ℝ)^4687 ≤ (11245446344247/25000000000000 : ℝ)^3663 := by
    have hnat : (1338998453 : ℕ)^4687*25000000000000^3663 ≤ 11245446344247^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338998453 2500000000 11245446344247 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2676967557/5000000000 : ℝ)^4687 ≤ (22479831699287/50000000000000 : ℝ)^3663 := by
    have hnat : (2676967557 : ℕ)^4687*50000000000000^3663 ≤ 22479831699287^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676967557 5000000000 22479831699287 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1661338527/10000000000 : ℝ), (1338998453/2500000000 : ℝ), (2676967557/5000000000 : ℝ)] ![(5029275609331/50000000000000 : ℝ), (11245446344247/25000000000000 : ℝ), (22479831699287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1661338527/10000000000 : ℝ)|^4687 ≤ (5029275609331/50000000000000 : ℝ)^3663
        have hw : |(-1661338527/10000000000 : ℝ)|=(1661338527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1338998453/2500000000 : ℝ)|^4687 ≤ (11245446344247/25000000000000 : ℝ)^3663
        have hw : |(1338998453/2500000000 : ℝ)|=(1338998453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2676967557/5000000000 : ℝ)|^4687 ≤ (22479831699287/50000000000000 : ℝ)^3663
        have hw : |(2676967557/5000000000 : ℝ)|=(2676967557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_12 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2807795413/5000000000 : ℝ)*x 0 + (-1307483453/10000000000 : ℝ)*x 1 + (1334916649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2807795413/5000000000 : ℝ)^4687 ≤ (5973768621303/12500000000000 : ℝ)^3663 := by
    have hnat : (2807795413 : ℕ)^4687*12500000000000^3663 ≤ 5973768621303^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2807795413 5000000000 5973768621303 12500000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307483453/10000000000 : ℝ)^4687 ≤ (1850861560633/25000000000000 : ℝ)^3663 := by
    have hnat : (1307483453 : ℕ)^4687*25000000000000^3663 ≤ 1850861560633^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307483453 10000000000 1850861560633 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1334916649/2500000000 : ℝ)^4687 ≤ (8961280953879/20000000000000 : ℝ)^3663 := by
    have hnat : (1334916649 : ℕ)^4687*20000000000000^3663 ≤ 8961280953879^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334916649 2500000000 8961280953879 20000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2807795413/5000000000 : ℝ), (-1307483453/10000000000 : ℝ), (1334916649/2500000000 : ℝ)] ![(5973768621303/12500000000000 : ℝ), (1850861560633/25000000000000 : ℝ), (8961280953879/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2807795413/5000000000 : ℝ)|^4687 ≤ (5973768621303/12500000000000 : ℝ)^3663
        have hw : |(2807795413/5000000000 : ℝ)|=(2807795413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1307483453/10000000000 : ℝ)|^4687 ≤ (1850861560633/25000000000000 : ℝ)^3663
        have hw : |(-1307483453/10000000000 : ℝ)|=(1307483453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1334916649/2500000000 : ℝ)|^4687 ≤ (8961280953879/20000000000000 : ℝ)^3663
        have hw : |(1334916649/2500000000 : ℝ)|=(1334916649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_13 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2403750633/5000000000 : ℝ)*x 0 + (5970089459/10000000000 : ℝ)*x 1 + (-385448633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2403750633/5000000000 : ℝ)^4687 ≤ (9793530071227/25000000000000 : ℝ)^3663 := by
    have hnat : (2403750633 : ℕ)^4687*25000000000000^3663 ≤ 9793530071227^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403750633 5000000000 9793530071227 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5970089459/10000000000 : ℝ)^4687 ≤ (51683958813267/100000000000000 : ℝ)^3663 := by
    have hnat : (5970089459 : ℕ)^4687*100000000000000^3663 ≤ 51683958813267^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5970089459 10000000000 51683958813267 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385448633/2500000000 : ℝ)^4687 ≤ (9141920885143/100000000000000 : ℝ)^3663 := by
    have hnat : (385448633 : ℕ)^4687*100000000000000^3663 ≤ 9141920885143^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385448633 2500000000 9141920885143 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2403750633/5000000000 : ℝ), (5970089459/10000000000 : ℝ), (-385448633/2500000000 : ℝ)] ![(9793530071227/25000000000000 : ℝ), (51683958813267/100000000000000 : ℝ), (9141920885143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2403750633/5000000000 : ℝ)|^4687 ≤ (9793530071227/25000000000000 : ℝ)^3663
        have hw : |(2403750633/5000000000 : ℝ)|=(2403750633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5970089459/10000000000 : ℝ)|^4687 ≤ (51683958813267/100000000000000 : ℝ)^3663
        have hw : |(5970089459/10000000000 : ℝ)|=(5970089459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-385448633/2500000000 : ℝ)|^4687 ≤ (9141920885143/100000000000000 : ℝ)^3663
        have hw : |(-385448633/2500000000 : ℝ)|=(385448633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_s5_14 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (809820771/2000000000 : ℝ)*x 0 + (4331346407/10000000000 : ℝ)*x 1 + (4330553109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (809820771/2000000000 : ℝ)^4687 ≤ (15724078755629/50000000000000 : ℝ)^3663 := by
    have hnat : (809820771 : ℕ)^4687*50000000000000^3663 ≤ 15724078755629^3663*2000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809820771 2000000000 15724078755629 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4331346407/10000000000 : ℝ)^4687 ≤ (3427993794953/10000000000000 : ℝ)^3663 := by
    have hnat : (4331346407 : ℕ)^4687*10000000000000^3663 ≤ 3427993794953^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331346407 10000000000 3427993794953 10000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4330553109/10000000000 : ℝ)^4687 ≤ (17135952265589/50000000000000 : ℝ)^3663 := by
    have hnat : (4330553109 : ℕ)^4687*50000000000000^3663 ≤ 17135952265589^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330553109 10000000000 17135952265589 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(809820771/2000000000 : ℝ), (4331346407/10000000000 : ℝ), (4330553109/10000000000 : ℝ)] ![(15724078755629/50000000000000 : ℝ), (3427993794953/10000000000000 : ℝ), (17135952265589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(809820771/2000000000 : ℝ)|^4687 ≤ (15724078755629/50000000000000 : ℝ)^3663
        have hw : |(809820771/2000000000 : ℝ)|=(809820771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4331346407/10000000000 : ℝ)|^4687 ≤ (3427993794953/10000000000000 : ℝ)^3663
        have hw : |(4331346407/10000000000 : ℝ)|=(4331346407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4330553109/10000000000 : ℝ)|^4687 ≤ (17135952265589/50000000000000 : ℝ)^3663
        have hw : |(4330553109/10000000000 : ℝ)|=(4330553109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1592_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169960057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10311/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1637/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4093/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4093/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4093/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4093/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4093/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4093/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10309/100000 : ℝ) ^ (4683/1024 : ℝ) ≤ (3070437411734093/100000000000000000000 : ℝ) := by
    have hpowers : (10309/100000 : ℝ)^4683 ≤ (3070437411734093/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10309 : ℕ)^4683*100000000000000000000^1024 ≤ 3070437411734093^1024*100000^4683 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10309 100000 3070437411734093 100000000000000000000 4683 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10309/100000 : ℝ)) (X := (3070437411734093/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4093/25000 : ℝ) ^ (4683/1024 : ℝ) ≤ (5092451476773167/20000000000000000000 : ℝ) := by
    have hpowers : (4093/25000 : ℝ)^4683 ≤ (5092451476773167/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4093 : ℕ)^4683*20000000000000000000^1024 ≤ 5092451476773167^1024*25000^4683 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4093 25000 5092451476773167 20000000000000000000 4683 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4093/25000 : ℝ)) (X := (5092451476773167/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50003070437411734093/50000000000000000000 : ℝ) ≤ (5000067137571713/5000000000000000 : ℝ) ^ (4683/1024 : ℝ) := by
    have hpowers : (50003070437411734093/50000000000000000000 : ℝ)^1024 ≤ (5000067137571713/5000000000000000 : ℝ)^4683 := by
      have hnat : (50003070437411734093 : ℕ)^1024*5000000000000000^4683 ≤ 5000067137571713^4683*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003070437411734093 50000000000000000000 5000067137571713 5000000000000000 1024 4683 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000067137571713/5000000000000000 : ℝ)) (X := (50003070437411734093/50000000000000000000 : ℝ)) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503566586849449991/12500000000000000000 : ℝ) ≤ (10000623835643863/10000000000000000 : ℝ) ^ (4683/1024 : ℝ) := by
    have hpowers : (12503566586849449991/12500000000000000000 : ℝ)^1024 ≤ (10000623835643863/10000000000000000 : ℝ)^4683 := by
      have hnat : (12503566586849449991 : ℕ)^1024*10000000000000000^4683 ≤ 10000623835643863^4683*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503566586849449991 12500000000000000000 10000623835643863 10000000000000000 1024 4683 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000623835643863/10000000000000000 : ℝ)) (X := (12503566586849449991/12500000000000000000 : ℝ)) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005092451476773167/10000000000000000000 : ℝ) ≤ (100011133961443/100000000000000 : ℝ) ^ (4683/1024 : ℝ) := by
    have hpowers : (10005092451476773167/10000000000000000000 : ℝ)^1024 ≤ (100011133961443/100000000000000 : ℝ)^4683 := by
      have hnat : (10005092451476773167 : ℕ)^1024*100000000000000^4683 ≤ 100011133961443^4683*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005092451476773167 10000000000000000000 100011133961443 100000000000000 1024 4683 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100011133961443/100000000000000 : ℝ)) (X := (10005092451476773167/10000000000000000000 : ℝ)) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3070437411734093/100000000000000000000 : ℝ) ≤ ((5051726695983048481/5052500000000000000 : ℝ)+2*(163186833479/202100000000000 : ℝ)*(10309/100000 : ℝ))^(4683/1024 : ℝ) := by
    rw [show (5051726695983048481/5052500000000000000 : ℝ)+2*(163186833479/202100000000000 : ℝ)*(10309/100000 : ℝ)=(5000067137571713/5000000000000000 : ℝ) by norm_num, show 1+2*(3070437411734093/100000000000000000000 : ℝ)=(50003070437411734093/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5092451476773167/20000000000000000000 : ℝ)+(3070437411734093/100000000000000000000 : ℝ) ≤ ((5051726695983048481/5052500000000000000 : ℝ)+(163186833479/202100000000000 : ℝ)*((4093/25000 : ℝ)+(10309/100000 : ℝ)))^(4683/1024 : ℝ) := by
    rw [show (5051726695983048481/5052500000000000000 : ℝ)+(163186833479/202100000000000 : ℝ)*((4093/25000 : ℝ)+(10309/100000 : ℝ))=(10000623835643863/10000000000000000 : ℝ) by norm_num, show 1+(5092451476773167/20000000000000000000 : ℝ)+(3070437411734093/100000000000000000000 : ℝ)=(12503566586849449991/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5092451476773167/20000000000000000000 : ℝ) ≤ ((5051726695983048481/5052500000000000000 : ℝ)+2*(163186833479/202100000000000 : ℝ)*(4093/25000 : ℝ))^(4683/1024 : ℝ) := by
    rw [show (5051726695983048481/5052500000000000000 : ℝ)+2*(163186833479/202100000000000 : ℝ)*(4093/25000 : ℝ)=(100011133961443/100000000000000 : ℝ) by norm_num, show 1+2*(5092451476773167/20000000000000000000 : ℝ)=(10005092451476773167/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5051726695983048481/5052500000000000000 : ℝ)*(X 1 0+X 2 0)+(163186833479/202100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4683/1024 : ℝ)) (lo := (10309/100000 : ℝ)) (hi := (4093/25000 : ℝ)) (c := (5051726695983048481/5052500000000000000 : ℝ)) (alpha := (163186833479/202100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5051726695983048481/5052500000000000000 : ℝ)*(X 0 1+X 2 1)+(163186833479/202100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4683/1024 : ℝ)) (lo := (10309/100000 : ℝ)) (hi := (4093/25000 : ℝ)) (c := (5051726695983048481/5052500000000000000 : ℝ)) (alpha := (163186833479/202100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5051726695983048481/5052500000000000000 : ℝ)*(X 0 2+X 1 2)+(163186833479/202100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4683/1024 : ℝ)) (lo := (10309/100000 : ℝ)) (hi := (4093/25000 : ℝ)) (c := (5051726695983048481/5052500000000000000 : ℝ)) (alpha := (163186833479/202100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1750662371/10000000000 : ℝ)*X 0 0+(2732509907/5000000000 : ℝ)*X 0 1+(5178903263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1339015703/2500000000 : ℝ)*X 1 0+(-949159871/5000000000 : ℝ)*X 1 1+(5178902949/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356062727/10000000000 : ℝ)*X 2 0+(5178903223/10000000000 : ℝ)*X 2 1+(-474579873/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((845527533/2000000000 : ℝ)*X 0 0+(389544623/1000000000 : ℝ)*X 0 1+(572737177/1250000000 : ℝ)*X 0 2+(845527533/2000000000 : ℝ)*X 1 0+(389544623/1000000000 : ℝ)*X 1 1+(572737177/1250000000 : ℝ)*X 1 2+(845527533/2000000000 : ℝ)*X 2 0+(389544623/1000000000 : ℝ)*X 2 1+(572737177/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-109421449/625000000 : ℝ)*X 0 0+(5180999699/10000000000 : ℝ)*X 0 1+(5462895639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41252593/78125000 : ℝ)*X 1 0+(-403585647/2500000000 : ℝ)*X 1 1+(1092579067/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056072061/2000000000 : ℝ)*X 2 0+(5462870353/10000000000 : ℝ)*X 2 1+(-807169079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((16911267/40000000 : ℝ)*X 0 0+(4576841987/10000000000 : ℝ)*X 0 1+(3900551339/10000000000 : ℝ)*X 0 2+(16911267/40000000 : ℝ)*X 1 0+(4576841987/10000000000 : ℝ)*X 1 1+(3900551339/10000000000 : ℝ)*X 1 2+(16911267/40000000 : ℝ)*X 2 0+(4576841987/10000000000 : ℝ)*X 2 1+(3900551339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((4826172647/10000000000 : ℝ)*X 1 0+(-984296203/5000000000 : ℝ)*X 1 1+(5647073573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((-1508987867/10000000000 : ℝ)*X 0 0+(5410068237/10000000000 : ℝ)*X 0 1+(5408104887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_9 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5891534337/10000000000 : ℝ)*X 1 0+(-756303791/5000000000 : ℝ)*X 1 1+(4911673557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_10 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((-1661338527/10000000000 : ℝ)*X 0 0+(1338998453/2500000000 : ℝ)*X 0 1+(2676967557/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_11 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((2807795413/5000000000 : ℝ)*X 1 0+(-1307483453/10000000000 : ℝ)*X 1 1+(1334916649/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_12 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2403750633/5000000000 : ℝ)*X 2 0+(5970089459/10000000000 : ℝ)*X 2 1+(-385448633/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_13 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((809820771/2000000000 : ℝ)*X 0 0+(4331346407/10000000000 : ℝ)*X 0 1+(4330553109/10000000000 : ℝ)*X 0 2+(809820771/2000000000 : ℝ)*X 1 0+(4331346407/10000000000 : ℝ)*X 1 1+(4330553109/10000000000 : ℝ)*X 1 2+(809820771/2000000000 : ℝ)*X 2 0+(4331346407/10000000000 : ℝ)*X 2 1+(4330553109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_s5_14 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33445632472760087152955667/7894531250000000000000000000000 : ℝ) := by norm_num
    linear_combination (26728977/25000000000000 : ℝ)*(lower2) + (71296207/100000000000000 : ℝ)*(upper4) + (4835790104067/195312500000 : ℝ)*(major0) + (4835790104067/195312500000 : ℝ)*(major1) + (4835790104067/195312500000 : ℝ)*(major2) + (873768831500933/25000000000000 : ℝ)*(sp0) + (699015011061723/20000000000000 : ℝ)*(sp1) + (873770042103619/25000000000000 : ℝ)*(sp2) + (728383282508649/50000000000000 : ℝ)*(sp3) + (1376055641/100000000000000 : ℝ)*(sp5) + (4017325933/100000000000000 : ℝ)*(sp8) + (5122686457/100000000000000 : ℝ)*(sp9) + (280275713/100000000000000 : ℝ)*(sp13) + (955819273/50000000000000 : ℝ)*(sp14) + (364192119163961/25000000000000 : ℝ)*(f.failure) + (873770112172547/25000000000000 : ℝ)*(f.sum) + (37668227853671/10105000000000000000000000000 : ℝ)*base65 + (223657603471435611/31578125000000000000000000000000 : ℝ)*base68 + (121389680599529361/31578125000000000000000000000000 : ℝ)*base70 + (11237176917689389/31578125000000000000000000000000 : ℝ)*base71 + (10919011337193/5052500000000000000000000000 : ℝ)*base73 + (43846945383654361/31578125000000000000000000000000 : ℝ)*base76 + (24425443045178743/15789062500000000000000000000000 : ℝ)*base78 + (173371121196716861/31578125000000000000000000000000 : ℝ)*base80 + (2746267974173/5052500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3905777/2500000000000000000000 : ℝ)*base89 + (3905777/2500000000000000000000 : ℝ)*base91 + (3905777/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34213432127298537201626091/25262500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (265213467/50000000000000 : ℝ)*(upper4) + (251319926959021/10000000000000 : ℝ)*(major0) + (251319926959021/10000000000000 : ℝ)*(major1) + (251319926959021/10000000000000 : ℝ)*(major2) + (70948456829751/2000000000000 : ℝ)*(sp4) + (443450379772947/12500000000000 : ℝ)*(sp5) + (1773793888574033/50000000000000 : ℝ)*(sp6) + (369664518610569/25000000000000 : ℝ)*(sp7) + (448977719/50000000000000 : ℝ)*(sp9) + (20028849891/50000000000000 : ℝ)*(sp10) + (137404735209/50000000000000 : ℝ)*(sp11) + (1732907189/3125000000000 : ℝ)*(sp12) + (5538588267/5000000000000 : ℝ)*(sp13) + (10467670209/25000000000000 : ℝ)*(sp14) + (184837493140389/12500000000000 : ℝ)*(f.failure) + (1773849274456703/50000000000000 : ℝ)*(f.sum) + (1447827472039/202100000000000000000000000 : ℝ)*base66 + (71294172118372101/50525000000000000000000000000000 : ℝ)*base67 + (415850321089372101/50525000000000000000000000000000 : ℝ)*base69 + (55288542795122101/50525000000000000000000000000000 : ℝ)*base71 + (10658115377/40420000000000000000000000 : ℝ)*base73 + (234481661584022101/50525000000000000000000000000000 : ℝ)*base75 + (155546427811022101/50525000000000000000000000000000 : ℝ)*base77 + (103341437608222101/50525000000000000000000000000000 : ℝ)*base79 + (160974598569/1010500000000000000000000000 : ℝ)*base81 + (1557827/1250000000000000000000 : ℝ)*base90 + (1557827/1250000000000000000000 : ℝ)*base92 + (1557827/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1592_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169960057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1637/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1592_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1592_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169960057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (518/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5063/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1637/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1592_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1592_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1592_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169960057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (518/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5063/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1637/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1592_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
