-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1537_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:06:16.355108+00:00
-- url     : https://prove2.me/submissions/afb733bc-7263-445c-ac87-2fed6a13f3f4

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
theorem support_rectangle_w1537_s0_0 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1659637011/10000000000 : ℝ)*x 0 + (5893837897/10000000000 : ℝ)*x 1 + (152058319/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1659637011/10000000000 : ℝ)^4571 ≤ (9881777082901/100000000000000 : ℝ)^3547 := by
    have hnat : (1659637011 : ℕ)^4571*100000000000000^3547 ≤ 9881777082901^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1659637011 10000000000 9881777082901 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5893837897/10000000000 : ℝ)^4571 ≤ (25297835908513/50000000000000 : ℝ)^3547 := by
    have hnat : (5893837897 : ℕ)^4571*50000000000000^3547 ≤ 25297835908513^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5893837897 10000000000 25297835908513 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152058319/312500000 : ℝ)^4571 ≤ (39522551087453/100000000000000 : ℝ)^3547 := by
    have hnat : (152058319 : ℕ)^4571*100000000000000^3547 ≤ 39522551087453^3547*312500000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152058319 312500000 39522551087453 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1659637011/10000000000 : ℝ), (5893837897/10000000000 : ℝ), (152058319/312500000 : ℝ)] ![(9881777082901/100000000000000 : ℝ), (25297835908513/50000000000000 : ℝ), (39522551087453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1659637011/10000000000 : ℝ)|^4571 ≤ (9881777082901/100000000000000 : ℝ)^3547
        have hw : |(-1659637011/10000000000 : ℝ)|=(1659637011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5893837897/10000000000 : ℝ)|^4571 ≤ (25297835908513/50000000000000 : ℝ)^3547
        have hw : |(5893837897/10000000000 : ℝ)|=(5893837897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(152058319/312500000 : ℝ)|^4571 ≤ (39522551087453/100000000000000 : ℝ)^3547
        have hw : |(152058319/312500000 : ℝ)|=(152058319/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s0_1 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (342035063/625000000 : ℝ)*x 0 + (-8726593/39062500 : ℝ)*x 1 + (4865866259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342035063/625000000 : ℝ)^4571 ≤ (11496023558129/25000000000000 : ℝ)^3547 := by
    have hnat : (342035063 : ℕ)^4571*25000000000000^3547 ≤ 11496023558129^3547*625000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342035063 625000000 11496023558129 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8726593/39062500 : ℝ)^4571 ≤ (2898670827397/20000000000000 : ℝ)^3547 := by
    have hnat : (8726593 : ℕ)^4571*20000000000000^3547 ≤ 2898670827397^3547*39062500^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8726593 39062500 2898670827397 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4865866259/10000000000 : ℝ)^4571 ≤ (7904510324257/20000000000000 : ℝ)^3547 := by
    have hnat : (4865866259 : ℕ)^4571*20000000000000^3547 ≤ 7904510324257^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4865866259 10000000000 7904510324257 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(342035063/625000000 : ℝ), (-8726593/39062500 : ℝ), (4865866259/10000000000 : ℝ)] ![(11496023558129/25000000000000 : ℝ), (2898670827397/20000000000000 : ℝ), (7904510324257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(342035063/625000000 : ℝ)|^4571 ≤ (11496023558129/25000000000000 : ℝ)^3547
        have hw : |(342035063/625000000 : ℝ)|=(342035063/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8726593/39062500 : ℝ)|^4571 ≤ (2898670827397/20000000000000 : ℝ)^3547
        have hw : |(-8726593/39062500 : ℝ)|=(8726593/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4865866259/10000000000 : ℝ)|^4571 ≤ (7904510324257/20000000000000 : ℝ)^3547
        have hw : |(4865866259/10000000000 : ℝ)|=(4865866259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s0_2 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5472560957/10000000000 : ℝ)*x 0 + (4865866237/10000000000 : ℝ)*x 1 + (-2234007901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5472560957/10000000000 : ℝ)^4571 ≤ (5748011710033/12500000000000 : ℝ)^3547 := by
    have hnat : (5472560957 : ℕ)^4571*12500000000000^3547 ≤ 5748011710033^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472560957 10000000000 5748011710033 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4865866237/10000000000 : ℝ)^4571 ≤ (9880637847751/25000000000000 : ℝ)^3547 := by
    have hnat : (4865866237 : ℕ)^4571*25000000000000^3547 ≤ 9880637847751^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4865866237 10000000000 9880637847751 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2234007901/10000000000 : ℝ)^4571 ≤ (2898670982903/20000000000000 : ℝ)^3547 := by
    have hnat : (2234007901 : ℕ)^4571*20000000000000^3547 ≤ 2898670982903^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234007901 10000000000 2898670982903 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5472560957/10000000000 : ℝ), (4865866237/10000000000 : ℝ), (-2234007901/10000000000 : ℝ)] ![(5748011710033/12500000000000 : ℝ), (9880637847751/25000000000000 : ℝ), (2898670982903/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5472560957/10000000000 : ℝ)|^4571 ≤ (5748011710033/12500000000000 : ℝ)^3547
        have hw : |(5472560957/10000000000 : ℝ)|=(5472560957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4865866237/10000000000 : ℝ)|^4571 ≤ (9880637847751/25000000000000 : ℝ)^3547
        have hw : |(4865866237/10000000000 : ℝ)|=(4865866237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2234007901/10000000000 : ℝ)|^4571 ≤ (2898670982903/20000000000000 : ℝ)^3547
        have hw : |(-2234007901/10000000000 : ℝ)|=(2234007901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s0_3 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2069234507/5000000000 : ℝ)*x 0 + (1545872479/5000000000 : ℝ)*x 1 + (2731940183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069234507/5000000000 : ℝ)^4571 ≤ (32079188474409/100000000000000 : ℝ)^3547 := by
    have hnat : (2069234507 : ℕ)^4571*100000000000000^3547 ≤ 32079188474409^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069234507 5000000000 32079188474409 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1545872479/5000000000 : ℝ)^4571 ≤ (2203069381413/10000000000000 : ℝ)^3547 := by
    have hnat : (1545872479 : ℕ)^4571*10000000000000^3547 ≤ 2203069381413^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545872479 5000000000 2203069381413 10000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731940183/5000000000 : ℝ)^4571 ≤ (917802354003/2000000000000 : ℝ)^3547 := by
    have hnat : (2731940183 : ℕ)^4571*2000000000000^3547 ≤ 917802354003^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731940183 5000000000 917802354003 2000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2069234507/5000000000 : ℝ), (1545872479/5000000000 : ℝ), (2731940183/5000000000 : ℝ)] ![(32079188474409/100000000000000 : ℝ), (2203069381413/10000000000000 : ℝ), (917802354003/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2069234507/5000000000 : ℝ)|^4571 ≤ (32079188474409/100000000000000 : ℝ)^3547
        have hw : |(2069234507/5000000000 : ℝ)|=(2069234507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1545872479/5000000000 : ℝ)|^4571 ≤ (2203069381413/10000000000000 : ℝ)^3547
        have hw : |(1545872479/5000000000 : ℝ)|=(1545872479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731940183/5000000000 : ℝ)|^4571 ≤ (917802354003/2000000000000 : ℝ)^3547
        have hw : |(2731940183/5000000000 : ℝ)|=(2731940183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s0_4 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1662948241/10000000000 : ℝ)*x 0 + (4891958023/10000000000 : ℝ)*x 1 + (2933408137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1662948241/10000000000 : ℝ)^4571 ≤ (4953595930433/50000000000000 : ℝ)^3547 := by
    have hnat : (1662948241 : ℕ)^4571*50000000000000^3547 ≤ 4953595930433^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1662948241 10000000000 4953595930433 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4891958023/10000000000 : ℝ)^4571 ≤ (39795873173427/100000000000000 : ℝ)^3547 := by
    have hnat : (4891958023 : ℕ)^4571*100000000000000^3547 ≤ 39795873173427^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4891958023 10000000000 39795873173427 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2933408137/5000000000 : ℝ)^4571 ≤ (50296934950069/100000000000000 : ℝ)^3547 := by
    have hnat : (2933408137 : ℕ)^4571*100000000000000^3547 ≤ 50296934950069^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2933408137 5000000000 50296934950069 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1662948241/10000000000 : ℝ), (4891958023/10000000000 : ℝ), (2933408137/5000000000 : ℝ)] ![(4953595930433/50000000000000 : ℝ), (39795873173427/100000000000000 : ℝ), (50296934950069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1662948241/10000000000 : ℝ)|^4571 ≤ (4953595930433/50000000000000 : ℝ)^3547
        have hw : |(-1662948241/10000000000 : ℝ)|=(1662948241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4891958023/10000000000 : ℝ)|^4571 ≤ (39795873173427/100000000000000 : ℝ)^3547
        have hw : |(4891958023/10000000000 : ℝ)|=(4891958023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2933408137/5000000000 : ℝ)|^4571 ≤ (50296934950069/100000000000000 : ℝ)^3547
        have hw : |(2933408137/5000000000 : ℝ)|=(2933408137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s0_5 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2595807347/5000000000 : ℝ)*x 0 + (-616528649/5000000000 : ℝ)*x 1 + (733351953/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2595807347/5000000000 : ℝ)^4571 ≤ (8592940087803/20000000000000 : ℝ)^3547 := by
    have hnat : (2595807347 : ℕ)^4571*20000000000000^3547 ≤ 8592940087803^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595807347 5000000000 8592940087803 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (616528649/5000000000 : ℝ)^4571 ≤ (16845929423/250000000000 : ℝ)^3547 := by
    have hnat : (616528649 : ℕ)^4571*250000000000^3547 ≤ 16845929423^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616528649 5000000000 16845929423 250000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (733351953/1250000000 : ℝ)^4571 ≤ (2514846388439/5000000000000 : ℝ)^3547 := by
    have hnat : (733351953 : ℕ)^4571*5000000000000^3547 ≤ 2514846388439^3547*1250000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733351953 1250000000 2514846388439 5000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2595807347/5000000000 : ℝ), (-616528649/5000000000 : ℝ), (733351953/1250000000 : ℝ)] ![(8592940087803/20000000000000 : ℝ), (16845929423/250000000000 : ℝ), (2514846388439/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2595807347/5000000000 : ℝ)|^4571 ≤ (8592940087803/20000000000000 : ℝ)^3547
        have hw : |(2595807347/5000000000 : ℝ)|=(2595807347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-616528649/5000000000 : ℝ)|^4571 ≤ (16845929423/250000000000 : ℝ)^3547
        have hw : |(-616528649/5000000000 : ℝ)|=(616528649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(733351953/1250000000 : ℝ)|^4571 ≤ (2514846388439/5000000000000 : ℝ)^3547
        have hw : |(733351953/1250000000 : ℝ)|=(733351953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s0_6 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5191614391/10000000000 : ℝ)*x 0 + (2933407621/5000000000 : ℝ)*x 1 + (-1233058357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5191614391/10000000000 : ℝ)^4571 ≤ (10741174301883/25000000000000 : ℝ)^3547 := by
    have hnat : (5191614391 : ℕ)^4571*25000000000000^3547 ≤ 10741174301883^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191614391 10000000000 10741174301883 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2933407621/5000000000 : ℝ)^4571 ≤ (50296923548391/100000000000000 : ℝ)^3547 := by
    have hnat : (2933407621 : ℕ)^4571*100000000000000^3547 ≤ 50296923548391^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2933407621 5000000000 50296923548391 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1233058357/10000000000 : ℝ)^4571 ≤ (6738379227121/100000000000000 : ℝ)^3547 := by
    have hnat : (1233058357 : ℕ)^4571*100000000000000^3547 ≤ 6738379227121^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233058357 10000000000 6738379227121 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5191614391/10000000000 : ℝ), (2933407621/5000000000 : ℝ), (-1233058357/10000000000 : ℝ)] ![(10741174301883/25000000000000 : ℝ), (50296923548391/100000000000000 : ℝ), (6738379227121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5191614391/10000000000 : ℝ)|^4571 ≤ (10741174301883/25000000000000 : ℝ)^3547
        have hw : |(5191614391/10000000000 : ℝ)|=(5191614391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2933407621/5000000000 : ℝ)|^4571 ≤ (50296923548391/100000000000000 : ℝ)^3547
        have hw : |(2933407621/5000000000 : ℝ)|=(2933407621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1233058357/10000000000 : ℝ)|^4571 ≤ (6738379227121/100000000000000 : ℝ)^3547
        have hw : |(-1233058357/10000000000 : ℝ)|=(1233058357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s0_7 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (414611199/1000000000 : ℝ)*x 0 + (5403671863/10000000000 : ℝ)*x 1 + (3154100829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414611199/1000000000 : ℝ)^4571 ≤ (32155556559897/100000000000000 : ℝ)^3547 := by
    have hnat : (414611199 : ℕ)^4571*100000000000000^3547 ≤ 32155556559897^3547*1000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414611199 1000000000 32155556559897 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403671863/10000000000 : ℝ)^4571 ≤ (45239489789443/100000000000000 : ℝ)^3547 := by
    have hnat : (5403671863 : ℕ)^4571*100000000000000^3547 ≤ 45239489789443^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403671863 10000000000 45239489789443 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154100829/10000000000 : ℝ)^4571 ≤ (22604953634259/100000000000000 : ℝ)^3547 := by
    have hnat : (3154100829 : ℕ)^4571*100000000000000^3547 ≤ 22604953634259^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154100829 10000000000 22604953634259 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(414611199/1000000000 : ℝ), (5403671863/10000000000 : ℝ), (3154100829/10000000000 : ℝ)] ![(32155556559897/100000000000000 : ℝ), (45239489789443/100000000000000 : ℝ), (22604953634259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(414611199/1000000000 : ℝ)|^4571 ≤ (32155556559897/100000000000000 : ℝ)^3547
        have hw : |(414611199/1000000000 : ℝ)|=(414611199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403671863/10000000000 : ℝ)|^4571 ≤ (45239489789443/100000000000000 : ℝ)^3547
        have hw : |(5403671863/10000000000 : ℝ)|=(5403671863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154100829/10000000000 : ℝ)|^4571 ≤ (22604953634259/100000000000000 : ℝ)^3547
        have hw : |(3154100829/10000000000 : ℝ)|=(3154100829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1537_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (393/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6291/25000 : ℝ)*pair X 0 0 := by
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
  have base53 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign3]
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (4569/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4569 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4569*1^1024 ≤ 0^1024*1^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4569/1024 : ℝ) ≤ (209573271197547097/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4569 ≤ (209573271197547097/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4569*12500000000000000000^1024 ≤ 209573271197547097^1024*5^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 209573271197547097 12500000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (209573271197547097/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4569 := by
      have hnat : (1 : ℕ)^1024*1^4569 ≤ 1^4569*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12709573271197547097/12500000000000000000 : ℝ) ≤ (10037333493009677/10000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (12709573271197547097/12500000000000000000 : ℝ)^1024 ≤ (10037333493009677/10000000000000000 : ℝ)^4569 := by
      have hnat : (12709573271197547097 : ℕ)^1024*10000000000000000^4569 ≤ 10037333493009677^4569*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12709573271197547097 12500000000000000000 10037333493009677 10000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10037333493009677/10000000000000000 : ℝ)) (X := (12709573271197547097/12500000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6459573271197547097/6250000000000000000 : ℝ) ≤ (5037333493009677/5000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (6459573271197547097/6250000000000000000 : ℝ)^1024 ≤ (5037333493009677/5000000000000000 : ℝ)^4569 := by
      have hnat : (6459573271197547097 : ℕ)^1024*5000000000000000^4569 ≤ 5037333493009677^4569*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6459573271197547097 6250000000000000000 5037333493009677 5000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5037333493009677/5000000000000000 : ℝ)) (X := (6459573271197547097/6250000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(37333493009677/4000000000000000 : ℝ)*(0 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(37333493009677/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(209573271197547097/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(37333493009677/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4569/1024 : ℝ) := by
    rw [show (1 : ℝ)+(37333493009677/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10037333493009677/10000000000000000 : ℝ) by norm_num, show 1+(209573271197547097/12500000000000000000 : ℝ)+(0 : ℝ)=(12709573271197547097/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(209573271197547097/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(37333493009677/4000000000000000 : ℝ)*(2/5 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(37333493009677/4000000000000000 : ℝ)*(2/5 : ℝ)=(5037333493009677/5000000000000000 : ℝ) by norm_num, show 1+2*(209573271197547097/12500000000000000000 : ℝ)=(6459573271197547097/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(37333493009677/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (37333493009677/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(37333493009677/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (37333493009677/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(37333493009677/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (37333493009677/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1659637011/10000000000 : ℝ)*X 0 0+(5893837897/10000000000 : ℝ)*X 0 1+(152058319/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((342035063/625000000 : ℝ)*X 1 0+(-8726593/39062500 : ℝ)*X 1 1+(4865866259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5472560957/10000000000 : ℝ)*X 2 0+(4865866237/10000000000 : ℝ)*X 2 1+(-2234007901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2069234507/5000000000 : ℝ)*X 0 0+(1545872479/5000000000 : ℝ)*X 0 1+(2731940183/5000000000 : ℝ)*X 0 2+(2069234507/5000000000 : ℝ)*X 1 0+(1545872479/5000000000 : ℝ)*X 1 1+(2731940183/5000000000 : ℝ)*X 1 2+(2069234507/5000000000 : ℝ)*X 2 0+(1545872479/5000000000 : ℝ)*X 2 1+(2731940183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1662948241/10000000000 : ℝ)*X 0 0+(4891958023/10000000000 : ℝ)*X 0 1+(2933408137/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2595807347/5000000000 : ℝ)*X 1 0+(-616528649/5000000000 : ℝ)*X 1 1+(733351953/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5191614391/10000000000 : ℝ)*X 2 0+(2933407621/5000000000 : ℝ)*X 2 1+(-1233058357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((414611199/1000000000 : ℝ)*X 0 0+(5403671863/10000000000 : ℝ)*X 0 1+(3154100829/10000000000 : ℝ)*X 0 2+(414611199/1000000000 : ℝ)*X 1 0+(5403671863/10000000000 : ℝ)*X 1 1+(3154100829/10000000000 : ℝ)*X 1 2+(414611199/1000000000 : ℝ)*X 2 0+(5403671863/10000000000 : ℝ)*X 2 1+(3154100829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43498156688117011860279/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22199611/50000000000000 : ℝ)*(base1) + (349880699/50000000000000 : ℝ)*(base19) + (690695721/100000000000000 : ℝ)*(base23) + (103712033/100000000000000 : ℝ)*(upper3) + (73933957/100000000000000 : ℝ)*(upper5) + (87147348593003/12500000000000 : ℝ)*(major0) + (87147348593003/12500000000000 : ℝ)*(major1) + (87147348593003/12500000000000 : ℝ)*(major2) + (486395961765487/50000000000000 : ℝ)*(sp0) + (121599195777849/12500000000000 : ℝ)*(sp1) + (97279357528847/10000000000000 : ℝ)*(sp2) + (210781027649661/50000000000000 : ℝ)*(sp3) + (1193426219/50000000000000 : ℝ)*(sp4) + (1095810223/100000000000000 : ℝ)*(sp7) + (421563195508767/100000000000000 : ℝ)*(f.failure) + (97279426598419/10000000000000 : ℝ)*(f.sum) + (72336736659969/25000000000000000000000000000 : ℝ)*base66 + (117403470359969/50000000000000000000000000000 : ℝ)*base68 + (229897652659969/50000000000000000000000000000 : ℝ)*base70 + (251617017209969/50000000000000000000000000000 : ℝ)*base72 + (57548536234969/25000000000000000000000000000 : ℝ)*base74 + (347231278859969/50000000000000000000000000000 : ℝ)*base76 + (431325589909969/50000000000000000000000000000 : ℝ)*base78 + (582536252259969/50000000000000000000000000000 : ℝ)*base80 + (92400317734969/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2756759/400000000000000000000 : ℝ)*base89 + (2756759/400000000000000000000 : ℝ)*base91 + (2756759/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (119002098920835298040823/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81182061/20000000000000 : ℝ)*(base19) + (268032499/50000000000000 : ℝ)*(base23) + (298647/20000000000000 : ℝ)*(base53) + (21960967/20000000000000 : ℝ)*(base59) + (183789856631167/25000000000000 : ℝ)*(major0) + (183789856631167/25000000000000 : ℝ)*(major1) + (183789856631167/25000000000000 : ℝ)*(major2) + (12417131/12500000000000 : ℝ)*(sp0) + (1124235211/100000000000000 : ℝ)*(sp1) + (90910773/12500000000000 : ℝ)*(sp2) + (1025789721320261/100000000000000 : ℝ)*(sp4) + (1025788290511793/100000000000000 : ℝ)*(sp5) + (1025788557306127/100000000000000 : ℝ)*(sp6) + (444528953057291/100000000000000 : ℝ)*(sp7) + (444528953057291/100000000000000 : ℝ)*(f.failure) + (1025789820657309/100000000000000 : ℝ)*(f.sum) + (125212717753059/50000000000000000000000000000 : ℝ)*base65 + (212142568396941/100000000000000000000000000000 : ℝ)*base68 + (141819377103059/100000000000000000000000000000 : ℝ)*base69 + (411816861196941/100000000000000000000000000000 : ℝ)*base72 + (146845934253059/50000000000000000000000000000 : ℝ)*base73 + (2870421196941/100000000000000000000000000000 : ℝ)*base76 + (150942132696941/100000000000000000000000000000 : ℝ)*base78 + (279727096696941/100000000000000000000000000000 : ℝ)*base80 + (262278895003059/50000000000000000000000000000 : ℝ)*base81 + (894493/400000000000000000000 : ℝ)*base90 + (894493/400000000000000000000 : ℝ)*base92 + (894493/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1537_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (393/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6291/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1537_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1537_s1_0 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1806729397/10000000000 : ℝ)*x 0 + (5554431643/10000000000 : ℝ)*x 1 + (2555311669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1806729397/10000000000 : ℝ)^4571 ≤ (5512290741423/50000000000000 : ℝ)^3547 := by
    have hnat : (1806729397 : ℕ)^4571*50000000000000^3547 ≤ 5512290741423^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806729397 10000000000 5512290741423 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5554431643/10000000000 : ℝ)^4571 ≤ (585906694461/1250000000000 : ℝ)^3547 := by
    have hnat : (5554431643 : ℕ)^4571*1250000000000^3547 ≤ 585906694461^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5554431643 10000000000 585906694461 1250000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2555311669/5000000000 : ℝ)^4571 ≤ (8420576588477/20000000000000 : ℝ)^3547 := by
    have hnat : (2555311669 : ℕ)^4571*20000000000000^3547 ≤ 8420576588477^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2555311669 5000000000 8420576588477 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1806729397/10000000000 : ℝ), (5554431643/10000000000 : ℝ), (2555311669/5000000000 : ℝ)] ![(5512290741423/50000000000000 : ℝ), (585906694461/1250000000000 : ℝ), (8420576588477/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1806729397/10000000000 : ℝ)|^4571 ≤ (5512290741423/50000000000000 : ℝ)^3547
        have hw : |(-1806729397/10000000000 : ℝ)|=(1806729397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5554431643/10000000000 : ℝ)|^4571 ≤ (585906694461/1250000000000 : ℝ)^3547
        have hw : |(5554431643/10000000000 : ℝ)|=(5554431643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2555311669/5000000000 : ℝ)|^4571 ≤ (8420576588477/20000000000000 : ℝ)^3547
        have hw : |(2555311669/5000000000 : ℝ)|=(2555311669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s1_1 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382136283/10000000000 : ℝ)*x 0 + (-2039720381/10000000000 : ℝ)*x 1 + (5110623769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382136283/10000000000 : ℝ)^4571 ≤ (45007277506899/100000000000000 : ℝ)^3547 := by
    have hnat : (5382136283 : ℕ)^4571*100000000000000^3547 ≤ 45007277506899^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382136283 10000000000 45007277506899 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039720381/10000000000 : ℝ)^4571 ≤ (103118679689/800000000000 : ℝ)^3547 := by
    have hnat : (2039720381 : ℕ)^4571*800000000000^3547 ≤ 103118679689^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039720381 10000000000 103118679689 800000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5110623769/10000000000 : ℝ)^4571 ≤ (21051443759083/50000000000000 : ℝ)^3547 := by
    have hnat : (5110623769 : ℕ)^4571*50000000000000^3547 ≤ 21051443759083^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5110623769 10000000000 21051443759083 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382136283/10000000000 : ℝ), (-2039720381/10000000000 : ℝ), (5110623769/10000000000 : ℝ)] ![(45007277506899/100000000000000 : ℝ), (103118679689/800000000000 : ℝ), (21051443759083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382136283/10000000000 : ℝ)|^4571 ≤ (45007277506899/100000000000000 : ℝ)^3547
        have hw : |(5382136283/10000000000 : ℝ)|=(5382136283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2039720381/10000000000 : ℝ)|^4571 ≤ (103118679689/800000000000 : ℝ)^3547
        have hw : |(-2039720381/10000000000 : ℝ)|=(2039720381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5110623769/10000000000 : ℝ)|^4571 ≤ (21051443759083/50000000000000 : ℝ)^3547
        have hw : |(5110623769/10000000000 : ℝ)|=(5110623769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s1_2 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382136873/10000000000 : ℝ)*x 0 + (319413953/625000000 : ℝ)*x 1 + (-50993007/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382136873/10000000000 : ℝ)^4571 ≤ (562591048313/1250000000000 : ℝ)^3547 := by
    have hnat : (5382136873 : ℕ)^4571*1250000000000^3547 ≤ 562591048313^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382136873 10000000000 562591048313 1250000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319413953/625000000 : ℝ)^4571 ≤ (8420576397377/20000000000000 : ℝ)^3547 := by
    have hnat : (319413953 : ℕ)^4571*20000000000000^3547 ≤ 8420576397377^3547*625000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319413953 625000000 8420576397377 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50993007/250000000 : ℝ)^4571 ≤ (6444917069301/50000000000000 : ℝ)^3547 := by
    have hnat : (50993007 : ℕ)^4571*50000000000000^3547 ≤ 6444917069301^3547*250000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50993007 250000000 6444917069301 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382136873/10000000000 : ℝ), (319413953/625000000 : ℝ), (-50993007/250000000 : ℝ)] ![(562591048313/1250000000000 : ℝ), (8420576397377/20000000000000 : ℝ), (6444917069301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382136873/10000000000 : ℝ)|^4571 ≤ (562591048313/1250000000000 : ℝ)^3547
        have hw : |(5382136873/10000000000 : ℝ)|=(5382136873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(319413953/625000000 : ℝ)|^4571 ≤ (8420576397377/20000000000000 : ℝ)^3547
        have hw : |(319413953/625000000 : ℝ)|=(319413953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50993007/250000000 : ℝ)|^4571 ≤ (6444917069301/50000000000000 : ℝ)^3547
        have hw : |(-50993007/250000000 : ℝ)|=(50993007/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s1_3 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (848097937/2000000000 : ℝ)*x 0 + (750802387/2000000000 : ℝ)*x 1 + (191125507/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848097937/2000000000 : ℝ)^4571 ≤ (16550952914611/50000000000000 : ℝ)^3547 := by
    have hnat : (848097937 : ℕ)^4571*50000000000000^3547 ≤ 16550952914611^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848097937 2000000000 16550952914611 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (750802387/2000000000 : ℝ)^4571 ≤ (2829142417623/10000000000000 : ℝ)^3547 := by
    have hnat : (750802387 : ℕ)^4571*10000000000000^3547 ≤ 2829142417623^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750802387 2000000000 2829142417623 10000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191125507/400000000 : ℝ)^4571 ≤ (19303334987763/50000000000000 : ℝ)^3547 := by
    have hnat : (191125507 : ℕ)^4571*50000000000000^3547 ≤ 19303334987763^3547*400000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191125507 400000000 19303334987763 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848097937/2000000000 : ℝ), (750802387/2000000000 : ℝ), (191125507/400000000 : ℝ)] ![(16550952914611/50000000000000 : ℝ), (2829142417623/10000000000000 : ℝ), (19303334987763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848097937/2000000000 : ℝ)|^4571 ≤ (16550952914611/50000000000000 : ℝ)^3547
        have hw : |(848097937/2000000000 : ℝ)|=(848097937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(750802387/2000000000 : ℝ)|^4571 ≤ (2829142417623/10000000000000 : ℝ)^3547
        have hw : |(750802387/2000000000 : ℝ)|=(750802387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(191125507/400000000 : ℝ)|^4571 ≤ (19303334987763/50000000000000 : ℝ)^3547
        have hw : |(191125507/400000000 : ℝ)|=(191125507/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s1_4 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-903493843/5000000000 : ℝ)*x 0 + (5115415457/10000000000 : ℝ)*x 1 + (277478267/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903493843/5000000000 : ℝ)^4571 ≤ (2205322519001/20000000000000 : ℝ)^3547 := by
    have hnat : (903493843 : ℕ)^4571*20000000000000^3547 ≤ 2205322519001^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903493843 5000000000 2205322519001 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5115415457/10000000000 : ℝ)^4571 ≤ (42153766135013/100000000000000 : ℝ)^3547 := by
    have hnat : (5115415457 : ℕ)^4571*100000000000000^3547 ≤ 42153766135013^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5115415457 10000000000 42153766135013 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277478267/500000000 : ℝ)^4571 ≤ (11704905313993/25000000000000 : ℝ)^3547 := by
    have hnat : (277478267 : ℕ)^4571*25000000000000^3547 ≤ 11704905313993^3547*500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277478267 500000000 11704905313993 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-903493843/5000000000 : ℝ), (5115415457/10000000000 : ℝ), (277478267/500000000 : ℝ)] ![(2205322519001/20000000000000 : ℝ), (42153766135013/100000000000000 : ℝ), (11704905313993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-903493843/5000000000 : ℝ)|^4571 ≤ (2205322519001/20000000000000 : ℝ)^3547
        have hw : |(-903493843/5000000000 : ℝ)|=(903493843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5115415457/10000000000 : ℝ)|^4571 ≤ (42153766135013/100000000000000 : ℝ)^3547
        have hw : |(5115415457/10000000000 : ℝ)|=(5115415457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(277478267/500000000 : ℝ)|^4571 ≤ (11704905313993/25000000000000 : ℝ)^3547
        have hw : |(277478267/500000000 : ℝ)|=(277478267/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s1_5 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264902217/10000000000 : ℝ)*x 0 + (-320155751/2000000000 : ℝ)*x 1 + (1387391331/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264902217/10000000000 : ℝ)^4571 ≤ (5468487069761/12500000000000 : ℝ)^3547 := by
    have hnat : (5264902217 : ℕ)^4571*12500000000000^3547 ≤ 5468487069761^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264902217 10000000000 5468487069761 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320155751/2000000000 : ℝ)^4571 ≤ (4716241175449/50000000000000 : ℝ)^3547 := by
    have hnat : (320155751 : ℕ)^4571*50000000000000^3547 ≤ 4716241175449^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320155751 2000000000 4716241175449 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1387391331/2500000000 : ℝ)^4571 ≤ (1463113158813/3125000000000 : ℝ)^3547 := by
    have hnat : (1387391331 : ℕ)^4571*3125000000000^3547 ≤ 1463113158813^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387391331 2500000000 1463113158813 3125000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264902217/10000000000 : ℝ), (-320155751/2000000000 : ℝ), (1387391331/2500000000 : ℝ)] ![(5468487069761/12500000000000 : ℝ), (4716241175449/50000000000000 : ℝ), (1463113158813/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264902217/10000000000 : ℝ)|^4571 ≤ (5468487069761/12500000000000 : ℝ)^3547
        have hw : |(5264902217/10000000000 : ℝ)|=(5264902217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-320155751/2000000000 : ℝ)|^4571 ≤ (4716241175449/50000000000000 : ℝ)^3547
        have hw : |(-320155751/2000000000 : ℝ)|=(320155751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1387391331/2500000000 : ℝ)|^4571 ≤ (1463113158813/3125000000000 : ℝ)^3547
        have hw : |(1387391331/2500000000 : ℝ)|=(1387391331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s1_6 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632451253/5000000000 : ℝ)*x 0 + (5549565301/10000000000 : ℝ)*x 1 + (-80038919/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632451253/5000000000 : ℝ)^4571 ≤ (1093697491319/2500000000000 : ℝ)^3547 := by
    have hnat : (2632451253 : ℕ)^4571*2500000000000^3547 ≤ 1093697491319^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632451253 5000000000 1093697491319 2500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5549565301/10000000000 : ℝ)^4571 ≤ (9363924166391/20000000000000 : ℝ)^3547 := by
    have hnat : (5549565301 : ℕ)^4571*20000000000000^3547 ≤ 9363924166391^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5549565301 10000000000 9363924166391 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80038919/500000000 : ℝ)^4571 ≤ (4716239751659/50000000000000 : ℝ)^3547 := by
    have hnat : (80038919 : ℕ)^4571*50000000000000^3547 ≤ 4716239751659^3547*500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80038919 500000000 4716239751659 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632451253/5000000000 : ℝ), (5549565301/10000000000 : ℝ), (-80038919/500000000 : ℝ)] ![(1093697491319/2500000000000 : ℝ), (9363924166391/20000000000000 : ℝ), (4716239751659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632451253/5000000000 : ℝ)|^4571 ≤ (1093697491319/2500000000000 : ℝ)^3547
        have hw : |(2632451253/5000000000 : ℝ)|=(2632451253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5549565301/10000000000 : ℝ)|^4571 ≤ (9363924166391/20000000000000 : ℝ)^3547
        have hw : |(5549565301/10000000000 : ℝ)|=(5549565301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-80038919/500000000 : ℝ)|^4571 ≤ (4716239751659/50000000000000 : ℝ)^3547
        have hw : |(-80038919/500000000 : ℝ)|=(80038919/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s1_7 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4241086691/10000000000 : ℝ)*x 0 + (2383539809/5000000000 : ℝ)*x 1 + (3765240329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4241086691/10000000000 : ℝ)^4571 ≤ (33107911680061/100000000000000 : ℝ)^3547 := by
    have hnat : (4241086691 : ℕ)^4571*100000000000000^3547 ≤ 33107911680061^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241086691 10000000000 33107911680061 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2383539809/5000000000 : ℝ)^4571 ≤ (38491566786801/100000000000000 : ℝ)^3547 := by
    have hnat : (2383539809 : ℕ)^4571*100000000000000^3547 ≤ 38491566786801^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383539809 5000000000 38491566786801 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3765240329/10000000000 : ℝ)^4571 ≤ (14200260759167/50000000000000 : ℝ)^3547 := by
    have hnat : (3765240329 : ℕ)^4571*50000000000000^3547 ≤ 14200260759167^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3765240329 10000000000 14200260759167 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4241086691/10000000000 : ℝ), (2383539809/5000000000 : ℝ), (3765240329/10000000000 : ℝ)] ![(33107911680061/100000000000000 : ℝ), (38491566786801/100000000000000 : ℝ), (14200260759167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4241086691/10000000000 : ℝ)|^4571 ≤ (33107911680061/100000000000000 : ℝ)^3547
        have hw : |(4241086691/10000000000 : ℝ)|=(4241086691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2383539809/5000000000 : ℝ)|^4571 ≤ (38491566786801/100000000000000 : ℝ)^3547
        have hw : |(2383539809/5000000000 : ℝ)|=(2383539809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3765240329/10000000000 : ℝ)|^4571 ≤ (14200260759167/50000000000000 : ℝ)^3547
        have hw : |(3765240329/10000000000 : ℝ)|=(3765240329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1537_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6291/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (8679/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18071/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6291/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (393/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6291/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (393/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6291/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (393/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6291/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (393/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6291/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (393/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6291/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (393/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (393/12500 : ℝ) ^ (4569/1024 : ℝ) ≤ (9882486020263/50000000000000000000 : ℝ) := by
    have hpowers : (393/12500 : ℝ)^4569 ≤ (9882486020263/50000000000000000000 : ℝ)^1024 := by
      have hnat : (393 : ℕ)^4569*50000000000000000000^1024 ≤ 9882486020263^1024*12500^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        393 12500 9882486020263 50000000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (393/12500 : ℝ)) (X := (9882486020263/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6291/25000 : ℝ) ^ (4569/1024 : ℝ) ≤ (211997340180350431/100000000000000000000 : ℝ) := by
    have hpowers : (6291/25000 : ℝ)^4569 ≤ (211997340180350431/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6291 : ℕ)^4569*100000000000000000000^1024 ≤ 211997340180350431^1024*25000^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6291 25000 211997340180350431 100000000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6291/25000 : ℝ)) (X := (211997340180350431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000009882486020263/25000000000000000000 : ℝ) ≤ (2500000221485317/2500000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (25000009882486020263/25000000000000000000 : ℝ)^1024 ≤ (2500000221485317/2500000000000000 : ℝ)^4569 := by
      have hnat : (25000009882486020263 : ℕ)^1024*2500000000000000^4569 ≤ 2500000221485317^4569*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000009882486020263 25000000000000000000 2500000221485317 2500000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000221485317/2500000000000000 : ℝ)) (X := (25000009882486020263/25000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100212017105152390957/100000000000000000000 : ℝ) ≤ (5002373902058899/5000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (100212017105152390957/100000000000000000000 : ℝ)^1024 ≤ (5002373902058899/5000000000000000 : ℝ)^4569 := by
      have hnat : (100212017105152390957 : ℕ)^1024*5000000000000000^4569 ≤ 5002373902058899^4569*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100212017105152390957 100000000000000000000 5002373902058899 5000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002373902058899/5000000000000000 : ℝ)) (X := (100212017105152390957/100000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50211997340180350431/50000000000000000000 : ℝ) ≤ (1251186840286791/1250000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (50211997340180350431/50000000000000000000 : ℝ)^1024 ≤ (1251186840286791/1250000000000000 : ℝ)^4569 := by
      have hnat : (50211997340180350431 : ℕ)^1024*1250000000000000^4569 ≤ 1251186840286791^4569*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50211997340180350431 50000000000000000000 1251186840286791 1250000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251186840286791/1250000000000000 : ℝ)) (X := (50211997340180350431/50000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9882486020263/50000000000000000000 : ℝ) ≤ ((917375712028886253/917500000000000000 : ℝ)+2*(474691817653/220200000000000 : ℝ)*(393/12500 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (917375712028886253/917500000000000000 : ℝ)+2*(474691817653/220200000000000 : ℝ)*(393/12500 : ℝ)=(2500000221485317/2500000000000000 : ℝ) by norm_num, show 1+2*(9882486020263/50000000000000000000 : ℝ)=(25000009882486020263/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(211997340180350431/100000000000000000000 : ℝ)+(9882486020263/50000000000000000000 : ℝ) ≤ ((917375712028886253/917500000000000000 : ℝ)+(474691817653/220200000000000 : ℝ)*((6291/25000 : ℝ)+(393/12500 : ℝ)))^(4569/1024 : ℝ) := by
    rw [show (917375712028886253/917500000000000000 : ℝ)+(474691817653/220200000000000 : ℝ)*((6291/25000 : ℝ)+(393/12500 : ℝ))=(5002373902058899/5000000000000000 : ℝ) by norm_num, show 1+(211997340180350431/100000000000000000000 : ℝ)+(9882486020263/50000000000000000000 : ℝ)=(100212017105152390957/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(211997340180350431/100000000000000000000 : ℝ) ≤ ((917375712028886253/917500000000000000 : ℝ)+2*(474691817653/220200000000000 : ℝ)*(6291/25000 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (917375712028886253/917500000000000000 : ℝ)+2*(474691817653/220200000000000 : ℝ)*(6291/25000 : ℝ)=(1251186840286791/1250000000000000 : ℝ) by norm_num, show 1+2*(211997340180350431/100000000000000000000 : ℝ)=(50211997340180350431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (917375712028886253/917500000000000000 : ℝ)*(X 1 0+X 2 0)+(474691817653/220200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (393/12500 : ℝ)) (hi := (6291/25000 : ℝ)) (c := (917375712028886253/917500000000000000 : ℝ)) (alpha := (474691817653/220200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (917375712028886253/917500000000000000 : ℝ)*(X 0 1+X 2 1)+(474691817653/220200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (393/12500 : ℝ)) (hi := (6291/25000 : ℝ)) (c := (917375712028886253/917500000000000000 : ℝ)) (alpha := (474691817653/220200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (917375712028886253/917500000000000000 : ℝ)*(X 0 2+X 1 2)+(474691817653/220200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (393/12500 : ℝ)) (hi := (6291/25000 : ℝ)) (c := (917375712028886253/917500000000000000 : ℝ)) (alpha := (474691817653/220200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1806729397/10000000000 : ℝ)*X 0 0+(5554431643/10000000000 : ℝ)*X 0 1+(2555311669/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5382136283/10000000000 : ℝ)*X 1 0+(-2039720381/10000000000 : ℝ)*X 1 1+(5110623769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5382136873/10000000000 : ℝ)*X 2 0+(319413953/625000000 : ℝ)*X 2 1+(-50993007/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((848097937/2000000000 : ℝ)*X 0 0+(750802387/2000000000 : ℝ)*X 0 1+(191125507/400000000 : ℝ)*X 0 2+(848097937/2000000000 : ℝ)*X 1 0+(750802387/2000000000 : ℝ)*X 1 1+(191125507/400000000 : ℝ)*X 1 2+(848097937/2000000000 : ℝ)*X 2 0+(750802387/2000000000 : ℝ)*X 2 1+(191125507/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-903493843/5000000000 : ℝ)*X 0 0+(5115415457/10000000000 : ℝ)*X 0 1+(277478267/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5264902217/10000000000 : ℝ)*X 1 0+(-320155751/2000000000 : ℝ)*X 1 1+(1387391331/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2632451253/5000000000 : ℝ)*X 2 0+(5549565301/10000000000 : ℝ)*X 2 1+(-80038919/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4241086691/10000000000 : ℝ)*X 0 0+(2383539809/5000000000 : ℝ)*X 0 1+(3765240329/10000000000 : ℝ)*X 0 2+(4241086691/10000000000 : ℝ)*X 1 0+(2383539809/5000000000 : ℝ)*X 1 1+(3765240329/10000000000 : ℝ)*X 1 2+(4241086691/10000000000 : ℝ)*X 2 0+(2383539809/5000000000 : ℝ)*X 2 1+(3765240329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (430005242465051112726636691/45875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (696375437/50000000000000 : ℝ)*(base19) + (62652203/4000000000000 : ℝ)*(base23) + (78939369/50000000000000 : ℝ)*(upper3) + (39532493/100000000000000 : ℝ)*(upper4) + (3209497/1562500000000 : ℝ)*(upper5) + (1614852226639183/100000000000000 : ℝ)*(major0) + (1614852226639183/100000000000000 : ℝ)*(major1) + (1614852226639183/100000000000000 : ℝ)*(major2) + (450647417999319/20000000000000 : ℝ)*(sp0) + (563312456695483/25000000000000 : ℝ)*(sp1) + (2253249653227731/100000000000000 : ℝ)*(sp2) + (122055956408991/12500000000000 : ℝ)*(sp3) + (14129536211/100000000000000 : ℝ)*(sp4) + (1054005317/20000000000000 : ℝ)*(sp7) + (976452921298513/100000000000000 : ℝ)*(f.failure) + (1126625609766403/50000000000000 : ℝ)*(f.sum) + (6467106983959/11010000000000000000000000000 : ℝ)*base65 + (3212326267047208603/275250000000000000000000000000000 : ℝ)*base68 + (1205952082745458603/275250000000000000000000000000000 : ℝ)*base70 + (731775317384458603/275250000000000000000000000000000 : ℝ)*base72 + (51686690891681/11010000000000000000000000000 : ℝ)*base74 + (1996162038909958603/275250000000000000000000000000000 : ℝ)*base76 + (1594735375911208603/275250000000000000000000000000000 : ℝ)*base78 + (533048623266208603/275250000000000000000000000000000 : ℝ)*base80 + (11724302370649/11010000000000000000000000000 : ℝ)*base81 + (1331801/400000000000000000000 : ℝ)*base89 + (1331801/400000000000000000000 : ℝ)*base91 + (1331801/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22741813812757015900322361/5734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50724513/10000000000000 : ℝ)*(base19) + (147022101/20000000000000 : ℝ)*(base23) + (104077937/100000000000000 : ℝ)*(upper3) + (23768929/100000000000000 : ℝ)*(lower4) + (49577749/50000000000000 : ℝ)*(upper5) + (206344788330027/12500000000000 : ℝ)*(major0) + (206344788330027/12500000000000 : ℝ)*(major1) + (206344788330027/12500000000000 : ℝ)*(major2) + (2687893861/100000000000000 : ℝ)*(sp1) + (2607783833/50000000000000 : ℝ)*(sp2) + (1151676112689871/50000000000000 : ℝ)*(sp4) + (143959314390047/6250000000000 : ℝ)*(sp5) + (575836568675393/25000000000000 : ℝ)*(sp6) + (998164255704853/100000000000000 : ℝ)*(sp7) + (998164255704853/100000000000000 : ℝ)*(f.failure) + (1151676112689871/50000000000000 : ℝ)*(f.sum) + (1664717411323/1835000000000000000000000000 : ℝ)*base65 + (68107747186631331/11468750000000000000000000000000 : ℝ)*base67 + (15312507360962419/11468750000000000000000000000000 : ℝ)*base70 + (24300089096931169/11468750000000000000000000000000 : ℝ)*base72 + (12744214472753/1835000000000000000000000000 : ℝ)*base73 + (69276685987806169/11468750000000000000000000000000 : ℝ)*base76 + (27058117068837419/11468750000000000000000000000000 : ℝ)*base78 + (87369282509681169/11468750000000000000000000000000 : ℝ)*base80 + (96850266987/1835000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1646019/400000000000000000000 : ℝ)*base90 + (1646019/400000000000000000000 : ℝ)*base92 + (1646019/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1537_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6291/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8679/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18071/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1537_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1537_s2_0 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1828516459/10000000000 : ℝ)*x 0 + (1090065941/2000000000 : ℝ)*x 1 + (1300143919/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1828516459/10000000000 : ℝ)^4571 ≤ (11196202652997/100000000000000 : ℝ)^3547 := by
    have hnat : (1828516459 : ℕ)^4571*100000000000000^3547 ≤ 11196202652997^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828516459 10000000000 11196202652997 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090065941/2000000000 : ℝ)^4571 ≤ (11435876138627/25000000000000 : ℝ)^3547 := by
    have hnat : (1090065941 : ℕ)^4571*25000000000000^3547 ≤ 11435876138627^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090065941 2000000000 11435876138627 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1300143919/2500000000 : ℝ)^4571 ≤ (43060292784989/100000000000000 : ℝ)^3547 := by
    have hnat : (1300143919 : ℕ)^4571*100000000000000^3547 ≤ 43060292784989^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300143919 2500000000 43060292784989 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1828516459/10000000000 : ℝ), (1090065941/2000000000 : ℝ), (1300143919/2500000000 : ℝ)] ![(11196202652997/100000000000000 : ℝ), (11435876138627/25000000000000 : ℝ), (43060292784989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1828516459/10000000000 : ℝ)|^4571 ≤ (11196202652997/100000000000000 : ℝ)^3547
        have hw : |(-1828516459/10000000000 : ℝ)|=(1828516459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090065941/2000000000 : ℝ)|^4571 ≤ (11435876138627/25000000000000 : ℝ)^3547
        have hw : |(1090065941/2000000000 : ℝ)|=(1090065941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1300143919/2500000000 : ℝ)|^4571 ≤ (43060292784989/100000000000000 : ℝ)^3547
        have hw : |(1300143919/2500000000 : ℝ)|=(1300143919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s2_1 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338871789/2500000000 : ℝ)*x 0 + (-1956906351/10000000000 : ℝ)*x 1 + (5200575949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338871789/2500000000 : ℝ)^4571 ≤ (2795018653461/6250000000000 : ℝ)^3547 := by
    have hnat : (1338871789 : ℕ)^4571*6250000000000^3547 ≤ 2795018653461^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338871789 2500000000 2795018653461 6250000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1956906351/10000000000 : ℝ)^4571 ≤ (6109702916101/50000000000000 : ℝ)^3547 := by
    have hnat : (1956906351 : ℕ)^4571*50000000000000^3547 ≤ 6109702916101^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956906351 10000000000 6109702916101 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5200575949/10000000000 : ℝ)^4571 ≤ (21530147848987/50000000000000 : ℝ)^3547 := by
    have hnat : (5200575949 : ℕ)^4571*50000000000000^3547 ≤ 21530147848987^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200575949 10000000000 21530147848987 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338871789/2500000000 : ℝ), (-1956906351/10000000000 : ℝ), (5200575949/10000000000 : ℝ)] ![(2795018653461/6250000000000 : ℝ), (6109702916101/50000000000000 : ℝ), (21530147848987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338871789/2500000000 : ℝ)|^4571 ≤ (2795018653461/6250000000000 : ℝ)^3547
        have hw : |(1338871789/2500000000 : ℝ)|=(1338871789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1956906351/10000000000 : ℝ)|^4571 ≤ (6109702916101/50000000000000 : ℝ)^3547
        have hw : |(-1956906351/10000000000 : ℝ)|=(1956906351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5200575949/10000000000 : ℝ)|^4571 ≤ (21530147848987/50000000000000 : ℝ)^3547
        have hw : |(5200575949/10000000000 : ℝ)|=(5200575949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s2_2 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355487799/10000000000 : ℝ)*x 0 + (260028779/500000000 : ℝ)*x 1 + (-97845299/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355487799/10000000000 : ℝ)^4571 ≤ (44720305374749/100000000000000 : ℝ)^3547 := by
    have hnat : (5355487799 : ℕ)^4571*100000000000000^3547 ≤ 44720305374749^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355487799 10000000000 44720305374749 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260028779/500000000 : ℝ)^4571 ≤ (21530145880321/50000000000000 : ℝ)^3547 := by
    have hnat : (260028779 : ℕ)^4571*50000000000000^3547 ≤ 21530145880321^3547*500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260028779 500000000 21530145880321 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97845299/500000000 : ℝ)^4571 ≤ (1527425355849/12500000000000 : ℝ)^3547 := by
    have hnat : (97845299 : ℕ)^4571*12500000000000^3547 ≤ 1527425355849^3547*500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97845299 500000000 1527425355849 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355487799/10000000000 : ℝ), (260028779/500000000 : ℝ), (-97845299/500000000 : ℝ)] ![(44720305374749/100000000000000 : ℝ), (21530145880321/50000000000000 : ℝ), (1527425355849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355487799/10000000000 : ℝ)|^4571 ≤ (44720305374749/100000000000000 : ℝ)^3547
        have hw : |(5355487799/10000000000 : ℝ)|=(5355487799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260028779/500000000 : ℝ)|^4571 ≤ (21530145880321/50000000000000 : ℝ)^3547
        have hw : |(260028779/500000000 : ℝ)|=(260028779/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97845299/500000000 : ℝ)|^4571 ≤ (1527425355849/12500000000000 : ℝ)^3547
        have hw : |(-97845299/500000000 : ℝ)|=(97845299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s2_3 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4256196717/10000000000 : ℝ)*x 0 + (397613839/1000000000 : ℝ)*x 1 + (4552469407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256196717/10000000000 : ℝ)^4571 ≤ (33259998992129/100000000000000 : ℝ)^3547 := by
    have hnat : (4256196717 : ℕ)^4571*100000000000000^3547 ≤ 33259998992129^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256196717 10000000000 33259998992129 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397613839/1000000000 : ℝ)^4571 ≤ (30466892384643/100000000000000 : ℝ)^3547 := by
    have hnat : (397613839 : ℕ)^4571*100000000000000^3547 ≤ 30466892384643^3547*1000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397613839 1000000000 30466892384643 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4552469407/10000000000 : ℝ)^4571 ≤ (283383661023/781250000000 : ℝ)^3547 := by
    have hnat : (4552469407 : ℕ)^4571*781250000000^3547 ≤ 283383661023^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4552469407 10000000000 283383661023 781250000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256196717/10000000000 : ℝ), (397613839/1000000000 : ℝ), (4552469407/10000000000 : ℝ)] ![(33259998992129/100000000000000 : ℝ), (30466892384643/100000000000000 : ℝ), (283383661023/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256196717/10000000000 : ℝ)|^4571 ≤ (33259998992129/100000000000000 : ℝ)^3547
        have hw : |(4256196717/10000000000 : ℝ)|=(4256196717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(397613839/1000000000 : ℝ)|^4571 ≤ (30466892384643/100000000000000 : ℝ)^3547
        have hw : |(397613839/1000000000 : ℝ)|=(397613839/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4552469407/10000000000 : ℝ)|^4571 ≤ (283383661023/781250000000 : ℝ)^3547
        have hw : |(4552469407/10000000000 : ℝ)|=(4552469407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s2_4 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-91428123/500000000 : ℝ)*x 0 + (1300525281/2500000000 : ℝ)*x 1 + (5448791087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91428123/500000000 : ℝ)^4571 ≤ (1399570704967/12500000000000 : ℝ)^3547 := by
    have hnat : (91428123 : ℕ)^4571*12500000000000^3547 ≤ 1399570704967^3547*500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91428123 500000000 1399570704967 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300525281/2500000000 : ℝ)^4571 ≤ (10769142605741/25000000000000 : ℝ)^3547 := by
    have hnat : (1300525281 : ℕ)^4571*25000000000000^3547 ≤ 10769142605741^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300525281 2500000000 10769142605741 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448791087/10000000000 : ℝ)^4571 ≤ (285792899519/625000000000 : ℝ)^3547 := by
    have hnat : (5448791087 : ℕ)^4571*625000000000^3547 ≤ 285792899519^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448791087 10000000000 285792899519 625000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-91428123/500000000 : ℝ), (1300525281/2500000000 : ℝ), (5448791087/10000000000 : ℝ)] ![(1399570704967/12500000000000 : ℝ), (10769142605741/25000000000000 : ℝ), (285792899519/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-91428123/500000000 : ℝ)|^4571 ≤ (1399570704967/12500000000000 : ℝ)^3547
        have hw : |(-91428123/500000000 : ℝ)|=(91428123/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1300525281/2500000000 : ℝ)|^4571 ≤ (10769142605741/25000000000000 : ℝ)^3547
        have hw : |(1300525281/2500000000 : ℝ)|=(1300525281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448791087/10000000000 : ℝ)|^4571 ≤ (285792899519/625000000000 : ℝ)^3547
        have hw : |(5448791087/10000000000 : ℝ)|=(5448791087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s2_5 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322419347/2500000000 : ℝ)*x 0 + (-1708690729/10000000000 : ℝ)*x 1 + (5448790611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322419347/2500000000 : ℝ)^4571 ≤ (11003343577341/25000000000000 : ℝ)^3547 := by
    have hnat : (1322419347 : ℕ)^4571*25000000000000^3547 ≤ 11003343577341^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322419347 2500000000 11003343577341 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1708690729/10000000000 : ℝ)^4571 ≤ (5129883446951/50000000000000 : ℝ)^3547 := by
    have hnat : (1708690729 : ℕ)^4571*50000000000000^3547 ≤ 5129883446951^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708690729 10000000000 5129883446951 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448790611/10000000000 : ℝ)^4571 ≤ (22863429387581/50000000000000 : ℝ)^3547 := by
    have hnat : (5448790611 : ℕ)^4571*50000000000000^3547 ≤ 22863429387581^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448790611 10000000000 22863429387581 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322419347/2500000000 : ℝ), (-1708690729/10000000000 : ℝ), (5448790611/10000000000 : ℝ)] ![(11003343577341/25000000000000 : ℝ), (5129883446951/50000000000000 : ℝ), (22863429387581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322419347/2500000000 : ℝ)|^4571 ≤ (11003343577341/25000000000000 : ℝ)^3547
        have hw : |(1322419347/2500000000 : ℝ)|=(1322419347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1708690729/10000000000 : ℝ)|^4571 ≤ (5129883446951/50000000000000 : ℝ)^3547
        have hw : |(-1708690729/10000000000 : ℝ)|=(1708690729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448790611/10000000000 : ℝ)|^4571 ≤ (22863429387581/50000000000000 : ℝ)^3547
        have hw : |(5448790611/10000000000 : ℝ)|=(5448790611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s2_6 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661209611/1250000000 : ℝ)*x 0 + (1362197701/2500000000 : ℝ)*x 1 + (-1708691153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661209611/1250000000 : ℝ)^4571 ≤ (22006684473999/50000000000000 : ℝ)^3547 := by
    have hnat : (661209611 : ℕ)^4571*50000000000000^3547 ≤ 22006684473999^3547*1250000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661209611 1250000000 22006684473999 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362197701/2500000000 : ℝ)^4571 ≤ (1428964401951/3125000000000 : ℝ)^3547 := by
    have hnat : (1362197701 : ℕ)^4571*3125000000000^3547 ≤ 1428964401951^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362197701 2500000000 1428964401951 3125000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1708691153/10000000000 : ℝ)^4571 ≤ (5129885087389/50000000000000 : ℝ)^3547 := by
    have hnat : (1708691153 : ℕ)^4571*50000000000000^3547 ≤ 5129885087389^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708691153 10000000000 5129885087389 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661209611/1250000000 : ℝ), (1362197701/2500000000 : ℝ), (-1708691153/10000000000 : ℝ)] ![(22006684473999/50000000000000 : ℝ), (1428964401951/3125000000000 : ℝ), (5129885087389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661209611/1250000000 : ℝ)|^4571 ≤ (22006684473999/50000000000000 : ℝ)^3547
        have hw : |(661209611/1250000000 : ℝ)|=(661209611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362197701/2500000000 : ℝ)|^4571 ≤ (1428964401951/3125000000000 : ℝ)^3547
        have hw : |(1362197701/2500000000 : ℝ)|=(1362197701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1708691153/10000000000 : ℝ)|^4571 ≤ (5129885087389/50000000000000 : ℝ)^3547
        have hw : |(-1708691153/10000000000 : ℝ)|=(1708691153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s2_7 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2128151633/5000000000 : ℝ)*x 0 + (4548947909/10000000000 : ℝ)*x 1 + (994922673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128151633/5000000000 : ℝ)^4571 ≤ (3326107199657/10000000000000 : ℝ)^3547 := by
    have hnat : (2128151633 : ℕ)^4571*10000000000000^3547 ≤ 3326107199657^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128151633 5000000000 3326107199657 10000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4548947909/10000000000 : ℝ)^4571 ≤ (18118476874181/50000000000000 : ℝ)^3547 := by
    have hnat : (4548947909 : ℕ)^4571*50000000000000^3547 ≤ 18118476874181^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4548947909 10000000000 18118476874181 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (994922673/2500000000 : ℝ)^4571 ≤ (30501974241443/100000000000000 : ℝ)^3547 := by
    have hnat : (994922673 : ℕ)^4571*100000000000000^3547 ≤ 30501974241443^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994922673 2500000000 30501974241443 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128151633/5000000000 : ℝ), (4548947909/10000000000 : ℝ), (994922673/2500000000 : ℝ)] ![(3326107199657/10000000000000 : ℝ), (18118476874181/50000000000000 : ℝ), (30501974241443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128151633/5000000000 : ℝ)|^4571 ≤ (3326107199657/10000000000000 : ℝ)^3547
        have hw : |(2128151633/5000000000 : ℝ)|=(2128151633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4548947909/10000000000 : ℝ)|^4571 ≤ (18118476874181/50000000000000 : ℝ)^3547
        have hw : |(4548947909/10000000000 : ℝ)|=(4548947909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(994922673/2500000000 : ℝ)|^4571 ≤ (30501974241443/100000000000000 : ℝ)^3547
        have hw : |(994922673/2500000000 : ℝ)|=(994922673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1537_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8679/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5309/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15909/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8679/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8679/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8679/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8679/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8679/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8679/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8679/100000 : ℝ) ^ (4569/1024 : ℝ) ≤ (458651674509767/25000000000000000000 : ℝ) := by
    have hpowers : (8679/100000 : ℝ)^4569 ≤ (458651674509767/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8679 : ℕ)^4569*25000000000000000000^1024 ≤ 458651674509767^1024*100000^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8679 100000 458651674509767 25000000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8679/100000 : ℝ)) (X := (458651674509767/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18071/100000 : ℝ) ^ (4569/1024 : ℝ) ≤ (48385849089772997/100000000000000000000 : ℝ) := by
    have hpowers : (18071/100000 : ℝ)^4569 ≤ (48385849089772997/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18071 : ℕ)^4569*100000000000000000000^1024 ≤ 48385849089772997^1024*100000^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18071 100000 48385849089772997 100000000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18071/100000 : ℝ)) (X := (48385849089772997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500458651674509767/12500000000000000000 : ℝ) ≤ (10000082232896397/10000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (12500458651674509767/12500000000000000000 : ℝ)^1024 ≤ (10000082232896397/10000000000000000 : ℝ)^4569 := by
      have hnat : (12500458651674509767 : ℕ)^1024*10000000000000000^4569 ≤ 10000082232896397^4569*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500458651674509767 12500000000000000000 10000082232896397 10000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000082232896397/10000000000000000 : ℝ)) (X := (12500458651674509767/12500000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010044091157562413/20000000000000000000 : ℝ) ≤ (10001125316932783/10000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (20010044091157562413/20000000000000000000 : ℝ)^1024 ≤ (10001125316932783/10000000000000000 : ℝ)^4569 := by
      have hnat : (20010044091157562413 : ℕ)^1024*10000000000000000^4569 ≤ 10001125316932783^4569*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010044091157562413 20000000000000000000 10001125316932783 10000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001125316932783/10000000000000000 : ℝ)) (X := (20010044091157562413/20000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50048385849089772997/50000000000000000000 : ℝ) ≤ (10002168400969169/10000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (50048385849089772997/50000000000000000000 : ℝ)^1024 ≤ (10002168400969169/10000000000000000 : ℝ)^4569 := by
      have hnat : (50048385849089772997 : ℕ)^1024*10000000000000000^4569 ≤ 10002168400969169^4569*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048385849089772997 50000000000000000000 10002168400969169 10000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002168400969169/10000000000000000 : ℝ)) (X := (50048385849089772997/50000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(458651674509767/25000000000000000000 : ℝ) ≤ ((23475666619664843109/23480000000000000000 : ℝ)+2*(521542018193/469600000000000 : ℝ)*(8679/100000 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (23475666619664843109/23480000000000000000 : ℝ)+2*(521542018193/469600000000000 : ℝ)*(8679/100000 : ℝ)=(10000082232896397/10000000000000000 : ℝ) by norm_num, show 1+2*(458651674509767/25000000000000000000 : ℝ)=(12500458651674509767/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48385849089772997/100000000000000000000 : ℝ)+(458651674509767/25000000000000000000 : ℝ) ≤ ((23475666619664843109/23480000000000000000 : ℝ)+(521542018193/469600000000000 : ℝ)*((18071/100000 : ℝ)+(8679/100000 : ℝ)))^(4569/1024 : ℝ) := by
    rw [show (23475666619664843109/23480000000000000000 : ℝ)+(521542018193/469600000000000 : ℝ)*((18071/100000 : ℝ)+(8679/100000 : ℝ))=(10001125316932783/10000000000000000 : ℝ) by norm_num, show 1+(48385849089772997/100000000000000000000 : ℝ)+(458651674509767/25000000000000000000 : ℝ)=(20010044091157562413/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48385849089772997/100000000000000000000 : ℝ) ≤ ((23475666619664843109/23480000000000000000 : ℝ)+2*(521542018193/469600000000000 : ℝ)*(18071/100000 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (23475666619664843109/23480000000000000000 : ℝ)+2*(521542018193/469600000000000 : ℝ)*(18071/100000 : ℝ)=(10002168400969169/10000000000000000 : ℝ) by norm_num, show 1+2*(48385849089772997/100000000000000000000 : ℝ)=(50048385849089772997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23475666619664843109/23480000000000000000 : ℝ)*(X 1 0+X 2 0)+(521542018193/469600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (8679/100000 : ℝ)) (hi := (18071/100000 : ℝ)) (c := (23475666619664843109/23480000000000000000 : ℝ)) (alpha := (521542018193/469600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23475666619664843109/23480000000000000000 : ℝ)*(X 0 1+X 2 1)+(521542018193/469600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (8679/100000 : ℝ)) (hi := (18071/100000 : ℝ)) (c := (23475666619664843109/23480000000000000000 : ℝ)) (alpha := (521542018193/469600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23475666619664843109/23480000000000000000 : ℝ)*(X 0 2+X 1 2)+(521542018193/469600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (8679/100000 : ℝ)) (hi := (18071/100000 : ℝ)) (c := (23475666619664843109/23480000000000000000 : ℝ)) (alpha := (521542018193/469600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1828516459/10000000000 : ℝ)*X 0 0+(1090065941/2000000000 : ℝ)*X 0 1+(1300143919/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338871789/2500000000 : ℝ)*X 1 0+(-1956906351/10000000000 : ℝ)*X 1 1+(5200575949/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355487799/10000000000 : ℝ)*X 2 0+(260028779/500000000 : ℝ)*X 2 1+(-97845299/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4256196717/10000000000 : ℝ)*X 0 0+(397613839/1000000000 : ℝ)*X 0 1+(4552469407/10000000000 : ℝ)*X 0 2+(4256196717/10000000000 : ℝ)*X 1 0+(397613839/1000000000 : ℝ)*X 1 1+(4552469407/10000000000 : ℝ)*X 1 2+(4256196717/10000000000 : ℝ)*X 2 0+(397613839/1000000000 : ℝ)*X 2 1+(4552469407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-91428123/500000000 : ℝ)*X 0 0+(1300525281/2500000000 : ℝ)*X 0 1+(5448791087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322419347/2500000000 : ℝ)*X 1 0+(-1708690729/10000000000 : ℝ)*X 1 1+(5448790611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661209611/1250000000 : ℝ)*X 2 0+(1362197701/2500000000 : ℝ)*X 2 1+(-1708691153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2128151633/5000000000 : ℝ)*X 0 0+(4548947909/10000000000 : ℝ)*X 0 1+(994922673/2500000000 : ℝ)*X 0 2+(2128151633/5000000000 : ℝ)*X 1 0+(4548947909/10000000000 : ℝ)*X 1 1+(994922673/2500000000 : ℝ)*X 1 2+(2128151633/5000000000 : ℝ)*X 2 0+(4548947909/10000000000 : ℝ)*X 2 1+(994922673/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10953861636222749755213220673/1174000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1927993441/100000000000000 : ℝ)*(base19) + (2121703879/100000000000000 : ℝ)*(base23) + (21158923/12500000000000 : ℝ)*(upper3) + (76857803/50000000000000 : ℝ)*(upper4) + (18194917/5000000000000 : ℝ)*(upper5) + (2869571668778901/100000000000000 : ℝ)*(major0) + (2869571668778901/100000000000000 : ℝ)*(major1) + (1434785834389451/50000000000000 : ℝ)*(major2) + (200198193080563/5000000000000 : ℝ)*(sp0) + (2001998398514439/50000000000000 : ℝ)*(sp1) + (100099915082961/2500000000000 : ℝ)*(sp2) + (1735129114369019/100000000000000 : ℝ)*(sp3) + (34863411059/100000000000000 : ℝ)*(sp4) + (2966241/19531250000 : ℝ)*(sp7) + (867572150761469/50000000000000 : ℝ)*(f.failure) + (4003998725022319/100000000000000 : ℝ)*(f.sum) + (26235296856501/46960000000000000000000000000 : ℝ)*base66 + (12087714736509256791/2348000000000000000000000000000000 : ℝ)*base68 + (4301186894082968159/1174000000000000000000000000000000 : ℝ)*base69 + (9963720992249256791/2348000000000000000000000000000000 : ℝ)*base72 + (303301581413541/46960000000000000000000000000 : ℝ)*base74 + (6690145019836968159/1174000000000000000000000000000000 : ℝ)*base75 + (5878872060825093209/2348000000000000000000000000000000 : ℝ)*base77 + (12088636736650906791/2348000000000000000000000000000000 : ℝ)*base80 + (95373005156147/23480000000000000000000000000 : ℝ)*base82 + (215013/200000000000000000000 : ℝ)*base89 + (215013/200000000000000000000 : ℝ)*base91 + (1784987/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12956613041357184439030595169/1174000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2671587663/100000000000000 : ℝ)*(base19) + (1146535987/50000000000000 : ℝ)*(base23) + (76081293/100000000000000 : ℝ)*(upper2) + (24500019/20000000000000 : ℝ)*(upper3) + (380082817/100000000000000 : ℝ)*(upper5) + (2905172953481553/100000000000000 : ℝ)*(major0) + (2905172953481553/100000000000000 : ℝ)*(major1) + (2905172953481553/100000000000000 : ℝ)*(major2) + (36276684521/100000000000000 : ℝ)*(sp1) + (250894163/1000000000000 : ℝ)*(sp2) + (202683710188643/5000000000000 : ℝ)*(sp4) + (162145410220027/4000000000000 : ℝ)*(sp5) + (506705852660573/12500000000000 : ℝ)*(sp6) + (87833566765683/5000000000000 : ℝ)*(sp7) + (87833566765683/5000000000000 : ℝ)*(f.failure) + (202683710188643/5000000000000 : ℝ)*(f.sum) + (38962925392929/23480000000000000000000000000 : ℝ)*base65 + (467432660082881723/2348000000000000000000000000000000 : ℝ)*base68 + (2895781126162881723/2348000000000000000000000000000000 : ℝ)*base70 + (12375819385629118277/2348000000000000000000000000000000 : ℝ)*base71 + (50878461074609/23480000000000000000000000000 : ℝ)*base73 + (15707777342005118277/2348000000000000000000000000000000 : ℝ)*base75 + (8873849901261118277/2348000000000000000000000000000000 : ℝ)*base77 + (72429925684109118277/2348000000000000000000000000000000 : ℝ)*base79 + (24468359613089/23480000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (29109/20000000000000000000 : ℝ)*base90 + (29109/20000000000000000000 : ℝ)*base92 + (29109/20000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1537_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8679/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5309/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15909/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1537_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1537_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5309/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15909/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1537_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1537_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1537_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5309/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15909/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1537_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
