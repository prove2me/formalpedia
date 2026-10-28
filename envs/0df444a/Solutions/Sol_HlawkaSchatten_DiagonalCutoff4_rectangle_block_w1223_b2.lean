-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1223_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:12:14.818117+00:00
-- url     : https://prove2.me/submissions/0cec54d7-673e-4ab7-a351-a0364e64e71f

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
theorem support_rectangle_w1223_s6_0 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128722741/10000000000 : ℝ)*x 0 + (5391764437/10000000000 : ℝ)*x 1 + (5266754471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128722741/10000000000 : ℝ)^263 ≤ (12943055103519/100000000000000 : ℝ)^199 := by
    have hnat : (2128722741 : ℕ)^263*100000000000000^199 ≤ 12943055103519^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128722741 10000000000 12943055103519 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391764437/10000000000 : ℝ)^263 ≤ (44203169791717/100000000000000 : ℝ)^199 := by
    have hnat : (5391764437 : ℕ)^263*100000000000000^199 ≤ 44203169791717^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391764437 10000000000 44203169791717 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266754471/10000000000 : ℝ)^263 ≤ (1714151003353/4000000000000 : ℝ)^199 := by
    have hnat : (5266754471 : ℕ)^263*4000000000000^199 ≤ 1714151003353^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266754471 10000000000 1714151003353 4000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128722741/10000000000 : ℝ), (5391764437/10000000000 : ℝ), (5266754471/10000000000 : ℝ)] ![(12943055103519/100000000000000 : ℝ), (44203169791717/100000000000000 : ℝ), (1714151003353/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128722741/10000000000 : ℝ)|^263 ≤ (12943055103519/100000000000000 : ℝ)^199
        have hw : |(-2128722741/10000000000 : ℝ)|=(2128722741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391764437/10000000000 : ℝ)|^263 ≤ (44203169791717/100000000000000 : ℝ)^199
        have hw : |(5391764437/10000000000 : ℝ)|=(5391764437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266754471/10000000000 : ℝ)|^263 ≤ (1714151003353/4000000000000 : ℝ)^199
        have hw : |(5266754471/10000000000 : ℝ)|=(5266754471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s6_1 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (668057597/1250000000 : ℝ)*x 0 + (-1096056831/5000000000 : ℝ)*x 1 + (658344271/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668057597/1250000000 : ℝ)^263 ≤ (8738272709759/20000000000000 : ℝ)^199 := by
    have hnat : (668057597 : ℕ)^263*20000000000000^199 ≤ 8738272709759^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668057597 1250000000 8738272709759 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096056831/5000000000 : ℝ)^263 ≤ (1345486461123/10000000000000 : ℝ)^199 := by
    have hnat : (1096056831 : ℕ)^263*10000000000000^199 ≤ 1345486461123^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096056831 5000000000 1345486461123 10000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658344271/1250000000 : ℝ)^263 ≤ (10713442956381/25000000000000 : ℝ)^199 := by
    have hnat : (658344271 : ℕ)^263*25000000000000^199 ≤ 10713442956381^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658344271 1250000000 10713442956381 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668057597/1250000000 : ℝ), (-1096056831/5000000000 : ℝ), (658344271/1250000000 : ℝ)] ![(8738272709759/20000000000000 : ℝ), (1345486461123/10000000000000 : ℝ), (10713442956381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668057597/1250000000 : ℝ)|^263 ≤ (8738272709759/20000000000000 : ℝ)^199
        have hw : |(668057597/1250000000 : ℝ)|=(668057597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1096056831/5000000000 : ℝ)|^263 ≤ (1345486461123/10000000000000 : ℝ)^199
        have hw : |(-1096056831/5000000000 : ℝ)|=(1096056831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658344271/1250000000 : ℝ)|^263 ≤ (10713442956381/25000000000000 : ℝ)^199
        have hw : |(658344271/1250000000 : ℝ)|=(658344271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s6_2 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1336115151/2500000000 : ℝ)*x 0 + (5266754273/10000000000 : ℝ)*x 1 + (-274014219/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336115151/2500000000 : ℝ)^263 ≤ (8738272338093/20000000000000 : ℝ)^199 := by
    have hnat : (1336115151 : ℕ)^263*20000000000000^199 ≤ 8738272338093^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336115151 2500000000 8738272338093 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266754273/10000000000 : ℝ)^263 ≤ (21426886477319/50000000000000 : ℝ)^199 := by
    have hnat : (5266754273 : ℕ)^263*50000000000000^199 ≤ 21426886477319^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266754273 10000000000 21426886477319 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274014219/1250000000 : ℝ)^263 ≤ (2690973068259/20000000000000 : ℝ)^199 := by
    have hnat : (274014219 : ℕ)^263*20000000000000^199 ≤ 2690973068259^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274014219 1250000000 2690973068259 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336115151/2500000000 : ℝ), (5266754273/10000000000 : ℝ), (-274014219/1250000000 : ℝ)] ![(8738272338093/20000000000000 : ℝ), (21426886477319/50000000000000 : ℝ), (2690973068259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336115151/2500000000 : ℝ)|^263 ≤ (8738272338093/20000000000000 : ℝ)^199
        have hw : |(1336115151/2500000000 : ℝ)|=(1336115151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266754273/10000000000 : ℝ)|^263 ≤ (21426886477319/50000000000000 : ℝ)^199
        have hw : |(5266754273/10000000000 : ℝ)|=(5266754273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274014219/1250000000 : ℝ)|^263 ≤ (2690973068259/20000000000000 : ℝ)^199
        have hw : |(-274014219/1250000000 : ℝ)|=(274014219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s6_3 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (435337469/1000000000 : ℝ)*x 0 + (4228834151/10000000000 : ℝ)*x 1 + (2240748123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435337469/1000000000 : ℝ)^263 ≤ (16658642395273/50000000000000 : ℝ)^199 := by
    have hnat : (435337469 : ℕ)^263*50000000000000^199 ≤ 16658642395273^199*1000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435337469 1000000000 16658642395273 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228834151/10000000000 : ℝ)^263 ≤ (16031723507407/50000000000000 : ℝ)^199 := by
    have hnat : (4228834151 : ℕ)^263*50000000000000^199 ≤ 16031723507407^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228834151 10000000000 16031723507407 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240748123/5000000000 : ℝ)^263 ≤ (8654817044607/25000000000000 : ℝ)^199 := by
    have hnat : (2240748123 : ℕ)^263*25000000000000^199 ≤ 8654817044607^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240748123 5000000000 8654817044607 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435337469/1000000000 : ℝ), (4228834151/10000000000 : ℝ), (2240748123/5000000000 : ℝ)] ![(16658642395273/50000000000000 : ℝ), (16031723507407/50000000000000 : ℝ), (8654817044607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435337469/1000000000 : ℝ)|^263 ≤ (16658642395273/50000000000000 : ℝ)^199
        have hw : |(435337469/1000000000 : ℝ)|=(435337469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228834151/10000000000 : ℝ)|^263 ≤ (16031723507407/50000000000000 : ℝ)^199
        have hw : |(4228834151/10000000000 : ℝ)|=(4228834151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240748123/5000000000 : ℝ)|^263 ≤ (8654817044607/25000000000000 : ℝ)^199
        have hw : |(2240748123/5000000000 : ℝ)|=(2240748123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s6_4 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-266090997/1250000000 : ℝ)*x 0 + (658383769/1250000000 : ℝ)*x 1 + (5391447241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266090997/1250000000 : ℝ)^263 ≤ (12943097170101/100000000000000 : ℝ)^199 := by
    have hnat : (266090997 : ℕ)^263*100000000000000^199 ≤ 12943097170101^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266090997 1250000000 12943097170101 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658383769/1250000000 : ℝ)^263 ≤ (42857169783157/100000000000000 : ℝ)^199 := by
    have hnat : (658383769 : ℕ)^263*100000000000000^199 ≤ 42857169783157^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658383769 1250000000 42857169783157 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391447241/10000000000 : ℝ)^263 ≤ (8839946607033/20000000000000 : ℝ)^199 := by
    have hnat : (5391447241 : ℕ)^263*20000000000000^199 ≤ 8839946607033^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391447241 10000000000 8839946607033 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-266090997/1250000000 : ℝ), (658383769/1250000000 : ℝ), (5391447241/10000000000 : ℝ)] ![(12943097170101/100000000000000 : ℝ), (42857169783157/100000000000000 : ℝ), (8839946607033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-266090997/1250000000 : ℝ)|^263 ≤ (12943097170101/100000000000000 : ℝ)^199
        have hw : |(-266090997/1250000000 : ℝ)|=(266090997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658383769/1250000000 : ℝ)|^263 ≤ (42857169783157/100000000000000 : ℝ)^199
        have hw : |(658383769/1250000000 : ℝ)|=(658383769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391447241/10000000000 : ℝ)|^263 ≤ (8839946607033/20000000000000 : ℝ)^199
        have hw : |(5391447241/10000000000 : ℝ)|=(5391447241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s6_5 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5312605053/10000000000 : ℝ)*x 0 + (-1033710163/5000000000 : ℝ)*x 1 + (2156579/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312605053/10000000000 : ℝ)^263 ≤ (8669503376149/20000000000000 : ℝ)^199 := by
    have hnat : (5312605053 : ℕ)^263*20000000000000^199 ≤ 8669503376149^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312605053 10000000000 8669503376149 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033710163/5000000000 : ℝ)^263 ≤ (12452747262883/100000000000000 : ℝ)^199 := by
    have hnat : (1033710163 : ℕ)^263*100000000000000^199 ≤ 12452747262883^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033710163 5000000000 12452747262883 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156579/4000000 : ℝ)^263 ≤ (44199735841353/100000000000000 : ℝ)^199 := by
    have hnat : (2156579 : ℕ)^263*100000000000000^199 ≤ 44199735841353^199*4000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156579 4000000 44199735841353 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312605053/10000000000 : ℝ), (-1033710163/5000000000 : ℝ), (2156579/4000000 : ℝ)] ![(8669503376149/20000000000000 : ℝ), (12452747262883/100000000000000 : ℝ), (44199735841353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312605053/10000000000 : ℝ)|^263 ≤ (8669503376149/20000000000000 : ℝ)^199
        have hw : |(5312605053/10000000000 : ℝ)|=(5312605053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1033710163/5000000000 : ℝ)|^263 ≤ (12452747262883/100000000000000 : ℝ)^199
        have hw : |(-1033710163/5000000000 : ℝ)|=(1033710163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2156579/4000000 : ℝ)|^263 ≤ (44199735841353/100000000000000 : ℝ)^199
        have hw : |(2156579/4000000 : ℝ)|=(2156579/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s6_6 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2656302383/5000000000 : ℝ)*x 0 + (1078289469/2000000000 : ℝ)*x 1 + (-2067420927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656302383/5000000000 : ℝ)^263 ≤ (43347513785883/100000000000000 : ℝ)^199 := by
    have hnat : (2656302383 : ℕ)^263*100000000000000^199 ≤ 43347513785883^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656302383 5000000000 43347513785883 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078289469/2000000000 : ℝ)^263 ≤ (22099867080987/50000000000000 : ℝ)^199 := by
    have hnat : (1078289469 : ℕ)^263*50000000000000^199 ≤ 22099867080987^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078289469 2000000000 22099867080987 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067420927/10000000000 : ℝ)^263 ≤ (1245275204713/10000000000000 : ℝ)^199 := by
    have hnat : (2067420927 : ℕ)^263*10000000000000^199 ≤ 1245275204713^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067420927 10000000000 1245275204713 10000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656302383/5000000000 : ℝ), (1078289469/2000000000 : ℝ), (-2067420927/10000000000 : ℝ)] ![(43347513785883/100000000000000 : ℝ), (22099867080987/50000000000000 : ℝ), (1245275204713/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656302383/5000000000 : ℝ)|^263 ≤ (43347513785883/100000000000000 : ℝ)^199
        have hw : |(2656302383/5000000000 : ℝ)|=(2656302383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078289469/2000000000 : ℝ)|^263 ≤ (22099867080987/50000000000000 : ℝ)^199
        have hw : |(1078289469/2000000000 : ℝ)|=(1078289469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2067420927/10000000000 : ℝ)|^263 ≤ (1245275204713/10000000000000 : ℝ)^199
        have hw : |(-2067420927/10000000000 : ℝ)|=(2067420927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s6_7 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4353384573/10000000000 : ℝ)*x 0 + (4480857197/10000000000 : ℝ)*x 1 + (132171101/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353384573/10000000000 : ℝ)^263 ≤ (16658692376301/50000000000000 : ℝ)^199 := by
    have hnat : (4353384573 : ℕ)^263*50000000000000^199 ≤ 16658692376301^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353384573 10000000000 16658692376301 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480857197/10000000000 : ℝ)^263 ≤ (17306372030879/50000000000000 : ℝ)^199 := by
    have hnat : (4480857197 : ℕ)^263*50000000000000^199 ≤ 17306372030879^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480857197 10000000000 17306372030879 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132171101/312500000 : ℝ)^263 ≤ (16034935582763/50000000000000 : ℝ)^199 := by
    have hnat : (132171101 : ℕ)^263*50000000000000^199 ≤ 16034935582763^199*312500000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132171101 312500000 16034935582763 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353384573/10000000000 : ℝ), (4480857197/10000000000 : ℝ), (132171101/312500000 : ℝ)] ![(16658692376301/50000000000000 : ℝ), (17306372030879/50000000000000 : ℝ), (16034935582763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353384573/10000000000 : ℝ)|^263 ≤ (16658692376301/50000000000000 : ℝ)^199
        have hw : |(4353384573/10000000000 : ℝ)|=(4353384573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480857197/10000000000 : ℝ)|^263 ≤ (17306372030879/50000000000000 : ℝ)^199
        have hw : |(4480857197/10000000000 : ℝ)|=(4480857197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132171101/312500000 : ℝ)|^263 ≤ (16034935582763/50000000000000 : ℝ)^199
        have hw : |(132171101/312500000 : ℝ)|=(132171101/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1223_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11451/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14099/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11429/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11429/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11429/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11429/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11429/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11429/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11429/100000 : ℝ) ^ (8415/2048 : ℝ) ≤ (13472945041799683/100000000000000000000 : ℝ) := by
    have hpowers : (11429/100000 : ℝ)^8415 ≤ (13472945041799683/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11429 : ℕ)^8415*100000000000000000000^2048 ≤ 13472945041799683^2048*100000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11429 100000 13472945041799683 100000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11429/100000 : ℝ)) (X := (13472945041799683/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7061/50000 : ℝ) ^ (8415/2048 : ℝ) ≤ (8034517938091457/25000000000000000000 : ℝ) := by
    have hpowers : (7061/50000 : ℝ)^8415 ≤ (8034517938091457/25000000000000000000 : ℝ)^2048 := by
      have hnat : (7061 : ℕ)^8415*25000000000000000000^2048 ≤ 8034517938091457^2048*50000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7061 50000 8034517938091457 25000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7061/50000 : ℝ)) (X := (8034517938091457/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013472945041799683/50000000000000000000 : ℝ) ≤ (8000524582847/8000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (50013472945041799683/50000000000000000000 : ℝ)^2048 ≤ (8000524582847/8000000000000 : ℝ)^8415 := by
      have hnat : (50013472945041799683 : ℕ)^2048*8000000000000^8415 ≤ 8000524582847^8415*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013472945041799683 50000000000000000000 8000524582847 8000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (8000524582847/8000000000000 : ℝ)) (X := (50013472945041799683/50000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045611016794165511/100000000000000000000 : ℝ) ≤ (10001109866290699/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (100045611016794165511/100000000000000000000 : ℝ)^2048 ≤ (10001109866290699/10000000000000000 : ℝ)^8415 := by
      have hnat : (100045611016794165511 : ℕ)^2048*10000000000000000^8415 ≤ 10001109866290699^8415*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045611016794165511 100000000000000000000 10001109866290699 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001109866290699/10000000000000000 : ℝ)) (X := (100045611016794165511/100000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508034517938091457/12500000000000000000 : ℝ) ≤ (1250195500502831/1250000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (12508034517938091457/12500000000000000000 : ℝ)^2048 ≤ (1250195500502831/1250000000000000 : ℝ)^8415 := by
      have hnat : (12508034517938091457 : ℕ)^2048*1250000000000000^8415 ≤ 1250195500502831^8415*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508034517938091457 12500000000000000000 1250195500502831 1250000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250195500502831/1250000000000000 : ℝ)) (X := (12508034517938091457/12500000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13472945041799683/100000000000000000000 : ℝ) ≤ ((6730346299182955877/6732500000000000000 : ℝ)+2*(454137731949/269300000000000 : ℝ)*(11429/100000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (6730346299182955877/6732500000000000000 : ℝ)+2*(454137731949/269300000000000 : ℝ)*(11429/100000 : ℝ)=(8000524582847/8000000000000 : ℝ) by norm_num, show 1+2*(13472945041799683/100000000000000000000 : ℝ)=(50013472945041799683/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8034517938091457/25000000000000000000 : ℝ)+(13472945041799683/100000000000000000000 : ℝ) ≤ ((6730346299182955877/6732500000000000000 : ℝ)+(454137731949/269300000000000 : ℝ)*((7061/50000 : ℝ)+(11429/100000 : ℝ)))^(8415/2048 : ℝ) := by
    rw [show (6730346299182955877/6732500000000000000 : ℝ)+(454137731949/269300000000000 : ℝ)*((7061/50000 : ℝ)+(11429/100000 : ℝ))=(10001109866290699/10000000000000000 : ℝ) by norm_num, show 1+(8034517938091457/25000000000000000000 : ℝ)+(13472945041799683/100000000000000000000 : ℝ)=(100045611016794165511/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8034517938091457/25000000000000000000 : ℝ) ≤ ((6730346299182955877/6732500000000000000 : ℝ)+2*(454137731949/269300000000000 : ℝ)*(7061/50000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (6730346299182955877/6732500000000000000 : ℝ)+2*(454137731949/269300000000000 : ℝ)*(7061/50000 : ℝ)=(1250195500502831/1250000000000000 : ℝ) by norm_num, show 1+2*(8034517938091457/25000000000000000000 : ℝ)=(12508034517938091457/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6730346299182955877/6732500000000000000 : ℝ)*(X 1 0+X 2 0)+(454137731949/269300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (11429/100000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (6730346299182955877/6732500000000000000 : ℝ)) (alpha := (454137731949/269300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6730346299182955877/6732500000000000000 : ℝ)*(X 0 1+X 2 1)+(454137731949/269300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (11429/100000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (6730346299182955877/6732500000000000000 : ℝ)) (alpha := (454137731949/269300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6730346299182955877/6732500000000000000 : ℝ)*(X 0 2+X 1 2)+(454137731949/269300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (11429/100000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (6730346299182955877/6732500000000000000 : ℝ)) (alpha := (454137731949/269300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2128722741/10000000000 : ℝ)*X 0 0+(5391764437/10000000000 : ℝ)*X 0 1+(5266754471/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668057597/1250000000 : ℝ)*X 1 0+(-1096056831/5000000000 : ℝ)*X 1 1+(658344271/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336115151/2500000000 : ℝ)*X 2 0+(5266754273/10000000000 : ℝ)*X 2 1+(-274014219/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((435337469/1000000000 : ℝ)*X 0 0+(4228834151/10000000000 : ℝ)*X 0 1+(2240748123/5000000000 : ℝ)*X 0 2+(435337469/1000000000 : ℝ)*X 1 0+(4228834151/10000000000 : ℝ)*X 1 1+(2240748123/5000000000 : ℝ)*X 1 2+(435337469/1000000000 : ℝ)*X 2 0+(4228834151/10000000000 : ℝ)*X 2 1+(2240748123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-266090997/1250000000 : ℝ)*X 0 0+(658383769/1250000000 : ℝ)*X 0 1+(5391447241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312605053/10000000000 : ℝ)*X 1 0+(-1033710163/5000000000 : ℝ)*X 1 1+(2156579/4000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656302383/5000000000 : ℝ)*X 2 0+(1078289469/2000000000 : ℝ)*X 2 1+(-2067420927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353384573/10000000000 : ℝ)*X 0 0+(4480857197/10000000000 : ℝ)*X 0 1+(132171101/312500000 : ℝ)*X 0 2+(4353384573/10000000000 : ℝ)*X 1 0+(4480857197/10000000000 : ℝ)*X 1 1+(132171101/312500000 : ℝ)*X 1 2+(4353384573/10000000000 : ℝ)*X 2 0+(4480857197/10000000000 : ℝ)*X 2 1+(132171101/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23394184112922452999900913/3366250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (159142119/20000000000000 : ℝ)*(base19) + (281784247/50000000000000 : ℝ)*(base23) + (5749213/50000000000000 : ℝ)*(upper3) + (6345397/20000000000000 : ℝ)*(lower4) + (119572630659673/2000000000000 : ℝ)*(major0) + (119572630659673/2000000000000 : ℝ)*(major1) + (119572630659673/2000000000000 : ℝ)*(major2) + (7999376570652123/100000000000000 : ℝ)*(sp0) + (1599877123820199/20000000000000 : ℝ)*(sp1) + (7999380136440099/100000000000000 : ℝ)*(sp2) + (395786660556787/10000000000000 : ℝ)*(sp3) + (9844159467/100000000000000 : ℝ)*(sp4) + (5714802997/100000000000000 : ℝ)*(sp6) + (4906966789/50000000000000 : ℝ)*(sp7) + (494734552437681/12500000000000 : ℝ)*(f.failure) + (799938641481159/10000000000000 : ℝ)*(f.sum) + (14409453910617/2693000000000000000000000000 : ℝ)*base66 + (103852623850341779/13465000000000000000000000000000 : ℝ)*base68 + (70172089165966779/13465000000000000000000000000000 : ℝ)*base70 + (29591891798336779/13465000000000000000000000000000 : ℝ)*base72 + (523464998663/168312500000000000000000000 : ℝ)*base74 + (87839847982166779/13465000000000000000000000000000 : ℝ)*base76 + (7570845403106779/13465000000000000000000000000000 : ℝ)*base78 + (368275959434153221/13465000000000000000000000000000 : ℝ)*base79 + (13106504810387/2693000000000000000000000000 : ℝ)*base82 + (4422869/1250000000000000000000 : ℝ)*base89 + (4422869/1250000000000000000000 : ℝ)*base91 + (4422869/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (768690965199136761438997521/168312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1173966483/100000000000000 : ℝ)*(base19) + (1017242963/100000000000000 : ℝ)*(base23) + (131393321/50000000000000 : ℝ)*(upper2) + (64467961/50000000000000 : ℝ)*(upper3) + (307165559/100000000000000 : ℝ)*(upper5) + (3004515114094809/50000000000000 : ℝ)*(major0) + (3004515114094809/50000000000000 : ℝ)*(major1) + (3004515114094809/50000000000000 : ℝ)*(major2) + (9949693903/20000000000000 : ℝ)*(sp1) + (13554619279/100000000000000 : ℝ)*(sp2) + (804005983480381/10000000000000 : ℝ)*(sp4) + (8040008912367813/100000000000000 : ℝ)*(sp5) + (804004526294157/10000000000000 : ℝ)*(sp6) + (497250058667567/12500000000000 : ℝ)*(sp7) + (497250058667567/12500000000000 : ℝ)*(f.failure) + (804005983480381/10000000000000 : ℝ)*(f.sum) + (7518100636319/6732500000000000000000000000 : ℝ)*base66 + (4495954157483267493/336625000000000000000000000000000 : ℝ)*base67 + (2799001999477017493/336625000000000000000000000000000 : ℝ)*base69 + (29601153547642493/336625000000000000000000000000000 : ℝ)*base71 + (48459310631661/6732500000000000000000000000 : ℝ)*base73 + (6298530258314232507/336625000000000000000000000000000 : ℝ)*base76 + (74181817458732507/336625000000000000000000000000000 : ℝ)*base78 + (3620331368730642493/336625000000000000000000000000000 : ℝ)*base79 + (69703272789/6574707031250000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (15753717/1250000000000000000000 : ℝ)*base90 + (15753717/1250000000000000000000 : ℝ)*base92 + (15753717/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1223_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1223_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1223_s7_0 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-532185303/2500000000 : ℝ)*x 0 + (5391549721/10000000000 : ℝ)*x 1 + (329184813/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532185303/2500000000 : ℝ)^263 ≤ (6471601764999/50000000000000 : ℝ)^199 := by
    have hnat : (532185303 : ℕ)^263*50000000000000^199 ≤ 6471601764999^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532185303 2500000000 6471601764999 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391549721/10000000000 : ℝ)^263 ≤ (44200843378789/100000000000000 : ℝ)^199 := by
    have hnat : (5391549721 : ℕ)^263*100000000000000^199 ≤ 44200843378789^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391549721 10000000000 44200843378789 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329184813/625000000 : ℝ)^263 ≤ (8571190614627/20000000000000 : ℝ)^199 := by
    have hnat : (329184813 : ℕ)^263*20000000000000^199 ≤ 8571190614627^199*625000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329184813 625000000 8571190614627 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532185303/2500000000 : ℝ), (5391549721/10000000000 : ℝ), (329184813/625000000 : ℝ)] ![(6471601764999/50000000000000 : ℝ), (44200843378789/100000000000000 : ℝ), (8571190614627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532185303/2500000000 : ℝ)|^263 ≤ (6471601764999/50000000000000 : ℝ)^199
        have hw : |(-532185303/2500000000 : ℝ)|=(532185303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391549721/10000000000 : ℝ)|^263 ≤ (44200843378789/100000000000000 : ℝ)^199
        have hw : |(5391549721/10000000000 : ℝ)|=(5391549721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329184813/625000000 : ℝ)|^263 ≤ (8571190614627/20000000000000 : ℝ)^199
        have hw : |(329184813/625000000 : ℝ)|=(329184813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s7_1 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5344406319/10000000000 : ℝ)*x 0 + (-273989661/1250000000 : ℝ)*x 1 + (5266957013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344406319/10000000000 : ℝ)^263 ≤ (43690775183053/100000000000000 : ℝ)^199 := by
    have hnat : (5344406319 : ℕ)^263*100000000000000^199 ≤ 43690775183053^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344406319 10000000000 43690775183053 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273989661/1250000000 : ℝ)^263 ≤ (538130867253/4000000000000 : ℝ)^199 := by
    have hnat : (273989661 : ℕ)^263*4000000000000^199 ≤ 538130867253^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273989661 1250000000 538130867253 4000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266957013/10000000000 : ℝ)^263 ≤ (42855953126903/100000000000000 : ℝ)^199 := by
    have hnat : (5266957013 : ℕ)^263*100000000000000^199 ≤ 42855953126903^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266957013 10000000000 42855953126903 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344406319/10000000000 : ℝ), (-273989661/1250000000 : ℝ), (5266957013/10000000000 : ℝ)] ![(43690775183053/100000000000000 : ℝ), (538130867253/4000000000000 : ℝ), (42855953126903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344406319/10000000000 : ℝ)|^263 ≤ (43690775183053/100000000000000 : ℝ)^199
        have hw : |(5344406319/10000000000 : ℝ)|=(5344406319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273989661/1250000000 : ℝ)|^263 ≤ (538130867253/4000000000000 : ℝ)^199
        have hw : |(-273989661/1250000000 : ℝ)|=(273989661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266957013/10000000000 : ℝ)|^263 ≤ (42855953126903/100000000000000 : ℝ)^199
        have hw : |(5266957013/10000000000 : ℝ)|=(5266957013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s7_2 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5344406311/10000000000 : ℝ)*x 0 + (2633478503/5000000000 : ℝ)*x 1 + (-2191917307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344406311/10000000000 : ℝ)^263 ≤ (43690775096619/100000000000000 : ℝ)^199 := by
    have hnat : (5344406311 : ℕ)^263*100000000000000^199 ≤ 43690775096619^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344406311 10000000000 43690775096619 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633478503/5000000000 : ℝ)^263 ≤ (10713988262907/25000000000000 : ℝ)^199 := by
    have hnat : (2633478503 : ℕ)^263*25000000000000^199 ≤ 10713988262907^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633478503 5000000000 10713988262907 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2191917307/10000000000 : ℝ)^263 ≤ (2690654367089/20000000000000 : ℝ)^199 := by
    have hnat : (2191917307 : ℕ)^263*20000000000000^199 ≤ 2690654367089^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191917307 10000000000 2690654367089 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344406311/10000000000 : ℝ), (2633478503/5000000000 : ℝ), (-2191917307/10000000000 : ℝ)] ![(43690775096619/100000000000000 : ℝ), (10713988262907/25000000000000 : ℝ), (2690654367089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344406311/10000000000 : ℝ)|^263 ≤ (43690775096619/100000000000000 : ℝ)^199
        have hw : |(5344406311/10000000000 : ℝ)|=(5344406311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633478503/5000000000 : ℝ)|^263 ≤ (10713988262907/25000000000000 : ℝ)^199
        have hw : |(2633478503/5000000000 : ℝ)|=(2633478503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2191917307/10000000000 : ℝ)|^263 ≤ (2690654367089/20000000000000 : ℝ)^199
        have hw : |(-2191917307/10000000000 : ℝ)|=(2191917307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s7_3 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (217669281/500000000 : ℝ)*x 0 + (2114627277/5000000000 : ℝ)*x 1 + (179242911/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217669281/500000000 : ℝ)^263 ≤ (4164674417817/12500000000000 : ℝ)^199 := by
    have hnat : (217669281 : ℕ)^263*12500000000000^199 ≤ 4164674417817^199*500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217669281 500000000 4164674417817 12500000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114627277/5000000000 : ℝ)^263 ≤ (8016914939483/25000000000000 : ℝ)^199 := by
    have hnat : (2114627277 : ℕ)^263*25000000000000^199 ≤ 8016914939483^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114627277 5000000000 8016914939483 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179242911/400000000 : ℝ)^263 ≤ (8653736221547/25000000000000 : ℝ)^199 := by
    have hnat : (179242911 : ℕ)^263*25000000000000^199 ≤ 8653736221547^199*400000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179242911 400000000 8653736221547 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217669281/500000000 : ℝ), (2114627277/5000000000 : ℝ), (179242911/400000000 : ℝ)] ![(4164674417817/12500000000000 : ℝ), (8016914939483/25000000000000 : ℝ), (8653736221547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217669281/500000000 : ℝ)|^263 ≤ (4164674417817/12500000000000 : ℝ)^199
        have hw : |(217669281/500000000 : ℝ)|=(217669281/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114627277/5000000000 : ℝ)|^263 ≤ (8016914939483/25000000000000 : ℝ)^199
        have hw : |(2114627277/5000000000 : ℝ)|=(2114627277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179242911/400000000 : ℝ)|^263 ≤ (8653736221547/25000000000000 : ℝ)^199
        have hw : |(179242911/400000000 : ℝ)|=(179242911/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s7_4 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-26609323/125000000 : ℝ)*x 0 + (2633635877/5000000000 : ℝ)*x 1 + (2695616947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26609323/125000000 : ℝ)^263 ≤ (1617905089881/12500000000000 : ℝ)^199 := by
    have hnat : (26609323 : ℕ)^263*12500000000000^199 ≤ 1617905089881^199*125000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26609323 125000000 1617905089881 12500000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633635877/5000000000 : ℝ)^263 ≤ (10714834439909/25000000000000 : ℝ)^199 := by
    have hnat : (2633635877 : ℕ)^263*25000000000000^199 ≤ 10714834439909^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633635877 5000000000 10714834439909 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695616947/5000000000 : ℝ)^263 ≤ (11049355374693/25000000000000 : ℝ)^199 := by
    have hnat : (2695616947 : ℕ)^263*25000000000000^199 ≤ 11049355374693^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695616947 5000000000 11049355374693 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26609323/125000000 : ℝ), (2633635877/5000000000 : ℝ), (2695616947/5000000000 : ℝ)] ![(1617905089881/12500000000000 : ℝ), (10714834439909/25000000000000 : ℝ), (11049355374693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26609323/125000000 : ℝ)|^263 ≤ (1617905089881/12500000000000 : ℝ)^199
        have hw : |(-26609323/125000000 : ℝ)|=(26609323/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633635877/5000000000 : ℝ)|^263 ≤ (10714834439909/25000000000000 : ℝ)^199
        have hw : |(2633635877/5000000000 : ℝ)|=(2633635877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695616947/5000000000 : ℝ)|^263 ≤ (11049355374693/25000000000000 : ℝ)^199
        have hw : |(2695616947/5000000000 : ℝ)|=(2695616947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s7_5 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2656328423/5000000000 : ℝ)*x 0 + (-1033819703/5000000000 : ℝ)*x 1 + (1078246997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656328423/5000000000 : ℝ)^263 ≤ (43348075390951/100000000000000 : ℝ)^199 := by
    have hnat : (2656328423 : ℕ)^263*100000000000000^199 ≤ 43348075390951^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656328423 5000000000 43348075390951 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033819703/5000000000 : ℝ)^263 ≤ (1245449127379/10000000000000 : ℝ)^199 := by
    have hnat : (1033819703 : ℕ)^263*10000000000000^199 ≤ 1245449127379^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033819703 5000000000 1245449127379 10000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078246997/2000000000 : ℝ)^263 ≤ (44197433319281/100000000000000 : ℝ)^199 := by
    have hnat : (1078246997 : ℕ)^263*100000000000000^199 ≤ 44197433319281^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078246997 2000000000 44197433319281 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656328423/5000000000 : ℝ), (-1033819703/5000000000 : ℝ), (1078246997/2000000000 : ℝ)] ![(43348075390951/100000000000000 : ℝ), (1245449127379/10000000000000 : ℝ), (44197433319281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656328423/5000000000 : ℝ)|^263 ≤ (43348075390951/100000000000000 : ℝ)^199
        have hw : |(2656328423/5000000000 : ℝ)|=(2656328423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1033819703/5000000000 : ℝ)|^263 ≤ (1245449127379/10000000000000 : ℝ)^199
        have hw : |(-1033819703/5000000000 : ℝ)|=(1033819703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078246997/2000000000 : ℝ)|^263 ≤ (44197433319281/100000000000000 : ℝ)^199
        have hw : |(1078246997/2000000000 : ℝ)|=(1078246997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s7_6 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1062531513/2000000000 : ℝ)*x 0 + (1078246769/2000000000 : ℝ)*x 1 + (-129227499/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062531513/2000000000 : ℝ)^263 ≤ (8669616628861/20000000000000 : ℝ)^199 := by
    have hnat : (1062531513 : ℕ)^263*20000000000000^199 ≤ 8669616628861^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062531513 2000000000 8669616628861 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078246769/2000000000 : ℝ)^263 ≤ (22098710483939/50000000000000 : ℝ)^199 := by
    have hnat : (1078246769 : ℕ)^263*50000000000000^199 ≤ 22098710483939^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078246769 2000000000 22098710483939 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129227499/625000000 : ℝ)^263 ≤ (6227247937551/50000000000000 : ℝ)^199 := by
    have hnat : (129227499 : ℕ)^263*50000000000000^199 ≤ 6227247937551^199*625000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129227499 625000000 6227247937551 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062531513/2000000000 : ℝ), (1078246769/2000000000 : ℝ), (-129227499/625000000 : ℝ)] ![(8669616628861/20000000000000 : ℝ), (22098710483939/50000000000000 : ℝ), (6227247937551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062531513/2000000000 : ℝ)|^263 ≤ (8669616628861/20000000000000 : ℝ)^199
        have hw : |(1062531513/2000000000 : ℝ)|=(1062531513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078246769/2000000000 : ℝ)|^263 ≤ (22098710483939/50000000000000 : ℝ)^199
        have hw : |(1078246769/2000000000 : ℝ)|=(1078246769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129227499/625000000 : ℝ)|^263 ≤ (6227247937551/50000000000000 : ℝ)^199
        have hw : |(-129227499/625000000 : ℝ)|=(129227499/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s7_7 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4353395107/10000000000 : ℝ)*x 0 + (4480438669/10000000000 : ℝ)*x 1 + (4229890959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353395107/10000000000 : ℝ)^263 ≤ (8329372824827/25000000000000 : ℝ)^199 := by
    have hnat : (4353395107 : ℕ)^263*25000000000000^199 ≤ 8329372824827^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353395107 10000000000 8329372824827 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480438669/10000000000 : ℝ)^263 ≤ (8652117857179/25000000000000 : ℝ)^199 := by
    have hnat : (4480438669 : ℕ)^263*25000000000000^199 ≤ 8652117857179^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480438669 10000000000 8652117857179 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229890959/10000000000 : ℝ)^263 ≤ (16037018627039/50000000000000 : ℝ)^199 := by
    have hnat : (4229890959 : ℕ)^263*50000000000000^199 ≤ 16037018627039^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229890959 10000000000 16037018627039 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353395107/10000000000 : ℝ), (4480438669/10000000000 : ℝ), (4229890959/10000000000 : ℝ)] ![(8329372824827/25000000000000 : ℝ), (8652117857179/25000000000000 : ℝ), (16037018627039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353395107/10000000000 : ℝ)|^263 ≤ (8329372824827/25000000000000 : ℝ)^199
        have hw : |(4353395107/10000000000 : ℝ)|=(4353395107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480438669/10000000000 : ℝ)|^263 ≤ (8652117857179/25000000000000 : ℝ)^199
        have hw : |(4480438669/10000000000 : ℝ)|=(4480438669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229890959/10000000000 : ℝ)|^263 ≤ (16037018627039/50000000000000 : ℝ)^199
        have hw : |(4229890959/10000000000 : ℝ)|=(4229890959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1223_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2291/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2819/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14099/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11451/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14099/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11451/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14099/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11451/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14099/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11451/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14099/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11451/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14099/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11451/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11451/100000 : ℝ) ^ (8415/2048 : ℝ) ≤ (13579826029938719/100000000000000000000 : ℝ) := by
    have hpowers : (11451/100000 : ℝ)^8415 ≤ (13579826029938719/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11451 : ℕ)^8415*100000000000000000000^2048 ≤ 13579826029938719^2048*100000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11451 100000 13579826029938719 100000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11451/100000 : ℝ)) (X := (13579826029938719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14099/100000 : ℝ) ^ (8415/2048 : ℝ) ≤ (31923547700439653/100000000000000000000 : ℝ) := by
    have hpowers : (14099/100000 : ℝ)^8415 ≤ (31923547700439653/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14099 : ℕ)^8415*100000000000000000000^2048 ≤ 31923547700439653^2048*100000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14099 100000 31923547700439653 100000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14099/100000 : ℝ)) (X := (31923547700439653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013579826029938719/50000000000000000000 : ℝ) ≤ (10000660929924637/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (50013579826029938719/50000000000000000000 : ℝ)^2048 ≤ (10000660929924637/10000000000000000 : ℝ)^8415 := by
      have hnat : (50013579826029938719 : ℕ)^2048*10000000000000000^8415 ≤ 10000660929924637^8415*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013579826029938719 50000000000000000000 10000660929924637 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000660929924637/10000000000000000 : ℝ)) (X := (50013579826029938719/50000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011375843432594593/25000000000000000000 : ℝ) ≤ (10001107247431097/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (25011375843432594593/25000000000000000000 : ℝ)^2048 ≤ (10001107247431097/10000000000000000 : ℝ)^8415 := by
      have hnat : (25011375843432594593 : ℕ)^2048*10000000000000000^8415 ≤ 10001107247431097^8415*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011375843432594593 25000000000000000000 10001107247431097 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001107247431097/10000000000000000 : ℝ)) (X := (25011375843432594593/25000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031923547700439653/50000000000000000000 : ℝ) ≤ (10001553564937557/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (50031923547700439653/50000000000000000000 : ℝ)^2048 ≤ (10001553564937557/10000000000000000 : ℝ)^8415 := by
      have hnat : (50031923547700439653 : ℕ)^2048*10000000000000000^8415 ≤ 10001553564937557^8415*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031923547700439653 50000000000000000000 10001553564937557 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001553564937557/10000000000000000 : ℝ)) (X := (50031923547700439653/50000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13579826029938719/100000000000000000000 : ℝ) ≤ ((1654470536181718241/1655000000000000000 : ℝ)+2*(22315875323/13240000000000 : ℝ)*(11451/100000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (1654470536181718241/1655000000000000000 : ℝ)+2*(22315875323/13240000000000 : ℝ)*(11451/100000 : ℝ)=(10000660929924637/10000000000000000 : ℝ) by norm_num, show 1+2*(13579826029938719/100000000000000000000 : ℝ)=(50013579826029938719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31923547700439653/100000000000000000000 : ℝ)+(13579826029938719/100000000000000000000 : ℝ) ≤ ((1654470536181718241/1655000000000000000 : ℝ)+(22315875323/13240000000000 : ℝ)*((14099/100000 : ℝ)+(11451/100000 : ℝ)))^(8415/2048 : ℝ) := by
    rw [show (1654470536181718241/1655000000000000000 : ℝ)+(22315875323/13240000000000 : ℝ)*((14099/100000 : ℝ)+(11451/100000 : ℝ))=(10001107247431097/10000000000000000 : ℝ) by norm_num, show 1+(31923547700439653/100000000000000000000 : ℝ)+(13579826029938719/100000000000000000000 : ℝ)=(25011375843432594593/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31923547700439653/100000000000000000000 : ℝ) ≤ ((1654470536181718241/1655000000000000000 : ℝ)+2*(22315875323/13240000000000 : ℝ)*(14099/100000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (1654470536181718241/1655000000000000000 : ℝ)+2*(22315875323/13240000000000 : ℝ)*(14099/100000 : ℝ)=(10001553564937557/10000000000000000 : ℝ) by norm_num, show 1+2*(31923547700439653/100000000000000000000 : ℝ)=(50031923547700439653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1654470536181718241/1655000000000000000 : ℝ)*(X 1 0+X 2 0)+(22315875323/13240000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (11451/100000 : ℝ)) (hi := (14099/100000 : ℝ)) (c := (1654470536181718241/1655000000000000000 : ℝ)) (alpha := (22315875323/13240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1654470536181718241/1655000000000000000 : ℝ)*(X 0 1+X 2 1)+(22315875323/13240000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (11451/100000 : ℝ)) (hi := (14099/100000 : ℝ)) (c := (1654470536181718241/1655000000000000000 : ℝ)) (alpha := (22315875323/13240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1654470536181718241/1655000000000000000 : ℝ)*(X 0 2+X 1 2)+(22315875323/13240000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (11451/100000 : ℝ)) (hi := (14099/100000 : ℝ)) (c := (1654470536181718241/1655000000000000000 : ℝ)) (alpha := (22315875323/13240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-532185303/2500000000 : ℝ)*X 0 0+(5391549721/10000000000 : ℝ)*X 0 1+(329184813/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344406319/10000000000 : ℝ)*X 1 0+(-273989661/1250000000 : ℝ)*X 1 1+(5266957013/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344406311/10000000000 : ℝ)*X 2 0+(2633478503/5000000000 : ℝ)*X 2 1+(-2191917307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((217669281/500000000 : ℝ)*X 0 0+(2114627277/5000000000 : ℝ)*X 0 1+(179242911/400000000 : ℝ)*X 0 2+(217669281/500000000 : ℝ)*X 1 0+(2114627277/5000000000 : ℝ)*X 1 1+(179242911/400000000 : ℝ)*X 1 2+(217669281/500000000 : ℝ)*X 2 0+(2114627277/5000000000 : ℝ)*X 2 1+(179242911/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-26609323/125000000 : ℝ)*X 0 0+(2633635877/5000000000 : ℝ)*X 0 1+(2695616947/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656328423/5000000000 : ℝ)*X 1 0+(-1033819703/5000000000 : ℝ)*X 1 1+(1078246997/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062531513/2000000000 : ℝ)*X 2 0+(1078246769/2000000000 : ℝ)*X 2 1+(-129227499/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353395107/10000000000 : ℝ)*X 0 0+(4480438669/10000000000 : ℝ)*X 0 1+(4229890959/10000000000 : ℝ)*X 0 2+(4353395107/10000000000 : ℝ)*X 1 0+(4480438669/10000000000 : ℝ)*X 1 1+(4229890959/10000000000 : ℝ)*X 1 2+(4353395107/10000000000 : ℝ)*X 2 0+(4480438669/10000000000 : ℝ)*X 2 1+(4229890959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (284618379113392855461/33100000000000000000000000 : ℝ) := by norm_num
    linear_combination (25860901/1562500000000 : ℝ)*(base19) + (386782331/25000000000000 : ℝ)*(base23) + (2051267/4000000000000 : ℝ)*(lower2) + (115616151/50000000000000 : ℝ)*(upper3) + (126735717/100000000000000 : ℝ)*(upper5) + (299935253851709/5000000000000 : ℝ)*(major0) + (299935253851709/5000000000000 : ℝ)*(major1) + (299935253851709/5000000000000 : ℝ)*(major2) + (2006549984056699/25000000000000 : ℝ)*(sp0) + (8026243031659739/100000000000000 : ℝ)*(sp1) + (8026243139628079/100000000000000 : ℝ)*(sp2) + (1985570241867271/50000000000000 : ℝ)*(sp3) + (44750530607/100000000000000 : ℝ)*(sp4) + (6174237913/25000000000000 : ℝ)*(sp7) + (1985582590343097/50000000000000 : ℝ)*(f.failure) + (8026244686757403/100000000000000 : ℝ)*(f.sum) + (1560709236069/165500000000000000000000000 : ℝ)*base65 + (74619017103551131/8275000000000000000000000000000 : ℝ)*base68 + (30931468613598869/8275000000000000000000000000000 : ℝ)*base69 + (125380428174676131/8275000000000000000000000000000 : ℝ)*base72 + (205598856737/165500000000000000000000000 : ℝ)*base74 + (3355328419176131/8275000000000000000000000000000 : ℝ)*base76 + (11728743348623869/8275000000000000000000000000000 : ℝ)*base77 + (137276649814448869/8275000000000000000000000000000 : ℝ)*base79 + (529595590711/66200000000000000000000000 : ℝ)*base81 + (41207747/5000000000000000000000 : ℝ)*base90 + (41207747/5000000000000000000000 : ℝ)*base92 + (41207747/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5866090940150056496517/662000000000000000000000000 : ℝ) := by norm_num
    linear_combination (304297273/20000000000000 : ℝ)*(base19) + (1367842661/50000000000000 : ℝ)*(base23) + (154253947/50000000000000 : ℝ)*(upper3) + (106235171/100000000000000 : ℝ)*(lower4) + (6029142855841159/100000000000000 : ℝ)*(major0) + (6029142855841159/100000000000000 : ℝ)*(major1) + (6029142855841159/100000000000000 : ℝ)*(major2) + (6401053313/6250000000000 : ℝ)*(sp1) + (44723059403/50000000000000 : ℝ)*(sp2) + (12256281731/50000000000000 : ℝ)*(sp3) + (4033485156147467/50000000000000 : ℝ)*(sp4) + (8066866373955561/100000000000000 : ℝ)*(sp5) + (1613375626098161/20000000000000 : ℝ)*(sp6) + (3991290591451763/100000000000000 : ℝ)*(sp7) + (159652604160609/4000000000000 : ℝ)*(f.failure) + (4033485156147467/50000000000000 : ℝ)*(f.sum) + (900486431109/132400000000000000000000000 : ℝ)*base66 + (1576250562478006319/165500000000000000000000000000000 : ℝ)*base67 + (1452485172132006319/165500000000000000000000000000000 : ℝ)*base69 + (820006495145993681/165500000000000000000000000000000 : ℝ)*base72 + (2245756775793/662000000000000000000000000 : ℝ)*base74 + (213926664059493681/165500000000000000000000000000000 : ℝ)*base76 + (1117568811742506319/165500000000000000000000000000000 : ℝ)*base77 + (802291576559493681/165500000000000000000000000000000 : ℝ)*base80 + (6449354086353/662000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1278341/400000000000000000000 : ℝ)*base89 + (1278341/400000000000000000000 : ℝ)*base91 + (1278341/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1223_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1223_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1223_s8_0 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064371933/5000000000 : ℝ)*x 0 + (1078302411/2000000000 : ℝ)*x 1 + (210679719/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064371933/5000000000 : ℝ)^263 ≤ (6471612428323/50000000000000 : ℝ)^199 := by
    have hnat : (1064371933 : ℕ)^263*50000000000000^199 ≤ 6471612428323^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064371933 5000000000 6471612428323 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078302411/2000000000 : ℝ)^263 ≤ (22100217638439/50000000000000 : ℝ)^199 := by
    have hnat : (1078302411 : ℕ)^263*50000000000000^199 ≤ 22100217638439^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078302411 2000000000 22100217638439 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210679719/400000000 : ℝ)^263 ≤ (857126796969/2000000000000 : ℝ)^199 := by
    have hnat : (210679719 : ℕ)^263*2000000000000^199 ≤ 857126796969^199*400000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210679719 400000000 857126796969 2000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064371933/5000000000 : ℝ), (1078302411/2000000000 : ℝ), (210679719/400000000 : ℝ)] ![(6471612428323/50000000000000 : ℝ), (22100217638439/50000000000000 : ℝ), (857126796969/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064371933/5000000000 : ℝ)|^263 ≤ (6471612428323/50000000000000 : ℝ)^199
        have hw : |(-1064371933/5000000000 : ℝ)|=(1064371933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078302411/2000000000 : ℝ)|^263 ≤ (22100217638439/50000000000000 : ℝ)^199
        have hw : |(1078302411/2000000000 : ℝ)|=(1078302411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210679719/400000000 : ℝ)|^263 ≤ (857126796969/2000000000000 : ℝ)^199
        have hw : |(210679719/400000000 : ℝ)|=(210679719/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s8_1 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5344397013/10000000000 : ℝ)*x 0 + (-1095941031/5000000000 : ℝ)*x 1 + (2633496467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344397013/10000000000 : ℝ)^263 ≤ (21845337319559/50000000000000 : ℝ)^199 := by
    have hnat : (5344397013 : ℕ)^263*50000000000000^199 ≤ 21845337319559^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344397013 10000000000 21845337319559 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095941031/5000000000 : ℝ)^263 ≤ (1345298594291/10000000000000 : ℝ)^199 := by
    have hnat : (1095941031 : ℕ)^263*10000000000000^199 ≤ 1345298594291^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095941031 5000000000 1345298594291 10000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633496467/5000000000 : ℝ)^263 ≤ (669630303243/1562500000000 : ℝ)^199 := by
    have hnat : (2633496467 : ℕ)^263*1562500000000^199 ≤ 669630303243^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633496467 5000000000 669630303243 1562500000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344397013/10000000000 : ℝ), (-1095941031/5000000000 : ℝ), (2633496467/5000000000 : ℝ)] ![(21845337319559/50000000000000 : ℝ), (1345298594291/10000000000000 : ℝ), (669630303243/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344397013/10000000000 : ℝ)|^263 ≤ (21845337319559/50000000000000 : ℝ)^199
        have hw : |(5344397013/10000000000 : ℝ)|=(5344397013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1095941031/5000000000 : ℝ)|^263 ≤ (1345298594291/10000000000000 : ℝ)^199
        have hw : |(-1095941031/5000000000 : ℝ)|=(1095941031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633496467/5000000000 : ℝ)|^263 ≤ (669630303243/1562500000000 : ℝ)^199
        have hw : |(2633496467/5000000000 : ℝ)|=(2633496467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s8_2 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1336099247/2500000000 : ℝ)*x 0 + (2633496463/5000000000 : ℝ)*x 1 + (-1095941053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336099247/2500000000 : ℝ)^263 ≤ (10922668592253/25000000000000 : ℝ)^199 := by
    have hnat : (1336099247 : ℕ)^263*25000000000000^199 ≤ 10922668592253^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336099247 2500000000 10922668592253 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633496463/5000000000 : ℝ)^263 ≤ (42856339321523/100000000000000 : ℝ)^199 := by
    have hnat : (2633496463 : ℕ)^263*100000000000000^199 ≤ 42856339321523^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633496463 5000000000 42856339321523 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095941053/5000000000 : ℝ)^263 ≤ (13452986299819/100000000000000 : ℝ)^199 := by
    have hnat : (1095941053 : ℕ)^263*100000000000000^199 ≤ 13452986299819^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095941053 5000000000 13452986299819 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336099247/2500000000 : ℝ), (2633496463/5000000000 : ℝ), (-1095941053/5000000000 : ℝ)] ![(10922668592253/25000000000000 : ℝ), (42856339321523/100000000000000 : ℝ), (13452986299819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336099247/2500000000 : ℝ)|^263 ≤ (10922668592253/25000000000000 : ℝ)^199
        have hw : |(1336099247/2500000000 : ℝ)|=(1336099247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633496463/5000000000 : ℝ)|^263 ≤ (42856339321523/100000000000000 : ℝ)^199
        have hw : |(2633496463/5000000000 : ℝ)|=(2633496463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1095941053/5000000000 : ℝ)|^263 ≤ (13452986299819/100000000000000 : ℝ)^199
        have hw : |(-1095941053/5000000000 : ℝ)|=(1095941053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s8_3 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (870677491/2000000000 : ℝ)*x 0 + (33041631/78125000 : ℝ)*x 1 + (448099811/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870677491/2000000000 : ℝ)^263 ≤ (33317413902737/100000000000000 : ℝ)^199 := by
    have hnat : (870677491 : ℕ)^263*100000000000000^199 ≤ 33317413902737^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870677491 2000000000 33317413902737 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33041631/78125000 : ℝ)^263 ≤ (641368069001/2000000000000 : ℝ)^199 := by
    have hnat : (33041631 : ℕ)^263*2000000000000^199 ≤ 641368069001^199*78125000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33041631 78125000 641368069001 2000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448099811/1000000000 : ℝ)^263 ≤ (34614182631287/100000000000000 : ℝ)^199 := by
    have hnat : (448099811 : ℕ)^263*100000000000000^199 ≤ 34614182631287^199*1000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448099811 1000000000 34614182631287 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870677491/2000000000 : ℝ), (33041631/78125000 : ℝ), (448099811/1000000000 : ℝ)] ![(33317413902737/100000000000000 : ℝ), (641368069001/2000000000000 : ℝ), (34614182631287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870677491/2000000000 : ℝ)|^263 ≤ (33317413902737/100000000000000 : ℝ)^199
        have hw : |(870677491/2000000000 : ℝ)|=(870677491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33041631/78125000 : ℝ)|^263 ≤ (641368069001/2000000000000 : ℝ)^199
        have hw : |(33041631/78125000 : ℝ)|=(33041631/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448099811/1000000000 : ℝ)|^263 ≤ (34614182631287/100000000000000 : ℝ)^199
        have hw : |(448099811/1000000000 : ℝ)|=(448099811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s8_4 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064374297/5000000000 : ℝ)*x 0 + (658413319/1250000000 : ℝ)*x 1 + (2695598657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064374297/5000000000 : ℝ)^263 ≤ (6471631424639/50000000000000 : ℝ)^199 := by
    have hnat : (1064374297 : ℕ)^263*50000000000000^199 ≤ 6471631424639^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064374297 5000000000 6471631424639 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658413319/1250000000 : ℝ)^263 ≤ (2678731998197/6250000000000 : ℝ)^199 := by
    have hnat : (658413319 : ℕ)^263*6250000000000^199 ≤ 2678731998197^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658413319 1250000000 2678731998197 6250000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695598657/5000000000 : ℝ)^263 ≤ (2209851258543/5000000000000 : ℝ)^199 := by
    have hnat : (2695598657 : ℕ)^263*5000000000000^199 ≤ 2209851258543^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695598657 5000000000 2209851258543 5000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064374297/5000000000 : ℝ), (658413319/1250000000 : ℝ), (2695598657/5000000000 : ℝ)] ![(6471631424639/50000000000000 : ℝ), (2678731998197/6250000000000 : ℝ), (2209851258543/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064374297/5000000000 : ℝ)|^263 ≤ (6471631424639/50000000000000 : ℝ)^199
        have hw : |(-1064374297/5000000000 : ℝ)|=(1064374297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658413319/1250000000 : ℝ)|^263 ≤ (2678731998197/6250000000000 : ℝ)^199
        have hw : |(658413319/1250000000 : ℝ)|=(658413319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695598657/5000000000 : ℝ)|^263 ≤ (2209851258543/5000000000000 : ℝ)^199
        have hw : |(2695598657/5000000000 : ℝ)|=(2695598657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s8_5 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (531266639/1000000000 : ℝ)*x 0 + (-6461493/31250000 : ℝ)*x 1 + (1078239461/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531266639/1000000000 : ℝ)^263 ≤ (21674089154469/50000000000000 : ℝ)^199 := by
    have hnat : (531266639 : ℕ)^263*50000000000000^199 ≤ 21674089154469^199*1000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531266639 1000000000 21674089154469 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6461493/31250000 : ℝ)^263 ≤ (12454796601221/100000000000000 : ℝ)^199 := by
    have hnat : (6461493 : ℕ)^263*100000000000000^199 ≤ 12454796601221^199*31250000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6461493 31250000 12454796601221 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078239461/2000000000 : ℝ)^263 ≤ (883940501467/2000000000000 : ℝ)^199 := by
    have hnat : (1078239461 : ℕ)^263*2000000000000^199 ≤ 883940501467^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078239461 2000000000 883940501467 2000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531266639/1000000000 : ℝ), (-6461493/31250000 : ℝ), (1078239461/2000000000 : ℝ)] ![(21674089154469/50000000000000 : ℝ), (12454796601221/100000000000000 : ℝ), (883940501467/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531266639/1000000000 : ℝ)|^263 ≤ (21674089154469/50000000000000 : ℝ)^199
        have hw : |(531266639/1000000000 : ℝ)|=(531266639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6461493/31250000 : ℝ)|^263 ≤ (12454796601221/100000000000000 : ℝ)^199
        have hw : |(-6461493/31250000 : ℝ)|=(6461493/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078239461/2000000000 : ℝ)|^263 ≤ (883940501467/2000000000000 : ℝ)^199
        have hw : |(1078239461/2000000000 : ℝ)|=(1078239461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s8_6 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5312666389/10000000000 : ℝ)*x 0 + (5391197301/10000000000 : ℝ)*x 1 + (-2067677767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312666389/10000000000 : ℝ)^263 ≤ (8669635659631/20000000000000 : ℝ)^199 := by
    have hnat : (5312666389 : ℕ)^263*20000000000000^199 ≤ 8669635659631^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312666389 10000000000 8669635659631 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391197301/10000000000 : ℝ)^263 ≤ (44197025030011/100000000000000 : ℝ)^199 := by
    have hnat : (5391197301 : ℕ)^263*100000000000000^199 ≤ 44197025030011^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391197301 10000000000 44197025030011 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067677767/10000000000 : ℝ)^263 ≤ (6227398328473/50000000000000 : ℝ)^199 := by
    have hnat : (2067677767 : ℕ)^263*50000000000000^199 ≤ 6227398328473^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067677767 10000000000 6227398328473 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312666389/10000000000 : ℝ), (5391197301/10000000000 : ℝ), (-2067677767/10000000000 : ℝ)] ![(8669635659631/20000000000000 : ℝ), (44197025030011/100000000000000 : ℝ), (6227398328473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312666389/10000000000 : ℝ)|^263 ≤ (8669635659631/20000000000000 : ℝ)^199
        have hw : |(5312666389/10000000000 : ℝ)|=(5312666389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391197301/10000000000 : ℝ)|^263 ≤ (44197025030011/100000000000000 : ℝ)^199
        have hw : |(5391197301/10000000000 : ℝ)|=(5391197301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2067677767/10000000000 : ℝ)|^263 ≤ (6227398328473/50000000000000 : ℝ)^199
        have hw : |(-2067677767/10000000000 : ℝ)|=(2067677767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s8_7 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (870679393/2000000000 : ℝ)*x 0 + (448036429/1000000000 : ℝ)*x 1 + (4229964853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870679393/2000000000 : ℝ)^263 ≤ (8329377523039/25000000000000 : ℝ)^199 := by
    have hnat : (870679393 : ℕ)^263*25000000000000^199 ≤ 8329377523039^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870679393 2000000000 8329377523039 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448036429/1000000000 : ℝ)^263 ≤ (34607712128141/100000000000000 : ℝ)^199 := by
    have hnat : (448036429 : ℕ)^263*100000000000000^199 ≤ 34607712128141^199*1000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448036429 1000000000 34607712128141 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229964853/10000000000 : ℝ)^263 ≤ (1002336805479/3125000000000 : ℝ)^199 := by
    have hnat : (4229964853 : ℕ)^263*3125000000000^199 ≤ 1002336805479^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229964853 10000000000 1002336805479 3125000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870679393/2000000000 : ℝ), (448036429/1000000000 : ℝ), (4229964853/10000000000 : ℝ)] ![(8329377523039/25000000000000 : ℝ), (34607712128141/100000000000000 : ℝ), (1002336805479/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870679393/2000000000 : ℝ)|^263 ≤ (8329377523039/25000000000000 : ℝ)^199
        have hw : |(870679393/2000000000 : ℝ)|=(870679393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448036429/1000000000 : ℝ)|^263 ≤ (34607712128141/100000000000000 : ℝ)^199
        have hw : |(448036429/1000000000 : ℝ)|=(448036429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229964853/10000000000 : ℝ)|^263 ≤ (1002336805479/3125000000000 : ℝ)^199
        have hw : |(4229964853/10000000000 : ℝ)|=(4229964853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1223_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (358/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7047/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2291/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2291/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2291/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2291/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2291/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2291/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2291/20000 : ℝ) ^ (8415/2048 : ℝ) ≤ (2719865530638601/20000000000000000000 : ℝ) := by
    have hpowers : (2291/20000 : ℝ)^8415 ≤ (2719865530638601/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2291 : ℕ)^8415*20000000000000000000^2048 ≤ 2719865530638601^2048*20000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2291 20000 2719865530638601 20000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2291/20000 : ℝ)) (X := (2719865530638601/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2819/20000 : ℝ) ^ (8415/2048 : ℝ) ≤ (15943175026820069/50000000000000000000 : ℝ) := by
    have hpowers : (2819/20000 : ℝ)^8415 ≤ (15943175026820069/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2819 : ℕ)^8415*50000000000000000000^2048 ≤ 15943175026820069^2048*20000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 20000 15943175026820069 50000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/20000 : ℝ)) (X := (15943175026820069/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002719865530638601/10000000000000000000 : ℝ) ≤ (100006618789707/100000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (10002719865530638601/10000000000000000000 : ℝ)^2048 ≤ (100006618789707/100000000000000 : ℝ)^8415 := by
      have hnat : (10002719865530638601 : ℕ)^2048*100000000000000^8415 ≤ 100006618789707^8415*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002719865530638601 10000000000000000000 100006618789707 100000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100006618789707/100000000000000 : ℝ)) (X := (10002719865530638601/10000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045485677706833143/100000000000000000000 : ℝ) ≤ (2000221363380489/2000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (100045485677706833143/100000000000000000000 : ℝ)^2048 ≤ (2000221363380489/2000000000000000 : ℝ)^8415 := by
      have hnat : (100045485677706833143 : ℕ)^2048*2000000000000000^8415 ≤ 2000221363380489^8415*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045485677706833143 100000000000000000000 2000221363380489 2000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000221363380489/2000000000000000 : ℝ)) (X := (100045485677706833143/100000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015943175026820069/25000000000000000000 : ℝ) ≤ (1000155175483419/1000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (25015943175026820069/25000000000000000000 : ℝ)^2048 ≤ (1000155175483419/1000000000000000 : ℝ)^8415 := by
      have hnat : (25015943175026820069 : ℕ)^2048*1000000000000000^8415 ≤ 1000155175483419^8415*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015943175026820069 25000000000000000000 1000155175483419 1000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000155175483419/1000000000000000 : ℝ)) (X := (25015943175026820069/25000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2719865530638601/20000000000000000000 : ℝ) ≤ ((175943692216442467/176000000000000000 : ℝ)+2*(29662528783/17600000000000 : ℝ)*(2291/20000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (175943692216442467/176000000000000000 : ℝ)+2*(29662528783/17600000000000 : ℝ)*(2291/20000 : ℝ)=(100006618789707/100000000000000 : ℝ) by norm_num, show 1+2*(2719865530638601/20000000000000000000 : ℝ)=(10002719865530638601/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15943175026820069/50000000000000000000 : ℝ)+(2719865530638601/20000000000000000000 : ℝ) ≤ ((175943692216442467/176000000000000000 : ℝ)+(29662528783/17600000000000 : ℝ)*((2819/20000 : ℝ)+(2291/20000 : ℝ)))^(8415/2048 : ℝ) := by
    rw [show (175943692216442467/176000000000000000 : ℝ)+(29662528783/17600000000000 : ℝ)*((2819/20000 : ℝ)+(2291/20000 : ℝ))=(2000221363380489/2000000000000000 : ℝ) by norm_num, show 1+(15943175026820069/50000000000000000000 : ℝ)+(2719865530638601/20000000000000000000 : ℝ)=(100045485677706833143/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15943175026820069/50000000000000000000 : ℝ) ≤ ((175943692216442467/176000000000000000 : ℝ)+2*(29662528783/17600000000000 : ℝ)*(2819/20000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (175943692216442467/176000000000000000 : ℝ)+2*(29662528783/17600000000000 : ℝ)*(2819/20000 : ℝ)=(1000155175483419/1000000000000000 : ℝ) by norm_num, show 1+2*(15943175026820069/50000000000000000000 : ℝ)=(25015943175026820069/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (175943692216442467/176000000000000000 : ℝ)*(X 1 0+X 2 0)+(29662528783/17600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (2291/20000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (175943692216442467/176000000000000000 : ℝ)) (alpha := (29662528783/17600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (175943692216442467/176000000000000000 : ℝ)*(X 0 1+X 2 1)+(29662528783/17600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (2291/20000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (175943692216442467/176000000000000000 : ℝ)) (alpha := (29662528783/17600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (175943692216442467/176000000000000000 : ℝ)*(X 0 2+X 1 2)+(29662528783/17600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (2291/20000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (175943692216442467/176000000000000000 : ℝ)) (alpha := (29662528783/17600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1064371933/5000000000 : ℝ)*X 0 0+(1078302411/2000000000 : ℝ)*X 0 1+(210679719/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344397013/10000000000 : ℝ)*X 1 0+(-1095941031/5000000000 : ℝ)*X 1 1+(2633496467/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336099247/2500000000 : ℝ)*X 2 0+(2633496463/5000000000 : ℝ)*X 2 1+(-1095941053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870677491/2000000000 : ℝ)*X 0 0+(33041631/78125000 : ℝ)*X 0 1+(448099811/1000000000 : ℝ)*X 0 2+(870677491/2000000000 : ℝ)*X 1 0+(33041631/78125000 : ℝ)*X 1 1+(448099811/1000000000 : ℝ)*X 1 2+(870677491/2000000000 : ℝ)*X 2 0+(33041631/78125000 : ℝ)*X 2 1+(448099811/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1064374297/5000000000 : ℝ)*X 0 0+(658413319/1250000000 : ℝ)*X 0 1+(2695598657/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531266639/1000000000 : ℝ)*X 1 0+(-6461493/31250000 : ℝ)*X 1 1+(1078239461/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312666389/10000000000 : ℝ)*X 2 0+(5391197301/10000000000 : ℝ)*X 2 1+(-2067677767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870679393/2000000000 : ℝ)*X 0 0+(448036429/1000000000 : ℝ)*X 0 1+(4229964853/10000000000 : ℝ)*X 0 2+(870679393/2000000000 : ℝ)*X 1 0+(448036429/1000000000 : ℝ)*X 1 1+(4229964853/10000000000 : ℝ)*X 1 2+(870679393/2000000000 : ℝ)*X 2 0+(448036429/1000000000 : ℝ)*X 2 1+(4229964853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26395562313200601877891167/4400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (134710979/10000000000000 : ℝ)*(base19) + (243756671/20000000000000 : ℝ)*(base23) + (24252657/50000000000000 : ℝ)*(lower2) + (181417523/100000000000000 : ℝ)*(upper3) + (35827163/100000000000000 : ℝ)*(upper5) + (6002238166660367/100000000000000 : ℝ)*(major0) + (6002238166660367/100000000000000 : ℝ)*(major1) + (6002238166660367/100000000000000 : ℝ)*(major2) + (4015468978872179/50000000000000 : ℝ)*(sp0) + (401548534351059/5000000000000 : ℝ)*(sp1) + (1606194163069523/20000000000000 : ℝ)*(sp2) + (496685526849463/12500000000000 : ℝ)*(sp3) + (34076386613/100000000000000 : ℝ)*(sp4) + (2485553459/12500000000000 : ℝ)*(sp7) + (248344006201461/6250000000000 : ℝ)*(f.failure) + (803097203413097/10000000000000 : ℝ)*(f.sum) + (2118542368639/880000000000000000000000000 : ℝ)*base66 + (39822785858584611/17600000000000000000000000000000 : ℝ)*base68 + (38853106290584611/17600000000000000000000000000000 : ℝ)*base70 + (254149857445784611/17600000000000000000000000000000 : ℝ)*base72 + (1515780861599/880000000000000000000000000 : ℝ)*base74 + (114173620960615389/17600000000000000000000000000000 : ℝ)*base75 + (351288627173784611/17600000000000000000000000000000 : ℝ)*base78 + (13963940520984611/17600000000000000000000000000000 : ℝ)*base80 + (1975037086719/880000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3668089/625000000000000000000 : ℝ)*base89 + (3668089/625000000000000000000 : ℝ)*base91 + (3668089/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34272262096130132771660181/4400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (754290023/50000000000000 : ℝ)*(base19) + (1596908487/100000000000000 : ℝ)*(base23) + (525977851/100000000000000 : ℝ)*(lower1) + (81016257/50000000000000 : ℝ)*(upper3) + (1716071/4000000000000 : ℝ)*(lower4) + (170595891/100000000000000 : ℝ)*(upper5) + (6032590721315781/100000000000000 : ℝ)*(major0) + (6032590721315781/100000000000000 : ℝ)*(major1) + (6032590721315781/100000000000000 : ℝ)*(major2) + (60904127/4000000000000 : ℝ)*(sp2) + (2017895894786903/25000000000000 : ℝ)*(sp4) + (8071582070567567/100000000000000 : ℝ)*(sp5) + (161431609192719/2000000000000 : ℝ)*(sp6) + (249599850240347/6250000000000 : ℝ)*(sp7) + (249599850240347/6250000000000 : ℝ)*(f.failure) + (2017895894786903/25000000000000 : ℝ)*(f.sum) + (240503530763/880000000000000000000000000 : ℝ)*base65 + (1018809902139498273/17600000000000000000000000000000 : ℝ)*base68 + (17130649851498273/17600000000000000000000000000000 : ℝ)*base70 + (4741476206085098273/17600000000000000000000000000000 : ℝ)*base72 + (2571767843723/880000000000000000000000000 : ℝ)*base73 + (2010268037449301727/17600000000000000000000000000000 : ℝ)*base75 + (54690336517098273/17600000000000000000000000000000 : ℝ)*base78 + (273449148437098273/17600000000000000000000000000000 : ℝ)*base80 + (1878608192757/880000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7132503/625000000000000000000 : ℝ)*base89 + (7132503/625000000000000000000 : ℝ)*base91 + (7132503/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1223_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1223_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1223_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1223_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1223_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1223_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1223_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
