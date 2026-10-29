-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1556_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:22:23.73779+00:00
-- url     : https://prove2.me/submissions/46e4f5fa-11c2-417a-9dcf-d760384ccd1f

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
theorem support_rectangle_w1556_s3_0 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-14437009/80000000 : ℝ)*x 0 + (678692227/1250000000 : ℝ)*x 1 + (2608894923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14437009/80000000 : ℝ)^4609 ≤ (1383234232981/12500000000000 : ℝ)^3585 := by
    have hnat : (14437009 : ℕ)^4609*12500000000000^3585 ≤ 1383234232981^3585*80000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14437009 80000000 1383234232981 12500000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678692227/1250000000 : ℝ)^4609 ≤ (11400974393283/25000000000000 : ℝ)^3585 := by
    have hnat : (678692227 : ℕ)^4609*25000000000000^3585 ≤ 11400974393283^3585*1250000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678692227 1250000000 11400974393283 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608894923/5000000000 : ℝ)^4609 ≤ (10832557136469/25000000000000 : ℝ)^3585 := by
    have hnat : (2608894923 : ℕ)^4609*25000000000000^3585 ≤ 10832557136469^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608894923 5000000000 10832557136469 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14437009/80000000 : ℝ), (678692227/1250000000 : ℝ), (2608894923/5000000000 : ℝ)] ![(1383234232981/12500000000000 : ℝ), (11400974393283/25000000000000 : ℝ), (10832557136469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14437009/80000000 : ℝ)|^4609 ≤ (1383234232981/12500000000000 : ℝ)^3585
        have hw : |(-14437009/80000000 : ℝ)|=(14437009/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678692227/1250000000 : ℝ)|^4609 ≤ (11400974393283/25000000000000 : ℝ)^3585
        have hw : |(678692227/1250000000 : ℝ)|=(678692227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608894923/5000000000 : ℝ)|^4609 ≤ (10832557136469/25000000000000 : ℝ)^3585
        have hw : |(2608894923/5000000000 : ℝ)|=(2608894923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s3_1 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349561357/10000000000 : ℝ)*x 0 + (-956512727/5000000000 : ℝ)*x 1 + (521778987/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349561357/10000000000 : ℝ)^4609 ≤ (2796381778249/6250000000000 : ℝ)^3585 := by
    have hnat : (5349561357 : ℕ)^4609*6250000000000^3585 ≤ 2796381778249^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349561357 10000000000 2796381778249 6250000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956512727/5000000000 : ℝ)^4609 ≤ (5963831362277/50000000000000 : ℝ)^3585 := by
    have hnat : (956512727 : ℕ)^4609*50000000000000^3585 ≤ 5963831362277^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956512727 5000000000 5963831362277 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521778987/1000000000 : ℝ)^4609 ≤ (10832557200527/25000000000000 : ℝ)^3585 := by
    have hnat : (521778987 : ℕ)^4609*25000000000000^3585 ≤ 10832557200527^3585*1000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521778987 1000000000 10832557200527 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349561357/10000000000 : ℝ), (-956512727/5000000000 : ℝ), (521778987/1000000000 : ℝ)] ![(2796381778249/6250000000000 : ℝ), (5963831362277/50000000000000 : ℝ), (10832557200527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349561357/10000000000 : ℝ)|^4609 ≤ (2796381778249/6250000000000 : ℝ)^3585
        have hw : |(5349561357/10000000000 : ℝ)|=(5349561357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-956512727/5000000000 : ℝ)|^4609 ≤ (5963831362277/50000000000000 : ℝ)^3585
        have hw : |(-956512727/5000000000 : ℝ)|=(956512727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521778987/1000000000 : ℝ)|^4609 ≤ (10832557200527/25000000000000 : ℝ)^3585
        have hw : |(521778987/1000000000 : ℝ)|=(521778987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s3_2 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349561327/10000000000 : ℝ)*x 0 + (1304447471/2500000000 : ℝ)*x 1 + (-478256369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349561327/10000000000 : ℝ)^4609 ≤ (11185527032351/25000000000000 : ℝ)^3585 := by
    have hnat : (5349561327 : ℕ)^4609*25000000000000^3585 ≤ 11185527032351^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349561327 10000000000 11185527032351 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304447471/2500000000 : ℝ)^4609 ≤ (5416278618947/12500000000000 : ℝ)^3585 := by
    have hnat : (1304447471 : ℕ)^4609*12500000000000^3585 ≤ 5416278618947^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304447471 2500000000 5416278618947 12500000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478256369/2500000000 : ℝ)^4609 ≤ (1490957862613/12500000000000 : ℝ)^3585 := by
    have hnat : (478256369 : ℕ)^4609*12500000000000^3585 ≤ 1490957862613^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478256369 2500000000 1490957862613 12500000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349561327/10000000000 : ℝ), (1304447471/2500000000 : ℝ), (-478256369/2500000000 : ℝ)] ![(11185527032351/25000000000000 : ℝ), (5416278618947/12500000000000 : ℝ), (1490957862613/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349561327/10000000000 : ℝ)|^4609 ≤ (11185527032351/25000000000000 : ℝ)^3585
        have hw : |(5349561327/10000000000 : ℝ)|=(5349561327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304447471/2500000000 : ℝ)|^4609 ≤ (5416278618947/12500000000000 : ℝ)^3585
        have hw : |(1304447471/2500000000 : ℝ)|=(1304447471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-478256369/2500000000 : ℝ)|^4609 ≤ (1490957862613/12500000000000 : ℝ)^3585
        have hw : |(-478256369/2500000000 : ℝ)|=(478256369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s3_3 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062381621/2500000000 : ℝ)*x 0 + (500986331/1250000000 : ℝ)*x 1 + (4502971231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062381621/2500000000 : ℝ)^4609 ≤ (2079992460107/6250000000000 : ℝ)^3585 := by
    have hnat : (1062381621 : ℕ)^4609*6250000000000^3585 ≤ 2079992460107^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062381621 2500000000 2079992460107 6250000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500986331/1250000000 : ℝ)^4609 ≤ (6173406791831/20000000000000 : ℝ)^3585 := by
    have hnat : (500986331 : ℕ)^4609*20000000000000^3585 ≤ 6173406791831^3585*1250000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500986331 1250000000 6173406791831 20000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502971231/10000000000 : ℝ)^4609 ≤ (17926543334577/50000000000000 : ℝ)^3585 := by
    have hnat : (4502971231 : ℕ)^4609*50000000000000^3585 ≤ 17926543334577^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502971231 10000000000 17926543334577 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062381621/2500000000 : ℝ), (500986331/1250000000 : ℝ), (4502971231/10000000000 : ℝ)] ![(2079992460107/6250000000000 : ℝ), (6173406791831/20000000000000 : ℝ), (17926543334577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062381621/2500000000 : ℝ)|^4609 ≤ (2079992460107/6250000000000 : ℝ)^3585
        have hw : |(1062381621/2500000000 : ℝ)|=(1062381621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(500986331/1250000000 : ℝ)|^4609 ≤ (6173406791831/20000000000000 : ℝ)^3585
        have hw : |(500986331/1250000000 : ℝ)|=(500986331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502971231/10000000000 : ℝ)|^4609 ≤ (17926543334577/50000000000000 : ℝ)^3585
        have hw : |(4502971231/10000000000 : ℝ)|=(4502971231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s3_4 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-225581847/1250000000 : ℝ)*x 0 + (1304727343/2500000000 : ℝ)*x 1 + (2714204977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225581847/1250000000 : ℝ)^4609 ≤ (11066099732933/100000000000000 : ℝ)^3585 := by
    have hnat : (225581847 : ℕ)^4609*100000000000000^3585 ≤ 11066099732933^3585*1250000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225581847 1250000000 11066099732933 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304727343/2500000000 : ℝ)^4609 ≤ (21671090669953/50000000000000 : ℝ)^3585 := by
    have hnat : (1304727343 : ℕ)^4609*50000000000000^3585 ≤ 21671090669953^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304727343 2500000000 21671090669953 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714204977/5000000000 : ℝ)^4609 ≤ (45591718906939/100000000000000 : ℝ)^3585 := by
    have hnat : (2714204977 : ℕ)^4609*100000000000000^3585 ≤ 45591718906939^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714204977 5000000000 45591718906939 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-225581847/1250000000 : ℝ), (1304727343/2500000000 : ℝ), (2714204977/5000000000 : ℝ)] ![(11066099732933/100000000000000 : ℝ), (21671090669953/50000000000000 : ℝ), (45591718906939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-225581847/1250000000 : ℝ)|^4609 ≤ (11066099732933/100000000000000 : ℝ)^3585
        have hw : |(-225581847/1250000000 : ℝ)|=(225581847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304727343/2500000000 : ℝ)|^4609 ≤ (21671090669953/50000000000000 : ℝ)^3585
        have hw : |(1304727343/2500000000 : ℝ)|=(1304727343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714204977/5000000000 : ℝ)|^4609 ≤ (45591718906939/100000000000000 : ℝ)^3585
        have hw : |(2714204977/5000000000 : ℝ)|=(2714204977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s3_5 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646817167/5000000000 : ℝ)*x 0 + (-851202767/5000000000 : ℝ)*x 1 + (2714205159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646817167/5000000000 : ℝ)^4609 ≤ (1379426389043/3125000000000 : ℝ)^3585 := by
    have hnat : (2646817167 : ℕ)^4609*3125000000000^3585 ≤ 1379426389043^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646817167 5000000000 1379426389043 3125000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (851202767/5000000000 : ℝ)^4609 ≤ (10266632704739/100000000000000 : ℝ)^3585 := by
    have hnat : (851202767 : ℕ)^4609*100000000000000^3585 ≤ 10266632704739^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851202767 5000000000 10266632704739 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714205159/5000000000 : ℝ)^4609 ≤ (45591722837299/100000000000000 : ℝ)^3585 := by
    have hnat : (2714205159 : ℕ)^4609*100000000000000^3585 ≤ 45591722837299^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714205159 5000000000 45591722837299 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646817167/5000000000 : ℝ), (-851202767/5000000000 : ℝ), (2714205159/5000000000 : ℝ)] ![(1379426389043/3125000000000 : ℝ), (10266632704739/100000000000000 : ℝ), (45591722837299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646817167/5000000000 : ℝ)|^4609 ≤ (1379426389043/3125000000000 : ℝ)^3585
        have hw : |(2646817167/5000000000 : ℝ)|=(2646817167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-851202767/5000000000 : ℝ)|^4609 ≤ (10266632704739/100000000000000 : ℝ)^3585
        have hw : |(-851202767/5000000000 : ℝ)|=(851202767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714205159/5000000000 : ℝ)|^4609 ≤ (45591722837299/100000000000000 : ℝ)^3585
        have hw : |(2714205159/5000000000 : ℝ)|=(2714205159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s3_6 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293635011/10000000000 : ℝ)*x 0 + (5428409877/10000000000 : ℝ)*x 1 + (-425601303/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293635011/10000000000 : ℝ)^4609 ≤ (22070825853553/50000000000000 : ℝ)^3585 := by
    have hnat : (5293635011 : ℕ)^4609*50000000000000^3585 ≤ 22070825853553^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293635011 10000000000 22070825853553 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428409877/10000000000 : ℝ)^4609 ≤ (45591718075517/100000000000000 : ℝ)^3585 := by
    have hnat : (5428409877 : ℕ)^4609*100000000000000^3585 ≤ 45591718075517^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428409877 10000000000 45591718075517 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425601303/2500000000 : ℝ)^4609 ≤ (51333151041/500000000000 : ℝ)^3585 := by
    have hnat : (425601303 : ℕ)^4609*500000000000^3585 ≤ 51333151041^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425601303 2500000000 51333151041 500000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293635011/10000000000 : ℝ), (5428409877/10000000000 : ℝ), (-425601303/2500000000 : ℝ)] ![(22070825853553/50000000000000 : ℝ), (45591718075517/100000000000000 : ℝ), (51333151041/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293635011/10000000000 : ℝ)|^4609 ≤ (22070825853553/50000000000000 : ℝ)^3585
        have hw : |(5293635011/10000000000 : ℝ)|=(5293635011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428409877/10000000000 : ℝ)|^4609 ≤ (45591718075517/100000000000000 : ℝ)^3585
        have hw : |(5428409877/10000000000 : ℝ)|=(5428409877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425601303/2500000000 : ℝ)|^4609 ≤ (51333151041/500000000000 : ℝ)^3585
        have hw : |(-425601303/2500000000 : ℝ)|=(425601303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s3_7 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249593657/10000000000 : ℝ)*x 0 + (900070833/2000000000 : ℝ)*x 1 + (2005263733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249593657/10000000000 : ℝ)^4609 ≤ (3328055568521/10000000000000 : ℝ)^3585 := by
    have hnat : (4249593657 : ℕ)^4609*10000000000000^3585 ≤ 3328055568521^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249593657 10000000000 3328055568521 10000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900070833/2000000000 : ℝ)^4609 ≤ (35826299701849/100000000000000 : ℝ)^3585 := by
    have hnat : (900070833 : ℕ)^4609*100000000000000^3585 ≤ 35826299701849^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900070833 2000000000 35826299701849 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005263733/5000000000 : ℝ)^4609 ≤ (6178628920073/20000000000000 : ℝ)^3585 := by
    have hnat : (2005263733 : ℕ)^4609*20000000000000^3585 ≤ 6178628920073^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005263733 5000000000 6178628920073 20000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249593657/10000000000 : ℝ), (900070833/2000000000 : ℝ), (2005263733/5000000000 : ℝ)] ![(3328055568521/10000000000000 : ℝ), (35826299701849/100000000000000 : ℝ), (6178628920073/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249593657/10000000000 : ℝ)|^4609 ≤ (3328055568521/10000000000000 : ℝ)^3585
        have hw : |(4249593657/10000000000 : ℝ)|=(4249593657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900070833/2000000000 : ℝ)|^4609 ≤ (35826299701849/100000000000000 : ℝ)^3585
        have hw : |(900070833/2000000000 : ℝ)|=(900070833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2005263733/5000000000 : ℝ)|^4609 ≤ (6178628920073/20000000000000 : ℝ)^3585
        have hw : |(2005263733/5000000000 : ℝ)|=(2005263733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1556_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (317/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11037/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7763/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (317/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5369/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (317/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5369/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (317/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5369/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (317/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5369/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (317/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5369/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (317/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5369/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5369/50000 : ℝ) ^ (4607/1024 : ℝ) ≤ (1091545065943759/25000000000000000000 : ℝ) := by
    have hpowers : (5369/50000 : ℝ)^4607 ≤ (1091545065943759/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5369 : ℕ)^4607*25000000000000000000^1024 ≤ 1091545065943759^1024*50000^4607 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5369 50000 1091545065943759 25000000000000000000 4607 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5369/50000 : ℝ)) (X := (1091545065943759/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (317/2000 : ℝ) ^ (4607/1024 : ℝ) ≤ (25171721664880699/100000000000000000000 : ℝ) := by
    have hpowers : (317/2000 : ℝ)^4607 ≤ (25171721664880699/100000000000000000000 : ℝ)^1024 := by
      have hnat : (317 : ℕ)^4607*100000000000000000000^1024 ≤ 25171721664880699^1024*2000^4607 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        317 2000 25171721664880699 100000000000000000000 4607 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (317/2000 : ℝ)) (X := (25171721664880699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501091545065943759/12500000000000000000 : ℝ) ≤ (2500048521996711/2500000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (12501091545065943759/12500000000000000000 : ℝ)^1024 ≤ (2500048521996711/2500000000000000 : ℝ)^4607 := by
      have hnat : (12501091545065943759 : ℕ)^1024*2500000000000000^4607 ≤ 2500048521996711^4607*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501091545065943759 12500000000000000000 2500048521996711 2500000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500048521996711/2500000000000000 : ℝ)) (X := (12501091545065943759/12500000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005907580385731147/20000000000000000000 : ℝ) ≤ (10000656464900341/10000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (20005907580385731147/20000000000000000000 : ℝ)^1024 ≤ (10000656464900341/10000000000000000 : ℝ)^4607 := by
      have hnat : (20005907580385731147 : ℕ)^1024*10000000000000000^4607 ≤ 10000656464900341^4607*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005907580385731147 20000000000000000000 10000656464900341 10000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000656464900341/10000000000000000 : ℝ)) (X := (20005907580385731147/20000000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025171721664880699/50000000000000000000 : ℝ) ≤ (5000559420906919/5000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (50025171721664880699/50000000000000000000 : ℝ)^1024 ≤ (5000559420906919/5000000000000000 : ℝ)^4607 := by
      have hnat : (50025171721664880699 : ℕ)^1024*5000000000000000^4607 ≤ 5000559420906919^4607*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025171721664880699 50000000000000000000 5000559420906919 5000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000559420906919/5000000000000000 : ℝ)) (X := (50025171721664880699/50000000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1091545065943759/25000000000000000000 : ℝ) ≤ ((12777765542798621239/12780000000000000000 : ℝ)+2*(462376913497/511200000000000 : ℝ)*(5369/50000 : ℝ))^(4607/1024 : ℝ) := by
    rw [show (12777765542798621239/12780000000000000000 : ℝ)+2*(462376913497/511200000000000 : ℝ)*(5369/50000 : ℝ)=(2500048521996711/2500000000000000 : ℝ) by norm_num, show 1+2*(1091545065943759/25000000000000000000 : ℝ)=(12501091545065943759/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25171721664880699/100000000000000000000 : ℝ)+(1091545065943759/25000000000000000000 : ℝ) ≤ ((12777765542798621239/12780000000000000000 : ℝ)+(462376913497/511200000000000 : ℝ)*((317/2000 : ℝ)+(5369/50000 : ℝ)))^(4607/1024 : ℝ) := by
    rw [show (12777765542798621239/12780000000000000000 : ℝ)+(462376913497/511200000000000 : ℝ)*((317/2000 : ℝ)+(5369/50000 : ℝ))=(10000656464900341/10000000000000000 : ℝ) by norm_num, show 1+(25171721664880699/100000000000000000000 : ℝ)+(1091545065943759/25000000000000000000 : ℝ)=(20005907580385731147/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25171721664880699/100000000000000000000 : ℝ) ≤ ((12777765542798621239/12780000000000000000 : ℝ)+2*(462376913497/511200000000000 : ℝ)*(317/2000 : ℝ))^(4607/1024 : ℝ) := by
    rw [show (12777765542798621239/12780000000000000000 : ℝ)+2*(462376913497/511200000000000 : ℝ)*(317/2000 : ℝ)=(5000559420906919/5000000000000000 : ℝ) by norm_num, show 1+2*(25171721664880699/100000000000000000000 : ℝ)=(50025171721664880699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12777765542798621239/12780000000000000000 : ℝ)*(X 1 0+X 2 0)+(462376913497/511200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (5369/50000 : ℝ)) (hi := (317/2000 : ℝ)) (c := (12777765542798621239/12780000000000000000 : ℝ)) (alpha := (462376913497/511200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12777765542798621239/12780000000000000000 : ℝ)*(X 0 1+X 2 1)+(462376913497/511200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (5369/50000 : ℝ)) (hi := (317/2000 : ℝ)) (c := (12777765542798621239/12780000000000000000 : ℝ)) (alpha := (462376913497/511200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12777765542798621239/12780000000000000000 : ℝ)*(X 0 2+X 1 2)+(462376913497/511200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (5369/50000 : ℝ)) (hi := (317/2000 : ℝ)) (c := (12777765542798621239/12780000000000000000 : ℝ)) (alpha := (462376913497/511200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-14437009/80000000 : ℝ)*X 0 0+(678692227/1250000000 : ℝ)*X 0 1+(2608894923/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349561357/10000000000 : ℝ)*X 1 0+(-956512727/5000000000 : ℝ)*X 1 1+(521778987/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349561327/10000000000 : ℝ)*X 2 0+(1304447471/2500000000 : ℝ)*X 2 1+(-478256369/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1062381621/2500000000 : ℝ)*X 0 0+(500986331/1250000000 : ℝ)*X 0 1+(4502971231/10000000000 : ℝ)*X 0 2+(1062381621/2500000000 : ℝ)*X 1 0+(500986331/1250000000 : ℝ)*X 1 1+(4502971231/10000000000 : ℝ)*X 1 2+(1062381621/2500000000 : ℝ)*X 2 0+(500986331/1250000000 : ℝ)*X 2 1+(4502971231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-225581847/1250000000 : ℝ)*X 0 0+(1304727343/2500000000 : ℝ)*X 0 1+(2714204977/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646817167/5000000000 : ℝ)*X 1 0+(-851202767/5000000000 : ℝ)*X 1 1+(2714205159/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293635011/10000000000 : ℝ)*X 2 0+(5428409877/10000000000 : ℝ)*X 2 1+(-425601303/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4249593657/10000000000 : ℝ)*X 0 0+(900070833/2000000000 : ℝ)*X 0 1+(2005263733/5000000000 : ℝ)*X 0 2+(4249593657/10000000000 : ℝ)*X 1 0+(900070833/2000000000 : ℝ)*X 1 1+(2005263733/5000000000 : ℝ)*X 1 2+(4249593657/10000000000 : ℝ)*X 2 0+(900070833/2000000000 : ℝ)*X 2 1+(2005263733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (794192817360011253646311211/106500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (647966403/50000000000000 : ℝ)*(base19) + (1169119191/100000000000000 : ℝ)*(base23) + (13417953/25000000000000 : ℝ)*(lower2) + (205491581/100000000000000 : ℝ)*(upper3) + (106953813/100000000000000 : ℝ)*(upper5) + (3371264667147049/100000000000000 : ℝ)*(major0) + (3371264667147049/100000000000000 : ℝ)*(major1) + (3371264667147049/100000000000000 : ℝ)*(major2) + (2361308772580607/50000000000000 : ℝ)*(sp0) + (4722636455516009/100000000000000 : ℝ)*(sp1) + (590329572791203/12500000000000 : ℝ)*(sp2) + (1009940784315861/50000000000000 : ℝ)*(sp3) + (50515719/250000000000 : ℝ)*(sp4) + (9765639897/100000000000000 : ℝ)*(sp7) + (1009945667135809/50000000000000 : ℝ)*(f.failure) + (944527550289763/20000000000000 : ℝ)*(f.sum) + (37109343506233/25560000000000000000000000000 : ℝ)*base65 + (14985642459053601289/1278000000000000000000000000000000 : ℝ)*base68 + (3549969148992398711/1278000000000000000000000000000000 : ℝ)*base69 + (6306246428843601289/1278000000000000000000000000000000 : ℝ)*base72 + (135788678268647/25560000000000000000000000000 : ℝ)*base74 + (18577355294315601289/1278000000000000000000000000000000 : ℝ)*base76 + (2313246403973601289/1278000000000000000000000000000000 : ℝ)*base78 + (11233265497229601289/1278000000000000000000000000000000 : ℝ)*base80 + (4150486045247/25560000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (60940379/5000000000000000000000 : ℝ)*base90 + (60940379/5000000000000000000000 : ℝ)*base92 + (60940379/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53690286591254222520560081/6656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100345513/20000000000000 : ℝ)*(base19) + (1446965771/100000000000000 : ℝ)*(base23) + (189182941/100000000000000 : ℝ)*(upper3) + (95208899/100000000000000 : ℝ)*(lower4) + (4008139/5000000000000 : ℝ)*(upper5) + (212962386588629/6250000000000 : ℝ)*(major0) + (212962386588629/6250000000000 : ℝ)*(major1) + (212962386588629/6250000000000 : ℝ)*(major2) + (5078633431/50000000000000 : ℝ)*(sp1) + (24822468339/100000000000000 : ℝ)*(sp2) + (119331384762233/2500000000000 : ℝ)*(sp4) + (4773244731494893/100000000000000 : ℝ)*(sp5) + (477322912105521/10000000000000 : ℝ)*(sp6) + (1020770355737629/50000000000000 : ℝ)*(sp7) + (1020770355737629/50000000000000 : ℝ)*(f.failure) + (119331384762233/2500000000000 : ℝ)*(f.sum) + (616875728261/798750000000000000000000000 : ℝ)*base66 + (420860925208133669/79875000000000000000000000000000 : ℝ)*base68 + (83176611814116331/79875000000000000000000000000000 : ℝ)*base69 + (178671130331633669/79875000000000000000000000000000 : ℝ)*base72 + (6709758084487/1597500000000000000000000000 : ℝ)*base74 + (1077974461076633669/79875000000000000000000000000000 : ℝ)*base76 + (138252396795758669/79875000000000000000000000000000 : ℝ)*base78 + (736917099087383669/79875000000000000000000000000000 : ℝ)*base80 + (1577798768573/1597500000000000000000000000 : ℝ)*base81 + (13590799/5000000000000000000000 : ℝ)*base90 + (13590799/5000000000000000000000 : ℝ)*base92 + (13590799/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1556_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (317/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11037/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7763/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1556_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1556_s4_0 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1804889901/10000000000 : ℝ)*x 0 + (5427771989/10000000000 : ℝ)*x 1 + (2609690461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1804889901/10000000000 : ℝ)^4609 ≤ (2213590674151/20000000000000 : ℝ)^3585 := by
    have hnat : (1804889901 : ℕ)^4609*20000000000000^3585 ≤ 2213590674151^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804889901 10000000000 2213590674151 20000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427771989/10000000000 : ℝ)^4609 ≤ (142452595231/312500000000 : ℝ)^3585 := by
    have hnat : (5427771989 : ℕ)^4609*312500000000^3585 ≤ 142452595231^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427771989 10000000000 142452595231 312500000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609690461/5000000000 : ℝ)^4609 ≤ (21673608068141/50000000000000 : ℝ)^3585 := by
    have hnat : (2609690461 : ℕ)^4609*50000000000000^3585 ≤ 21673608068141^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609690461 5000000000 21673608068141 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1804889901/10000000000 : ℝ), (5427771989/10000000000 : ℝ), (2609690461/5000000000 : ℝ)] ![(2213590674151/20000000000000 : ℝ), (142452595231/312500000000 : ℝ), (21673608068141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1804889901/10000000000 : ℝ)|^4609 ≤ (2213590674151/20000000000000 : ℝ)^3585
        have hw : |(-1804889901/10000000000 : ℝ)|=(1804889901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427771989/10000000000 : ℝ)|^4609 ≤ (142452595231/312500000000 : ℝ)^3585
        have hw : |(5427771989/10000000000 : ℝ)|=(5427771989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609690461/5000000000 : ℝ)|^4609 ≤ (21673608068141/50000000000000 : ℝ)^3585
        have hw : |(2609690461/5000000000 : ℝ)|=(2609690461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s4_1 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349095103/10000000000 : ℝ)*x 0 + (-955765733/5000000000 : ℝ)*x 1 + (5219380959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349095103/10000000000 : ℝ)^4609 ≤ (44737095044721/100000000000000 : ℝ)^3585 := by
    have hnat : (5349095103 : ℕ)^4609*100000000000000^3585 ≤ 44737095044721^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349095103 10000000000 44737095044721 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955765733/5000000000 : ℝ)^4609 ≤ (11915688405973/100000000000000 : ℝ)^3585 := by
    have hnat : (955765733 : ℕ)^4609*100000000000000^3585 ≤ 11915688405973^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955765733 5000000000 11915688405973 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219380959/10000000000 : ℝ)^4609 ≤ (43347216531341/100000000000000 : ℝ)^3585 := by
    have hnat : (5219380959 : ℕ)^4609*100000000000000^3585 ≤ 43347216531341^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219380959 10000000000 43347216531341 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349095103/10000000000 : ℝ), (-955765733/5000000000 : ℝ), (5219380959/10000000000 : ℝ)] ![(44737095044721/100000000000000 : ℝ), (11915688405973/100000000000000 : ℝ), (43347216531341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349095103/10000000000 : ℝ)|^4609 ≤ (44737095044721/100000000000000 : ℝ)^3585
        have hw : |(5349095103/10000000000 : ℝ)|=(5349095103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-955765733/5000000000 : ℝ)|^4609 ≤ (11915688405973/100000000000000 : ℝ)^3585
        have hw : |(-955765733/5000000000 : ℝ)|=(955765733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219380959/10000000000 : ℝ)|^4609 ≤ (43347216531341/100000000000000 : ℝ)^3585
        have hw : |(5219380959/10000000000 : ℝ)|=(5219380959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s4_2 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069819033/2000000000 : ℝ)*x 0 + (5219380903/10000000000 : ℝ)*x 1 + (-1911531459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069819033/2000000000 : ℝ)^4609 ≤ (44737095711369/100000000000000 : ℝ)^3585 := by
    have hnat : (1069819033 : ℕ)^4609*100000000000000^3585 ≤ 44737095711369^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069819033 2000000000 44737095711369 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219380903/10000000000 : ℝ)^4609 ≤ (21673607966707/50000000000000 : ℝ)^3585 := by
    have hnat : (5219380903 : ℕ)^4609*50000000000000^3585 ≤ 21673607966707^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219380903 10000000000 21673607966707 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1911531459/10000000000 : ℝ)^4609 ≤ (5957844174937/50000000000000 : ℝ)^3585 := by
    have hnat : (1911531459 : ℕ)^4609*50000000000000^3585 ≤ 5957844174937^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911531459 10000000000 5957844174937 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069819033/2000000000 : ℝ), (5219380903/10000000000 : ℝ), (-1911531459/10000000000 : ℝ)] ![(44737095711369/100000000000000 : ℝ), (21673607966707/50000000000000 : ℝ), (5957844174937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069819033/2000000000 : ℝ)|^4609 ≤ (44737095711369/100000000000000 : ℝ)^3585
        have hw : |(1069819033/2000000000 : ℝ)|=(1069819033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219380903/10000000000 : ℝ)|^4609 ≤ (21673607966707/50000000000000 : ℝ)^3585
        have hw : |(5219380903/10000000000 : ℝ)|=(5219380903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1911531459/10000000000 : ℝ)|^4609 ≤ (5957844174937/50000000000000 : ℝ)^3585
        have hw : |(-1911531459/10000000000 : ℝ)|=(1911531459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s4_3 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849938677/2000000000 : ℝ)*x 0 + (501474533/1250000000 : ℝ)*x 1 + (4499028229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849938677/2000000000 : ℝ)^4609 ≤ (33281559790551/100000000000000 : ℝ)^3585 := by
    have hnat : (849938677 : ℕ)^4609*100000000000000^3585 ≤ 33281559790551^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849938677 2000000000 33281559790551 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501474533/1250000000 : ℝ)^4609 ≤ (30905710404223/100000000000000 : ℝ)^3585 := by
    have hnat : (501474533 : ℕ)^4609*100000000000000^3585 ≤ 30905710404223^3585*1250000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501474533 1250000000 30905710404223 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499028229/10000000000 : ℝ)^4609 ≤ (1432509191513/4000000000000 : ℝ)^3585 := by
    have hnat : (4499028229 : ℕ)^4609*4000000000000^3585 ≤ 1432509191513^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499028229 10000000000 1432509191513 4000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849938677/2000000000 : ℝ), (501474533/1250000000 : ℝ), (4499028229/10000000000 : ℝ)] ![(33281559790551/100000000000000 : ℝ), (30905710404223/100000000000000 : ℝ), (1432509191513/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849938677/2000000000 : ℝ)|^4609 ≤ (33281559790551/100000000000000 : ℝ)^3585
        have hw : |(849938677/2000000000 : ℝ)|=(849938677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501474533/1250000000 : ℝ)|^4609 ≤ (30905710404223/100000000000000 : ℝ)^3585
        have hw : |(501474533/1250000000 : ℝ)|=(501474533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499028229/10000000000 : ℝ)|^4609 ≤ (1432509191513/4000000000000 : ℝ)^3585
        have hw : |(4499028229/10000000000 : ℝ)|=(4499028229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s4_4 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1804917277/10000000000 : ℝ)*x 0 + (5220465257/10000000000 : ℝ)*x 1 + (271333983/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1804917277/10000000000 : ℝ)^4609 ≤ (5534084598707/50000000000000 : ℝ)^3585 := by
    have hnat : (1804917277 : ℕ)^4609*50000000000000^3585 ≤ 5534084598707^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804917277 10000000000 5534084598707 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220465257/10000000000 : ℝ)^4609 ≤ (433587942051/1000000000000 : ℝ)^3585 := by
    have hnat : (5220465257 : ℕ)^4609*1000000000000^3585 ≤ 433587942051^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220465257 10000000000 433587942051 1000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271333983/500000000 : ℝ)^4609 ≤ (45573036578367/100000000000000 : ℝ)^3585 := by
    have hnat : (271333983 : ℕ)^4609*100000000000000^3585 ≤ 45573036578367^3585*500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271333983 500000000 45573036578367 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1804917277/10000000000 : ℝ), (5220465257/10000000000 : ℝ), (271333983/500000000 : ℝ)] ![(5534084598707/50000000000000 : ℝ), (433587942051/1000000000000 : ℝ), (45573036578367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1804917277/10000000000 : ℝ)|^4609 ≤ (5534084598707/50000000000000 : ℝ)^3585
        have hw : |(-1804917277/10000000000 : ℝ)|=(1804917277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220465257/10000000000 : ℝ)|^4609 ≤ (433587942051/1000000000000 : ℝ)^3585
        have hw : |(5220465257/10000000000 : ℝ)|=(5220465257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271333983/500000000 : ℝ)|^4609 ≤ (45573036578367/100000000000000 : ℝ)^3585
        have hw : |(271333983/500000000 : ℝ)|=(271333983/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s4_5 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323513901/2500000000 : ℝ)*x 0 + (-85211639/500000000 : ℝ)*x 1 + (1356669933/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323513901/2500000000 : ℝ)^4609 ≤ (44146160695341/100000000000000 : ℝ)^3585 := by
    have hnat : (1323513901 : ℕ)^4609*100000000000000^3585 ≤ 44146160695341^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323513901 2500000000 44146160695341 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85211639/500000000 : ℝ)^4609 ≤ (10280801930557/100000000000000 : ℝ)^3585 := by
    have hnat : (85211639 : ℕ)^4609*100000000000000^3585 ≤ 10280801930557^3585*500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85211639 500000000 10280801930557 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356669933/2500000000 : ℝ)^4609 ≤ (4557303735573/10000000000000 : ℝ)^3585 := by
    have hnat : (1356669933 : ℕ)^4609*10000000000000^3585 ≤ 4557303735573^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356669933 2500000000 4557303735573 10000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323513901/2500000000 : ℝ), (-85211639/500000000 : ℝ), (1356669933/2500000000 : ℝ)] ![(44146160695341/100000000000000 : ℝ), (10280801930557/100000000000000 : ℝ), (4557303735573/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323513901/2500000000 : ℝ)|^4609 ≤ (44146160695341/100000000000000 : ℝ)^3585
        have hw : |(1323513901/2500000000 : ℝ)|=(1323513901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85211639/500000000 : ℝ)|^4609 ≤ (10280801930557/100000000000000 : ℝ)^3585
        have hw : |(-85211639/500000000 : ℝ)|=(85211639/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356669933/2500000000 : ℝ)|^4609 ≤ (4557303735573/10000000000000 : ℝ)^3585
        have hw : |(1356669933/2500000000 : ℝ)|=(1356669933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s4_6 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647027813/5000000000 : ℝ)*x 0 + (5426679773/10000000000 : ℝ)*x 1 + (-1704232693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647027813/5000000000 : ℝ)^4609 ≤ (11036540232799/25000000000000 : ℝ)^3585 := by
    have hnat : (2647027813 : ℕ)^4609*25000000000000^3585 ≤ 11036540232799^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647027813 5000000000 11036540232799 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426679773/10000000000 : ℝ)^4609 ≤ (9114607559679/20000000000000 : ℝ)^3585 := by
    have hnat : (5426679773 : ℕ)^4609*20000000000000^3585 ≤ 9114607559679^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426679773 10000000000 9114607559679 20000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1704232693/10000000000 : ℝ)^4609 ≤ (10280801255819/100000000000000 : ℝ)^3585 := by
    have hnat : (1704232693 : ℕ)^4609*100000000000000^3585 ≤ 10280801255819^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704232693 10000000000 10280801255819 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647027813/5000000000 : ℝ), (5426679773/10000000000 : ℝ), (-1704232693/10000000000 : ℝ)] ![(11036540232799/25000000000000 : ℝ), (9114607559679/20000000000000 : ℝ), (10280801255819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647027813/5000000000 : ℝ)|^4609 ≤ (11036540232799/25000000000000 : ℝ)^3585
        have hw : |(2647027813/5000000000 : ℝ)|=(2647027813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426679773/10000000000 : ℝ)|^4609 ≤ (9114607559679/20000000000000 : ℝ)^3585
        have hw : |(5426679773/10000000000 : ℝ)|=(5426679773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1704232693/10000000000 : ℝ)|^4609 ≤ (10280801255819/100000000000000 : ℝ)^3585
        have hw : |(-1704232693/10000000000 : ℝ)|=(1704232693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s4_7 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2124878721/5000000000 : ℝ)*x 0 + (4496493093/10000000000 : ℝ)*x 1 + (4014350211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124878721/5000000000 : ℝ)^4609 ≤ (16641102374067/50000000000000 : ℝ)^3585 := by
    have hnat : (2124878721 : ℕ)^4609*50000000000000^3585 ≤ 16641102374067^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124878721 5000000000 16641102374067 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496493093/10000000000 : ℝ)^4609 ≤ (35786787841153/100000000000000 : ℝ)^3585 := by
    have hnat : (4496493093 : ℕ)^4609*100000000000000^3585 ≤ 35786787841153^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496493093 10000000000 35786787841153 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4014350211/10000000000 : ℝ)^4609 ≤ (1237240295579/4000000000000 : ℝ)^3585 := by
    have hnat : (4014350211 : ℕ)^4609*4000000000000^3585 ≤ 1237240295579^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014350211 10000000000 1237240295579 4000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2124878721/5000000000 : ℝ), (4496493093/10000000000 : ℝ), (4014350211/10000000000 : ℝ)] ![(16641102374067/50000000000000 : ℝ), (35786787841153/100000000000000 : ℝ), (1237240295579/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2124878721/5000000000 : ℝ)|^4609 ≤ (16641102374067/50000000000000 : ℝ)^3585
        have hw : |(2124878721/5000000000 : ℝ)|=(2124878721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496493093/10000000000 : ℝ)|^4609 ≤ (35786787841153/100000000000000 : ℝ)^3585
        have hw : |(4496493093/10000000000 : ℝ)|=(4496493093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4014350211/10000000000 : ℝ)|^4609 ≤ (1237240295579/4000000000000 : ℝ)^3585
        have hw : |(4014350211/10000000000 : ℝ)|=(4014350211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1556_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7763/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11037/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11071/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7763/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11037/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7763/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11037/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7763/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11037/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7763/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11037/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7763/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11037/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7763/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11037/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11037/100000 : ℝ) ^ (4607/1024 : ℝ) ≤ (4940426098318919/100000000000000000000 : ℝ) := by
    have hpowers : (11037/100000 : ℝ)^4607 ≤ (4940426098318919/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11037 : ℕ)^4607*100000000000000000000^1024 ≤ 4940426098318919^1024*100000^4607 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11037 100000 4940426098318919 100000000000000000000 4607 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11037/100000 : ℝ)) (X := (4940426098318919/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7763/50000 : ℝ) ^ (4607/1024 : ℝ) ≤ (5734533679956253/25000000000000000000 : ℝ) := by
    have hpowers : (7763/50000 : ℝ)^4607 ≤ (5734533679956253/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7763 : ℕ)^4607*25000000000000000000^1024 ≤ 5734533679956253^1024*50000^4607 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7763 50000 5734533679956253 25000000000000000000 4607 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7763/50000 : ℝ)) (X := (5734533679956253/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004940426098318919/50000000000000000000 : ℝ) ≤ (2000043922743247/2000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (50004940426098318919/50000000000000000000 : ℝ)^1024 ≤ (2000043922743247/2000000000000000 : ℝ)^4607 := by
      have hnat : (50004940426098318919 : ℕ)^1024*2000000000000000^4607 ≤ 2000043922743247^4607*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004940426098318919 50000000000000000000 2000043922743247 2000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000043922743247/2000000000000000 : ℝ)) (X := (50004940426098318919/50000000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027878560818143931/100000000000000000000 : ℝ) ≤ (10000619590882167/10000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (100027878560818143931/100000000000000000000 : ℝ)^1024 ≤ (10000619590882167/10000000000000000 : ℝ)^4607 := by
      have hnat : (100027878560818143931 : ℕ)^1024*10000000000000000^4607 ≤ 10000619590882167^4607*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027878560818143931 100000000000000000000 10000619590882167 10000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000619590882167/10000000000000000 : ℝ)) (X := (100027878560818143931/100000000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505734533679956253/12500000000000000000 : ℝ) ≤ (10001019568048099/10000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (12505734533679956253/12500000000000000000 : ℝ)^1024 ≤ (10001019568048099/10000000000000000 : ℝ)^4607 := by
      have hnat : (12505734533679956253 : ℕ)^1024*10000000000000000^4607 ≤ 10001019568048099^4607*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505734533679956253 12500000000000000000 10001019568048099 10000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001019568048099/10000000000000000 : ℝ)) (X := (12505734533679956253/12500000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4940426098318919/100000000000000000000 : ℝ) ≤ ((44882156750011395947/44890000000000000000 : ℝ)+2*(99994291483/112225000000000 : ℝ)*(11037/100000 : ℝ))^(4607/1024 : ℝ) := by
    rw [show (44882156750011395947/44890000000000000000 : ℝ)+2*(99994291483/112225000000000 : ℝ)*(11037/100000 : ℝ)=(2000043922743247/2000000000000000 : ℝ) by norm_num, show 1+2*(4940426098318919/100000000000000000000 : ℝ)=(50004940426098318919/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5734533679956253/25000000000000000000 : ℝ)+(4940426098318919/100000000000000000000 : ℝ) ≤ ((44882156750011395947/44890000000000000000 : ℝ)+(99994291483/112225000000000 : ℝ)*((7763/50000 : ℝ)+(11037/100000 : ℝ)))^(4607/1024 : ℝ) := by
    rw [show (44882156750011395947/44890000000000000000 : ℝ)+(99994291483/112225000000000 : ℝ)*((7763/50000 : ℝ)+(11037/100000 : ℝ))=(10000619590882167/10000000000000000 : ℝ) by norm_num, show 1+(5734533679956253/25000000000000000000 : ℝ)+(4940426098318919/100000000000000000000 : ℝ)=(100027878560818143931/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5734533679956253/25000000000000000000 : ℝ) ≤ ((44882156750011395947/44890000000000000000 : ℝ)+2*(99994291483/112225000000000 : ℝ)*(7763/50000 : ℝ))^(4607/1024 : ℝ) := by
    rw [show (44882156750011395947/44890000000000000000 : ℝ)+2*(99994291483/112225000000000 : ℝ)*(7763/50000 : ℝ)=(10001019568048099/10000000000000000 : ℝ) by norm_num, show 1+2*(5734533679956253/25000000000000000000 : ℝ)=(12505734533679956253/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44882156750011395947/44890000000000000000 : ℝ)*(X 1 0+X 2 0)+(99994291483/112225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (11037/100000 : ℝ)) (hi := (7763/50000 : ℝ)) (c := (44882156750011395947/44890000000000000000 : ℝ)) (alpha := (99994291483/112225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44882156750011395947/44890000000000000000 : ℝ)*(X 0 1+X 2 1)+(99994291483/112225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (11037/100000 : ℝ)) (hi := (7763/50000 : ℝ)) (c := (44882156750011395947/44890000000000000000 : ℝ)) (alpha := (99994291483/112225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44882156750011395947/44890000000000000000 : ℝ)*(X 0 2+X 1 2)+(99994291483/112225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (11037/100000 : ℝ)) (hi := (7763/50000 : ℝ)) (c := (44882156750011395947/44890000000000000000 : ℝ)) (alpha := (99994291483/112225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1804889901/10000000000 : ℝ)*X 0 0+(5427771989/10000000000 : ℝ)*X 0 1+(2609690461/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349095103/10000000000 : ℝ)*X 1 0+(-955765733/5000000000 : ℝ)*X 1 1+(5219380959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069819033/2000000000 : ℝ)*X 2 0+(5219380903/10000000000 : ℝ)*X 2 1+(-1911531459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((849938677/2000000000 : ℝ)*X 0 0+(501474533/1250000000 : ℝ)*X 0 1+(4499028229/10000000000 : ℝ)*X 0 2+(849938677/2000000000 : ℝ)*X 1 0+(501474533/1250000000 : ℝ)*X 1 1+(4499028229/10000000000 : ℝ)*X 1 2+(849938677/2000000000 : ℝ)*X 2 0+(501474533/1250000000 : ℝ)*X 2 1+(4499028229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1804917277/10000000000 : ℝ)*X 0 0+(5220465257/10000000000 : ℝ)*X 0 1+(271333983/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323513901/2500000000 : ℝ)*X 1 0+(-85211639/500000000 : ℝ)*X 1 1+(1356669933/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647027813/5000000000 : ℝ)*X 2 0+(5426679773/10000000000 : ℝ)*X 2 1+(-1704232693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2124878721/5000000000 : ℝ)*X 0 0+(4496493093/10000000000 : ℝ)*X 0 1+(4014350211/10000000000 : ℝ)*X 0 2+(2124878721/5000000000 : ℝ)*X 1 0+(4496493093/10000000000 : ℝ)*X 1 1+(4014350211/10000000000 : ℝ)*X 1 2+(2124878721/5000000000 : ℝ)*X 2 0+(4496493093/10000000000 : ℝ)*X 2 1+(4014350211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (292099098361058394972085491/35070312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1431313091/100000000000000 : ℝ)*(base19) + (21230327/1562500000000 : ℝ)*(base23) + (68571579/100000000000000 : ℝ)*(lower2) + (217631277/100000000000000 : ℝ)*(upper3) + (70631199/50000000000000 : ℝ)*(upper5) + (107049196465059/3125000000000 : ℝ)*(major0) + (107049196465059/3125000000000 : ℝ)*(major1) + (107049196465059/3125000000000 : ℝ)*(major2) + (959738803474071/20000000000000 : ℝ)*(sp0) + (599839494043381/12500000000000 : ℝ)*(sp1) + (4798716024919211/100000000000000 : ℝ)*(sp2) + (1026209986181533/50000000000000 : ℝ)*(sp3) + (2920786223/12500000000000 : ℝ)*(sp4) + (1094010869/10000000000000 : ℝ)*(sp7) + (513107728117939/25000000000000 : ℝ)*(f.failure) + (4798717383660139/100000000000000 : ℝ)*(f.sum) + (86477419467699/22445000000000000000000000000 : ℝ)*base66 + (134127567431265377/140281250000000000000000000000000 : ℝ)*base68 + (451696300039171627/140281250000000000000000000000000 : ℝ)*base70 + (610720651299171627/140281250000000000000000000000000 : ℝ)*base72 + (51229633163977/11222500000000000000000000000 : ℝ)*base74 + (1250892368410984127/140281250000000000000000000000000 : ℝ)*base76 + (1348937945734140377/140281250000000000000000000000000 : ℝ)*base78 + (1163400129885952877/140281250000000000000000000000000 : ℝ)*base80 + (61946347230859/22445000000000000000000000000 : ℝ)*base82 + (36642591/2500000000000000000000 : ℝ)*base89 + (36642591/2500000000000000000000 : ℝ)*base91 + (36642591/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74576193275808388955283/11222500000000000000000000000 : ℝ) := by norm_num
    linear_combination (792333779/100000000000000 : ℝ)*(base19) + (496100399/50000000000000 : ℝ)*(base23) + (17411723/12500000000000 : ℝ)*(upper3) + (1380533/2000000000000 : ℝ)*(lower4) + (14925643/12500000000000 : ℝ)*(upper5) + (865424293940849/25000000000000 : ℝ)*(major0) + (865424293940849/25000000000000 : ℝ)*(major1) + (865424293940849/25000000000000 : ℝ)*(major2) + (12444884807/100000000000000 : ℝ)*(sp1) + (4297436989/25000000000000 : ℝ)*(sp2) + (18942657066157/390625000000 : ℝ)*(sp4) + (2424653485858803/50000000000000 : ℝ)*(sp5) + (2424651013493719/50000000000000 : ℝ)*(sp6) + (1037036960541317/50000000000000 : ℝ)*(sp7) + (1037036960541317/50000000000000 : ℝ)*(f.failure) + (18942657066157/390625000000 : ℝ)*(f.sum) + (19787272661877/5611250000000000000000000000 : ℝ)*base66 + (6564663766554639003/1122250000000000000000000000000000 : ℝ)*base67 + (674367423928360997/1122250000000000000000000000000000 : ℝ)*base70 + (6363990739136110997/1122250000000000000000000000000000 : ℝ)*base72 + (21275786515543/5611250000000000000000000000 : ℝ)*base73 + (4995579859105389003/1122250000000000000000000000000000 : ℝ)*base75 + (6080757590642139003/1122250000000000000000000000000000 : ℝ)*base77 + (1945912933825860997/1122250000000000000000000000000000 : ℝ)*base80 + (3090461806487/5611250000000000000000000000 : ℝ)*base82 + (16865273/5000000000000000000000 : ℝ)*base89 + (16865273/5000000000000000000000 : ℝ)*base91 + (16865273/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1556_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7763/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11037/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1556_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1556_s5_0 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1804918313/10000000000 : ℝ)*x 0 + (5427584219/10000000000 : ℝ)*x 1 + (5219549823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1804918313/10000000000 : ℝ)^4609 ≤ (11068177365039/100000000000000 : ℝ)^3585 := by
    have hnat : (1804918313 : ℕ)^4609*100000000000000^3585 ≤ 11068177365039^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804918313 10000000000 11068177365039 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427584219/10000000000 : ℝ)^4609 ≤ (2848925191853/6250000000000 : ℝ)^3585 := by
    have hnat : (5427584219 : ℕ)^4609*6250000000000^3585 ≤ 2848925191853^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427584219 10000000000 2848925191853 6250000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219549823/10000000000 : ℝ)^4609 ≤ (43349019544289/100000000000000 : ℝ)^3585 := by
    have hnat : (5219549823 : ℕ)^4609*100000000000000^3585 ≤ 43349019544289^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219549823 10000000000 43349019544289 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1804918313/10000000000 : ℝ), (5427584219/10000000000 : ℝ), (5219549823/10000000000 : ℝ)] ![(11068177365039/100000000000000 : ℝ), (2848925191853/6250000000000 : ℝ), (43349019544289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1804918313/10000000000 : ℝ)|^4609 ≤ (11068177365039/100000000000000 : ℝ)^3585
        have hw : |(-1804918313/10000000000 : ℝ)|=(1804918313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427584219/10000000000 : ℝ)|^4609 ≤ (2848925191853/6250000000000 : ℝ)^3585
        have hw : |(5427584219/10000000000 : ℝ)|=(5427584219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219549823/10000000000 : ℝ)|^4609 ≤ (43349019544289/100000000000000 : ℝ)^3585
        have hw : |(5219549823/10000000000 : ℝ)|=(5219549823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s5_1 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349045389/10000000000 : ℝ)*x 0 + (-382274637/2000000000 : ℝ)*x 1 + (5219549823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349045389/10000000000 : ℝ)^4609 ≤ (44736560501113/100000000000000 : ℝ)^3585 := by
    have hnat : (5349045389 : ℕ)^4609*100000000000000^3585 ≤ 44736560501113^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349045389 10000000000 44736560501113 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (382274637/2000000000 : ℝ)^4609 ≤ (11914419939817/100000000000000 : ℝ)^3585 := by
    have hnat : (382274637 : ℕ)^4609*100000000000000^3585 ≤ 11914419939817^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382274637 2000000000 11914419939817 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219549823/10000000000 : ℝ)^4609 ≤ (43349019544289/100000000000000 : ℝ)^3585 := by
    have hnat : (5219549823 : ℕ)^4609*100000000000000^3585 ≤ 43349019544289^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219549823 10000000000 43349019544289 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349045389/10000000000 : ℝ), (-382274637/2000000000 : ℝ), (5219549823/10000000000 : ℝ)] ![(44736560501113/100000000000000 : ℝ), (11914419939817/100000000000000 : ℝ), (43349019544289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349045389/10000000000 : ℝ)|^4609 ≤ (44736560501113/100000000000000 : ℝ)^3585
        have hw : |(5349045389/10000000000 : ℝ)|=(5349045389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-382274637/2000000000 : ℝ)|^4609 ≤ (11914419939817/100000000000000 : ℝ)^3585
        have hw : |(-382274637/2000000000 : ℝ)|=(382274637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219549823/10000000000 : ℝ)|^4609 ≤ (43349019544289/100000000000000 : ℝ)^3585
        have hw : |(5219549823/10000000000 : ℝ)|=(5219549823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s5_2 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349045389/10000000000 : ℝ)*x 0 + (5219549823/10000000000 : ℝ)*x 1 + (-14932603/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349045389/10000000000 : ℝ)^4609 ≤ (44736560501113/100000000000000 : ℝ)^3585 := by
    have hnat : (5349045389 : ℕ)^4609*100000000000000^3585 ≤ 44736560501113^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349045389 10000000000 44736560501113 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219549823/10000000000 : ℝ)^4609 ≤ (43349019544289/100000000000000 : ℝ)^3585 := by
    have hnat : (5219549823 : ℕ)^4609*100000000000000^3585 ≤ 43349019544289^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219549823 10000000000 43349019544289 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14932603/78125000 : ℝ)^4609 ≤ (11914419931803/100000000000000 : ℝ)^3585 := by
    have hnat : (14932603 : ℕ)^4609*100000000000000^3585 ≤ 11914419931803^3585*78125000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14932603 78125000 11914419931803 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349045389/10000000000 : ℝ), (5219549823/10000000000 : ℝ), (-14932603/78125000 : ℝ)] ![(44736560501113/100000000000000 : ℝ), (43349019544289/100000000000000 : ℝ), (11914419931803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349045389/10000000000 : ℝ)|^4609 ≤ (44736560501113/100000000000000 : ℝ)^3585
        have hw : |(5349045389/10000000000 : ℝ)|=(5349045389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219549823/10000000000 : ℝ)|^4609 ≤ (43349019544289/100000000000000 : ℝ)^3585
        have hw : |(5219549823/10000000000 : ℝ)|=(5219549823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14932603/78125000 : ℝ)|^4609 ≤ (11914419931803/100000000000000 : ℝ)^3585
        have hw : |(-14932603/78125000 : ℝ)|=(14932603/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s5_3 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249710879/10000000000 : ℝ)*x 0 + (401221131/1000000000 : ℝ)*x 1 + (4498609329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249710879/10000000000 : ℝ)^4609 ≤ (16640867964263/50000000000000 : ℝ)^3585 := by
    have hnat : (4249710879 : ℕ)^4609*50000000000000^3585 ≤ 16640867964263^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249710879 10000000000 16640867964263 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401221131/1000000000 : ℝ)^4609 ≤ (30909821144693/100000000000000 : ℝ)^3585 := by
    have hnat : (401221131 : ℕ)^4609*100000000000000^3585 ≤ 30909821144693^3585*1000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401221131 1000000000 30909821144693 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498609329/10000000000 : ℝ)^4609 ≤ (35808442912619/100000000000000 : ℝ)^3585 := by
    have hnat : (4498609329 : ℕ)^4609*100000000000000^3585 ≤ 35808442912619^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498609329 10000000000 35808442912619 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249710879/10000000000 : ℝ), (401221131/1000000000 : ℝ), (4498609329/10000000000 : ℝ)] ![(16640867964263/50000000000000 : ℝ), (30909821144693/100000000000000 : ℝ), (35808442912619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249710879/10000000000 : ℝ)|^4609 ≤ (16640867964263/50000000000000 : ℝ)^3585
        have hw : |(4249710879/10000000000 : ℝ)|=(4249710879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401221131/1000000000 : ℝ)|^4609 ≤ (30909821144693/100000000000000 : ℝ)^3585
        have hw : |(401221131/1000000000 : ℝ)|=(401221131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498609329/10000000000 : ℝ)|^4609 ≤ (35808442912619/100000000000000 : ℝ)^3585
        have hw : |(4498609329/10000000000 : ℝ)|=(4498609329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s5_4 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-72197829/400000000 : ℝ)*x 0 + (5220630377/10000000000 : ℝ)*x 1 + (5426495583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72197829/400000000 : ℝ)^4609 ≤ (11068393476487/100000000000000 : ℝ)^3585 := by
    have hnat : (72197829 : ℕ)^4609*100000000000000^3585 ≤ 11068393476487^3585*400000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72197829 400000000 11068393476487 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220630377/10000000000 : ℝ)^4609 ≤ (21680278673317/50000000000000 : ℝ)^3585 := by
    have hnat : (5220630377 : ℕ)^4609*50000000000000^3585 ≤ 21680278673317^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220630377 10000000000 21680278673317 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426495583/10000000000 : ℝ)^4609 ≤ (45571049162497/100000000000000 : ℝ)^3585 := by
    have hnat : (5426495583 : ℕ)^4609*100000000000000^3585 ≤ 45571049162497^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426495583 10000000000 45571049162497 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-72197829/400000000 : ℝ), (5220630377/10000000000 : ℝ), (5426495583/10000000000 : ℝ)] ![(11068393476487/100000000000000 : ℝ), (21680278673317/50000000000000 : ℝ), (45571049162497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-72197829/400000000 : ℝ)|^4609 ≤ (11068393476487/100000000000000 : ℝ)^3585
        have hw : |(-72197829/400000000 : ℝ)|=(72197829/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220630377/10000000000 : ℝ)|^4609 ≤ (21680278673317/50000000000000 : ℝ)^3585
        have hw : |(5220630377/10000000000 : ℝ)|=(5220630377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426495583/10000000000 : ℝ)|^4609 ≤ (45571049162497/100000000000000 : ℝ)^3585
        have hw : |(5426495583/10000000000 : ℝ)|=(5426495583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s5_5 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41360157/78125000 : ℝ)*x 0 + (-1704427599/10000000000 : ℝ)*x 1 + (2713247803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41360157/78125000 : ℝ)^4609 ≤ (44146637680031/100000000000000 : ℝ)^3585 := by
    have hnat : (41360157 : ℕ)^4609*100000000000000^3585 ≤ 44146637680031^3585*78125000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41360157 78125000 44146637680031 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1704427599/10000000000 : ℝ)^4609 ≤ (10282312894239/100000000000000 : ℝ)^3585 := by
    have hnat : (1704427599 : ℕ)^4609*100000000000000^3585 ≤ 10282312894239^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704427599 10000000000 10282312894239 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713247803/5000000000 : ℝ)^4609 ≤ (45571049410819/100000000000000 : ℝ)^3585 := by
    have hnat : (2713247803 : ℕ)^4609*100000000000000^3585 ≤ 45571049410819^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713247803 5000000000 45571049410819 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41360157/78125000 : ℝ), (-1704427599/10000000000 : ℝ), (2713247803/5000000000 : ℝ)] ![(44146637680031/100000000000000 : ℝ), (10282312894239/100000000000000 : ℝ), (45571049410819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41360157/78125000 : ℝ)|^4609 ≤ (44146637680031/100000000000000 : ℝ)^3585
        have hw : |(41360157/78125000 : ℝ)|=(41360157/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1704427599/10000000000 : ℝ)|^4609 ≤ (10282312894239/100000000000000 : ℝ)^3585
        have hw : |(-1704427599/10000000000 : ℝ)|=(1704427599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713247803/5000000000 : ℝ)|^4609 ≤ (45571049410819/100000000000000 : ℝ)^3585
        have hw : |(2713247803/5000000000 : ℝ)|=(2713247803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s5_6 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058820019/2000000000 : ℝ)*x 0 + (1356623929/2500000000 : ℝ)*x 1 + (-1704427447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058820019/2000000000 : ℝ)^4609 ≤ (4414663766931/10000000000000 : ℝ)^3585 := by
    have hnat : (1058820019 : ℕ)^4609*10000000000000^3585 ≤ 4414663766931^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058820019 2000000000 4414663766931 10000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356623929/2500000000 : ℝ)^4609 ≤ (9114210119689/20000000000000 : ℝ)^3585 := by
    have hnat : (1356623929 : ℕ)^4609*20000000000000^3585 ≤ 9114210119689^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356623929 2500000000 9114210119689 20000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1704427447/10000000000 : ℝ)^4609 ≤ (10282311715349/100000000000000 : ℝ)^3585 := by
    have hnat : (1704427447 : ℕ)^4609*100000000000000^3585 ≤ 10282311715349^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704427447 10000000000 10282311715349 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058820019/2000000000 : ℝ), (1356623929/2500000000 : ℝ), (-1704427447/10000000000 : ℝ)] ![(4414663766931/10000000000000 : ℝ), (9114210119689/20000000000000 : ℝ), (10282311715349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058820019/2000000000 : ℝ)|^4609 ≤ (4414663766931/10000000000000 : ℝ)^3585
        have hw : |(1058820019/2000000000 : ℝ)|=(1058820019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356623929/2500000000 : ℝ)|^4609 ≤ (9114210119689/20000000000000 : ℝ)^3585
        have hw : |(1356623929/2500000000 : ℝ)|=(1356623929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1704427447/10000000000 : ℝ)|^4609 ≤ (10282311715349/100000000000000 : ℝ)^3585
        have hw : |(-1704427447/10000000000 : ℝ)|=(1704427447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s5_7 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2124887347/5000000000 : ℝ)*x 0 + (4496083009/10000000000 : ℝ)*x 1 + (4014756253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124887347/5000000000 : ℝ)^4609 ≤ (8320594612571/25000000000000 : ℝ)^3585 := by
    have hnat : (2124887347 : ℕ)^4609*25000000000000^3585 ≤ 8320594612571^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124887347 5000000000 8320594612571 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496083009/10000000000 : ℝ)^4609 ≤ (35782591860237/100000000000000 : ℝ)^3585 := by
    have hnat : (4496083009 : ℕ)^4609*100000000000000^3585 ≤ 35782591860237^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496083009 10000000000 35782591860237 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4014756253/10000000000 : ℝ)^4609 ≤ (30935029681399/100000000000000 : ℝ)^3585 := by
    have hnat : (4014756253 : ℕ)^4609*100000000000000^3585 ≤ 30935029681399^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014756253 10000000000 30935029681399 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2124887347/5000000000 : ℝ), (4496083009/10000000000 : ℝ), (4014756253/10000000000 : ℝ)] ![(8320594612571/25000000000000 : ℝ), (35782591860237/100000000000000 : ℝ), (30935029681399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2124887347/5000000000 : ℝ)|^4609 ≤ (8320594612571/25000000000000 : ℝ)^3585
        have hw : |(2124887347/5000000000 : ℝ)|=(2124887347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496083009/10000000000 : ℝ)|^4609 ≤ (35782591860237/100000000000000 : ℝ)^3585
        have hw : |(4496083009/10000000000 : ℝ)|=(4496083009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4014756253/10000000000 : ℝ)|^4609 ≤ (30935029681399/100000000000000 : ℝ)^3585
        have hw : |(4014756253/10000000000 : ℝ)|=(4014756253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1556_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (443/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11071/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11071/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11071/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11071/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11071/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11071/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11071/100000 : ℝ) ^ (4607/1024 : ℝ) ≤ (2504633840279137/50000000000000000000 : ℝ) := by
    have hpowers : (11071/100000 : ℝ)^4607 ≤ (2504633840279137/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11071 : ℕ)^4607*50000000000000000000^1024 ≤ 2504633840279137^1024*100000^4607 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11071 100000 2504633840279137 50000000000000000000 4607 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11071/100000 : ℝ)) (X := (2504633840279137/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4607/1024 : ℝ) ≤ (11346612046059659/50000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4607 ≤ (11346612046059659/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4607*50000000000000000000^1024 ≤ 11346612046059659^1024*100000^4607 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 11346612046059659 50000000000000000000 4607 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (11346612046059659/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002504633840279137/25000000000000000000 : ℝ) ≤ (1250027834221181/1250000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (25002504633840279137/25000000000000000000 : ℝ)^1024 ≤ (1250027834221181/1250000000000000 : ℝ)^4607 := by
      have hnat : (25002504633840279137 : ℕ)^1024*1250000000000000^4607 ≤ 1250027834221181^4607*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002504633840279137 25000000000000000000 1250027834221181 1250000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250027834221181/1250000000000000 : ℝ)) (X := (25002504633840279137/25000000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503462811471584699/12500000000000000000 : ℝ) ≤ (2000123135646613/2000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (12503462811471584699/12500000000000000000 : ℝ)^1024 ≤ (2000123135646613/2000000000000000 : ℝ)^4607 := by
      have hnat : (12503462811471584699 : ℕ)^1024*2000000000000000^4607 ≤ 2000123135646613^4607*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503462811471584699 12500000000000000000 2000123135646613 2000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000123135646613/2000000000000000 : ℝ)) (X := (12503462811471584699/12500000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011346612046059659/25000000000000000000 : ℝ) ≤ (5000504341348341/5000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (25011346612046059659/25000000000000000000 : ℝ)^1024 ≤ (5000504341348341/5000000000000000 : ℝ)^4607 := by
      have hnat : (25011346612046059659 : ℕ)^1024*5000000000000000^4607 ≤ 5000504341348341^4607*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011346612046059659 25000000000000000000 5000504341348341 5000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000504341348341/5000000000000000 : ℝ)) (X := (25011346612046059659/25000000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2504633840279137/50000000000000000000 : ℝ) ≤ ((883445637357600273/883600000000000000 : ℝ)+2*(393004463617/441800000000000 : ℝ)*(11071/100000 : ℝ))^(4607/1024 : ℝ) := by
    rw [show (883445637357600273/883600000000000000 : ℝ)+2*(393004463617/441800000000000 : ℝ)*(11071/100000 : ℝ)=(1250027834221181/1250000000000000 : ℝ) by norm_num, show 1+2*(2504633840279137/50000000000000000000 : ℝ)=(25002504633840279137/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11346612046059659/50000000000000000000 : ℝ)+(2504633840279137/50000000000000000000 : ℝ) ≤ ((883445637357600273/883600000000000000 : ℝ)+(393004463617/441800000000000 : ℝ)*((15489/100000 : ℝ)+(11071/100000 : ℝ)))^(4607/1024 : ℝ) := by
    rw [show (883445637357600273/883600000000000000 : ℝ)+(393004463617/441800000000000 : ℝ)*((15489/100000 : ℝ)+(11071/100000 : ℝ))=(2000123135646613/2000000000000000 : ℝ) by norm_num, show 1+(11346612046059659/50000000000000000000 : ℝ)+(2504633840279137/50000000000000000000 : ℝ)=(12503462811471584699/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11346612046059659/50000000000000000000 : ℝ) ≤ ((883445637357600273/883600000000000000 : ℝ)+2*(393004463617/441800000000000 : ℝ)*(15489/100000 : ℝ))^(4607/1024 : ℝ) := by
    rw [show (883445637357600273/883600000000000000 : ℝ)+2*(393004463617/441800000000000 : ℝ)*(15489/100000 : ℝ)=(5000504341348341/5000000000000000 : ℝ) by norm_num, show 1+2*(11346612046059659/50000000000000000000 : ℝ)=(25011346612046059659/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (883445637357600273/883600000000000000 : ℝ)*(X 1 0+X 2 0)+(393004463617/441800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (11071/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (883445637357600273/883600000000000000 : ℝ)) (alpha := (393004463617/441800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (883445637357600273/883600000000000000 : ℝ)*(X 0 1+X 2 1)+(393004463617/441800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (11071/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (883445637357600273/883600000000000000 : ℝ)) (alpha := (393004463617/441800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (883445637357600273/883600000000000000 : ℝ)*(X 0 2+X 1 2)+(393004463617/441800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (11071/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (883445637357600273/883600000000000000 : ℝ)) (alpha := (393004463617/441800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1804918313/10000000000 : ℝ)*X 0 0+(5427584219/10000000000 : ℝ)*X 0 1+(5219549823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349045389/10000000000 : ℝ)*X 1 0+(-382274637/2000000000 : ℝ)*X 1 1+(5219549823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349045389/10000000000 : ℝ)*X 2 0+(5219549823/10000000000 : ℝ)*X 2 1+(-14932603/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4249710879/10000000000 : ℝ)*X 0 0+(401221131/1000000000 : ℝ)*X 0 1+(4498609329/10000000000 : ℝ)*X 0 2+(4249710879/10000000000 : ℝ)*X 1 0+(401221131/1000000000 : ℝ)*X 1 1+(4498609329/10000000000 : ℝ)*X 1 2+(4249710879/10000000000 : ℝ)*X 2 0+(401221131/1000000000 : ℝ)*X 2 1+(4498609329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-72197829/400000000 : ℝ)*X 0 0+(5220630377/10000000000 : ℝ)*X 0 1+(5426495583/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41360157/78125000 : ℝ)*X 1 0+(-1704427599/10000000000 : ℝ)*X 1 1+(2713247803/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058820019/2000000000 : ℝ)*X 2 0+(1356623929/2500000000 : ℝ)*X 2 1+(-1704427447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2124887347/5000000000 : ℝ)*X 0 0+(4496083009/10000000000 : ℝ)*X 0 1+(4014756253/10000000000 : ℝ)*X 0 2+(2124887347/5000000000 : ℝ)*X 1 0+(4496083009/10000000000 : ℝ)*X 1 1+(4014756253/10000000000 : ℝ)*X 1 2+(2124887347/5000000000 : ℝ)*X 2 0+(4496083009/10000000000 : ℝ)*X 2 1+(4014756253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (414477485722682336221749/94000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (188733529/25000000000000 : ℝ)*(base19) + (352508031/50000000000000 : ℝ)*(base23) + (13350697/50000000000000 : ℝ)*(lower2) + (109030633/100000000000000 : ℝ)*(upper3) + (73570781/100000000000000 : ℝ)*(upper5) + (343143120736137/10000000000000 : ℝ)*(major0) + (343143120736137/10000000000000 : ℝ)*(major1) + (343143120736137/10000000000000 : ℝ)*(major2) + (192276400568983/4000000000000 : ℝ)*(sp0) + (4806921429719083/100000000000000 : ℝ)*(sp1) + (300432592477321/6250000000000 : ℝ)*(sp2) + (1027967226906789/50000000000000 : ℝ)*(sp3) + (12170428623/100000000000000 : ℝ)*(sp4) + (2814639063/50000000000000 : ℝ)*(sp7) + (256992510386463/12500000000000 : ℝ)*(f.failure) + (2403461092326599/50000000000000 : ℝ)*(f.sum) + (439441943/75200000000000000000000 : ℝ)*base65 + (700373596611417/188000000000000000000000000000 : ℝ)*base68 + (419176801043417/188000000000000000000000000000 : ℝ)*base70 + (476019225015417/188000000000000000000000000000 : ℝ)*base72 + (45615056733/23500000000000000000000000 : ℝ)*base74 + (938545577543417/188000000000000000000000000000 : ℝ)*base76 + (1173209342988583/188000000000000000000000000000 : ℝ)*base77 + (2650357146572583/188000000000000000000000000000 : ℝ)*base79 + (73266018629/9400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3047547/1250000000000000000000 : ℝ)*base89 + (3047547/1250000000000000000000 : ℝ)*base91 + (3047547/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25058128847556314610338181/4418000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (375404367/50000000000000 : ℝ)*(base19) + (858416563/100000000000000 : ℝ)*(base23) + (621619/390625000000 : ℝ)*(lower1) + (11527329/50000000000000 : ℝ)*(upper2) + (97710287/50000000000000 : ℝ)*(upper3) + (57553183/50000000000000 : ℝ)*(upper5) + (346756279314999/10000000000000 : ℝ)*(major0) + (346756279314999/10000000000000 : ℝ)*(major1) + (346756279314999/10000000000000 : ℝ)*(major2) + (1252145747/20000000000000 : ℝ)*(sp2) + (485753709478949/10000000000000 : ℝ)*(sp4) + (4857536343980757/100000000000000 : ℝ)*(sp5) + (151797811738881/3125000000000 : ℝ)*(sp6) + (1298492689031/62500000000 : ℝ)*(sp7) + (1298492689031/62500000000 : ℝ)*(f.failure) + (485753709478949/10000000000000 : ℝ)*(f.sum) + (1860664767967/2209000000000000000000000000 : ℝ)*base66 + (59306055494519273/8836000000000000000000000000000 : ℝ)*base68 + (85503725969240727/8836000000000000000000000000000 : ℝ)*base69 + (18062178258031273/8836000000000000000000000000000 : ℝ)*base72 + (482766501963/220900000000000000000000000 : ℝ)*base74 + (114271439782951273/8836000000000000000000000000000 : ℝ)*base76 + (32456892453819273/8836000000000000000000000000000 : ℝ)*base78 + (91487285736588727/8836000000000000000000000000000 : ℝ)*base79 + (65405204153559/2209000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (32661/6250000000000000000 : ℝ)*base90 + (32661/6250000000000000000 : ℝ)*base92 + (32661/6250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1556_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1556_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1556_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (317/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1556_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1556_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1556_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (317/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1556_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
