-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1341_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:10.569458+00:00
-- url     : https://prove2.me/submissions/1811aa97-ad16-45f7-a28d-b7b6af59d80f

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
theorem support_rectangle_w1341_s6_0 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2044829231/10000000000 : ℝ)*x 0 + (1353193633/2500000000 : ℝ)*x 1 + (5244565523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2044829231/10000000000 : ℝ)^4301 ≤ (6226163526787/50000000000000 : ℝ)^3277 := by
    have hnat : (2044829231 : ℕ)^4301*50000000000000^3277 ≤ 6226163526787^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044829231 10000000000 6226163526787 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353193633/2500000000 : ℝ)^4301 ≤ (2234028740591/5000000000000 : ℝ)^3277 := by
    have hnat : (1353193633 : ℕ)^4301*5000000000000^3277 ≤ 2234028740591^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353193633 2500000000 2234028740591 5000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244565523/10000000000 : ℝ)^4301 ≤ (42867098124511/100000000000000 : ℝ)^3277 := by
    have hnat : (5244565523 : ℕ)^4301*100000000000000^3277 ≤ 42867098124511^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244565523 10000000000 42867098124511 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2044829231/10000000000 : ℝ), (1353193633/2500000000 : ℝ), (5244565523/10000000000 : ℝ)] ![(6226163526787/50000000000000 : ℝ), (2234028740591/5000000000000 : ℝ), (42867098124511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2044829231/10000000000 : ℝ)|^4301 ≤ (6226163526787/50000000000000 : ℝ)^3277
        have hw : |(-2044829231/10000000000 : ℝ)|=(2044829231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353193633/2500000000 : ℝ)|^4301 ≤ (2234028740591/5000000000000 : ℝ)^3277
        have hw : |(1353193633/2500000000 : ℝ)|=(1353193633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244565523/10000000000 : ℝ)|^4301 ≤ (42867098124511/100000000000000 : ℝ)^3277
        have hw : |(5244565523/10000000000 : ℝ)|=(5244565523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s6_1 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668627527/1250000000 : ℝ)*x 0 + (-532633491/2500000000 : ℝ)*x 1 + (5244565517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668627527/1250000000 : ℝ)^4301 ≤ (21995565184041/50000000000000 : ℝ)^3277 := by
    have hnat : (668627527 : ℕ)^4301*50000000000000^3277 ≤ 21995565184041^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668627527 1250000000 21995565184041 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532633491/2500000000 : ℝ)^4301 ≤ (6570885777841/50000000000000 : ℝ)^3277 := by
    have hnat : (532633491 : ℕ)^4301*50000000000000^3277 ≤ 6570885777841^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532633491 2500000000 6570885777841 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244565517/10000000000 : ℝ)^4301 ≤ (8573419612029/20000000000000 : ℝ)^3277 := by
    have hnat : (5244565517 : ℕ)^4301*20000000000000^3277 ≤ 8573419612029^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244565517 10000000000 8573419612029 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668627527/1250000000 : ℝ), (-532633491/2500000000 : ℝ), (5244565517/10000000000 : ℝ)] ![(21995565184041/50000000000000 : ℝ), (6570885777841/50000000000000 : ℝ), (8573419612029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668627527/1250000000 : ℝ)|^4301 ≤ (21995565184041/50000000000000 : ℝ)^3277
        have hw : |(668627527/1250000000 : ℝ)|=(668627527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532633491/2500000000 : ℝ)|^4301 ≤ (6570885777841/50000000000000 : ℝ)^3277
        have hw : |(-532633491/2500000000 : ℝ)|=(532633491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244565517/10000000000 : ℝ)|^4301 ≤ (8573419612029/20000000000000 : ℝ)^3277
        have hw : |(5244565517/10000000000 : ℝ)|=(5244565517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s6_2 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349020201/10000000000 : ℝ)*x 0 + (2622282761/5000000000 : ℝ)*x 1 + (-1065266989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349020201/10000000000 : ℝ)^4301 ≤ (43991130206171/100000000000000 : ℝ)^3277 := by
    have hnat : (5349020201 : ℕ)^4301*100000000000000^3277 ≤ 43991130206171^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349020201 10000000000 43991130206171 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622282761/5000000000 : ℝ)^4301 ≤ (42867098113783/100000000000000 : ℝ)^3277 := by
    have hnat : (2622282761 : ℕ)^4301*100000000000000^3277 ≤ 42867098113783^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622282761 5000000000 42867098113783 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065266989/5000000000 : ℝ)^4301 ≤ (13141771669023/100000000000000 : ℝ)^3277 := by
    have hnat : (1065266989 : ℕ)^4301*100000000000000^3277 ≤ 13141771669023^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065266989 5000000000 13141771669023 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349020201/10000000000 : ℝ), (2622282761/5000000000 : ℝ), (-1065266989/5000000000 : ℝ)] ![(43991130206171/100000000000000 : ℝ), (42867098113783/100000000000000 : ℝ), (13141771669023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349020201/10000000000 : ℝ)|^4301 ≤ (43991130206171/100000000000000 : ℝ)^3277
        have hw : |(5349020201/10000000000 : ℝ)|=(5349020201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622282761/5000000000 : ℝ)|^4301 ≤ (42867098113783/100000000000000 : ℝ)^3277
        have hw : |(2622282761/5000000000 : ℝ)|=(2622282761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065266989/5000000000 : ℝ)|^4301 ≤ (13141771669023/100000000000000 : ℝ)^3277
        have hw : |(-1065266989/5000000000 : ℝ)|=(1065266989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s6_3 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4326879171/10000000000 : ℝ)*x 0 + (1038533261/2500000000 : ℝ)*x 1 + (4506326493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326879171/10000000000 : ℝ)^4301 ≤ (16651613648409/50000000000000 : ℝ)^3277 := by
    have hnat : (4326879171 : ℕ)^4301*50000000000000^3277 ≤ 16651613648409^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326879171 10000000000 16651613648409 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038533261/2500000000 : ℝ)^4301 ≤ (315691438073/1000000000000 : ℝ)^3277 := by
    have hnat : (1038533261 : ℕ)^4301*1000000000000^3277 ≤ 315691438073^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038533261 2500000000 315691438073 1000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506326493/10000000000 : ℝ)^4301 ≤ (8781907221233/25000000000000 : ℝ)^3277 := by
    have hnat : (4506326493 : ℕ)^4301*25000000000000^3277 ≤ 8781907221233^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506326493 10000000000 8781907221233 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326879171/10000000000 : ℝ), (1038533261/2500000000 : ℝ), (4506326493/10000000000 : ℝ)] ![(16651613648409/50000000000000 : ℝ), (315691438073/1000000000000 : ℝ), (8781907221233/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326879171/10000000000 : ℝ)|^4301 ≤ (16651613648409/50000000000000 : ℝ)^3277
        have hw : |(4326879171/10000000000 : ℝ)|=(4326879171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1038533261/2500000000 : ℝ)|^4301 ≤ (315691438073/1000000000000 : ℝ)^3277
        have hw : |(1038533261/2500000000 : ℝ)|=(1038533261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506326493/10000000000 : ℝ)|^4301 ≤ (8781907221233/25000000000000 : ℝ)^3277
        have hw : |(4506326493/10000000000 : ℝ)|=(4506326493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s6_4 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-408968263/2000000000 : ℝ)*x 0 + (1049033571/2000000000 : ℝ)*x 1 + (676521147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408968263/2000000000 : ℝ)^4301 ≤ (2490484727177/20000000000000 : ℝ)^3277 := by
    have hnat : (408968263 : ℕ)^4301*20000000000000^3277 ≤ 2490484727177^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408968263 2000000000 2490484727177 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049033571/2000000000 : ℝ)^4301 ≤ (10718389972899/25000000000000 : ℝ)^3277 := by
    have hnat : (1049033571 : ℕ)^4301*25000000000000^3277 ≤ 10718389972899^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049033571 2000000000 10718389972899 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676521147/1250000000 : ℝ)^4301 ≤ (44674016454449/100000000000000 : ℝ)^3277 := by
    have hnat : (676521147 : ℕ)^4301*100000000000000^3277 ≤ 44674016454449^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676521147 1250000000 44674016454449 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408968263/2000000000 : ℝ), (1049033571/2000000000 : ℝ), (676521147/1250000000 : ℝ)] ![(2490484727177/20000000000000 : ℝ), (10718389972899/25000000000000 : ℝ), (44674016454449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408968263/2000000000 : ℝ)|^4301 ≤ (2490484727177/20000000000000 : ℝ)^3277
        have hw : |(-408968263/2000000000 : ℝ)|=(408968263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049033571/2000000000 : ℝ)|^4301 ≤ (10718389972899/25000000000000 : ℝ)^3277
        have hw : |(1049033571/2000000000 : ℝ)|=(1049033571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676521147/1250000000 : ℝ)|^4301 ≤ (44674016454449/100000000000000 : ℝ)^3277
        have hw : |(676521147/1250000000 : ℝ)|=(676521147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s6_5 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326424541/2500000000 : ℝ)*x 0 + (-1962930413/10000000000 : ℝ)*x 1 + (1082433849/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326424541/2500000000 : ℝ)^4301 ≤ (1360128230787/3125000000000 : ℝ)^3277 := by
    have hnat : (1326424541 : ℕ)^4301*3125000000000^3277 ≤ 1360128230787^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326424541 2500000000 1360128230787 3125000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1962930413/10000000000 : ℝ)^4301 ≤ (1475234924663/12500000000000 : ℝ)^3277 := by
    have hnat : (1962930413 : ℕ)^4301*12500000000000^3277 ≤ 1475234924663^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962930413 10000000000 1475234924663 12500000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082433849/2000000000 : ℝ)^4301 ≤ (22337008600987/50000000000000 : ℝ)^3277 := by
    have hnat : (1082433849 : ℕ)^4301*50000000000000^3277 ≤ 22337008600987^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082433849 2000000000 22337008600987 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326424541/2500000000 : ℝ), (-1962930413/10000000000 : ℝ), (1082433849/2000000000 : ℝ)] ![(1360128230787/3125000000000 : ℝ), (1475234924663/12500000000000 : ℝ), (22337008600987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326424541/2500000000 : ℝ)|^4301 ≤ (1360128230787/3125000000000 : ℝ)^3277
        have hw : |(1326424541/2500000000 : ℝ)|=(1326424541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1962930413/10000000000 : ℝ)|^4301 ≤ (1475234924663/12500000000000 : ℝ)^3277
        have hw : |(-1962930413/10000000000 : ℝ)|=(1962930413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082433849/2000000000 : ℝ)|^4301 ≤ (22337008600987/50000000000000 : ℝ)^3277
        have hw : |(1082433849/2000000000 : ℝ)|=(1082433849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s6_6 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326424547/2500000000 : ℝ)*x 0 + (2706084627/5000000000 : ℝ)*x 1 + (-1962930367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326424547/2500000000 : ℝ)^4301 ≤ (680064119431/1562500000000 : ℝ)^3277 := by
    have hnat : (1326424547 : ℕ)^4301*1562500000000^3277 ≤ 680064119431^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326424547 2500000000 680064119431 1562500000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706084627/5000000000 : ℝ)^4301 ≤ (44674017299477/100000000000000 : ℝ)^3277 := by
    have hnat : (2706084627 : ℕ)^4301*100000000000000^3277 ≤ 44674017299477^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706084627 5000000000 44674017299477 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1962930367/10000000000 : ℝ)^4301 ≤ (1475234879289/12500000000000 : ℝ)^3277 := by
    have hnat : (1962930367 : ℕ)^4301*12500000000000^3277 ≤ 1475234879289^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962930367 10000000000 1475234879289 12500000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326424547/2500000000 : ℝ), (2706084627/5000000000 : ℝ), (-1962930367/10000000000 : ℝ)] ![(680064119431/1562500000000 : ℝ), (44674017299477/100000000000000 : ℝ), (1475234879289/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326424547/2500000000 : ℝ)|^4301 ≤ (680064119431/1562500000000 : ℝ)^3277
        have hw : |(1326424547/2500000000 : ℝ)|=(1326424547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706084627/5000000000 : ℝ)|^4301 ≤ (44674017299477/100000000000000 : ℝ)^3277
        have hw : |(2706084627/5000000000 : ℝ)|=(2706084627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1962930367/10000000000 : ℝ)|^4301 ≤ (1475234879289/12500000000000 : ℝ)^3277
        have hw : |(-1962930367/10000000000 : ℝ)|=(1962930367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s6_7 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4326904763/10000000000 : ℝ)*x 0 + (180202617/400000000 : ℝ)*x 1 + (2077700277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326904763/10000000000 : ℝ)^4301 ≤ (33303485825769/100000000000000 : ℝ)^3277 := by
    have hnat : (4326904763 : ℕ)^4301*100000000000000^3277 ≤ 33303485825769^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326904763 10000000000 33303485825769 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180202617/400000000 : ℝ)^4301 ≤ (7022945485949/20000000000000 : ℝ)^3277 := by
    have hnat : (180202617 : ℕ)^4301*20000000000000^3277 ≤ 7022945485949^3277*400000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180202617 400000000 7022945485949 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077700277/5000000000 : ℝ)^4301 ≤ (6316357346097/20000000000000 : ℝ)^3277 := by
    have hnat : (2077700277 : ℕ)^4301*20000000000000^3277 ≤ 6316357346097^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077700277 5000000000 6316357346097 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326904763/10000000000 : ℝ), (180202617/400000000 : ℝ), (2077700277/5000000000 : ℝ)] ![(33303485825769/100000000000000 : ℝ), (7022945485949/20000000000000 : ℝ), (6316357346097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326904763/10000000000 : ℝ)|^4301 ≤ (33303485825769/100000000000000 : ℝ)^3277
        have hw : |(4326904763/10000000000 : ℝ)|=(4326904763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180202617/400000000 : ℝ)|^4301 ≤ (7022945485949/20000000000000 : ℝ)^3277
        have hw : |(180202617/400000000 : ℝ)|=(180202617/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2077700277/5000000000 : ℝ)|^4301 ≤ (6316357346097/20000000000000 : ℝ)^3277
        have hw : |(2077700277/5000000000 : ℝ)|=(2077700277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1341_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5573/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14707/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2943/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11139/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2943/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11139/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2943/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11139/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2943/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11139/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2943/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11139/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2943/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11139/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11139/100000 : ℝ) ^ (1075/256 : ℝ) ≤ (4971285580187649/50000000000000000000 : ℝ) := by
    have hpowers : (11139/100000 : ℝ)^1075 ≤ (4971285580187649/50000000000000000000 : ℝ)^256 := by
      have hnat : (11139 : ℕ)^1075*50000000000000000000^256 ≤ 4971285580187649^256*100000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11139 100000 4971285580187649 50000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11139/100000 : ℝ)) (X := (4971285580187649/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2943/20000 : ℝ) ^ (1075/256 : ℝ) ≤ (800171935005551/2500000000000000000 : ℝ) := by
    have hpowers : (2943/20000 : ℝ)^1075 ≤ (800171935005551/2500000000000000000 : ℝ)^256 := by
      have hnat : (2943 : ℕ)^1075*2500000000000000000^256 ≤ 800171935005551^256*20000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2943 20000 800171935005551 2500000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2943/20000 : ℝ)) (X := (800171935005551/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004971285580187649/25000000000000000000 : ℝ) ≤ (10000473507988279/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (25004971285580187649/25000000000000000000 : ℝ)^256 ≤ (10000473507988279/10000000000000000 : ℝ)^1075 := by
      have hnat : (25004971285580187649 : ℕ)^256*10000000000000000^1075 ≤ 10000473507988279^1075*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004971285580187649 25000000000000000000 10000473507988279 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000473507988279/10000000000000000 : ℝ)) (X := (25004971285580187649/25000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020974724280298669/50000000000000000000 : ℝ) ≤ (1000099882262071/1000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50020974724280298669/50000000000000000000 : ℝ)^256 ≤ (1000099882262071/1000000000000000 : ℝ)^1075 := by
      have hnat : (50020974724280298669 : ℕ)^256*1000000000000000^1075 ≤ 1000099882262071^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020974724280298669 50000000000000000000 1000099882262071 1000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000099882262071/1000000000000000 : ℝ)) (X := (50020974724280298669/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250800171935005551/1250000000000000000 : ℝ) ≤ (10001524137253141/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (1250800171935005551/1250000000000000000 : ℝ)^256 ≤ (10001524137253141/10000000000000000 : ℝ)^1075 := by
      have hnat : (1250800171935005551 : ℕ)^256*10000000000000000^1075 ≤ 10001524137253141^1075*1250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250800171935005551 1250000000000000000 10001524137253141 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001524137253141/10000000000000000 : ℝ)) (X := (1250800171935005551/1250000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4971285580187649/50000000000000000000 : ℝ) ≤ ((5958331717530797981/5960000000000000000 : ℝ)+2*(175104877477/119200000000000 : ℝ)*(11139/100000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (5958331717530797981/5960000000000000000 : ℝ)+2*(175104877477/119200000000000 : ℝ)*(11139/100000 : ℝ)=(10000473507988279/10000000000000000 : ℝ) by norm_num, show 1+2*(4971285580187649/50000000000000000000 : ℝ)=(25004971285580187649/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(800171935005551/2500000000000000000 : ℝ)+(4971285580187649/50000000000000000000 : ℝ) ≤ ((5958331717530797981/5960000000000000000 : ℝ)+(175104877477/119200000000000 : ℝ)*((2943/20000 : ℝ)+(11139/100000 : ℝ)))^(1075/256 : ℝ) := by
    rw [show (5958331717530797981/5960000000000000000 : ℝ)+(175104877477/119200000000000 : ℝ)*((2943/20000 : ℝ)+(11139/100000 : ℝ))=(1000099882262071/1000000000000000 : ℝ) by norm_num, show 1+(800171935005551/2500000000000000000 : ℝ)+(4971285580187649/50000000000000000000 : ℝ)=(50020974724280298669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(800171935005551/2500000000000000000 : ℝ) ≤ ((5958331717530797981/5960000000000000000 : ℝ)+2*(175104877477/119200000000000 : ℝ)*(2943/20000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (5958331717530797981/5960000000000000000 : ℝ)+2*(175104877477/119200000000000 : ℝ)*(2943/20000 : ℝ)=(10001524137253141/10000000000000000 : ℝ) by norm_num, show 1+2*(800171935005551/2500000000000000000 : ℝ)=(1250800171935005551/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5958331717530797981/5960000000000000000 : ℝ)*(X 1 0+X 2 0)+(175104877477/119200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (11139/100000 : ℝ)) (hi := (2943/20000 : ℝ)) (c := (5958331717530797981/5960000000000000000 : ℝ)) (alpha := (175104877477/119200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5958331717530797981/5960000000000000000 : ℝ)*(X 0 1+X 2 1)+(175104877477/119200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (11139/100000 : ℝ)) (hi := (2943/20000 : ℝ)) (c := (5958331717530797981/5960000000000000000 : ℝ)) (alpha := (175104877477/119200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5958331717530797981/5960000000000000000 : ℝ)*(X 0 2+X 1 2)+(175104877477/119200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (11139/100000 : ℝ)) (hi := (2943/20000 : ℝ)) (c := (5958331717530797981/5960000000000000000 : ℝ)) (alpha := (175104877477/119200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2044829231/10000000000 : ℝ)*X 0 0+(1353193633/2500000000 : ℝ)*X 0 1+(5244565523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668627527/1250000000 : ℝ)*X 1 0+(-532633491/2500000000 : ℝ)*X 1 1+(5244565517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349020201/10000000000 : ℝ)*X 2 0+(2622282761/5000000000 : ℝ)*X 2 1+(-1065266989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4326879171/10000000000 : ℝ)*X 0 0+(1038533261/2500000000 : ℝ)*X 0 1+(4506326493/10000000000 : ℝ)*X 0 2+(4326879171/10000000000 : ℝ)*X 1 0+(1038533261/2500000000 : ℝ)*X 1 1+(4506326493/10000000000 : ℝ)*X 1 2+(4326879171/10000000000 : ℝ)*X 2 0+(1038533261/2500000000 : ℝ)*X 2 1+(4506326493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-408968263/2000000000 : ℝ)*X 0 0+(1049033571/2000000000 : ℝ)*X 0 1+(676521147/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326424541/2500000000 : ℝ)*X 1 0+(-1962930413/10000000000 : ℝ)*X 1 1+(1082433849/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326424547/2500000000 : ℝ)*X 2 0+(2706084627/5000000000 : ℝ)*X 2 1+(-1962930367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4326904763/10000000000 : ℝ)*X 0 0+(180202617/400000000 : ℝ)*X 0 1+(2077700277/5000000000 : ℝ)*X 0 2+(4326904763/10000000000 : ℝ)*X 1 0+(180202617/400000000 : ℝ)*X 1 1+(2077700277/5000000000 : ℝ)*X 1 2+(4326904763/10000000000 : ℝ)*X 2 0+(180202617/400000000 : ℝ)*X 2 1+(2077700277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (590007134420888434176919227/74500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1473883763/100000000000000 : ℝ)*(base19) + (679230463/50000000000000 : ℝ)*(base23) + (52822341/100000000000000 : ℝ)*(lower2) + (12353767/6250000000000 : ℝ)*(upper3) + (13136557/12500000000000 : ℝ)*(upper5) + (2196106415323189/50000000000000 : ℝ)*(major0) + (2196106415323189/50000000000000 : ℝ)*(major1) + (2196106415323189/50000000000000 : ℝ)*(major2) + (237800672197119/4000000000000 : ℝ)*(sp0) + (5945045143548821/100000000000000 : ℝ)*(sp1) + (2972522629485829/50000000000000 : ℝ)*(sp2) + (709840704834073/25000000000000 : ℝ)*(sp3) + (29812504609/100000000000000 : ℝ)*(sp4) + (15960538579/100000000000000 : ℝ)*(sp7) + (2839378779874871/100000000000000 : ℝ)*(f.failure) + (743130827179073/12500000000000 : ℝ)*(f.sum) + (7867525679867/2980000000000000000000000000 : ℝ)*base66 + (1461217290127331409/298000000000000000000000000000000 : ℝ)*base67 + (3273512354746668591/298000000000000000000000000000000 : ℝ)*base70 + (1167724026518668591/298000000000000000000000000000000 : ℝ)*base72 + (12533430373267/2980000000000000000000000000 : ℝ)*base74 + (1262509224450668591/298000000000000000000000000000000 : ℝ)*base76 + (1053440407274668591/298000000000000000000000000000000 : ℝ)*base78 + (1930469436010668591/298000000000000000000000000000000 : ℝ)*base80 + (16045222455887/2980000000000000000000000000 : ℝ)*base82 + (66420439/5000000000000000000000 : ℝ)*base89 + (66420439/5000000000000000000000 : ℝ)*base91 + (66420439/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144394764780081921959391423/18625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (375652921/50000000000000 : ℝ)*(base19) + (1095962353/100000000000000 : ℝ)*(base23) + (66942327/50000000000000 : ℝ)*(upper3) + (13481191/10000000000000 : ℝ)*(lower4) + (114046779/100000000000000 : ℝ)*(upper5) + (276495451803639/6250000000000 : ℝ)*(major0) + (276495451803639/6250000000000 : ℝ)*(major1) + (276495451803639/6250000000000 : ℝ)*(major2) + (15042551311/100000000000000 : ℝ)*(sp1) + (22817202917/100000000000000 : ℝ)*(sp2) + (299398670494489/5000000000000 : ℝ)*(sp4) + (5987957616032627/100000000000000 : ℝ)*(sp5) + (598794949672451/10000000000000 : ℝ)*(sp6) + (714970197350507/25000000000000 : ℝ)*(sp7) + (714970197350507/25000000000000 : ℝ)*(f.failure) + (299398670494489/5000000000000 : ℝ)*(f.sum) + (501954763537/372500000000000000000000000 : ℝ)*base66 + (106629137779802859/37250000000000000000000000000000 : ℝ)*base67 + (142085885827802859/37250000000000000000000000000000 : ℝ)*base69 + (121104532128197141/37250000000000000000000000000000 : ℝ)*base72 + (1681017219581/745000000000000000000000000 : ℝ)*base73 + (318417025783302859/37250000000000000000000000000000 : ℝ)*base75 + (281306689182552859/37250000000000000000000000000000 : ℝ)*base77 + (659127356166697141/37250000000000000000000000000000 : ℝ)*base80 + (971761081593/372500000000000000000000000 : ℝ)*base81 + (133237/1250000000000000000000 : ℝ)*base90 + (133237/1250000000000000000000 : ℝ)*base92 + (133237/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1341_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1341_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1341_s7_0 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-204483793/1000000000 : ℝ)*x 0 + (338294443/625000000 : ℝ)*x 1 + (2622311557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204483793/1000000000 : ℝ)^4301 ≤ (12452396580991/100000000000000 : ℝ)^3277 := by
    have hnat : (204483793 : ℕ)^4301*100000000000000^3277 ≤ 12452396580991^3277*1000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204483793 1000000000 12452396580991 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338294443/625000000 : ℝ)^4301 ≤ (44679887456059/100000000000000 : ℝ)^3277 := by
    have hnat : (338294443 : ℕ)^4301*100000000000000^3277 ≤ 44679887456059^3277*625000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338294443 625000000 44679887456059 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622311557/5000000000 : ℝ)^4301 ≤ (21433857972947/50000000000000 : ℝ)^3277 := by
    have hnat : (2622311557 : ℕ)^4301*50000000000000^3277 ≤ 21433857972947^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622311557 5000000000 21433857972947 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204483793/1000000000 : ℝ), (338294443/625000000 : ℝ), (2622311557/5000000000 : ℝ)] ![(12452396580991/100000000000000 : ℝ), (44679887456059/100000000000000 : ℝ), (21433857972947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204483793/1000000000 : ℝ)|^4301 ≤ (12452396580991/100000000000000 : ℝ)^3277
        have hw : |(-204483793/1000000000 : ℝ)|=(204483793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338294443/625000000 : ℝ)|^4301 ≤ (44679887456059/100000000000000 : ℝ)^3277
        have hw : |(338294443/625000000 : ℝ)|=(338294443/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622311557/5000000000 : ℝ)|^4301 ≤ (21433857972947/50000000000000 : ℝ)^3277
        have hw : |(2622311557/5000000000 : ℝ)|=(2622311557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s7_1 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349003559/10000000000 : ℝ)*x 0 + (-1065239927/5000000000 : ℝ)*x 1 + (5244623111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349003559/10000000000 : ℝ)^4301 ≤ (43990950571903/100000000000000 : ℝ)^3277 := by
    have hnat : (5349003559 : ℕ)^4301*100000000000000^3277 ≤ 43990950571903^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349003559 10000000000 43990950571903 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065239927/5000000000 : ℝ)^4301 ≤ (3285333373753/25000000000000 : ℝ)^3277 := by
    have hnat : (1065239927 : ℕ)^4301*25000000000000^3277 ≤ 3285333373753^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065239927 5000000000 3285333373753 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244623111/10000000000 : ℝ)^4301 ≤ (42867715913711/100000000000000 : ℝ)^3277 := by
    have hnat : (5244623111 : ℕ)^4301*100000000000000^3277 ≤ 42867715913711^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244623111 10000000000 42867715913711 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349003559/10000000000 : ℝ), (-1065239927/5000000000 : ℝ), (5244623111/10000000000 : ℝ)] ![(43990950571903/100000000000000 : ℝ), (3285333373753/25000000000000 : ℝ), (42867715913711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349003559/10000000000 : ℝ)|^4301 ≤ (43990950571903/100000000000000 : ℝ)^3277
        have hw : |(5349003559/10000000000 : ℝ)|=(5349003559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1065239927/5000000000 : ℝ)|^4301 ≤ (3285333373753/25000000000000 : ℝ)^3277
        have hw : |(-1065239927/5000000000 : ℝ)|=(1065239927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244623111/10000000000 : ℝ)|^4301 ≤ (42867715913711/100000000000000 : ℝ)^3277
        have hw : |(5244623111/10000000000 : ℝ)|=(5244623111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s7_2 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349003561/10000000000 : ℝ)*x 0 + (655577889/1250000000 : ℝ)*x 1 + (-2130479851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349003561/10000000000 : ℝ)^4301 ≤ (43990950593491/100000000000000 : ℝ)^3277 := by
    have hnat : (5349003561 : ℕ)^4301*100000000000000^3277 ≤ 43990950593491^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349003561 10000000000 43990950593491 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655577889/1250000000 : ℝ)^4301 ≤ (42867715924439/100000000000000 : ℝ)^3277 := by
    have hnat : (655577889 : ℕ)^4301*100000000000000^3277 ≤ 42867715924439^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655577889 1250000000 42867715924439 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2130479851/10000000000 : ℝ)^4301 ≤ (525653338829/4000000000000 : ℝ)^3277 := by
    have hnat : (2130479851 : ℕ)^4301*4000000000000^3277 ≤ 525653338829^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130479851 10000000000 525653338829 4000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349003561/10000000000 : ℝ), (655577889/1250000000 : ℝ), (-2130479851/10000000000 : ℝ)] ![(43990950593491/100000000000000 : ℝ), (42867715924439/100000000000000 : ℝ), (525653338829/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349003561/10000000000 : ℝ)|^4301 ≤ (43990950593491/100000000000000 : ℝ)^3277
        have hw : |(5349003561/10000000000 : ℝ)|=(5349003561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655577889/1250000000 : ℝ)|^4301 ≤ (42867715924439/100000000000000 : ℝ)^3277
        have hw : |(655577889/1250000000 : ℝ)|=(655577889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2130479851/10000000000 : ℝ)|^4301 ≤ (525653338829/4000000000000 : ℝ)^3277
        have hw : |(-2130479851/10000000000 : ℝ)|=(2130479851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s7_3 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4326883493/10000000000 : ℝ)*x 0 + (415425923/1000000000 : ℝ)*x 1 + (4506199207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326883493/10000000000 : ℝ)^4301 ≤ (33303270957387/100000000000000 : ℝ)^3277 := by
    have hnat : (4326883493 : ℕ)^4301*100000000000000^3277 ≤ 33303270957387^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326883493 10000000000 33303270957387 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415425923/1000000000 : ℝ)^4301 ≤ (31570402409939/100000000000000 : ℝ)^3277 := by
    have hnat : (415425923 : ℕ)^4301*100000000000000^3277 ≤ 31570402409939^3277*1000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415425923 1000000000 31570402409939 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506199207/10000000000 : ℝ)^4301 ≤ (35126326624319/100000000000000 : ℝ)^3277 := by
    have hnat : (4506199207 : ℕ)^4301*100000000000000^3277 ≤ 35126326624319^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506199207 10000000000 35126326624319 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326883493/10000000000 : ℝ), (415425923/1000000000 : ℝ), (4506199207/10000000000 : ℝ)] ![(33303270957387/100000000000000 : ℝ), (31570402409939/100000000000000 : ℝ), (35126326624319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326883493/10000000000 : ℝ)|^4301 ≤ (33303270957387/100000000000000 : ℝ)^3277
        have hw : |(4326883493/10000000000 : ℝ)|=(4326883493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(415425923/1000000000 : ℝ)|^4301 ≤ (31570402409939/100000000000000 : ℝ)^3277
        have hw : |(415425923/1000000000 : ℝ)|=(415425923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506199207/10000000000 : ℝ)|^4301 ≤ (35126326624319/100000000000000 : ℝ)^3277
        have hw : |(4506199207/10000000000 : ℝ)|=(4506199207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s7_4 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1022425037/5000000000 : ℝ)*x 0 + (163913267/312500000 : ℝ)*x 1 + (2706053289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022425037/5000000000 : ℝ)^4301 ≤ (6226246821493/50000000000000 : ℝ)^3277 := by
    have hnat : (1022425037 : ℕ)^4301*50000000000000^3277 ≤ 6226246821493^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022425037 5000000000 6226246821493 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163913267/312500000 : ℝ)^4301 ≤ (10718542014591/25000000000000 : ℝ)^3277 := by
    have hnat : (163913267 : ℕ)^4301*25000000000000^3277 ≤ 10718542014591^3277*312500000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163913267 312500000 10718542014591 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706053289/5000000000 : ℝ)^4301 ≤ (44673338287983/100000000000000 : ℝ)^3277 := by
    have hnat : (2706053289 : ℕ)^4301*100000000000000^3277 ≤ 44673338287983^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706053289 5000000000 44673338287983 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1022425037/5000000000 : ℝ), (163913267/312500000 : ℝ), (2706053289/5000000000 : ℝ)] ![(6226246821493/50000000000000 : ℝ), (10718542014591/25000000000000 : ℝ), (44673338287983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1022425037/5000000000 : ℝ)|^4301 ≤ (6226246821493/50000000000000 : ℝ)^3277
        have hw : |(-1022425037/5000000000 : ℝ)|=(1022425037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163913267/312500000 : ℝ)|^4301 ≤ (10718542014591/25000000000000 : ℝ)^3277
        have hw : |(163913267/312500000 : ℝ)|=(163913267/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706053289/5000000000 : ℝ)|^4301 ≤ (44673338287983/100000000000000 : ℝ)^3277
        have hw : |(2706053289/5000000000 : ℝ)|=(2706053289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s7_5 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165803529/312500000 : ℝ)*x 0 + (-490749107/2500000000 : ℝ)*x 1 + (676513311/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165803529/312500000 : ℝ)^4301 ≤ (10881065585991/25000000000000 : ℝ)^3277 := by
    have hnat : (165803529 : ℕ)^4301*25000000000000^3277 ≤ 10881065585991^3277*312500000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165803529 312500000 10881065585991 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (490749107/2500000000 : ℝ)^4301 ≤ (5901200166537/50000000000000 : ℝ)^3277 := by
    have hnat : (490749107 : ℕ)^4301*50000000000000^3277 ≤ 5901200166537^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490749107 2500000000 5901200166537 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676513311/1250000000 : ℝ)^4301 ≤ (22336668656477/50000000000000 : ℝ)^3277 := by
    have hnat : (676513311 : ℕ)^4301*50000000000000^3277 ≤ 22336668656477^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676513311 1250000000 22336668656477 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165803529/312500000 : ℝ), (-490749107/2500000000 : ℝ), (676513311/1250000000 : ℝ)] ![(10881065585991/25000000000000 : ℝ), (5901200166537/50000000000000 : ℝ), (22336668656477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165803529/312500000 : ℝ)|^4301 ≤ (10881065585991/25000000000000 : ℝ)^3277
        have hw : |(165803529/312500000 : ℝ)|=(165803529/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-490749107/2500000000 : ℝ)|^4301 ≤ (5901200166537/50000000000000 : ℝ)^3277
        have hw : |(-490749107/2500000000 : ℝ)|=(490749107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676513311/1250000000 : ℝ)|^4301 ≤ (22336668656477/50000000000000 : ℝ)^3277
        have hw : |(676513311/1250000000 : ℝ)|=(676513311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s7_6 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326428243/2500000000 : ℝ)*x 0 + (5412106527/10000000000 : ℝ)*x 1 + (-1962996313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326428243/2500000000 : ℝ)^4301 ≤ (43524262817697/100000000000000 : ℝ)^3277 := by
    have hnat : (1326428243 : ℕ)^4301*100000000000000^3277 ≤ 43524262817697^3277*2500000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326428243 2500000000 43524262817697 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412106527/10000000000 : ℝ)^4301 ≤ (44673337735467/100000000000000 : ℝ)^3277 := by
    have hnat : (5412106527 : ℕ)^4301*100000000000000^3277 ≤ 44673337735467^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412106527 10000000000 44673337735467 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1962996313/10000000000 : ℝ)^4301 ≤ (2360479885117/20000000000000 : ℝ)^3277 := by
    have hnat : (1962996313 : ℕ)^4301*20000000000000^3277 ≤ 2360479885117^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962996313 10000000000 2360479885117 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326428243/2500000000 : ℝ), (5412106527/10000000000 : ℝ), (-1962996313/10000000000 : ℝ)] ![(43524262817697/100000000000000 : ℝ), (44673337735467/100000000000000 : ℝ), (2360479885117/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326428243/2500000000 : ℝ)|^4301 ≤ (43524262817697/100000000000000 : ℝ)^3277
        have hw : |(1326428243/2500000000 : ℝ)|=(1326428243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412106527/10000000000 : ℝ)|^4301 ≤ (44673337735467/100000000000000 : ℝ)^3277
        have hw : |(5412106527/10000000000 : ℝ)|=(5412106527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1962996313/10000000000 : ℝ)|^4301 ≤ (2360479885117/20000000000000 : ℝ)^3277
        have hw : |(-1962996313/10000000000 : ℝ)|=(1962996313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s7_7 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2163454487/5000000000 : ℝ)*x 0 + (4504940077/10000000000 : ℝ)*x 1 + (2077762421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163454487/5000000000 : ℝ)^4301 ≤ (33303528365101/100000000000000 : ℝ)^3277 := by
    have hnat : (2163454487 : ℕ)^4301*100000000000000^3277 ≤ 33303528365101^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163454487 5000000000 33303528365101 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504940077/10000000000 : ℝ)^4301 ≤ (35113445108843/100000000000000 : ℝ)^3277 := by
    have hnat : (4504940077 : ℕ)^4301*100000000000000^3277 ≤ 35113445108843^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504940077 10000000000 35113445108843 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077762421/5000000000 : ℝ)^4301 ≤ (31583026520211/100000000000000 : ℝ)^3277 := by
    have hnat : (2077762421 : ℕ)^4301*100000000000000^3277 ≤ 31583026520211^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077762421 5000000000 31583026520211 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163454487/5000000000 : ℝ), (4504940077/10000000000 : ℝ), (2077762421/5000000000 : ℝ)] ![(33303528365101/100000000000000 : ℝ), (35113445108843/100000000000000 : ℝ), (31583026520211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163454487/5000000000 : ℝ)|^4301 ≤ (33303528365101/100000000000000 : ℝ)^3277
        have hw : |(2163454487/5000000000 : ℝ)|=(2163454487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504940077/10000000000 : ℝ)|^4301 ≤ (35113445108843/100000000000000 : ℝ)^3277
        have hw : |(4504940077/10000000000 : ℝ)|=(4504940077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2077762421/5000000000 : ℝ)|^4301 ≤ (31583026520211/100000000000000 : ℝ)^3277
        have hw : |(2077762421/5000000000 : ℝ)|=(2077762421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1341_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11147/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7353/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14707/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5573/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14707/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5573/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14707/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5573/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14707/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5573/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14707/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5573/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14707/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5573/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5573/50000 : ℝ) ^ (1075/256 : ℝ) ≤ (9968834841136293/100000000000000000000 : ℝ) := by
    have hpowers : (5573/50000 : ℝ)^1075 ≤ (9968834841136293/100000000000000000000 : ℝ)^256 := by
      have hnat : (5573 : ℕ)^1075*100000000000000000000^256 ≤ 9968834841136293^256*50000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5573 50000 9968834841136293 100000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5573/50000 : ℝ)) (X := (9968834841136293/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14707/100000 : ℝ) ^ (1075/256 : ℝ) ≤ (31933870513548049/100000000000000000000 : ℝ) := by
    have hpowers : (14707/100000 : ℝ)^1075 ≤ (31933870513548049/100000000000000000000 : ℝ)^256 := by
      have hnat : (14707 : ℕ)^1075*100000000000000000000^256 ≤ 31933870513548049^256*100000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14707 100000 31933870513548049 100000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14707/100000 : ℝ)) (X := (31933870513548049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009968834841136293/50000000000000000000 : ℝ) ≤ (10000474758682701/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50009968834841136293/50000000000000000000 : ℝ)^256 ≤ (10000474758682701/10000000000000000 : ℝ)^1075 := by
      have hnat : (50009968834841136293 : ℕ)^256*10000000000000000^1075 ≤ 10000474758682701^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009968834841136293 50000000000000000000 10000474758682701 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000474758682701/10000000000000000 : ℝ)) (X := (50009968834841136293/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020951352677342171/50000000000000000000 : ℝ) ≤ (2000199541967121/2000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50020951352677342171/50000000000000000000 : ℝ)^256 ≤ (2000199541967121/2000000000000000 : ℝ)^1075 := by
      have hnat : (50020951352677342171 : ℕ)^256*2000000000000000^1075 ≤ 2000199541967121^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020951352677342171 50000000000000000000 2000199541967121 2000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000199541967121/2000000000000000 : ℝ)) (X := (50020951352677342171/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031933870513548049/50000000000000000000 : ℝ) ≤ (10001520660988509/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (50031933870513548049/50000000000000000000 : ℝ)^256 ≤ (10001520660988509/10000000000000000 : ℝ)^1075 := by
      have hnat : (50031933870513548049 : ℕ)^256*10000000000000000^1075 ≤ 10001520660988509^1075*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031933870513548049 50000000000000000000 10001520660988509 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001520660988509/10000000000000000 : ℝ)) (X := (50031933870513548049/50000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9968834841136293/100000000000000000000 : ℝ) ≤ ((11866677662856187431/11870000000000000000 : ℝ)+2*(21789631371/14837500000000 : ℝ)*(5573/50000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (11866677662856187431/11870000000000000000 : ℝ)+2*(21789631371/14837500000000 : ℝ)*(5573/50000 : ℝ)=(10000474758682701/10000000000000000 : ℝ) by norm_num, show 1+2*(9968834841136293/100000000000000000000 : ℝ)=(50009968834841136293/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31933870513548049/100000000000000000000 : ℝ)+(9968834841136293/100000000000000000000 : ℝ) ≤ ((11866677662856187431/11870000000000000000 : ℝ)+(21789631371/14837500000000 : ℝ)*((14707/100000 : ℝ)+(5573/50000 : ℝ)))^(1075/256 : ℝ) := by
    rw [show (11866677662856187431/11870000000000000000 : ℝ)+(21789631371/14837500000000 : ℝ)*((14707/100000 : ℝ)+(5573/50000 : ℝ))=(2000199541967121/2000000000000000 : ℝ) by norm_num, show 1+(31933870513548049/100000000000000000000 : ℝ)+(9968834841136293/100000000000000000000 : ℝ)=(50020951352677342171/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31933870513548049/100000000000000000000 : ℝ) ≤ ((11866677662856187431/11870000000000000000 : ℝ)+2*(21789631371/14837500000000 : ℝ)*(14707/100000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (11866677662856187431/11870000000000000000 : ℝ)+2*(21789631371/14837500000000 : ℝ)*(14707/100000 : ℝ)=(10001520660988509/10000000000000000 : ℝ) by norm_num, show 1+2*(31933870513548049/100000000000000000000 : ℝ)=(50031933870513548049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11866677662856187431/11870000000000000000 : ℝ)*(X 1 0+X 2 0)+(21789631371/14837500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (5573/50000 : ℝ)) (hi := (14707/100000 : ℝ)) (c := (11866677662856187431/11870000000000000000 : ℝ)) (alpha := (21789631371/14837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11866677662856187431/11870000000000000000 : ℝ)*(X 0 1+X 2 1)+(21789631371/14837500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (5573/50000 : ℝ)) (hi := (14707/100000 : ℝ)) (c := (11866677662856187431/11870000000000000000 : ℝ)) (alpha := (21789631371/14837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11866677662856187431/11870000000000000000 : ℝ)*(X 0 2+X 1 2)+(21789631371/14837500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (5573/50000 : ℝ)) (hi := (14707/100000 : ℝ)) (c := (11866677662856187431/11870000000000000000 : ℝ)) (alpha := (21789631371/14837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-204483793/1000000000 : ℝ)*X 0 0+(338294443/625000000 : ℝ)*X 0 1+(2622311557/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349003559/10000000000 : ℝ)*X 1 0+(-1065239927/5000000000 : ℝ)*X 1 1+(5244623111/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349003561/10000000000 : ℝ)*X 2 0+(655577889/1250000000 : ℝ)*X 2 1+(-2130479851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4326883493/10000000000 : ℝ)*X 0 0+(415425923/1000000000 : ℝ)*X 0 1+(4506199207/10000000000 : ℝ)*X 0 2+(4326883493/10000000000 : ℝ)*X 1 0+(415425923/1000000000 : ℝ)*X 1 1+(4506199207/10000000000 : ℝ)*X 1 2+(4326883493/10000000000 : ℝ)*X 2 0+(415425923/1000000000 : ℝ)*X 2 1+(4506199207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1022425037/5000000000 : ℝ)*X 0 0+(163913267/312500000 : ℝ)*X 0 1+(2706053289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165803529/312500000 : ℝ)*X 1 0+(-490749107/2500000000 : ℝ)*X 1 1+(676513311/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326428243/2500000000 : ℝ)*X 2 0+(5412106527/10000000000 : ℝ)*X 2 1+(-1962996313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163454487/5000000000 : ℝ)*X 0 0+(4504940077/10000000000 : ℝ)*X 0 1+(2077762421/5000000000 : ℝ)*X 0 2+(2163454487/5000000000 : ℝ)*X 1 0+(4504940077/10000000000 : ℝ)*X 1 1+(2077762421/5000000000 : ℝ)*X 1 2+(2163454487/5000000000 : ℝ)*X 2 0+(4504940077/10000000000 : ℝ)*X 2 1+(2077762421/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5999812240201280218298745033/593500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (237246929/12500000000000 : ℝ)*(base19) + (884901757/50000000000000 : ℝ)*(base23) + (34874537/50000000000000 : ℝ)*(lower2) + (25180481/10000000000000 : ℝ)*(upper3) + (160234133/100000000000000 : ℝ)*(upper5) + (4395388292190181/100000000000000 : ℝ)*(major0) + (4395388292190181/100000000000000 : ℝ)*(major1) + (4395388292190181/100000000000000 : ℝ)*(major2) + (1487326479612329/25000000000000 : ℝ)*(sp0) + (5949342768731277/100000000000000 : ℝ)*(sp1) + (1189868579380639/20000000000000 : ℝ)*(sp2) + (568282316555929/20000000000000 : ℝ)*(sp3) + (38748257393/100000000000000 : ℝ)*(sp4) + (19997920557/100000000000000 : ℝ)*(sp7) + (1420715790350101/50000000000000 : ℝ)*(f.failure) + (5949344666706709/100000000000000 : ℝ)*(f.sum) + (15085556559373/5935000000000000000000000000 : ℝ)*base65 + (12454891205938384989/1187000000000000000000000000000000 : ℝ)*base68 + (1364315583514384989/1187000000000000000000000000000000 : ℝ)*base70 + (5976705176747384989/1187000000000000000000000000000000 : ℝ)*base72 + (6030088166527/5935000000000000000000000000 : ℝ)*base74 + (271351585917384989/1187000000000000000000000000000000 : ℝ)*base76 + (4303115374028615011/1187000000000000000000000000000000 : ℝ)*base77 + (1490728758181615011/1187000000000000000000000000000000 : ℝ)*base79 + (2197542773033/1483750000000000000000000000 : ℝ)*base82 + (9955509/2500000000000000000000 : ℝ)*base89 + (9955509/2500000000000000000000 : ℝ)*base91 + (9955509/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1421746845429088543759064157/148375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1762457381/100000000000000 : ℝ)*(base19) + (102145137/5000000000000 : ℝ)*(base23) + (67172891/12500000000000 : ℝ)*(lower1) + (43456713/20000000000000 : ℝ)*(upper3) + (8163693/10000000000000 : ℝ)*(lower4) + (80064807/50000000000000 : ℝ)*(upper5) + (1106766443352649/25000000000000 : ℝ)*(major0) + (1106766443352649/25000000000000 : ℝ)*(major1) + (1106766443352649/25000000000000 : ℝ)*(major2) + (2355798873/25000000000000 : ℝ)*(sp2) + (5992221502454611/100000000000000 : ℝ)*(sp4) + (599221973999723/10000000000000 : ℝ)*(sp5) + (5992210036356379/100000000000000 : ℝ)*(sp6) + (14309548624813/500000000000 : ℝ)*(sp7) + (14309548624813/500000000000 : ℝ)*(f.failure) + (5992221502454611/100000000000000 : ℝ)*(f.sum) + (14449172959009/2967500000000000000000000000 : ℝ)*base65 + (29263034618304445281/296750000000000000000000000000000 : ℝ)*base68 + (4675768195238945281/296750000000000000000000000000000 : ℝ)*base70 + (19631106954977554719/296750000000000000000000000000000 : ℝ)*base71 + (436566041073/92734375000000000000000000 : ℝ)*base74 + (19584880545677554719/296750000000000000000000000000000 : ℝ)*base75 + (1879471413652445281/296750000000000000000000000000000 : ℝ)*base78 + (2691512724732195281/296750000000000000000000000000000 : ℝ)*base80 + (11802782018193/5935000000000000000000000000 : ℝ)*base81 + (183117/25000000000000000000 : ℝ)*base89 + (183117/25000000000000000000 : ℝ)*base91 + (183117/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1341_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1341_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1341_s8_0 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1022419469/5000000000 : ℝ)*x 0 + (676587811/1250000000 : ℝ)*x 1 + (5244631049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022419469/5000000000 : ℝ)^4301 ≤ (6226202318757/50000000000000 : ℝ)^3277 := by
    have hnat : (1022419469 : ℕ)^4301*50000000000000^3277 ≤ 6226202318757^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022419469 5000000000 6226202318757 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676587811/1250000000 : ℝ)^4301 ≤ (44679794283383/100000000000000 : ℝ)^3277 := by
    have hnat : (676587811 : ℕ)^4301*100000000000000^3277 ≤ 44679794283383^3277*1250000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676587811 1250000000 44679794283383 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244631049/10000000000 : ℝ)^4301 ≤ (10716950267673/25000000000000 : ℝ)^3277 := by
    have hnat : (5244631049 : ℕ)^4301*25000000000000^3277 ≤ 10716950267673^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244631049 10000000000 10716950267673 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1022419469/5000000000 : ℝ), (676587811/1250000000 : ℝ), (5244631049/10000000000 : ℝ)] ![(6226202318757/50000000000000 : ℝ), (44679794283383/100000000000000 : ℝ), (10716950267673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1022419469/5000000000 : ℝ)|^4301 ≤ (6226202318757/50000000000000 : ℝ)^3277
        have hw : |(-1022419469/5000000000 : ℝ)|=(1022419469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676587811/1250000000 : ℝ)|^4301 ≤ (44679794283383/100000000000000 : ℝ)^3277
        have hw : |(676587811/1250000000 : ℝ)|=(676587811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244631049/10000000000 : ℝ)|^4301 ≤ (10716950267673/25000000000000 : ℝ)^3277
        have hw : |(5244631049/10000000000 : ℝ)|=(5244631049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s8_1 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349001363/10000000000 : ℝ)*x 0 + (-2130472289/10000000000 : ℝ)*x 1 + (524463103/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349001363/10000000000 : ℝ)^4301 ≤ (43990926868223/100000000000000 : ℝ)^3277 := by
    have hnat : (5349001363 : ℕ)^4301*100000000000000^3277 ≤ 43990926868223^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349001363 10000000000 43990926868223 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130472289/10000000000 : ℝ)^4301 ≤ (13141272250991/100000000000000 : ℝ)^3277 := by
    have hnat : (2130472289 : ℕ)^4301*100000000000000^3277 ≤ 13141272250991^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130472289 10000000000 13141272250991 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524463103/1000000000 : ℝ)^4301 ≤ (8573560173373/20000000000000 : ℝ)^3277 := by
    have hnat : (524463103 : ℕ)^4301*20000000000000^3277 ≤ 8573560173373^3277*1000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524463103 1000000000 8573560173373 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349001363/10000000000 : ℝ), (-2130472289/10000000000 : ℝ), (524463103/1000000000 : ℝ)] ![(43990926868223/100000000000000 : ℝ), (13141272250991/100000000000000 : ℝ), (8573560173373/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349001363/10000000000 : ℝ)|^4301 ≤ (43990926868223/100000000000000 : ℝ)^3277
        have hw : |(5349001363/10000000000 : ℝ)|=(5349001363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2130472289/10000000000 : ℝ)|^4301 ≤ (13141272250991/100000000000000 : ℝ)^3277
        have hw : |(-2130472289/10000000000 : ℝ)|=(2130472289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524463103/1000000000 : ℝ)|^4301 ≤ (8573560173373/20000000000000 : ℝ)^3277
        have hw : |(524463103/1000000000 : ℝ)|=(524463103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s8_2 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349001563/10000000000 : ℝ)*x 0 + (5244630601/10000000000 : ℝ)*x 1 + (-213047259/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349001563/10000000000 : ℝ)^4301 ≤ (10997732256757/25000000000000 : ℝ)^3277 := by
    have hnat : (5349001563 : ℕ)^4301*25000000000000^3277 ≤ 10997732256757^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349001563 10000000000 10997732256757 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244630601/10000000000 : ℝ)^4301 ≤ (42867796264653/100000000000000 : ℝ)^3277 := by
    have hnat : (5244630601 : ℕ)^4301*100000000000000^3277 ≤ 42867796264653^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244630601 10000000000 42867796264653 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213047259/1000000000 : ℝ)^4301 ≤ (13141274687797/100000000000000 : ℝ)^3277 := by
    have hnat : (213047259 : ℕ)^4301*100000000000000^3277 ≤ 13141274687797^3277*1000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213047259 1000000000 13141274687797 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349001563/10000000000 : ℝ), (5244630601/10000000000 : ℝ), (-213047259/1000000000 : ℝ)] ![(10997732256757/25000000000000 : ℝ), (42867796264653/100000000000000 : ℝ), (13141274687797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349001563/10000000000 : ℝ)|^4301 ≤ (10997732256757/25000000000000 : ℝ)^3277
        have hw : |(5349001563/10000000000 : ℝ)|=(5349001563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244630601/10000000000 : ℝ)|^4301 ≤ (42867796264653/100000000000000 : ℝ)^3277
        have hw : |(5244630601/10000000000 : ℝ)|=(5244630601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-213047259/1000000000 : ℝ)|^4301 ≤ (13141274687797/100000000000000 : ℝ)^3277
        have hw : |(-213047259/1000000000 : ℝ)|=(213047259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s8_3 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4326884491/10000000000 : ℝ)*x 0 + (2077137811/5000000000 : ℝ)*x 1 + (28163639/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326884491/10000000000 : ℝ)^4301 ≤ (33303281039121/100000000000000 : ℝ)^3277 := by
    have hnat : (4326884491 : ℕ)^4301*100000000000000^3277 ≤ 33303281039121^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326884491 10000000000 33303281039121 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077137811/5000000000 : ℝ)^4301 ≤ (31570565907673/100000000000000 : ℝ)^3277 := by
    have hnat : (2077137811 : ℕ)^4301*100000000000000^3277 ≤ 31570565907673^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077137811 5000000000 31570565907673 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28163639/62500000 : ℝ)^4301 ≤ (17563076518069/50000000000000 : ℝ)^3277 := by
    have hnat : (28163639 : ℕ)^4301*50000000000000^3277 ≤ 17563076518069^3277*62500000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28163639 62500000 17563076518069 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326884491/10000000000 : ℝ), (2077137811/5000000000 : ℝ), (28163639/62500000 : ℝ)] ![(33303281039121/100000000000000 : ℝ), (31570565907673/100000000000000 : ℝ), (17563076518069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326884491/10000000000 : ℝ)|^4301 ≤ (33303281039121/100000000000000 : ℝ)^3277
        have hw : |(4326884491/10000000000 : ℝ)|=(4326884491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2077137811/5000000000 : ℝ)|^4301 ≤ (31570565907673/100000000000000 : ℝ)^3277
        have hw : |(2077137811/5000000000 : ℝ)|=(2077137811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28163639/62500000 : ℝ)|^4301 ≤ (17563076518069/50000000000000 : ℝ)^3277
        have hw : |(28163639/62500000 : ℝ)|=(28163639/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s8_4 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305714633/10000000000 : ℝ)*x 0 + (1082419727/2000000000 : ℝ)*x 1 + (-1963004883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305714633/10000000000 : ℝ)^4301 ≤ (21762140350553/50000000000000 : ℝ)^3277 := by
    have hnat : (5305714633 : ℕ)^4301*50000000000000^3277 ≤ 21762140350553^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305714633 10000000000 21762140350553 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082419727/2000000000 : ℝ)^4301 ≤ (11168313059067/25000000000000 : ℝ)^3277 := by
    have hnat : (1082419727 : ℕ)^4301*25000000000000^3277 ≤ 11168313059067^3277*2000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082419727 2000000000 11168313059067 25000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1963004883/10000000000 : ℝ)^4301 ≤ (2360493410667/20000000000000 : ℝ)^3277 := by
    have hnat : (1963004883 : ℕ)^4301*20000000000000^3277 ≤ 2360493410667^3277*10000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963004883 10000000000 2360493410667 20000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305714633/10000000000 : ℝ), (1082419727/2000000000 : ℝ), (-1963004883/10000000000 : ℝ)] ![(21762140350553/50000000000000 : ℝ), (11168313059067/25000000000000 : ℝ), (2360493410667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305714633/10000000000 : ℝ)|^4301 ≤ (21762140350553/50000000000000 : ℝ)^3277
        have hw : |(5305714633/10000000000 : ℝ)|=(5305714633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082419727/2000000000 : ℝ)|^4301 ≤ (11168313059067/25000000000000 : ℝ)^3277
        have hw : |(1082419727/2000000000 : ℝ)|=(1082419727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1963004883/10000000000 : ℝ)|^4301 ≤ (2360493410667/20000000000000 : ℝ)^3277
        have hw : |(-1963004883/10000000000 : ℝ)|=(1963004883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1341_s8_5 (p : ℝ) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270431839/625000000 : ℝ)*x 0 + (2252461629/5000000000 : ℝ)*x 1 + (2077770817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270431839/625000000 : ℝ)^4301 ≤ (16651766455491/50000000000000 : ℝ)^3277 := by
    have hnat : (270431839 : ℕ)^4301*50000000000000^3277 ≤ 16651766455491^3277*625000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270431839 625000000 16651766455491 50000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252461629/5000000000 : ℝ)^4301 ≤ (4389159131233/12500000000000 : ℝ)^3277 := by
    have hnat : (2252461629 : ℕ)^4301*12500000000000^3277 ≤ 4389159131233^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252461629 5000000000 4389159131233 12500000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077770817/5000000000 : ℝ)^4301 ≤ (31583194023587/100000000000000 : ℝ)^3277 := by
    have hnat : (2077770817 : ℕ)^4301*100000000000000^3277 ≤ 31583194023587^3277*5000000000^4301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077770817 5000000000 31583194023587 100000000000000 4301 3277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4301/1024 : ℝ)) 4301 3277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270431839/625000000 : ℝ), (2252461629/5000000000 : ℝ), (2077770817/5000000000 : ℝ)] ![(16651766455491/50000000000000 : ℝ), (4389159131233/12500000000000 : ℝ), (31583194023587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270431839/625000000 : ℝ)|^4301 ≤ (16651766455491/50000000000000 : ℝ)^3277
        have hw : |(270431839/625000000 : ℝ)|=(270431839/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252461629/5000000000 : ℝ)|^4301 ≤ (4389159131233/12500000000000 : ℝ)^3277
        have hw : |(2252461629/5000000000 : ℝ)|=(2252461629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2077770817/5000000000 : ℝ)|^4301 ≤ (31583194023587/100000000000000 : ℝ)^3277
        have hw : |(2077770817/5000000000 : ℝ)|=(2077770817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1341_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2787/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7353/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11147/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11147/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11147/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11147/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11147/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11147/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11147/100000 : ℝ) ^ (1075/256 : ℝ) ≤ (4986295552914713/50000000000000000000 : ℝ) := by
    have hpowers : (11147/100000 : ℝ)^1075 ≤ (4986295552914713/50000000000000000000 : ℝ)^256 := by
      have hnat : (11147 : ℕ)^1075*50000000000000000000^256 ≤ 4986295552914713^256*100000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11147 100000 4986295552914713 50000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11147/100000 : ℝ)) (X := (4986295552914713/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7353/50000 : ℝ) ^ (1075/256 : ℝ) ≤ (7981188395310401/25000000000000000000 : ℝ) := by
    have hpowers : (7353/50000 : ℝ)^1075 ≤ (7981188395310401/25000000000000000000 : ℝ)^256 := by
      have hnat : (7353 : ℕ)^1075*25000000000000000000^256 ≤ 7981188395310401^256*50000^1075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7353 50000 7981188395310401 25000000000000000000 1075 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7353/50000 : ℝ)) (X := (7981188395310401/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004986295552914713/25000000000000000000 : ℝ) ≤ (10000474937558551/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (25004986295552914713/25000000000000000000 : ℝ)^256 ≤ (10000474937558551/10000000000000000 : ℝ)^1075 := by
      have hnat : (25004986295552914713 : ℕ)^256*10000000000000000^1075 ≤ 10000474937558551^1075*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004986295552914713 25000000000000000000 10000474937558551 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000474937558551/10000000000000000 : ℝ)) (X := (25004986295552914713/25000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004189734468707103/10000000000000000000 : ℝ) ≤ (2500249395554413/2500000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (10004189734468707103/10000000000000000000 : ℝ)^256 ≤ (2500249395554413/2500000000000000 : ℝ)^1075 := by
      have hnat : (10004189734468707103 : ℕ)^256*2500000000000000^1075 ≤ 2500249395554413^1075*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004189734468707103 10000000000000000000 2500249395554413 2500000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500249395554413/2500000000000000 : ℝ)) (X := (10004189734468707103/10000000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507981188395310401/12500000000000000000 : ℝ) ≤ (10001520226876753/10000000000000000 : ℝ) ^ (1075/256 : ℝ) := by
    have hpowers : (12507981188395310401/12500000000000000000 : ℝ)^256 ≤ (10001520226876753/10000000000000000 : ℝ)^1075 := by
      have hnat : (12507981188395310401 : ℕ)^256*10000000000000000^1075 ≤ 10001520226876753^1075*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507981188395310401 12500000000000000000 10001520226876753 10000000000000000 256 1075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001520226876753/10000000000000000 : ℝ)) (X := (12507981188395310401/12500000000000000000 : ℝ)) (by norm_num) 1075 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4986295552914713/50000000000000000000 : ℝ) ≤ ((7116007692548177063/7118000000000000000 : ℝ)+2*(522644659101/355900000000000 : ℝ)*(11147/100000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (7116007692548177063/7118000000000000000 : ℝ)+2*(522644659101/355900000000000 : ℝ)*(11147/100000 : ℝ)=(10000474937558551/10000000000000000 : ℝ) by norm_num, show 1+2*(4986295552914713/50000000000000000000 : ℝ)=(25004986295552914713/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7981188395310401/25000000000000000000 : ℝ)+(4986295552914713/50000000000000000000 : ℝ) ≤ ((7116007692548177063/7118000000000000000 : ℝ)+(522644659101/355900000000000 : ℝ)*((7353/50000 : ℝ)+(11147/100000 : ℝ)))^(1075/256 : ℝ) := by
    rw [show (7116007692548177063/7118000000000000000 : ℝ)+(522644659101/355900000000000 : ℝ)*((7353/50000 : ℝ)+(11147/100000 : ℝ))=(2500249395554413/2500000000000000 : ℝ) by norm_num, show 1+(7981188395310401/25000000000000000000 : ℝ)+(4986295552914713/50000000000000000000 : ℝ)=(10004189734468707103/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7981188395310401/25000000000000000000 : ℝ) ≤ ((7116007692548177063/7118000000000000000 : ℝ)+2*(522644659101/355900000000000 : ℝ)*(7353/50000 : ℝ))^(1075/256 : ℝ) := by
    rw [show (7116007692548177063/7118000000000000000 : ℝ)+2*(522644659101/355900000000000 : ℝ)*(7353/50000 : ℝ)=(10001520226876753/10000000000000000 : ℝ) by norm_num, show 1+2*(7981188395310401/25000000000000000000 : ℝ)=(12507981188395310401/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7116007692548177063/7118000000000000000 : ℝ)*(X 1 0+X 2 0)+(522644659101/355900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (11147/100000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (7116007692548177063/7118000000000000000 : ℝ)) (alpha := (522644659101/355900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7116007692548177063/7118000000000000000 : ℝ)*(X 0 1+X 2 1)+(522644659101/355900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (11147/100000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (7116007692548177063/7118000000000000000 : ℝ)) (alpha := (522644659101/355900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7116007692548177063/7118000000000000000 : ℝ)*(X 0 2+X 1 2)+(522644659101/355900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1075/256 : ℝ)) (lo := (11147/100000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (7116007692548177063/7118000000000000000 : ℝ)) (alpha := (522644659101/355900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1022419469/5000000000 : ℝ)*X 0 0+(676587811/1250000000 : ℝ)*X 0 1+(5244631049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349001363/10000000000 : ℝ)*X 1 0+(-2130472289/10000000000 : ℝ)*X 1 1+(524463103/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349001563/10000000000 : ℝ)*X 2 0+(5244630601/10000000000 : ℝ)*X 2 1+(-213047259/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4326884491/10000000000 : ℝ)*X 0 0+(2077137811/5000000000 : ℝ)*X 0 1+(28163639/62500000 : ℝ)*X 0 2+(4326884491/10000000000 : ℝ)*X 1 0+(2077137811/5000000000 : ℝ)*X 1 1+(28163639/62500000 : ℝ)*X 1 2+(4326884491/10000000000 : ℝ)*X 2 0+(2077137811/5000000000 : ℝ)*X 2 1+(28163639/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5305714633/10000000000 : ℝ)*X 2 0+(1082419727/2000000000 : ℝ)*X 2 1+(-1963004883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s8_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((270431839/625000000 : ℝ)*X 0 0+(2252461629/5000000000 : ℝ)*X 0 1+(2077770817/5000000000 : ℝ)*X 0 2+(270431839/625000000 : ℝ)*X 1 0+(2252461629/5000000000 : ℝ)*X 1 1+(2077770817/5000000000 : ℝ)*X 1 2+(270431839/625000000 : ℝ)*X 2 0+(2252461629/5000000000 : ℝ)*X 2 1+(2077770817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1341_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (372400145697319152794853579/355900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64858389/12500000000000 : ℝ)*(base19) + (720902599/100000000000000 : ℝ)*(base23) + (235435729/100000000000000 : ℝ)*(upper3) + (238359/3125000000000 : ℝ)*(lower4) + (56648823/100000000000000 : ℝ)*(upper5) + (4395766081584511/100000000000000 : ℝ)*(major0) + (4395766081584511/100000000000000 : ℝ)*(major1) + (4395766081584511/100000000000000 : ℝ)*(major2) + (1487464080703817/25000000000000 : ℝ)*(sp0) + (1189971160789631/20000000000000 : ℝ)*(sp1) + (1487462828804233/25000000000000 : ℝ)*(sp2) + (355208465501717/12500000000000 : ℝ)*(sp3) + (535836967/12500000000000 : ℝ)*(sp4) + (4040730643/50000000000000 : ℝ)*(sp5) + (2841675805475021/100000000000000 : ℝ)*(f.failure) + (1487464080703817/25000000000000 : ℝ)*(f.sum) + (162406026260909/17795000000000000000000000000 : ℝ)*base66 + (4496678231776708807/711800000000000000000000000000000 : ℝ)*base68 + (2388871679814308807/711800000000000000000000000000000 : ℝ)*base70 + (2661365827539491193/711800000000000000000000000000000 : ℝ)*base71 + (9593320325279/1112187500000000000000000000 : ℝ)*base74 + (1378253425926708807/711800000000000000000000000000000 : ℝ)*base76 + (2171495894960708807/711800000000000000000000000000000 : ℝ)*base78 + (4245315030068891193/711800000000000000000000000000000 : ℝ)*base79 + (128802570018209/17795000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8511789/5000000000000000000000 : ℝ)*base89 + (8511789/5000000000000000000000 : ℝ)*base91 + (8511789/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1341_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1341_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1341_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1341_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1341_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1341_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1341_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
