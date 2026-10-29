-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1753_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:19:37.95365+00:00
-- url     : https://prove2.me/submissions/a9469cdf-85a9-4d42-9074-e70eacce35d6

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
theorem support_rectangle_w1753_s3_0 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (333386553/625000000 : ℝ)*x 0 + (5081979777/10000000000 : ℝ)*x 1 + (-710265597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333386553/625000000 : ℝ)^5823 ≤ (23323861437319/50000000000000 : ℝ)^4799 := by
    have hnat : (333386553 : ℕ)^5823*50000000000000^4799 ≤ 23323861437319^4799*625000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333386553 625000000 23323861437319 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5081979777/10000000000 : ℝ)^5823 ≤ (10996308080613/25000000000000 : ℝ)^4799 := by
    have hnat : (5081979777 : ℕ)^5823*25000000000000^4799 ≤ 10996308080613^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081979777 10000000000 10996308080613 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (710265597/5000000000 : ℝ)^5823 ≤ (9367044791893/100000000000000 : ℝ)^4799 := by
    have hnat : (710265597 : ℕ)^5823*100000000000000^4799 ≤ 9367044791893^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710265597 5000000000 9367044791893 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(333386553/625000000 : ℝ), (5081979777/10000000000 : ℝ), (-710265597/5000000000 : ℝ)] ![(23323861437319/50000000000000 : ℝ), (10996308080613/25000000000000 : ℝ), (9367044791893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(333386553/625000000 : ℝ)|^5823 ≤ (23323861437319/50000000000000 : ℝ)^4799
        have hw : |(333386553/625000000 : ℝ)|=(333386553/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5081979777/10000000000 : ℝ)|^5823 ≤ (10996308080613/25000000000000 : ℝ)^4799
        have hw : |(5081979777/10000000000 : ℝ)|=(5081979777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-710265597/5000000000 : ℝ)|^5823 ≤ (9367044791893/100000000000000 : ℝ)^4799
        have hw : |(-710265597/5000000000 : ℝ)|=(710265597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s3_1 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1205985063/10000000000 : ℝ)*x 0 + (2544348503/5000000000 : ℝ)*x 1 + (1371533571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1205985063/10000000000 : ℝ)^5823 ≤ (7679283527399/100000000000000 : ℝ)^4799 := by
    have hnat : (1205985063 : ℕ)^5823*100000000000000^4799 ≤ 7679283527399^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205985063 10000000000 7679283527399 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544348503/5000000000 : ℝ)^5823 ≤ (88111572557/200000000000 : ℝ)^4799 := by
    have hnat : (2544348503 : ℕ)^5823*200000000000^4799 ≤ 88111572557^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544348503 5000000000 88111572557 200000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1371533571/2500000000 : ℝ)^5823 ≤ (12066232543267/25000000000000 : ℝ)^4799 := by
    have hnat : (1371533571 : ℕ)^5823*25000000000000^4799 ≤ 12066232543267^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371533571 2500000000 12066232543267 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1205985063/10000000000 : ℝ), (2544348503/5000000000 : ℝ), (1371533571/2500000000 : ℝ)] ![(7679283527399/100000000000000 : ℝ), (88111572557/200000000000 : ℝ), (12066232543267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1205985063/10000000000 : ℝ)|^5823 ≤ (7679283527399/100000000000000 : ℝ)^4799
        have hw : |(-1205985063/10000000000 : ℝ)|=(1205985063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2544348503/5000000000 : ℝ)|^5823 ≤ (88111572557/200000000000 : ℝ)^4799
        have hw : |(2544348503/5000000000 : ℝ)|=(2544348503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1371533571/2500000000 : ℝ)|^5823 ≤ (12066232543267/25000000000000 : ℝ)^4799
        have hw : |(1371533571/2500000000 : ℝ)|=(1371533571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s3_2 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225321377/10000000000 : ℝ)*x 0 + (-1016376453/10000000000 : ℝ)*x 1 + (2743067601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225321377/10000000000 : ℝ)^5823 ≤ (11373773939157/25000000000000 : ℝ)^4799 := by
    have hnat : (5225321377 : ℕ)^5823*25000000000000^4799 ≤ 11373773939157^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225321377 10000000000 11373773939157 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016376453/10000000000 : ℝ)^5823 ≤ (1247992850639/20000000000000 : ℝ)^4799 := by
    have hnat : (1016376453 : ℕ)^5823*20000000000000^4799 ≤ 1247992850639^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016376453 10000000000 1247992850639 20000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743067601/5000000000 : ℝ)^5823 ≤ (4826493997257/10000000000000 : ℝ)^4799 := by
    have hnat : (2743067601 : ℕ)^5823*10000000000000^4799 ≤ 4826493997257^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743067601 5000000000 4826493997257 10000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225321377/10000000000 : ℝ), (-1016376453/10000000000 : ℝ), (2743067601/5000000000 : ℝ)] ![(11373773939157/25000000000000 : ℝ), (1247992850639/20000000000000 : ℝ), (4826493997257/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225321377/10000000000 : ℝ)|^5823 ≤ (11373773939157/25000000000000 : ℝ)^4799
        have hw : |(5225321377/10000000000 : ℝ)|=(5225321377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1016376453/10000000000 : ℝ)|^5823 ≤ (1247992850639/20000000000000 : ℝ)^4799
        have hw : |(-1016376453/10000000000 : ℝ)|=(1016376453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743067601/5000000000 : ℝ)|^5823 ≤ (4826493997257/10000000000000 : ℝ)^4799
        have hw : |(2743067601/5000000000 : ℝ)|=(2743067601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s3_3 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225321677/10000000000 : ℝ)*x 0 + (1371533829/2500000000 : ℝ)*x 1 + (-127046983/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225321677/10000000000 : ℝ)^5823 ≤ (45495098925969/100000000000000 : ℝ)^4799 := by
    have hnat : (5225321677 : ℕ)^5823*100000000000000^4799 ≤ 45495098925969^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225321677 10000000000 45495098925969 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1371533829/2500000000 : ℝ)^5823 ≤ (48264941189501/100000000000000 : ℝ)^4799 := by
    have hnat : (1371533829 : ℕ)^5823*100000000000000^4799 ≤ 48264941189501^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371533829 2500000000 48264941189501 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127046983/1250000000 : ℝ)^5823 ≤ (1559989966369/25000000000000 : ℝ)^4799 := by
    have hnat : (127046983 : ℕ)^5823*25000000000000^4799 ≤ 1559989966369^4799*1250000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127046983 1250000000 1559989966369 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225321677/10000000000 : ℝ), (1371533829/2500000000 : ℝ), (-127046983/1250000000 : ℝ)] ![(45495098925969/100000000000000 : ℝ), (48264941189501/100000000000000 : ℝ), (1559989966369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225321677/10000000000 : ℝ)|^5823 ≤ (45495098925969/100000000000000 : ℝ)^4799
        have hw : |(5225321677/10000000000 : ℝ)|=(5225321677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1371533829/2500000000 : ℝ)|^5823 ≤ (48264941189501/100000000000000 : ℝ)^4799
        have hw : |(1371533829/2500000000 : ℝ)|=(1371533829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127046983/1250000000 : ℝ)|^5823 ≤ (1559989966369/25000000000000 : ℝ)^4799
        have hw : |(-127046983/1250000000 : ℝ)|=(127046983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s3_4 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2007910399/5000000000 : ℝ)*x 0 + (941406591/2000000000 : ℝ)*x 1 + (3385217243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2007910399/5000000000 : ℝ)^5823 ≤ (33054345849493/100000000000000 : ℝ)^4799 := by
    have hnat : (2007910399 : ℕ)^5823*100000000000000^4799 ≤ 33054345849493^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007910399 5000000000 33054345849493 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941406591/2000000000 : ℝ)^5823 ≤ (40079174596247/100000000000000 : ℝ)^4799 := by
    have hnat : (941406591 : ℕ)^5823*100000000000000^4799 ≤ 40079174596247^4799*2000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941406591 2000000000 40079174596247 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3385217243/10000000000 : ℝ)^5823 ≤ (2686647953799/10000000000000 : ℝ)^4799 := by
    have hnat : (3385217243 : ℕ)^5823*10000000000000^4799 ≤ 2686647953799^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3385217243 10000000000 2686647953799 10000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2007910399/5000000000 : ℝ), (941406591/2000000000 : ℝ), (3385217243/10000000000 : ℝ)] ![(33054345849493/100000000000000 : ℝ), (40079174596247/100000000000000 : ℝ), (2686647953799/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2007910399/5000000000 : ℝ)|^5823 ≤ (33054345849493/100000000000000 : ℝ)^4799
        have hw : |(2007910399/5000000000 : ℝ)|=(2007910399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(941406591/2000000000 : ℝ)|^5823 ≤ (40079174596247/100000000000000 : ℝ)^4799
        have hw : |(941406591/2000000000 : ℝ)|=(941406591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3385217243/10000000000 : ℝ)|^5823 ≤ (2686647953799/10000000000000 : ℝ)^4799
        have hw : |(3385217243/10000000000 : ℝ)|=(3385217243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1753_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8959/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9077/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9077/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17917/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8959/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9077/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8959/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9077/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8959/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9077/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8959/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9077/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8959/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9077/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8959/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9077/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9077/100000 : ℝ) ^ (5807/1024 : ℝ) ≤ (123196059900509/100000000000000000000 : ℝ) := by
    have hpowers : (9077/100000 : ℝ)^5807 ≤ (123196059900509/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9077 : ℕ)^5807*100000000000000000000^1024 ≤ 123196059900509^1024*100000^5807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9077 100000 123196059900509 100000000000000000000 5807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9077/100000 : ℝ)) (X := (123196059900509/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8959/50000 : ℝ) ^ (5807/1024 : ℝ) ≤ (2913739889359379/50000000000000000000 : ℝ) := by
    have hpowers : (8959/50000 : ℝ)^5807 ≤ (2913739889359379/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8959 : ℕ)^5807*50000000000000000000^1024 ≤ 2913739889359379^1024*50000^5807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8959 50000 2913739889359379 50000000000000000000 5807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8959/50000 : ℝ)) (X := (2913739889359379/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000123196059900509/50000000000000000000 : ℝ) ≤ (5000002172423581/5000000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (50000123196059900509/50000000000000000000 : ℝ)^1024 ≤ (5000002172423581/5000000000000000 : ℝ)^5807 := by
      have hnat : (50000123196059900509 : ℕ)^1024*5000000000000000^5807 ≤ 5000002172423581^5807*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000123196059900509 50000000000000000000 5000002172423581 5000000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000002172423581/5000000000000000 : ℝ)) (X := (50000123196059900509/50000000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100005950675838619267/100000000000000000000 : ℝ) ≤ (10000104930992471/10000000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (100005950675838619267/100000000000000000000 : ℝ)^1024 ≤ (10000104930992471/10000000000000000 : ℝ)^5807 := by
      have hnat : (100005950675838619267 : ℕ)^1024*10000000000000000^5807 ≤ 10000104930992471^5807*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100005950675838619267 100000000000000000000 10000104930992471 10000000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000104930992471/10000000000000000 : ℝ)) (X := (100005950675838619267/100000000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25002913739889359379/25000000000000000000 : ℝ) ≤ (500010275856889/500000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (25002913739889359379/25000000000000000000 : ℝ)^1024 ≤ (500010275856889/500000000000000 : ℝ)^5807 := by
      have hnat : (25002913739889359379 : ℕ)^1024*500000000000000^5807 ≤ 500010275856889^5807*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002913739889359379 25000000000000000000 500010275856889 500000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500010275856889/500000000000000 : ℝ)) (X := (25002913739889359379/25000000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(123196059900509/100000000000000000000 : ℝ) ≤ ((3683675515496325819/3683750000000000000 : ℝ)+2*(33528715103/294700000000000 : ℝ)*(9077/100000 : ℝ))^(5807/1024 : ℝ) := by
    rw [show (3683675515496325819/3683750000000000000 : ℝ)+2*(33528715103/294700000000000 : ℝ)*(9077/100000 : ℝ)=(5000002172423581/5000000000000000 : ℝ) by norm_num, show 1+2*(123196059900509/100000000000000000000 : ℝ)=(50000123196059900509/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2913739889359379/50000000000000000000 : ℝ)+(123196059900509/100000000000000000000 : ℝ) ≤ ((3683675515496325819/3683750000000000000 : ℝ)+(33528715103/294700000000000 : ℝ)*((8959/50000 : ℝ)+(9077/100000 : ℝ)))^(5807/1024 : ℝ) := by
    rw [show (3683675515496325819/3683750000000000000 : ℝ)+(33528715103/294700000000000 : ℝ)*((8959/50000 : ℝ)+(9077/100000 : ℝ))=(10000104930992471/10000000000000000 : ℝ) by norm_num, show 1+(2913739889359379/50000000000000000000 : ℝ)+(123196059900509/100000000000000000000 : ℝ)=(100005950675838619267/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2913739889359379/50000000000000000000 : ℝ) ≤ ((3683675515496325819/3683750000000000000 : ℝ)+2*(33528715103/294700000000000 : ℝ)*(8959/50000 : ℝ))^(5807/1024 : ℝ) := by
    rw [show (3683675515496325819/3683750000000000000 : ℝ)+2*(33528715103/294700000000000 : ℝ)*(8959/50000 : ℝ)=(500010275856889/500000000000000 : ℝ) by norm_num, show 1+2*(2913739889359379/50000000000000000000 : ℝ)=(25002913739889359379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3683675515496325819/3683750000000000000 : ℝ)*(X 1 0+X 2 0)+(33528715103/294700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (9077/100000 : ℝ)) (hi := (8959/50000 : ℝ)) (c := (3683675515496325819/3683750000000000000 : ℝ)) (alpha := (33528715103/294700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3683675515496325819/3683750000000000000 : ℝ)*(X 0 1+X 2 1)+(33528715103/294700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (9077/100000 : ℝ)) (hi := (8959/50000 : ℝ)) (c := (3683675515496325819/3683750000000000000 : ℝ)) (alpha := (33528715103/294700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3683675515496325819/3683750000000000000 : ℝ)*(X 0 2+X 1 2)+(33528715103/294700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (9077/100000 : ℝ)) (hi := (8959/50000 : ℝ)) (c := (3683675515496325819/3683750000000000000 : ℝ)) (alpha := (33528715103/294700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((333386553/625000000 : ℝ)*X 2 0+(5081979777/10000000000 : ℝ)*X 2 1+(-710265597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s3_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1205985063/10000000000 : ℝ)*X 0 0+(2544348503/5000000000 : ℝ)*X 0 1+(1371533571/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s3_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5225321377/10000000000 : ℝ)*X 1 0+(-1016376453/10000000000 : ℝ)*X 1 1+(2743067601/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s3_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5225321677/10000000000 : ℝ)*X 2 0+(1371533829/2500000000 : ℝ)*X 2 1+(-127046983/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s3_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2007910399/5000000000 : ℝ)*X 0 0+(941406591/2000000000 : ℝ)*X 0 1+(3385217243/10000000000 : ℝ)*X 0 2+(2007910399/5000000000 : ℝ)*X 1 0+(941406591/2000000000 : ℝ)*X 1 1+(3385217243/10000000000 : ℝ)*X 1 2+(2007910399/5000000000 : ℝ)*X 2 0+(941406591/2000000000 : ℝ)*X 2 1+(3385217243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s3_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5745008979252989067691509/657812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1007933849/100000000000000 : ℝ)*(base19) + (2336739937/100000000000000 : ℝ)*(base23) + (150856561/100000000000000 : ℝ)*(lower1) + (95300233/20000000000000 : ℝ)*(upper2) + (107017953/20000000000000 : ℝ)*(upper3) + (127040391/50000000000000 : ℝ)*(upper5) + (163632072215157/10000000000000 : ℝ)*(major0) + (163632072215157/10000000000000 : ℝ)*(major1) + (163632072215157/10000000000000 : ℝ)*(major2) + (13076927837/100000000000000 : ℝ)*(sp0) + (314513363782409/12500000000000 : ℝ)*(sp1) + (157256618895339/6250000000000 : ℝ)*(sp2) + (1258045748295749/50000000000000 : ℝ)*(sp3) + (756534242927013/100000000000000 : ℝ)*(sp4) + (756534242927013/100000000000000 : ℝ)*(f.failure) + (314513363782409/12500000000000 : ℝ)*(f.sum) + (375021454177/105250000000000000000000000 : ℝ)*base65 + (45892379075073369/5262500000000000000000000000000 : ℝ)*base67 + (57092487518073369/5262500000000000000000000000000 : ℝ)*base69 + (7111795495864131/5262500000000000000000000000000 : ℝ)*base72 + (2661325862503/421000000000000000000000000 : ℝ)*base73 + (10688318238073369/5262500000000000000000000000000 : ℝ)*base75 + (42406608277210869/5262500000000000000000000000000 : ℝ)*base77 + (16341567677760869/5262500000000000000000000000000 : ℝ)*base79 + (3813198211617/421000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (82796991/10000000000000000000000 : ℝ)*base90 + (82796991/10000000000000000000000 : ℝ)*base92 + (82796991/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1753_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8959/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9077/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9077/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17917/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1753_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1753_box_0 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-41191841/500000000 : ℝ)*x 0 + (4235991/7812500 : ℝ)*x 1 + (216882729/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41191841/500000000 : ℝ)^5823 ≤ (2418108571523/50000000000000 : ℝ)^4799 := by
    have hnat : (41191841 : ℕ)^5823*50000000000000^4799 ≤ 2418108571523^4799*500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41191841 500000000 2418108571523 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235991/7812500 : ℝ)^5823 ≤ (47581892776319/100000000000000 : ℝ)^4799 := by
    have hnat : (4235991 : ℕ)^5823*100000000000000^4799 ≤ 47581892776319^4799*7812500^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235991 7812500 47581892776319 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216882729/400000000 : ℝ)^5823 ≤ (951637801221/2000000000000 : ℝ)^4799 := by
    have hnat : (216882729 : ℕ)^5823*2000000000000^4799 ≤ 951637801221^4799*400000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216882729 400000000 951637801221 2000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41191841/500000000 : ℝ), (4235991/7812500 : ℝ), (216882729/400000000 : ℝ)] ![(2418108571523/50000000000000 : ℝ), (47581892776319/100000000000000 : ℝ), (951637801221/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41191841/500000000 : ℝ)|^5823 ≤ (2418108571523/50000000000000 : ℝ)^4799
        have hw : |(-41191841/500000000 : ℝ)|=(41191841/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235991/7812500 : ℝ)|^5823 ≤ (47581892776319/100000000000000 : ℝ)^4799
        have hw : |(4235991/7812500 : ℝ)|=(4235991/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216882729/400000000 : ℝ)|^5823 ≤ (951637801221/2000000000000 : ℝ)^4799
        have hw : |(216882729/400000000 : ℝ)|=(216882729/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_1 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207764253/400000000 : ℝ)*x 0 + (-575240437/5000000000 : ℝ)*x 1 + (42359911/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207764253/400000000 : ℝ)^5823 ≤ (22582767927667/50000000000000 : ℝ)^4799 := by
    have hnat : (207764253 : ℕ)^5823*50000000000000^4799 ≤ 22582767927667^4799*400000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207764253 400000000 22582767927667 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (575240437/5000000000 : ℝ)^5823 ≤ (3626284994113/50000000000000 : ℝ)^4799 := by
    have hnat : (575240437 : ℕ)^5823*50000000000000^4799 ≤ 3626284994113^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575240437 5000000000 3626284994113 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42359911/78125000 : ℝ)^5823 ≤ (23790947069639/50000000000000 : ℝ)^4799 := by
    have hnat : (42359911 : ℕ)^5823*50000000000000^4799 ≤ 23790947069639^4799*78125000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42359911 78125000 23790947069639 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207764253/400000000 : ℝ), (-575240437/5000000000 : ℝ), (42359911/78125000 : ℝ)] ![(22582767927667/50000000000000 : ℝ), (3626284994113/50000000000000 : ℝ), (23790947069639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207764253/400000000 : ℝ)|^5823 ≤ (22582767927667/50000000000000 : ℝ)^4799
        have hw : |(207764253/400000000 : ℝ)|=(207764253/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-575240437/5000000000 : ℝ)|^5823 ≤ (3626284994113/50000000000000 : ℝ)^4799
        have hw : |(-575240437/5000000000 : ℝ)|=(575240437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42359911/78125000 : ℝ)|^5823 ≤ (23790947069639/50000000000000 : ℝ)^4799
        have hw : |(42359911/78125000 : ℝ)|=(42359911/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_2 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20776427/40000000 : ℝ)*x 0 + (5422068323/10000000000 : ℝ)*x 1 + (-230096137/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20776427/40000000 : ℝ)^5823 ≤ (5645692542437/12500000000000 : ℝ)^4799 := by
    have hnat : (20776427 : ℕ)^5823*12500000000000^4799 ≤ 5645692542437^4799*40000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20776427 40000000 5645692542437 12500000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422068323/10000000000 : ℝ)^5823 ≤ (9516378220913/20000000000000 : ℝ)^4799 := by
    have hnat : (5422068323 : ℕ)^5823*20000000000000^4799 ≤ 9516378220913^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422068323 10000000000 9516378220913 20000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230096137/2000000000 : ℝ)^5823 ≤ (906571067819/12500000000000 : ℝ)^4799 := by
    have hnat : (230096137 : ℕ)^5823*12500000000000^4799 ≤ 906571067819^4799*2000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230096137 2000000000 906571067819 12500000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20776427/40000000 : ℝ), (5422068323/10000000000 : ℝ), (-230096137/2000000000 : ℝ)] ![(5645692542437/12500000000000 : ℝ), (9516378220913/20000000000000 : ℝ), (906571067819/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20776427/40000000 : ℝ)|^5823 ≤ (5645692542437/12500000000000 : ℝ)^4799
        have hw : |(20776427/40000000 : ℝ)|=(20776427/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422068323/10000000000 : ℝ)|^5823 ≤ (9516378220913/20000000000000 : ℝ)^4799
        have hw : |(5422068323/10000000000 : ℝ)|=(5422068323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-230096137/2000000000 : ℝ)|^5823 ≤ (906571067819/12500000000000 : ℝ)^4799
        have hw : |(-230096137/2000000000 : ℝ)|=(230096137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_3 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1135134667/2500000000 : ℝ)*x 0 + (3790454283/10000000000 : ℝ)*x 1 + (14806463/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1135134667/2500000000 : ℝ)^5823 ≤ (7673114969423/20000000000000 : ℝ)^4799 := by
    have hnat : (1135134667 : ℕ)^5823*20000000000000^4799 ≤ 7673114969423^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135134667 2500000000 7673114969423 20000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3790454283/10000000000 : ℝ)^5823 ≤ (7704302839721/25000000000000 : ℝ)^4799 := by
    have hnat : (3790454283 : ℕ)^5823*25000000000000^4799 ≤ 7704302839721^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3790454283 10000000000 7704302839721 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14806463/39062500 : ℝ)^5823 ≤ (6163442755163/20000000000000 : ℝ)^4799 := by
    have hnat : (14806463 : ℕ)^5823*20000000000000^4799 ≤ 6163442755163^4799*39062500^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14806463 39062500 6163442755163 20000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1135134667/2500000000 : ℝ), (3790454283/10000000000 : ℝ), (14806463/39062500 : ℝ)] ![(7673114969423/20000000000000 : ℝ), (7704302839721/25000000000000 : ℝ), (6163442755163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1135134667/2500000000 : ℝ)|^5823 ≤ (7673114969423/20000000000000 : ℝ)^4799
        have hw : |(1135134667/2500000000 : ℝ)|=(1135134667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3790454283/10000000000 : ℝ)|^5823 ≤ (7704302839721/25000000000000 : ℝ)^4799
        have hw : |(3790454283/10000000000 : ℝ)|=(3790454283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14806463/39062500 : ℝ)|^5823 ≤ (6163442755163/20000000000000 : ℝ)^4799
        have hw : |(14806463/39062500 : ℝ)|=(14806463/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_4 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-406744087/2500000000 : ℝ)*x 0 + (320554903/625000000 : ℝ)*x 1 + (320554861/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406744087/2500000000 : ℝ)^5823 ≤ (11043519783999/100000000000000 : ℝ)^4799 := by
    have hnat : (406744087 : ℕ)^5823*100000000000000^4799 ≤ 11043519783999^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406744087 2500000000 11043519783999 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320554903/625000000 : ℝ)^5823 ≤ (11119560909589/25000000000000 : ℝ)^4799 := by
    have hnat : (320554903 : ℕ)^5823*25000000000000^4799 ≤ 11119560909589^4799*625000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320554903 625000000 11119560909589 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320554861/625000000 : ℝ)^5823 ≤ (22239118283599/50000000000000 : ℝ)^4799 := by
    have hnat : (320554861 : ℕ)^5823*50000000000000^4799 ≤ 22239118283599^4799*625000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320554861 625000000 22239118283599 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-406744087/2500000000 : ℝ), (320554903/625000000 : ℝ), (320554861/625000000 : ℝ)] ![(11043519783999/100000000000000 : ℝ), (11119560909589/25000000000000 : ℝ), (22239118283599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-406744087/2500000000 : ℝ)|^5823 ≤ (11043519783999/100000000000000 : ℝ)^4799
        have hw : |(-406744087/2500000000 : ℝ)|=(406744087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(320554903/625000000 : ℝ)|^5823 ≤ (11119560909589/25000000000000 : ℝ)^4799
        have hw : |(320554903/625000000 : ℝ)|=(320554903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320554861/625000000 : ℝ)|^5823 ≤ (22239118283599/50000000000000 : ℝ)^4799
        have hw : |(320554861/625000000 : ℝ)|=(320554861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_5 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695062629/5000000000 : ℝ)*x 0 + (-641593839/5000000000 : ℝ)*x 1 + (5128878311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695062629/5000000000 : ℝ)^5823 ≤ (5905246472087/12500000000000 : ℝ)^4799 := by
    have hnat : (2695062629 : ℕ)^5823*12500000000000^4799 ≤ 5905246472087^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695062629 5000000000 5905246472087 12500000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641593839/5000000000 : ℝ)^5823 ≤ (2069946502451/25000000000000 : ℝ)^4799 := by
    have hnat : (641593839 : ℕ)^5823*25000000000000^4799 ≤ 2069946502451^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641593839 5000000000 2069946502451 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128878311/10000000000 : ℝ)^5823 ≤ (22239121098383/50000000000000 : ℝ)^4799 := by
    have hnat : (5128878311 : ℕ)^5823*50000000000000^4799 ≤ 22239121098383^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128878311 10000000000 22239121098383 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695062629/5000000000 : ℝ), (-641593839/5000000000 : ℝ), (5128878311/10000000000 : ℝ)] ![(5905246472087/12500000000000 : ℝ), (2069946502451/25000000000000 : ℝ), (22239121098383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695062629/5000000000 : ℝ)|^5823 ≤ (5905246472087/12500000000000 : ℝ)^4799
        have hw : |(2695062629/5000000000 : ℝ)|=(2695062629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-641593839/5000000000 : ℝ)|^5823 ≤ (2069946502451/25000000000000 : ℝ)^4799
        have hw : |(-641593839/5000000000 : ℝ)|=(641593839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128878311/10000000000 : ℝ)|^5823 ≤ (22239121098383/50000000000000 : ℝ)^4799
        have hw : |(5128878311/10000000000 : ℝ)|=(5128878311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_6 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347531367/2500000000 : ℝ)*x 0 + (641109751/1250000000 : ℝ)*x 1 + (-6415939/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347531367/2500000000 : ℝ)^5823 ≤ (47241974009983/100000000000000 : ℝ)^4799 := by
    have hnat : (1347531367 : ℕ)^5823*100000000000000^4799 ≤ 47241974009983^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347531367 2500000000 47241974009983 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641109751/1250000000 : ℝ)^5823 ≤ (44478239008431/100000000000000 : ℝ)^4799 := by
    have hnat : (641109751 : ℕ)^5823*100000000000000^4799 ≤ 44478239008431^4799*1250000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641109751 1250000000 44478239008431 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6415939/50000000 : ℝ)^5823 ≤ (8279786964983/100000000000000 : ℝ)^4799 := by
    have hnat : (6415939 : ℕ)^5823*100000000000000^4799 ≤ 8279786964983^4799*50000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6415939 50000000 8279786964983 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347531367/2500000000 : ℝ), (641109751/1250000000 : ℝ), (-6415939/50000000 : ℝ)] ![(47241974009983/100000000000000 : ℝ), (44478239008431/100000000000000 : ℝ), (8279786964983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347531367/2500000000 : ℝ)|^5823 ≤ (47241974009983/100000000000000 : ℝ)^4799
        have hw : |(1347531367/2500000000 : ℝ)|=(1347531367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641109751/1250000000 : ℝ)|^5823 ≤ (44478239008431/100000000000000 : ℝ)^4799
        have hw : |(641109751/1250000000 : ℝ)|=(641109751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6415939/50000000 : ℝ)|^5823 ≤ (8279786964983/100000000000000 : ℝ)^4799
        have hw : |(-6415939/50000000 : ℝ)|=(6415939/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_7 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (862917059/2500000000 : ℝ)*x 0 + (2166394171/5000000000 : ℝ)*x 1 + (4332788337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862917059/2500000000 : ℝ)^5823 ≤ (2750772703643/10000000000000 : ℝ)^4799 := by
    have hnat : (862917059 : ℕ)^5823*10000000000000^4799 ≤ 2750772703643^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862917059 2500000000 2750772703643 10000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2166394171/5000000000 : ℝ)^5823 ≤ (36246136496241/100000000000000 : ℝ)^4799 := by
    have hnat : (2166394171 : ℕ)^5823*100000000000000^4799 ≤ 36246136496241^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166394171 5000000000 36246136496241 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4332788337/10000000000 : ℝ)^5823 ≤ (2265383527843/6250000000000 : ℝ)^4799 := by
    have hnat : (4332788337 : ℕ)^5823*6250000000000^4799 ≤ 2265383527843^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332788337 10000000000 2265383527843 6250000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862917059/2500000000 : ℝ), (2166394171/5000000000 : ℝ), (4332788337/10000000000 : ℝ)] ![(2750772703643/10000000000000 : ℝ), (36246136496241/100000000000000 : ℝ), (2265383527843/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862917059/2500000000 : ℝ)|^5823 ≤ (2750772703643/10000000000000 : ℝ)^4799
        have hw : |(862917059/2500000000 : ℝ)|=(862917059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2166394171/5000000000 : ℝ)|^5823 ≤ (36246136496241/100000000000000 : ℝ)^4799
        have hw : |(2166394171/5000000000 : ℝ)|=(2166394171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4332788337/10000000000 : ℝ)|^5823 ≤ (2265383527843/6250000000000 : ℝ)^4799
        have hw : |(4332788337/10000000000 : ℝ)|=(4332788337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_8 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-726116421/5000000000 : ℝ)*x 0 + (4905327873/10000000000 : ℝ)*x 1 + (5483960033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (726116421/5000000000 : ℝ)^5823 ≤ (384851687877/4000000000000 : ℝ)^4799 := by
    have hnat : (726116421 : ℕ)^5823*4000000000000^4799 ≤ 384851687877^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726116421 5000000000 384851687877 4000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4905327873/10000000000 : ℝ)^5823 ≤ (42136986410863/100000000000000 : ℝ)^4799 := by
    have hnat : (4905327873 : ℕ)^5823*100000000000000^4799 ≤ 42136986410863^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4905327873 10000000000 42136986410863 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5483960033/10000000000 : ℝ)^5823 ≤ (1507553793049/3125000000000 : ℝ)^4799 := by
    have hnat : (5483960033 : ℕ)^5823*3125000000000^4799 ≤ 1507553793049^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483960033 10000000000 1507553793049 3125000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-726116421/5000000000 : ℝ), (4905327873/10000000000 : ℝ), (5483960033/10000000000 : ℝ)] ![(384851687877/4000000000000 : ℝ), (42136986410863/100000000000000 : ℝ), (1507553793049/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-726116421/5000000000 : ℝ)|^5823 ≤ (384851687877/4000000000000 : ℝ)^4799
        have hw : |(-726116421/5000000000 : ℝ)|=(726116421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4905327873/10000000000 : ℝ)|^5823 ≤ (42136986410863/100000000000000 : ℝ)^4799
        have hw : |(4905327873/10000000000 : ℝ)|=(4905327873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5483960033/10000000000 : ℝ)|^5823 ≤ (1507553793049/3125000000000 : ℝ)^4799
        have hw : |(5483960033/10000000000 : ℝ)|=(5483960033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_9 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576398629/5000000000 : ℝ)*x 0 + (-1121070183/10000000000 : ℝ)*x 1 + (685494999/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576398629/5000000000 : ℝ)^5823 ≤ (349453560469/781250000000 : ℝ)^4799 := by
    have hnat : (2576398629 : ℕ)^5823*781250000000^4799 ≤ 349453560469^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576398629 5000000000 349453560469 781250000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121070183/10000000000 : ℝ)^5823 ≤ (3514111656559/50000000000000 : ℝ)^4799 := by
    have hnat : (1121070183 : ℕ)^5823*50000000000000^4799 ≤ 3514111656559^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121070183 10000000000 3514111656559 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685494999/1250000000 : ℝ)^5823 ≤ (48241720939937/100000000000000 : ℝ)^4799 := by
    have hnat : (685494999 : ℕ)^5823*100000000000000^4799 ≤ 48241720939937^4799*1250000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685494999 1250000000 48241720939937 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576398629/5000000000 : ℝ), (-1121070183/10000000000 : ℝ), (685494999/1250000000 : ℝ)] ![(349453560469/781250000000 : ℝ), (3514111656559/50000000000000 : ℝ), (48241720939937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576398629/5000000000 : ℝ)|^5823 ≤ (349453560469/781250000000 : ℝ)^4799
        have hw : |(2576398629/5000000000 : ℝ)|=(2576398629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1121070183/10000000000 : ℝ)|^5823 ≤ (3514111656559/50000000000000 : ℝ)^4799
        have hw : |(-1121070183/10000000000 : ℝ)|=(1121070183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685494999/1250000000 : ℝ)|^5823 ≤ (48241720939937/100000000000000 : ℝ)^4799
        have hw : |(685494999/1250000000 : ℝ)|=(685494999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_10 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152797439/10000000000 : ℝ)*x 0 + (5483959767/10000000000 : ℝ)*x 1 + (-1121070247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152797439/10000000000 : ℝ)^5823 ≤ (22365028823253/50000000000000 : ℝ)^4799 := by
    have hnat : (5152797439 : ℕ)^5823*50000000000000^4799 ≤ 22365028823253^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152797439 10000000000 22365028823253 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5483959767/10000000000 : ℝ)^5823 ≤ (24120859269151/50000000000000 : ℝ)^4799 := by
    have hnat : (5483959767 : ℕ)^5823*50000000000000^4799 ≤ 24120859269151^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483959767 10000000000 24120859269151 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121070247/10000000000 : ℝ)^5823 ≤ (175705594999/2500000000000 : ℝ)^4799 := by
    have hnat : (1121070247 : ℕ)^5823*2500000000000^4799 ≤ 175705594999^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121070247 10000000000 175705594999 2500000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152797439/10000000000 : ℝ), (5483959767/10000000000 : ℝ), (-1121070247/10000000000 : ℝ)] ![(22365028823253/50000000000000 : ℝ), (24120859269151/50000000000000 : ℝ), (175705594999/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152797439/10000000000 : ℝ)|^5823 ≤ (22365028823253/50000000000000 : ℝ)^4799
        have hw : |(5152797439/10000000000 : ℝ)|=(5152797439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5483959767/10000000000 : ℝ)|^5823 ≤ (24120859269151/50000000000000 : ℝ)^4799
        have hw : |(5483959767/10000000000 : ℝ)|=(5483959767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1121070247/10000000000 : ℝ)|^5823 ≤ (175705594999/2500000000000 : ℝ)^4799
        have hw : |(-1121070247/10000000000 : ℝ)|=(1121070247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_11 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1189959799/2500000000 : ℝ)*x 0 + (918885571/2500000000 : ℝ)*x 1 + (73510857/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1189959799/2500000000 : ℝ)^5823 ≤ (40625398622943/100000000000000 : ℝ)^4799 := by
    have hnat : (1189959799 : ℕ)^5823*100000000000000^4799 ≤ 40625398622943^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1189959799 2500000000 40625398622943 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (918885571/2500000000 : ℝ)^5823 ≤ (7421824476213/25000000000000 : ℝ)^4799 := by
    have hnat : (918885571 : ℕ)^5823*25000000000000^4799 ≤ 7421824476213^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918885571 2500000000 7421824476213 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73510857/200000000 : ℝ)^5823 ≤ (14843651725949/50000000000000 : ℝ)^4799 := by
    have hnat : (73510857 : ℕ)^5823*50000000000000^4799 ≤ 14843651725949^4799*200000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73510857 200000000 14843651725949 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1189959799/2500000000 : ℝ), (918885571/2500000000 : ℝ), (73510857/200000000 : ℝ)] ![(40625398622943/100000000000000 : ℝ), (7421824476213/25000000000000 : ℝ), (14843651725949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1189959799/2500000000 : ℝ)|^5823 ≤ (40625398622943/100000000000000 : ℝ)^4799
        have hw : |(1189959799/2500000000 : ℝ)|=(1189959799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(918885571/2500000000 : ℝ)|^5823 ≤ (7421824476213/25000000000000 : ℝ)^4799
        have hw : |(918885571/2500000000 : ℝ)|=(918885571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(73510857/200000000 : ℝ)|^5823 ≤ (14843651725949/50000000000000 : ℝ)^4799
        have hw : |(73510857/200000000 : ℝ)|=(73510857/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_12 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-246173177/2500000000 : ℝ)*x 0 + (225304077/400000000 : ℝ)*x 1 + (5098843713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246173177/2500000000 : ℝ)^5823 ≤ (6004729631043/100000000000000 : ℝ)^4799 := by
    have hnat : (246173177 : ℕ)^5823*100000000000000^4799 ≤ 6004729631043^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246173177 2500000000 6004729631043 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225304077/400000000 : ℝ)^5823 ≤ (24916435573643/50000000000000 : ℝ)^4799 := by
    have hnat : (225304077 : ℕ)^5823*50000000000000^4799 ≤ 24916435573643^4799*400000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225304077 400000000 24916435573643 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5098843713/10000000000 : ℝ)^5823 ≤ (44162399202643/100000000000000 : ℝ)^4799 := by
    have hnat : (5098843713 : ℕ)^5823*100000000000000^4799 ≤ 44162399202643^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098843713 10000000000 44162399202643 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-246173177/2500000000 : ℝ), (225304077/400000000 : ℝ), (5098843713/10000000000 : ℝ)] ![(6004729631043/100000000000000 : ℝ), (24916435573643/50000000000000 : ℝ), (44162399202643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-246173177/2500000000 : ℝ)|^5823 ≤ (6004729631043/100000000000000 : ℝ)^4799
        have hw : |(-246173177/2500000000 : ℝ)|=(246173177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225304077/400000000 : ℝ)|^5823 ≤ (24916435573643/50000000000000 : ℝ)^4799
        have hw : |(225304077/400000000 : ℝ)|=(225304077/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5098843713/10000000000 : ℝ)|^5823 ≤ (44162399202643/100000000000000 : ℝ)^4799
        have hw : |(5098843713/10000000000 : ℝ)|=(5098843713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_13 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5410279403/10000000000 : ℝ)*x 0 + (-1296129993/10000000000 : ℝ)*x 1 + (1274710591/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5410279403/10000000000 : ℝ)^5823 ≤ (949127809167/2000000000000 : ℝ)^4799 := by
    have hnat : (5410279403 : ℕ)^5823*2000000000000^4799 ≤ 949127809167^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410279403 10000000000 949127809167 2000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296129993/10000000000 : ℝ)^5823 ≤ (4190612251507/50000000000000 : ℝ)^4799 := by
    have hnat : (1296129993 : ℕ)^5823*50000000000000^4799 ≤ 4190612251507^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296129993 10000000000 4190612251507 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1274710591/2500000000 : ℝ)^5823 ≤ (11040596256373/25000000000000 : ℝ)^4799 := by
    have hnat : (1274710591 : ℕ)^5823*25000000000000^4799 ≤ 11040596256373^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274710591 2500000000 11040596256373 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5410279403/10000000000 : ℝ), (-1296129993/10000000000 : ℝ), (1274710591/2500000000 : ℝ)] ![(949127809167/2000000000000 : ℝ), (4190612251507/50000000000000 : ℝ), (11040596256373/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5410279403/10000000000 : ℝ)|^5823 ≤ (949127809167/2000000000000 : ℝ)^4799
        have hw : |(5410279403/10000000000 : ℝ)|=(5410279403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1296129993/10000000000 : ℝ)|^5823 ≤ (4190612251507/50000000000000 : ℝ)^4799
        have hw : |(-1296129993/10000000000 : ℝ)|=(1296129993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1274710591/2500000000 : ℝ)|^5823 ≤ (11040596256373/25000000000000 : ℝ)^4799
        have hw : |(1274710591/2500000000 : ℝ)|=(1274710591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_14 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5410279183/10000000000 : ℝ)*x 0 + (5098842889/10000000000 : ℝ)*x 1 + (-1296129587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5410279183/10000000000 : ℝ)^5823 ≤ (11864097029213/25000000000000 : ℝ)^4799 := by
    have hnat : (5410279183 : ℕ)^5823*25000000000000^4799 ≤ 11864097029213^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410279183 10000000000 11864097029213 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5098842889/10000000000 : ℝ)^5823 ≤ (11040597635729/25000000000000 : ℝ)^4799 := by
    have hnat : (5098842889 : ℕ)^5823*25000000000000^4799 ≤ 11040597635729^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098842889 10000000000 11040597635729 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296129587/10000000000 : ℝ)^5823 ≤ (8381221317489/100000000000000 : ℝ)^4799 := by
    have hnat : (1296129587 : ℕ)^5823*100000000000000^4799 ≤ 8381221317489^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296129587 10000000000 8381221317489 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5410279183/10000000000 : ℝ), (5098842889/10000000000 : ℝ), (-1296129587/10000000000 : ℝ)] ![(11864097029213/25000000000000 : ℝ), (11040597635729/25000000000000 : ℝ), (8381221317489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5410279183/10000000000 : ℝ)|^5823 ≤ (11864097029213/25000000000000 : ℝ)^4799
        have hw : |(5410279183/10000000000 : ℝ)|=(5410279183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5098842889/10000000000 : ℝ)|^5823 ≤ (11040597635729/25000000000000 : ℝ)^4799
        have hw : |(5098842889/10000000000 : ℝ)|=(5098842889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1296129587/10000000000 : ℝ)|^5823 ≤ (8381221317489/100000000000000 : ℝ)^4799
        have hw : |(-1296129587/10000000000 : ℝ)|=(1296129587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_box_15 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3334917461/10000000000 : ℝ)*x 0 + (2194059707/5000000000 : ℝ)*x 1 + (2194062063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3334917461/10000000000 : ℝ)^5823 ≤ (26382870238923/100000000000000 : ℝ)^4799 := by
    have hnat : (3334917461 : ℕ)^5823*100000000000000^4799 ≤ 26382870238923^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3334917461 10000000000 26382870238923 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194059707/5000000000 : ℝ)^5823 ≤ (36808540892413/100000000000000 : ℝ)^4799 := by
    have hnat : (2194059707 : ℕ)^5823*100000000000000^4799 ≤ 36808540892413^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194059707 5000000000 36808540892413 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194062063/5000000000 : ℝ)^5823 ≤ (3680858885157/10000000000000 : ℝ)^4799 := by
    have hnat : (2194062063 : ℕ)^5823*10000000000000^4799 ≤ 3680858885157^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194062063 5000000000 3680858885157 10000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3334917461/10000000000 : ℝ), (2194059707/5000000000 : ℝ), (2194062063/5000000000 : ℝ)] ![(26382870238923/100000000000000 : ℝ), (36808540892413/100000000000000 : ℝ), (3680858885157/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3334917461/10000000000 : ℝ)|^5823 ≤ (26382870238923/100000000000000 : ℝ)^4799
        have hw : |(3334917461/10000000000 : ℝ)|=(3334917461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2194059707/5000000000 : ℝ)|^5823 ≤ (36808540892413/100000000000000 : ℝ)^4799
        have hw : |(2194059707/5000000000 : ℝ)|=(2194059707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2194062063/5000000000 : ℝ)|^5823 ≤ (3680858885157/10000000000000 : ℝ)^4799
        have hw : |(2194062063/5000000000 : ℝ)|=(2194062063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1753_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17917/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9077/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6897/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2913/5000 : ℝ) ∧ (81739/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (18591/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17917/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9077/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17917/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9077/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17917/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9077/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17917/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9077/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17917/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9077/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17917/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9077/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9077/100000 : ℝ) ^ (5807/1024 : ℝ) ≤ (123196059900509/100000000000000000000 : ℝ) := by
    have hpowers : (9077/100000 : ℝ)^5807 ≤ (123196059900509/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9077 : ℕ)^5807*100000000000000000000^1024 ≤ 123196059900509^1024*100000^5807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9077 100000 123196059900509 100000000000000000000 5807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9077/100000 : ℝ)) (X := (123196059900509/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17917/100000 : ℝ) ^ (5807/1024 : ℝ) ≤ (1456408917515911/25000000000000000000 : ℝ) := by
    have hpowers : (17917/100000 : ℝ)^5807 ≤ (1456408917515911/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17917 : ℕ)^5807*25000000000000000000^1024 ≤ 1456408917515911^1024*100000^5807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17917 100000 1456408917515911 25000000000000000000 5807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17917/100000 : ℝ)) (X := (1456408917515911/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000123196059900509/50000000000000000000 : ℝ) ≤ (5000002172423581/5000000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (50000123196059900509/50000000000000000000 : ℝ)^1024 ≤ (5000002172423581/5000000000000000 : ℝ)^5807 := by
      have hnat : (50000123196059900509 : ℕ)^1024*5000000000000000^5807 ≤ 5000002172423581^5807*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000123196059900509 50000000000000000000 5000002172423581 5000000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000002172423581/5000000000000000 : ℝ)) (X := (50000123196059900509/50000000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100005948831729964153/100000000000000000000 : ℝ) ≤ (2000020979695051/2000000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (100005948831729964153/100000000000000000000 : ℝ)^1024 ≤ (2000020979695051/2000000000000000 : ℝ)^5807 := by
      have hnat : (100005948831729964153 : ℕ)^1024*2000000000000000^5807 ≤ 2000020979695051^5807*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100005948831729964153 100000000000000000000 2000020979695051 2000000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000020979695051/2000000000000000 : ℝ)) (X := (100005948831729964153/100000000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12501456408917515911/12500000000000000000 : ℝ) ≤ (2500051363025837/2500000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (12501456408917515911/12500000000000000000 : ℝ)^1024 ≤ (2500051363025837/2500000000000000 : ℝ)^5807 := by
      have hnat : (12501456408917515911 : ℕ)^1024*2500000000000000^5807 ≤ 2500051363025837^5807*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501456408917515911 12500000000000000000 2500051363025837 2500000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500051363025837/2500000000000000 : ℝ)) (X := (12501456408917515911/12500000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(123196059900509/100000000000000000000 : ℝ) ≤ ((44199106478942255879/44200000000000000000 : ℝ)+2*(100553628093/884000000000000 : ℝ)*(9077/100000 : ℝ))^(5807/1024 : ℝ) := by
    rw [show (44199106478942255879/44200000000000000000 : ℝ)+2*(100553628093/884000000000000 : ℝ)*(9077/100000 : ℝ)=(5000002172423581/5000000000000000 : ℝ) by norm_num, show 1+2*(123196059900509/100000000000000000000 : ℝ)=(50000123196059900509/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1456408917515911/25000000000000000000 : ℝ)+(123196059900509/100000000000000000000 : ℝ) ≤ ((44199106478942255879/44200000000000000000 : ℝ)+(100553628093/884000000000000 : ℝ)*((17917/100000 : ℝ)+(9077/100000 : ℝ)))^(5807/1024 : ℝ) := by
    rw [show (44199106478942255879/44200000000000000000 : ℝ)+(100553628093/884000000000000 : ℝ)*((17917/100000 : ℝ)+(9077/100000 : ℝ))=(2000020979695051/2000000000000000 : ℝ) by norm_num, show 1+(1456408917515911/25000000000000000000 : ℝ)+(123196059900509/100000000000000000000 : ℝ)=(100005948831729964153/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1456408917515911/25000000000000000000 : ℝ) ≤ ((44199106478942255879/44200000000000000000 : ℝ)+2*(100553628093/884000000000000 : ℝ)*(17917/100000 : ℝ))^(5807/1024 : ℝ) := by
    rw [show (44199106478942255879/44200000000000000000 : ℝ)+2*(100553628093/884000000000000 : ℝ)*(17917/100000 : ℝ)=(2500051363025837/2500000000000000 : ℝ) by norm_num, show 1+2*(1456408917515911/25000000000000000000 : ℝ)=(12501456408917515911/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44199106478942255879/44200000000000000000 : ℝ)*(X 1 0+X 2 0)+(100553628093/884000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (9077/100000 : ℝ)) (hi := (17917/100000 : ℝ)) (c := (44199106478942255879/44200000000000000000 : ℝ)) (alpha := (100553628093/884000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44199106478942255879/44200000000000000000 : ℝ)*(X 0 1+X 2 1)+(100553628093/884000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (9077/100000 : ℝ)) (hi := (17917/100000 : ℝ)) (c := (44199106478942255879/44200000000000000000 : ℝ)) (alpha := (100553628093/884000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44199106478942255879/44200000000000000000 : ℝ)*(X 0 2+X 1 2)+(100553628093/884000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (9077/100000 : ℝ)) (hi := (17917/100000 : ℝ)) (c := (44199106478942255879/44200000000000000000 : ℝ)) (alpha := (100553628093/884000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-41191841/500000000 : ℝ)*X 0 0+(4235991/7812500 : ℝ)*X 0 1+(216882729/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((207764253/400000000 : ℝ)*X 1 0+(-575240437/5000000000 : ℝ)*X 1 1+(42359911/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((20776427/40000000 : ℝ)*X 2 0+(5422068323/10000000000 : ℝ)*X 2 1+(-230096137/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1135134667/2500000000 : ℝ)*X 0 0+(3790454283/10000000000 : ℝ)*X 0 1+(14806463/39062500 : ℝ)*X 0 2+(1135134667/2500000000 : ℝ)*X 1 0+(3790454283/10000000000 : ℝ)*X 1 1+(14806463/39062500 : ℝ)*X 1 2+(1135134667/2500000000 : ℝ)*X 2 0+(3790454283/10000000000 : ℝ)*X 2 1+(14806463/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-406744087/2500000000 : ℝ)*X 0 0+(320554903/625000000 : ℝ)*X 0 1+(320554861/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2695062629/5000000000 : ℝ)*X 1 0+(-641593839/5000000000 : ℝ)*X 1 1+(5128878311/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1347531367/2500000000 : ℝ)*X 2 0+(641109751/1250000000 : ℝ)*X 2 1+(-6415939/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((862917059/2500000000 : ℝ)*X 0 0+(2166394171/5000000000 : ℝ)*X 0 1+(4332788337/10000000000 : ℝ)*X 0 2+(862917059/2500000000 : ℝ)*X 1 0+(2166394171/5000000000 : ℝ)*X 1 1+(4332788337/10000000000 : ℝ)*X 1 2+(862917059/2500000000 : ℝ)*X 2 0+(2166394171/5000000000 : ℝ)*X 2 1+(4332788337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-726116421/5000000000 : ℝ)*X 0 0+(4905327873/10000000000 : ℝ)*X 0 1+(5483960033/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2576398629/5000000000 : ℝ)*X 1 0+(-1121070183/10000000000 : ℝ)*X 1 1+(685494999/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5152797439/10000000000 : ℝ)*X 2 0+(5483959767/10000000000 : ℝ)*X 2 1+(-1121070247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1189959799/2500000000 : ℝ)*X 0 0+(918885571/2500000000 : ℝ)*X 0 1+(73510857/200000000 : ℝ)*X 0 2+(1189959799/2500000000 : ℝ)*X 1 0+(918885571/2500000000 : ℝ)*X 1 1+(73510857/200000000 : ℝ)*X 1 2+(1189959799/2500000000 : ℝ)*X 2 0+(918885571/2500000000 : ℝ)*X 2 1+(73510857/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-246173177/2500000000 : ℝ)*X 0 0+(225304077/400000000 : ℝ)*X 0 1+(5098843713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5410279403/10000000000 : ℝ)*X 1 0+(-1296129993/10000000000 : ℝ)*X 1 1+(1274710591/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5410279183/10000000000 : ℝ)*X 2 0+(5098842889/10000000000 : ℝ)*X 2 1+(-1296129587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3334917461/10000000000 : ℝ)*X 0 0+(2194059707/5000000000 : ℝ)*X 0 1+(2194062063/5000000000 : ℝ)*X 0 2+(3334917461/10000000000 : ℝ)*X 1 0+(2194059707/5000000000 : ℝ)*X 1 1+(2194062063/5000000000 : ℝ)*X 1 2+(3334917461/10000000000 : ℝ)*X 2 0+(2194059707/5000000000 : ℝ)*X 2 1+(2194062063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6897/10000 : ℝ) ≤ (-304835899843704947429187272880141/442000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43711827/100000000000000 : ℝ)*(lower1) + (70617081/100000000000000 : ℝ)*(lower2) + (41939641/100000000000000 : ℝ)*(lower4) + (15061957/25000000000000 : ℝ)*(lower5) + (211984934370931/20000000000000 : ℝ)*(major0) + (211984934370931/20000000000000 : ℝ)*(major1) + (211984934370931/20000000000000 : ℝ)*(major2) + (330558709472517/20000000000000 : ℝ)*(sp4) + (51649666920417/3125000000000 : ℝ)*(sp5) + (826396166983061/50000000000000 : ℝ)*(sp6) + (490044096078463/100000000000000 : ℝ)*(sp7) + (832986483/100000000000000 : ℝ)*(sp8) + (1259723931/25000000000000 : ℝ)*(sp13) + (1023191473/50000000000000 : ℝ)*(sp14) + (490044096078463/100000000000000 : ℝ)*(f.failure) + (413198595087267/25000000000000 : ℝ)*(f.sum) + (12846840933097/8840000000000000000000000000 : ℝ)*base66 + (7163948681990603349/884000000000000000000000000000000 : ℝ)*base67 + (2930787523010603349/884000000000000000000000000000000 : ℝ)*base69 + (3233640741002603349/884000000000000000000000000000000 : ℝ)*base71 + (26719706835703/8840000000000000000000000000 : ℝ)*base73 + (4567930222046603349/884000000000000000000000000000000 : ℝ)*base75 + (151598883042603349/884000000000000000000000000000000 : ℝ)*base77 + (3110271889786603349/884000000000000000000000000000000 : ℝ)*base79 + (38904604184223/8840000000000000000000000000 : ℝ)*base81 + (76892141/10000000000000000000000 : ℝ)*base90 + (76892141/10000000000000000000000 : ℝ)*base92 + (76892141/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2913/5000 : ℝ) ≤ (128760101268811876400783266554921/221000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20897791/50000000000000 : ℝ)*(upper0) + (1730973/25000000000000 : ℝ)*(lower1) + (14967079/20000000000000 : ℝ)*(upper4) + (118524434478267/10000000000000 : ℝ)*(major0) + (118524434478267/10000000000000 : ℝ)*(major1) + (118524434478267/10000000000000 : ℝ)*(major2) + (1803082846440073/100000000000000 : ℝ)*(sp0) + (28173151393449/1562500000000 : ℝ)*(sp1) + (901540890392577/50000000000000 : ℝ)*(sp2) + (34248973601987/6250000000000 : ℝ)*(sp3) + (1951568331/100000000000000 : ℝ)*(sp5) + (1859963913/100000000000000 : ℝ)*(sp6) + (80178813/12500000000000 : ℝ)*(sp7) + (397154497/50000000000000 : ℝ)*(sp8) + (68498027382787/12500000000000 : ℝ)*(f.failure) + (1803083640749067/100000000000000 : ℝ)*(f.sum) + (360393809/4420000000000000000000000000 : ℝ)*base66 + (70943950131968307/442000000000000000000000000000000 : ℝ)*base68 + (302738344178031693/442000000000000000000000000000000 : ℝ)*base69 + (857007929195968307/442000000000000000000000000000000 : ℝ)*base72 + (10827352078409/4420000000000000000000000000 : ℝ)*base74 + (2037196200894031693/442000000000000000000000000000000 : ℝ)*base75 + (401955616592031693/442000000000000000000000000000000 : ℝ)*base77 + (2330701396020031693/442000000000000000000000000000000 : ℝ)*base79 + (22276267482551/4420000000000000000000000000 : ℝ)*base81 + (15711609/1250000000000000000000 : ℝ)*base90 + (15711609/1250000000000000000000 : ℝ)*base92 + (15711609/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81739/100000 : ℝ) ≤ (451621107844043497471446513391173/552500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23799133/100000000000000 : ℝ)*(upper0) + (15498151/100000000000000 : ℝ)*(lower3) + (1255601/50000000000000 : ℝ)*(upper4) + (285411035618129/25000000000000 : ℝ)*(major0) + (285411035618129/25000000000000 : ℝ)*(major1) + (285411035618129/25000000000000 : ℝ)*(major2) + (3482224539/50000000000000 : ℝ)*(sp1) + (842063067/100000000000000 : ℝ)*(sp3) + (224114127/100000000000000 : ℝ)*(sp4) + (1728214078729447/100000000000000 : ℝ)*(sp8) + (345641606512667/20000000000000 : ℝ)*(sp9) + (1728214997012413/100000000000000 : ℝ)*(sp10) + (65978165025971/12500000000000 : ℝ)*(sp11) + (694168839/100000000000000 : ℝ)*(sp12) + (105565232454167/20000000000000 : ℝ)*(f.failure) + (1728214997012413/100000000000000 : ℝ)*(f.sum) + (9975617059103/11050000000000000000000000000 : ℝ)*base66 + (992916926525919609/1105000000000000000000000000000000 : ℝ)*base68 + (3101423649319080391/1105000000000000000000000000000000 : ℝ)*base69 + (461907838370919609/1105000000000000000000000000000000 : ℝ)*base72 + (36887857737803/11050000000000000000000000000 : ℝ)*base74 + (1264201770749080391/1105000000000000000000000000000000 : ℝ)*base75 + (1432160300705919609/1105000000000000000000000000000000 : ℝ)*base78 + (1664272460270919609/1105000000000000000000000000000000 : ℝ)*base80 + (9843497325253/11050000000000000000000000000 : ℝ)*base82 + (5334731/2000000000000000000000 : ℝ)*base89 + (5334731/2000000000000000000000 : ℝ)*base91 + (5334731/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-18591/20000 : ℝ) ≤ (-410848745596526237314846454858739/442000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131007191/100000000000000 : ℝ)*(lower3) + (118863783/100000000000000 : ℝ)*(lower4) + (15997121/6250000000000 : ℝ)*(upper5) + (239652622724851/20000000000000 : ℝ)*(major0) + (239652622724851/20000000000000 : ℝ)*(major1) + (239652622724851/20000000000000 : ℝ)*(major2) + (2761113299/100000000000000 : ℝ)*(sp4) + (43288679511/100000000000000 : ℝ)*(sp5) + (40908403457/50000000000000 : ℝ)*(sp6) + (20369527777/100000000000000 : ℝ)*(sp7) + (1873504235920041/100000000000000 : ℝ)*(sp12) + (1873463708353829/100000000000000 : ℝ)*(sp13) + (74937007209057/4000000000000 : ℝ)*(sp14) + (553982928982747/100000000000000 : ℝ)*(sp15) + (554003298510523/100000000000000 : ℝ)*(f.failure) + (93675349851667/5000000000000 : ℝ)*(f.sum) + (29889289693583/8840000000000000000000000000 : ℝ)*base65 + (11399024244384700971/884000000000000000000000000000000 : ℝ)*base68 + (984621445740700971/884000000000000000000000000000000 : ℝ)*base70 + (984200163164700971/884000000000000000000000000000000 : ℝ)*base72 + (87853708419937/8840000000000000000000000000 : ℝ)*base74 + (4274959985020700971/884000000000000000000000000000000 : ℝ)*base76 + (1170568227332700971/884000000000000000000000000000000 : ℝ)*base78 + (533011394224700971/884000000000000000000000000000000 : ℝ)*base80 + (30804219977497/8840000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (102014561/10000000000000000000000 : ℝ)*base90 + (102014561/10000000000000000000000 : ℝ)*base92 + (102014561/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1753_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17917/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9077/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6897/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2913/5000 : ℝ) else (81739/100000 : ℝ) ≤ X j i ∧ X j i ≤ (18591/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1753_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1753_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8959/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9077/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6897/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2913/5000 : ℝ) else (81739/100000 : ℝ) ≤ X j i ∧ X j i ≤ (18591/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1753_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1753_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8959/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9077/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6897/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2913/5000 : ℝ) else (81739/100000 : ℝ) ≤ X j i ∧ X j i ≤ (18591/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1753_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
