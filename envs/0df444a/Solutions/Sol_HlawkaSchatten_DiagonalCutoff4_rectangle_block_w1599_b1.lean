-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1599_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:38:30.188071+00:00
-- url     : https://prove2.me/submissions/6eb208ba-88b5-40b1-bd86-5d142219e10a

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
theorem support_rectangle_w1599_s3_0 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-173220689/1000000000 : ℝ)*x 0 + (341477/625000 : ℝ)*x 1 + (5178996261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173220689/1000000000 : ℝ)^4715 ≤ (2130067069841/20000000000000 : ℝ)^3691 := by
    have hnat : (173220689 : ℕ)^4715*20000000000000^3691 ≤ 2130067069841^3691*1000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173220689 1000000000 2130067069841 20000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341477/625000 : ℝ)^4715 ≤ (46200906662561/100000000000000 : ℝ)^3691 := by
    have hnat : (341477 : ℕ)^4715*100000000000000^3691 ≤ 46200906662561^3691*625000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341477 625000 46200906662561 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178996261/10000000000 : ℝ)^4715 ≤ (43148757969937/100000000000000 : ℝ)^3691 := by
    have hnat : (5178996261 : ℕ)^4715*100000000000000^3691 ≤ 43148757969937^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178996261 10000000000 43148757969937 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-173220689/1000000000 : ℝ), (341477/625000 : ℝ), (5178996261/10000000000 : ℝ)] ![(2130067069841/20000000000000 : ℝ), (46200906662561/100000000000000 : ℝ), (43148757969937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-173220689/1000000000 : ℝ)|^4715 ≤ (2130067069841/20000000000000 : ℝ)^3691
        have hw : |(-173220689/1000000000 : ℝ)|=(173220689/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341477/625000 : ℝ)|^4715 ≤ (46200906662561/100000000000000 : ℝ)^3691
        have hw : |(341477/625000 : ℝ)|=(341477/625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178996261/10000000000 : ℝ)|^4715 ≤ (43148757969937/100000000000000 : ℝ)^3691
        have hw : |(5178996261/10000000000 : ℝ)|=(5178996261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s3_1 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355313381/10000000000 : ℝ)*x 0 + (-375815057/2000000000 : ℝ)*x 1 + (258949813/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355313381/10000000000 : ℝ)^4715 ≤ (9006815077961/20000000000000 : ℝ)^3691 := by
    have hnat : (5355313381 : ℕ)^4715*20000000000000^3691 ≤ 9006815077961^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355313381 10000000000 9006815077961 20000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375815057/2000000000 : ℝ)^4715 ≤ (1181716663801/10000000000000 : ℝ)^3691 := by
    have hnat : (375815057 : ℕ)^4715*10000000000000^3691 ≤ 1181716663801^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375815057 2000000000 1181716663801 10000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258949813/500000000 : ℝ)^4715 ≤ (21574378979647/50000000000000 : ℝ)^3691 := by
    have hnat : (258949813 : ℕ)^4715*50000000000000^3691 ≤ 21574378979647^3691*500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258949813 500000000 21574378979647 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355313381/10000000000 : ℝ), (-375815057/2000000000 : ℝ), (258949813/500000000 : ℝ)] ![(9006815077961/20000000000000 : ℝ), (1181716663801/10000000000000 : ℝ), (21574378979647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355313381/10000000000 : ℝ)|^4715 ≤ (9006815077961/20000000000000 : ℝ)^3691
        have hw : |(5355313381/10000000000 : ℝ)|=(5355313381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-375815057/2000000000 : ℝ)|^4715 ≤ (1181716663801/10000000000000 : ℝ)^3691
        have hw : |(-375815057/2000000000 : ℝ)|=(375815057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258949813/500000000 : ℝ)|^4715 ≤ (21574378979647/50000000000000 : ℝ)^3691
        have hw : |(258949813/500000000 : ℝ)|=(258949813/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s3_2 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677656689/5000000000 : ℝ)*x 0 + (5178996263/10000000000 : ℝ)*x 1 + (-469768821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677656689/5000000000 : ℝ)^4715 ≤ (45034075357579/100000000000000 : ℝ)^3691 := by
    have hnat : (2677656689 : ℕ)^4715*100000000000000^3691 ≤ 45034075357579^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677656689 5000000000 45034075357579 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178996263/10000000000 : ℝ)^4715 ≤ (43148757991223/100000000000000 : ℝ)^3691 := by
    have hnat : (5178996263 : ℕ)^4715*100000000000000^3691 ≤ 43148757991223^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178996263 10000000000 43148757991223 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469768821/2500000000 : ℝ)^4715 ≤ (11817166629977/100000000000000 : ℝ)^3691 := by
    have hnat : (469768821 : ℕ)^4715*100000000000000^3691 ≤ 11817166629977^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469768821 2500000000 11817166629977 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677656689/5000000000 : ℝ), (5178996263/10000000000 : ℝ), (-469768821/2500000000 : ℝ)] ![(45034075357579/100000000000000 : ℝ), (43148757991223/100000000000000 : ℝ), (11817166629977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677656689/5000000000 : ℝ)|^4715 ≤ (45034075357579/100000000000000 : ℝ)^3691
        have hw : |(2677656689/5000000000 : ℝ)|=(2677656689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178996263/10000000000 : ℝ)|^4715 ≤ (43148757991223/100000000000000 : ℝ)^3691
        have hw : |(5178996263/10000000000 : ℝ)|=(5178996263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-469768821/2500000000 : ℝ)|^4715 ≤ (11817166629977/100000000000000 : ℝ)^3691
        have hw : |(-469768821/2500000000 : ℝ)|=(469768821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s3_3 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4221605373/10000000000 : ℝ)*x 0 + (777592459/2000000000 : ℝ)*x 1 + (4577289271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4221605373/10000000000 : ℝ)^4715 ≤ (33233287012237/100000000000000 : ℝ)^3691 := by
    have hnat : (4221605373 : ℕ)^4715*100000000000000^3691 ≤ 33233287012237^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221605373 10000000000 33233287012237 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777592459/2000000000 : ℝ)^4715 ≤ (14957808996367/50000000000000 : ℝ)^3691 := by
    have hnat : (777592459 : ℕ)^4715*50000000000000^3691 ≤ 14957808996367^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777592459 2000000000 14957808996367 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4577289271/10000000000 : ℝ)^4715 ≤ (18425547487893/50000000000000 : ℝ)^3691 := by
    have hnat : (4577289271 : ℕ)^4715*50000000000000^3691 ≤ 18425547487893^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4577289271 10000000000 18425547487893 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4221605373/10000000000 : ℝ), (777592459/2000000000 : ℝ), (4577289271/10000000000 : ℝ)] ![(33233287012237/100000000000000 : ℝ), (14957808996367/50000000000000 : ℝ), (18425547487893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4221605373/10000000000 : ℝ)|^4715 ≤ (33233287012237/100000000000000 : ℝ)^3691
        have hw : |(4221605373/10000000000 : ℝ)|=(4221605373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(777592459/2000000000 : ℝ)|^4715 ≤ (14957808996367/50000000000000 : ℝ)^3691
        have hw : |(777592459/2000000000 : ℝ)|=(777592459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4577289271/10000000000 : ℝ)|^4715 ≤ (18425547487893/50000000000000 : ℝ)^3691
        have hw : |(4577289271/10000000000 : ℝ)|=(4577289271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s3_4 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-866140099/5000000000 : ℝ)*x 0 + (1036222367/2000000000 : ℝ)*x 1 + (273074703/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866140099/5000000000 : ℝ)^4715 ≤ (266272778181/2500000000000 : ℝ)^3691 := by
    have hnat : (866140099 : ℕ)^4715*2500000000000^3691 ≤ 266272778181^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866140099 5000000000 266272778181 2500000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036222367/2000000000 : ℝ)^4715 ≤ (43171275107463/100000000000000 : ℝ)^3691 := by
    have hnat : (1036222367 : ℕ)^4715*100000000000000^3691 ≤ 43171275107463^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036222367 2000000000 43171275107463 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273074703/500000000 : ℝ)^4715 ≤ (1847112550137/4000000000000 : ℝ)^3691 := by
    have hnat : (273074703 : ℕ)^4715*4000000000000^3691 ≤ 1847112550137^3691*500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273074703 500000000 1847112550137 4000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-866140099/5000000000 : ℝ), (1036222367/2000000000 : ℝ), (273074703/500000000 : ℝ)] ![(266272778181/2500000000000 : ℝ), (43171275107463/100000000000000 : ℝ), (1847112550137/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-866140099/5000000000 : ℝ)|^4715 ≤ (266272778181/2500000000000 : ℝ)^3691
        have hw : |(-866140099/5000000000 : ℝ)|=(866140099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036222367/2000000000 : ℝ)|^4715 ≤ (43171275107463/100000000000000 : ℝ)^3691
        have hw : |(1036222367/2000000000 : ℝ)|=(1036222367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(273074703/500000000 : ℝ)|^4715 ≤ (1847112550137/4000000000000 : ℝ)^3691
        have hw : |(273074703/500000000 : ℝ)|=(273074703/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s3_5 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279877853/10000000000 : ℝ)*x 0 + (-1596577623/10000000000 : ℝ)*x 1 + (1092298687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279877853/10000000000 : ℝ)^4715 ≤ (176901276797/400000000000 : ℝ)^3691 := by
    have hnat : (5279877853 : ℕ)^4715*400000000000^3691 ≤ 176901276797^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279877853 10000000000 176901276797 400000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1596577623/10000000000 : ℝ)^4715 ≤ (599804611551/6250000000000 : ℝ)^3691 := by
    have hnat : (1596577623 : ℕ)^4715*6250000000000^3691 ≤ 599804611551^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596577623 10000000000 599804611551 6250000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092298687/2000000000 : ℝ)^4715 ≤ (46177807002869/100000000000000 : ℝ)^3691 := by
    have hnat : (1092298687 : ℕ)^4715*100000000000000^3691 ≤ 46177807002869^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092298687 2000000000 46177807002869 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279877853/10000000000 : ℝ), (-1596577623/10000000000 : ℝ), (1092298687/2000000000 : ℝ)] ![(176901276797/400000000000 : ℝ), (599804611551/6250000000000 : ℝ), (46177807002869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279877853/10000000000 : ℝ)|^4715 ≤ (176901276797/400000000000 : ℝ)^3691
        have hw : |(5279877853/10000000000 : ℝ)|=(5279877853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1596577623/10000000000 : ℝ)|^4715 ≤ (599804611551/6250000000000 : ℝ)^3691
        have hw : |(-1596577623/10000000000 : ℝ)|=(1596577623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092298687/2000000000 : ℝ)|^4715 ≤ (46177807002869/100000000000000 : ℝ)^3691
        have hw : |(1092298687/2000000000 : ℝ)|=(1092298687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s3_6 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055975453/2000000000 : ℝ)*x 0 + (682686757/1250000000 : ℝ)*x 1 + (-1596577567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055975453/2000000000 : ℝ)^4715 ≤ (11056328226909/25000000000000 : ℝ)^3691 := by
    have hnat : (1055975453 : ℕ)^4715*25000000000000^3691 ≤ 11056328226909^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055975453 2000000000 11056328226909 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682686757/1250000000 : ℝ)^4715 ≤ (46177813710221/100000000000000 : ℝ)^3691 := by
    have hnat : (682686757 : ℕ)^4715*100000000000000^3691 ≤ 46177813710221^3691*1250000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682686757 1250000000 46177813710221 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1596577567/10000000000 : ℝ)^4715 ≤ (9596873354819/100000000000000 : ℝ)^3691 := by
    have hnat : (1596577567 : ℕ)^4715*100000000000000^3691 ≤ 9596873354819^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596577567 10000000000 9596873354819 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055975453/2000000000 : ℝ), (682686757/1250000000 : ℝ), (-1596577567/10000000000 : ℝ)] ![(11056328226909/25000000000000 : ℝ), (46177813710221/100000000000000 : ℝ), (9596873354819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055975453/2000000000 : ℝ)|^4715 ≤ (11056328226909/25000000000000 : ℝ)^3691
        have hw : |(1055975453/2000000000 : ℝ)|=(1055975453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682686757/1250000000 : ℝ)|^4715 ≤ (46177813710221/100000000000000 : ℝ)^3691
        have hw : |(682686757/1250000000 : ℝ)|=(682686757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1596577567/10000000000 : ℝ)|^4715 ≤ (9596873354819/100000000000000 : ℝ)^3691
        have hw : |(-1596577567/10000000000 : ℝ)|=(1596577567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s3_7 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168871299/400000000 : ℝ)*x 0 + (2286082471/5000000000 : ℝ)*x 1 + (3893141019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168871299/400000000 : ℝ)^4715 ≤ (3323506799333/10000000000000 : ℝ)^3691 := by
    have hnat : (168871299 : ℕ)^4715*10000000000000^3691 ≤ 3323506799333^3691*400000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168871299 400000000 3323506799333 10000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2286082471/5000000000 : ℝ)^4715 ≤ (36798402424399/100000000000000 : ℝ)^3691 := by
    have hnat : (2286082471 : ℕ)^4715*100000000000000^3691 ≤ 36798402424399^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286082471 5000000000 36798402424399 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3893141019/10000000000 : ℝ)^4715 ≤ (468227024551/1562500000000 : ℝ)^3691 := by
    have hnat : (3893141019 : ℕ)^4715*1562500000000^3691 ≤ 468227024551^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3893141019 10000000000 468227024551 1562500000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168871299/400000000 : ℝ), (2286082471/5000000000 : ℝ), (3893141019/10000000000 : ℝ)] ![(3323506799333/10000000000000 : ℝ), (36798402424399/100000000000000 : ℝ), (468227024551/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168871299/400000000 : ℝ)|^4715 ≤ (3323506799333/10000000000000 : ℝ)^3691
        have hw : |(168871299/400000000 : ℝ)|=(168871299/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2286082471/5000000000 : ℝ)|^4715 ≤ (36798402424399/100000000000000 : ℝ)^3691
        have hw : |(2286082471/5000000000 : ℝ)|=(2286082471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3893141019/10000000000 : ℝ)|^4715 ≤ (468227024551/1562500000000 : ℝ)^3691
        have hw : |(3893141019/10000000000 : ℝ)|=(3893141019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1599_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16543/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2069/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2047/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16543/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2549/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16543/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2549/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16543/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2549/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16543/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2549/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16543/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2549/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16543/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2549/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2549/25000 : ℝ) ^ (4711/1024 : ℝ) ≤ (2742813037341797/100000000000000000000 : ℝ) := by
    have hpowers : (2549/25000 : ℝ)^4711 ≤ (2742813037341797/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2549 : ℕ)^4711*100000000000000000000^1024 ≤ 2742813037341797^1024*25000^4711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2549 25000 2742813037341797 100000000000000000000 4711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2549/25000 : ℝ)) (X := (2742813037341797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16543/100000 : ℝ) ^ (4711/1024 : ℝ) ≤ (508390929313791/2000000000000000000 : ℝ) := by
    have hpowers : (16543/100000 : ℝ)^4711 ≤ (508390929313791/2000000000000000000 : ℝ)^1024 := by
      have hnat : (16543 : ℕ)^4711*2000000000000000000^1024 ≤ 508390929313791^1024*100000^4711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16543 100000 508390929313791 2000000000000000000 4711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16543/100000 : ℝ)) (X := (508390929313791/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002742813037341797/50000000000000000000 : ℝ) ≤ (10000119234993047/10000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (50002742813037341797/50000000000000000000 : ℝ)^1024 ≤ (10000119234993047/10000000000000000 : ℝ)^4711 := by
      have hnat : (50002742813037341797 : ℕ)^1024*10000000000000000^4711 ≤ 10000119234993047^4711*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002742813037341797 50000000000000000000 10000119234993047 10000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000119234993047/10000000000000000 : ℝ)) (X := (50002742813037341797/50000000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028162359503031347/100000000000000000000 : ℝ) ≤ (5000306039891309/5000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (100028162359503031347/100000000000000000000 : ℝ)^1024 ≤ (5000306039891309/5000000000000000 : ℝ)^4711 := by
      have hnat : (100028162359503031347 : ℕ)^1024*5000000000000000^4711 ≤ 5000306039891309^4711*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028162359503031347 100000000000000000000 5000306039891309 5000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000306039891309/5000000000000000 : ℝ)) (X := (100028162359503031347/100000000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000508390929313791/1000000000000000000 : ℝ) ≤ (10001104924572189/10000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (1000508390929313791/1000000000000000000 : ℝ)^1024 ≤ (10001104924572189/10000000000000000 : ℝ)^4711 := by
      have hnat : (1000508390929313791 : ℕ)^1024*10000000000000000^4711 ≤ 10001104924572189^4711*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000508390929313791 1000000000000000000 10001104924572189 10000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001104924572189/10000000000000000 : ℝ)) (X := (1000508390929313791/1000000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2742813037341797/100000000000000000000 : ℝ) ≤ ((63460706693551937477/63470000000000000000 : ℝ)+2*(492844789571/634700000000000 : ℝ)*(2549/25000 : ℝ))^(4711/1024 : ℝ) := by
    rw [show (63460706693551937477/63470000000000000000 : ℝ)+2*(492844789571/634700000000000 : ℝ)*(2549/25000 : ℝ)=(10000119234993047/10000000000000000 : ℝ) by norm_num, show 1+2*(2742813037341797/100000000000000000000 : ℝ)=(50002742813037341797/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(508390929313791/2000000000000000000 : ℝ)+(2742813037341797/100000000000000000000 : ℝ) ≤ ((63460706693551937477/63470000000000000000 : ℝ)+(492844789571/634700000000000 : ℝ)*((16543/100000 : ℝ)+(2549/25000 : ℝ)))^(4711/1024 : ℝ) := by
    rw [show (63460706693551937477/63470000000000000000 : ℝ)+(492844789571/634700000000000 : ℝ)*((16543/100000 : ℝ)+(2549/25000 : ℝ))=(5000306039891309/5000000000000000 : ℝ) by norm_num, show 1+(508390929313791/2000000000000000000 : ℝ)+(2742813037341797/100000000000000000000 : ℝ)=(100028162359503031347/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(508390929313791/2000000000000000000 : ℝ) ≤ ((63460706693551937477/63470000000000000000 : ℝ)+2*(492844789571/634700000000000 : ℝ)*(16543/100000 : ℝ))^(4711/1024 : ℝ) := by
    rw [show (63460706693551937477/63470000000000000000 : ℝ)+2*(492844789571/634700000000000 : ℝ)*(16543/100000 : ℝ)=(10001104924572189/10000000000000000 : ℝ) by norm_num, show 1+2*(508390929313791/2000000000000000000 : ℝ)=(1000508390929313791/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (63460706693551937477/63470000000000000000 : ℝ)*(X 1 0+X 2 0)+(492844789571/634700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (2549/25000 : ℝ)) (hi := (16543/100000 : ℝ)) (c := (63460706693551937477/63470000000000000000 : ℝ)) (alpha := (492844789571/634700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (63460706693551937477/63470000000000000000 : ℝ)*(X 0 1+X 2 1)+(492844789571/634700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (2549/25000 : ℝ)) (hi := (16543/100000 : ℝ)) (c := (63460706693551937477/63470000000000000000 : ℝ)) (alpha := (492844789571/634700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (63460706693551937477/63470000000000000000 : ℝ)*(X 0 2+X 1 2)+(492844789571/634700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (2549/25000 : ℝ)) (hi := (16543/100000 : ℝ)) (c := (63460706693551937477/63470000000000000000 : ℝ)) (alpha := (492844789571/634700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-173220689/1000000000 : ℝ)*X 0 0+(341477/625000 : ℝ)*X 0 1+(5178996261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355313381/10000000000 : ℝ)*X 1 0+(-375815057/2000000000 : ℝ)*X 1 1+(258949813/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677656689/5000000000 : ℝ)*X 2 0+(5178996263/10000000000 : ℝ)*X 2 1+(-469768821/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4221605373/10000000000 : ℝ)*X 0 0+(777592459/2000000000 : ℝ)*X 0 1+(4577289271/10000000000 : ℝ)*X 0 2+(4221605373/10000000000 : ℝ)*X 1 0+(777592459/2000000000 : ℝ)*X 1 1+(4577289271/10000000000 : ℝ)*X 1 2+(4221605373/10000000000 : ℝ)*X 2 0+(777592459/2000000000 : ℝ)*X 2 1+(4577289271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-866140099/5000000000 : ℝ)*X 0 0+(1036222367/2000000000 : ℝ)*X 0 1+(273074703/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279877853/10000000000 : ℝ)*X 1 0+(-1596577623/10000000000 : ℝ)*X 1 1+(1092298687/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055975453/2000000000 : ℝ)*X 2 0+(682686757/1250000000 : ℝ)*X 2 1+(-1596577567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((168871299/400000000 : ℝ)*X 0 0+(2286082471/5000000000 : ℝ)*X 0 1+(3893141019/10000000000 : ℝ)*X 0 2+(168871299/400000000 : ℝ)*X 1 0+(2286082471/5000000000 : ℝ)*X 1 1+(3893141019/10000000000 : ℝ)*X 1 2+(168871299/400000000 : ℝ)*X 2 0+(2286082471/5000000000 : ℝ)*X 2 1+(3893141019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18387175208792023366769605347/1586750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1941448411/100000000000000 : ℝ)*(base19) + (1815570843/100000000000000 : ℝ)*(base23) + (4147337/6250000000000 : ℝ)*(lower2) + (288044439/100000000000000 : ℝ)*(upper3) + (98389233/50000000000000 : ℝ)*(upper5) + (1241004756583437/50000000000000 : ℝ)*(major0) + (1241004756583437/50000000000000 : ℝ)*(major1) + (1241004756583437/50000000000000 : ℝ)*(major2) + (1756642976621961/50000000000000 : ℝ)*(sp0) + (878326733765519/25000000000000 : ℝ)*(sp1) + (878326765234911/25000000000000 : ℝ)*(sp2) + (725349746397973/50000000000000 : ℝ)*(sp3) + (11461633283/50000000000000 : ℝ)*(sp4) + (10270762399/100000000000000 : ℝ)*(sp7) + (725354881779173/50000000000000 : ℝ)*(f.failure) + (439163609563811/12500000000000 : ℝ)*(f.sum) + (247994399925829/31735000000000000000000000000 : ℝ)*base65 + (3701765385432531551/3173500000000000000000000000000000 : ℝ)*base68 + (3636800701841031551/3173500000000000000000000000000000 : ℝ)*base70 + (19990483408906031551/3173500000000000000000000000000000 : ℝ)*base72 + (6149475283037/15867500000000000000000000000 : ℝ)*base73 + (10303552839745968449/3173500000000000000000000000000000 : ℝ)*base75 + (33656523407507968449/3173500000000000000000000000000000 : ℝ)*base77 + (8580824123139531551/3173500000000000000000000000000000 : ℝ)*base80 + (108532139717569/31735000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (44069879/5000000000000000000000 : ℝ)*base89 + (44069879/5000000000000000000000 : ℝ)*base91 + (44069879/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82965287544022775918888247/18031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1131367923/100000000000000 : ℝ)*(base19) + (193999531/25000000000000 : ℝ)*(base23) + (9488807/25000000000000 : ℝ)*(upper2) + (163003307/100000000000000 : ℝ)*(upper5) + (157477039027293/6250000000000 : ℝ)*(major0) + (157477039027293/6250000000000 : ℝ)*(major1) + (157477039027293/6250000000000 : ℝ)*(major2) + (352721899/20000000000000 : ℝ)*(sp0) + (12049088387/100000000000000 : ℝ)*(sp1) + (9944941051/100000000000000 : ℝ)*(sp2) + (445820404459313/12500000000000 : ℝ)*(sp4) + (445818977353461/12500000000000 : ℝ)*(sp5) + (3566554278344823/100000000000000 : ℝ)*(sp6) + (58908003848649/4000000000000 : ℝ)*(sp7) + (58908003848649/4000000000000 : ℝ)*(f.failure) + (1783282499641999/50000000000000 : ℝ)*(f.sum) + (50365666726093/31735000000000000000000000000 : ℝ)*base65 + (2560834643995265239/396687500000000000000000000000000 : ℝ)*base68 + (2261374821822765239/396687500000000000000000000000000 : ℝ)*base70 + (541785869791484761/396687500000000000000000000000000 : ℝ)*base71 + (130402557907937/31735000000000000000000000000 : ℝ)*base74 + (3319178727967547261/396687500000000000000000000000000 : ℝ)*base75 + (310664203759359761/396687500000000000000000000000000 : ℝ)*base77 + (1426204116106797261/396687500000000000000000000000000 : ℝ)*base79 + (15300560440299/15867500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (125373/400000000000000000000 : ℝ)*base90 + (125373/400000000000000000000 : ℝ)*base92 + (125373/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1599_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16543/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2069/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2047/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1599_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1599_s4_0 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1732358987/10000000000 : ℝ)*x 0 + (2731440453/5000000000 : ℝ)*x 1 + (1294911579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1732358987/10000000000 : ℝ)^4715 ≤ (5325764980929/50000000000000 : ℝ)^3691 := by
    have hnat : (1732358987 : ℕ)^4715*50000000000000^3691 ≤ 5325764980929^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732358987 10000000000 5325764980929 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731440453/5000000000 : ℝ)^4715 ≤ (23096396726247/50000000000000 : ℝ)^3691 := by
    have hnat : (2731440453 : ℕ)^4715*50000000000000^3691 ≤ 23096396726247^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731440453 5000000000 23096396726247 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294911579/2500000000 : ℝ)^4715 ≤ (21577838283339/50000000000000 : ℝ)^3691 := by
    have hnat : (1294911579 : ℕ)^4715*50000000000000^3691 ≤ 21577838283339^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294911579 2500000000 21577838283339 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1732358987/10000000000 : ℝ), (2731440453/5000000000 : ℝ), (1294911579/2500000000 : ℝ)] ![(5325764980929/50000000000000 : ℝ), (23096396726247/50000000000000 : ℝ), (21577838283339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1732358987/10000000000 : ℝ)|^4715 ≤ (5325764980929/50000000000000 : ℝ)^3691
        have hw : |(-1732358987/10000000000 : ℝ)|=(1732358987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731440453/5000000000 : ℝ)|^4715 ≤ (23096396726247/50000000000000 : ℝ)^3691
        have hw : |(2731440453/5000000000 : ℝ)|=(2731440453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294911579/2500000000 : ℝ)|^4715 ≤ (21577838283339/50000000000000 : ℝ)^3691
        have hw : |(1294911579/2500000000 : ℝ)|=(1294911579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s4_1 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355112877/10000000000 : ℝ)*x 0 + (-37569643/200000000 : ℝ)*x 1 + (1294911579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355112877/10000000000 : ℝ)^4715 ≤ (45031921543061/100000000000000 : ℝ)^3691 := by
    have hnat : (5355112877 : ℕ)^4715*100000000000000^3691 ≤ 45031921543061^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355112877 10000000000 45031921543061 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37569643/200000000 : ℝ)^4715 ≤ (369137558573/3125000000000 : ℝ)^3691 := by
    have hnat : (37569643 : ℕ)^4715*3125000000000^3691 ≤ 369137558573^3691*200000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37569643 200000000 369137558573 3125000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294911579/2500000000 : ℝ)^4715 ≤ (21577838283339/50000000000000 : ℝ)^3691 := by
    have hnat : (1294911579 : ℕ)^4715*50000000000000^3691 ≤ 21577838283339^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294911579 2500000000 21577838283339 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355112877/10000000000 : ℝ), (-37569643/200000000 : ℝ), (1294911579/2500000000 : ℝ)] ![(45031921543061/100000000000000 : ℝ), (369137558573/3125000000000 : ℝ), (21577838283339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355112877/10000000000 : ℝ)|^4715 ≤ (45031921543061/100000000000000 : ℝ)^3691
        have hw : |(5355112877/10000000000 : ℝ)|=(5355112877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37569643/200000000 : ℝ)|^4715 ≤ (369137558573/3125000000000 : ℝ)^3691
        have hw : |(-37569643/200000000 : ℝ)|=(37569643/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294911579/2500000000 : ℝ)|^4715 ≤ (21577838283339/50000000000000 : ℝ)^3691
        have hw : |(1294911579/2500000000 : ℝ)|=(1294911579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s4_2 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355112877/10000000000 : ℝ)*x 0 + (1294911579/2500000000 : ℝ)*x 1 + (-37569643/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355112877/10000000000 : ℝ)^4715 ≤ (45031921543061/100000000000000 : ℝ)^3691 := by
    have hnat : (5355112877 : ℕ)^4715*100000000000000^3691 ≤ 45031921543061^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355112877 10000000000 45031921543061 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294911579/2500000000 : ℝ)^4715 ≤ (21577838283339/50000000000000 : ℝ)^3691 := by
    have hnat : (1294911579 : ℕ)^4715*50000000000000^3691 ≤ 21577838283339^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294911579 2500000000 21577838283339 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37569643/200000000 : ℝ)^4715 ≤ (369137558573/3125000000000 : ℝ)^3691 := by
    have hnat : (37569643 : ℕ)^4715*3125000000000^3691 ≤ 369137558573^3691*200000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37569643 200000000 369137558573 3125000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355112877/10000000000 : ℝ), (1294911579/2500000000 : ℝ), (-37569643/200000000 : ℝ)] ![(45031921543061/100000000000000 : ℝ), (21577838283339/50000000000000 : ℝ), (369137558573/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355112877/10000000000 : ℝ)|^4715 ≤ (45031921543061/100000000000000 : ℝ)^3691
        have hw : |(5355112877/10000000000 : ℝ)|=(5355112877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294911579/2500000000 : ℝ)|^4715 ≤ (21577838283339/50000000000000 : ℝ)^3691
        have hw : |(1294911579/2500000000 : ℝ)|=(1294911579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37569643/200000000 : ℝ)|^4715 ≤ (369137558573/3125000000000 : ℝ)^3691
        have hw : |(-37569643/200000000 : ℝ)|=(37569643/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s4_3 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4221703023/10000000000 : ℝ)*x 0 + (1944824213/5000000000 : ℝ)*x 1 + (2287791061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4221703023/10000000000 : ℝ)^4715 ≤ (33234269001993/100000000000000 : ℝ)^3691 := by
    have hnat : (4221703023 : ℕ)^4715*100000000000000^3691 ≤ 33234269001993^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221703023 10000000000 33234269001993 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944824213/5000000000 : ℝ)^4715 ≤ (29932192133467/100000000000000 : ℝ)^3691 := by
    have hnat : (1944824213 : ℕ)^4715*100000000000000^3691 ≤ 29932192133467^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944824213 5000000000 29932192133467 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2287791061/5000000000 : ℝ)^4715 ≤ (115104808911/312500000000 : ℝ)^3691 := by
    have hnat : (2287791061 : ℕ)^4715*312500000000^3691 ≤ 115104808911^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287791061 5000000000 115104808911 312500000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4221703023/10000000000 : ℝ), (1944824213/5000000000 : ℝ), (2287791061/5000000000 : ℝ)] ![(33234269001993/100000000000000 : ℝ), (29932192133467/100000000000000 : ℝ), (115104808911/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4221703023/10000000000 : ℝ)|^4715 ≤ (33234269001993/100000000000000 : ℝ)^3691
        have hw : |(4221703023/10000000000 : ℝ)|=(4221703023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1944824213/5000000000 : ℝ)|^4715 ≤ (29932192133467/100000000000000 : ℝ)^3691
        have hw : |(1944824213/5000000000 : ℝ)|=(1944824213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2287791061/5000000000 : ℝ)|^4715 ≤ (115104808911/312500000000 : ℝ)^3691
        have hw : |(2287791061/5000000000 : ℝ)|=(2287791061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s4_4 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-173243111/1000000000 : ℝ)*x 0 + (5181741511/10000000000 : ℝ)*x 1 + (5460763757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173243111/1000000000 : ℝ)^4715 ≤ (5326048223187/50000000000000 : ℝ)^3691 := by
    have hnat : (173243111 : ℕ)^4715*50000000000000^3691 ≤ 5326048223187^3691*1000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173243111 1000000000 5326048223187 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181741511/10000000000 : ℝ)^4715 ≤ (43177977564259/100000000000000 : ℝ)^3691 := by
    have hnat : (5181741511 : ℕ)^4715*100000000000000^3691 ≤ 43177977564259^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181741511 10000000000 43177977564259 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460763757/10000000000 : ℝ)^4715 ≤ (23084962988587/50000000000000 : ℝ)^3691 := by
    have hnat : (5460763757 : ℕ)^4715*50000000000000^3691 ≤ 23084962988587^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460763757 10000000000 23084962988587 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-173243111/1000000000 : ℝ), (5181741511/10000000000 : ℝ), (5460763757/10000000000 : ℝ)] ![(5326048223187/50000000000000 : ℝ), (43177977564259/100000000000000 : ℝ), (23084962988587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-173243111/1000000000 : ℝ)|^4715 ≤ (5326048223187/50000000000000 : ℝ)^3691
        have hw : |(-173243111/1000000000 : ℝ)|=(173243111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181741511/10000000000 : ℝ)|^4715 ≤ (43177977564259/100000000000000 : ℝ)^3691
        have hw : |(5181741511/10000000000 : ℝ)|=(5181741511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460763757/10000000000 : ℝ)|^4715 ≤ (23084962988587/50000000000000 : ℝ)^3691
        have hw : |(5460763757/10000000000 : ℝ)|=(5460763757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s4_5 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528004949/1000000000 : ℝ)*x 0 + (-1597364817/10000000000 : ℝ)*x 1 + (136519093/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528004949/1000000000 : ℝ)^4715 ≤ (22113577863777/50000000000000 : ℝ)^3691 := by
    have hnat : (528004949 : ℕ)^4715*50000000000000^3691 ≤ 22113577863777^3691*1000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528004949 1000000000 22113577863777 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1597364817/10000000000 : ℝ)^4715 ≤ (1200364835167/12500000000000 : ℝ)^3691 := by
    have hnat : (1597364817 : ℕ)^4715*12500000000000^3691 ≤ 1200364835167^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1597364817 10000000000 1200364835167 12500000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136519093/250000000 : ℝ)^4715 ≤ (11542481394389/25000000000000 : ℝ)^3691 := by
    have hnat : (136519093 : ℕ)^4715*25000000000000^3691 ≤ 11542481394389^3691*250000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136519093 250000000 11542481394389 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528004949/1000000000 : ℝ), (-1597364817/10000000000 : ℝ), (136519093/250000000 : ℝ)] ![(22113577863777/50000000000000 : ℝ), (1200364835167/12500000000000 : ℝ), (11542481394389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528004949/1000000000 : ℝ)|^4715 ≤ (22113577863777/50000000000000 : ℝ)^3691
        have hw : |(528004949/1000000000 : ℝ)|=(528004949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1597364817/10000000000 : ℝ)|^4715 ≤ (1200364835167/12500000000000 : ℝ)^3691
        have hw : |(-1597364817/10000000000 : ℝ)|=(1597364817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136519093/250000000 : ℝ)|^4715 ≤ (11542481394389/25000000000000 : ℝ)^3691
        have hw : |(136519093/250000000 : ℝ)|=(136519093/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s4_6 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280049659/10000000000 : ℝ)*x 0 + (2730381849/5000000000 : ℝ)*x 1 + (-399341153/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280049659/10000000000 : ℝ)^4715 ≤ (22113578767937/50000000000000 : ℝ)^3691 := by
    have hnat : (5280049659 : ℕ)^4715*50000000000000^3691 ≤ 22113578767937^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280049659 10000000000 22113578767937 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730381849/5000000000 : ℝ)^4715 ≤ (9233985067989/20000000000000 : ℝ)^3691 := by
    have hnat : (2730381849 : ℕ)^4715*20000000000000^3691 ≤ 9233985067989^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730381849 5000000000 9233985067989 20000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399341153/2500000000 : ℝ)^4715 ≤ (600182319189/6250000000000 : ℝ)^3691 := by
    have hnat : (399341153 : ℕ)^4715*6250000000000^3691 ≤ 600182319189^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399341153 2500000000 600182319189 6250000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280049659/10000000000 : ℝ), (2730381849/5000000000 : ℝ), (-399341153/2500000000 : ℝ)] ![(22113578767937/50000000000000 : ℝ), (9233985067989/20000000000000 : ℝ), (600182319189/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280049659/10000000000 : ℝ)|^4715 ≤ (22113578767937/50000000000000 : ℝ)^3691
        have hw : |(5280049659/10000000000 : ℝ)|=(5280049659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730381849/5000000000 : ℝ)|^4715 ≤ (9233985067989/20000000000000 : ℝ)^3691
        have hw : |(2730381849/5000000000 : ℝ)|=(2730381849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-399341153/2500000000 : ℝ)|^4715 ≤ (600182319189/6250000000000 : ℝ)^3691
        have hw : |(-399341153/2500000000 : ℝ)|=(399341153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s4_7 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4221877969/10000000000 : ℝ)*x 0 + (914101603/2000000000 : ℝ)*x 1 + (155791027/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4221877969/10000000000 : ℝ)^4715 ≤ (33236028312987/100000000000000 : ℝ)^3691 := by
    have hnat : (4221877969 : ℕ)^4715*100000000000000^3691 ≤ 33236028312987^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221877969 10000000000 33236028312987 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914101603/2000000000 : ℝ)^4715 ≤ (36781368046891/100000000000000 : ℝ)^3691 := by
    have hnat : (914101603 : ℕ)^4715*100000000000000^3691 ≤ 36781368046891^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914101603 2000000000 36781368046891 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (155791027/400000000 : ℝ)^4715 ≤ (14991301816491/50000000000000 : ℝ)^3691 := by
    have hnat : (155791027 : ℕ)^4715*50000000000000^3691 ≤ 14991301816491^3691*400000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155791027 400000000 14991301816491 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4221877969/10000000000 : ℝ), (914101603/2000000000 : ℝ), (155791027/400000000 : ℝ)] ![(33236028312987/100000000000000 : ℝ), (36781368046891/100000000000000 : ℝ), (14991301816491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4221877969/10000000000 : ℝ)|^4715 ≤ (33236028312987/100000000000000 : ℝ)^3691
        have hw : |(4221877969/10000000000 : ℝ)|=(4221877969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(914101603/2000000000 : ℝ)|^4715 ≤ (36781368046891/100000000000000 : ℝ)^3691
        have hw : |(914101603/2000000000 : ℝ)|=(914101603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(155791027/400000000 : ℝ)|^4715 ≤ (14991301816491/50000000000000 : ℝ)^3691
        have hw : |(155791027/400000000 : ℝ)|=(155791027/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1599_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2047/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2069/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10359/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16361/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2047/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2069/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2047/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2069/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2047/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2069/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2047/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2069/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2047/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2069/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2047/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2069/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2069/20000 : ℝ) ^ (4711/1024 : ℝ) ≤ (1466064153434927/50000000000000000000 : ℝ) := by
    have hpowers : (2069/20000 : ℝ)^4711 ≤ (1466064153434927/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2069 : ℕ)^4711*50000000000000000000^1024 ≤ 1466064153434927^1024*20000^4711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2069 20000 1466064153434927 50000000000000000000 4711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2069/20000 : ℝ)) (X := (1466064153434927/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2047/12500 : ℝ) ^ (4711/1024 : ℝ) ≤ (2426026784132013/10000000000000000000 : ℝ) := by
    have hpowers : (2047/12500 : ℝ)^4711 ≤ (2426026784132013/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2047 : ℕ)^4711*10000000000000000000^1024 ≤ 2426026784132013^1024*12500^4711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2047 12500 2426026784132013 10000000000000000000 4711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2047/12500 : ℝ)) (X := (2426026784132013/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001466064153434927/25000000000000000000 : ℝ) ≤ (2000025492935577/2000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (25001466064153434927/25000000000000000000 : ℝ)^1024 ≤ (2000025492935577/2000000000000000 : ℝ)^4711 := by
      have hnat : (25001466064153434927 : ℕ)^1024*2000000000000000^4711 ≤ 2000025492935577^4711*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001466064153434927 25000000000000000000 2000025492935577 2000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000025492935577/2000000000000000 : ℝ)) (X := (25001466064153434927/25000000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125849762379630937/3125000000000000000 : ℝ) ≤ (10000591000874127/10000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (3125849762379630937/3125000000000000000 : ℝ)^1024 ≤ (10000591000874127/10000000000000000 : ℝ)^4711 := by
      have hnat : (3125849762379630937 : ℕ)^1024*10000000000000000^4711 ≤ 10000591000874127^4711*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125849762379630937 3125000000000000000 10000591000874127 10000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000591000874127/10000000000000000 : ℝ)) (X := (3125849762379630937/3125000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002426026784132013/5000000000000000000 : ℝ) ≤ (10001054537070369/10000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (5002426026784132013/5000000000000000000 : ℝ)^1024 ≤ (10001054537070369/10000000000000000 : ℝ)^4711 := by
      have hnat : (5002426026784132013 : ℕ)^1024*10000000000000000^4711 ≤ 10001054537070369^4711*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002426026784132013 5000000000000000000 10001054537070369 10000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001054537070369/10000000000000000 : ℝ)) (X := (5002426026784132013/5000000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1466064153434927/50000000000000000000 : ℝ) ≤ ((12060235635114415491/12062000000000000000 : ℝ)+2*(231768098121/301550000000000 : ℝ)*(2069/20000 : ℝ))^(4711/1024 : ℝ) := by
    rw [show (12060235635114415491/12062000000000000000 : ℝ)+2*(231768098121/301550000000000 : ℝ)*(2069/20000 : ℝ)=(2000025492935577/2000000000000000 : ℝ) by norm_num, show 1+2*(1466064153434927/50000000000000000000 : ℝ)=(25001466064153434927/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2426026784132013/10000000000000000000 : ℝ)+(1466064153434927/50000000000000000000 : ℝ) ≤ ((12060235635114415491/12062000000000000000 : ℝ)+(231768098121/301550000000000 : ℝ)*((2047/12500 : ℝ)+(2069/20000 : ℝ)))^(4711/1024 : ℝ) := by
    rw [show (12060235635114415491/12062000000000000000 : ℝ)+(231768098121/301550000000000 : ℝ)*((2047/12500 : ℝ)+(2069/20000 : ℝ))=(10000591000874127/10000000000000000 : ℝ) by norm_num, show 1+(2426026784132013/10000000000000000000 : ℝ)+(1466064153434927/50000000000000000000 : ℝ)=(3125849762379630937/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2426026784132013/10000000000000000000 : ℝ) ≤ ((12060235635114415491/12062000000000000000 : ℝ)+2*(231768098121/301550000000000 : ℝ)*(2047/12500 : ℝ))^(4711/1024 : ℝ) := by
    rw [show (12060235635114415491/12062000000000000000 : ℝ)+2*(231768098121/301550000000000 : ℝ)*(2047/12500 : ℝ)=(10001054537070369/10000000000000000 : ℝ) by norm_num, show 1+2*(2426026784132013/10000000000000000000 : ℝ)=(5002426026784132013/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12060235635114415491/12062000000000000000 : ℝ)*(X 1 0+X 2 0)+(231768098121/301550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (2069/20000 : ℝ)) (hi := (2047/12500 : ℝ)) (c := (12060235635114415491/12062000000000000000 : ℝ)) (alpha := (231768098121/301550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12060235635114415491/12062000000000000000 : ℝ)*(X 0 1+X 2 1)+(231768098121/301550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (2069/20000 : ℝ)) (hi := (2047/12500 : ℝ)) (c := (12060235635114415491/12062000000000000000 : ℝ)) (alpha := (231768098121/301550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12060235635114415491/12062000000000000000 : ℝ)*(X 0 2+X 1 2)+(231768098121/301550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (2069/20000 : ℝ)) (hi := (2047/12500 : ℝ)) (c := (12060235635114415491/12062000000000000000 : ℝ)) (alpha := (231768098121/301550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1732358987/10000000000 : ℝ)*X 0 0+(2731440453/5000000000 : ℝ)*X 0 1+(1294911579/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355112877/10000000000 : ℝ)*X 1 0+(-37569643/200000000 : ℝ)*X 1 1+(1294911579/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355112877/10000000000 : ℝ)*X 2 0+(1294911579/2500000000 : ℝ)*X 2 1+(-37569643/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4221703023/10000000000 : ℝ)*X 0 0+(1944824213/5000000000 : ℝ)*X 0 1+(2287791061/5000000000 : ℝ)*X 0 2+(4221703023/10000000000 : ℝ)*X 1 0+(1944824213/5000000000 : ℝ)*X 1 1+(2287791061/5000000000 : ℝ)*X 1 2+(4221703023/10000000000 : ℝ)*X 2 0+(1944824213/5000000000 : ℝ)*X 2 1+(2287791061/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-173243111/1000000000 : ℝ)*X 0 0+(5181741511/10000000000 : ℝ)*X 0 1+(5460763757/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528004949/1000000000 : ℝ)*X 1 0+(-1597364817/10000000000 : ℝ)*X 1 1+(136519093/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280049659/10000000000 : ℝ)*X 2 0+(2730381849/5000000000 : ℝ)*X 2 1+(-399341153/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4221877969/10000000000 : ℝ)*X 0 0+(914101603/2000000000 : ℝ)*X 0 1+(155791027/400000000 : ℝ)*X 0 2+(4221877969/10000000000 : ℝ)*X 1 0+(914101603/2000000000 : ℝ)*X 1 1+(155791027/400000000 : ℝ)*X 1 2+(4221877969/10000000000 : ℝ)*X 2 0+(914101603/2000000000 : ℝ)*X 2 1+(155791027/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (697804116374002392327294471/60310000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1933041407/100000000000000 : ℝ)*(base19) + (1808133913/100000000000000 : ℝ)*(base23) + (66889373/100000000000000 : ℝ)*(lower2) + (287453567/100000000000000 : ℝ)*(upper3) + (97834591/50000000000000 : ℝ)*(upper5) + (249428773981073/10000000000000 : ℝ)*(major0) + (249428773981073/10000000000000 : ℝ)*(major1) + (249428773981073/10000000000000 : ℝ)*(major2) + (882666477221067/25000000000000 : ℝ)*(sp0) + (220667931033721/6250000000000 : ℝ)*(sp1) + (353068702144703/10000000000000 : ℝ)*(sp2) + (36446899628503/2500000000000 : ℝ)*(sp3) + (916827867/4000000000000 : ℝ)*(sp4) + (5139612049/50000000000000 : ℝ)*(sp7) + (1457886264364217/100000000000000 : ℝ)*(f.failure) + (3530688829580943/100000000000000 : ℝ)*(f.sum) + (4616319850413/753875000000000000000000000 : ℝ)*base66 + (780783306505061843/120620000000000000000000000000000 : ℝ)*base67 + (43812460104461843/120620000000000000000000000000000 : ℝ)*base69 + (54551338193041843/120620000000000000000000000000000 : ℝ)*base71 + (5942448287721/3015500000000000000000000000 : ℝ)*base73 + (238894851977598157/120620000000000000000000000000000 : ℝ)*base76 + (108444325485481843/120620000000000000000000000000000 : ℝ)*base77 + (17778839958078157/120620000000000000000000000000000 : ℝ)*base80 + (1847559504829/3015500000000000000000000000 : ℝ)*base82 + (88044909/10000000000000000000000 : ℝ)*base90 + (88044909/10000000000000000000000 : ℝ)*base92 + (88044909/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3577841214545408095564869309/301550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (176176687/10000000000000 : ℝ)*(base19) + (135094891/6250000000000 : ℝ)*(base23) + (523867/97656250000 : ℝ)*(lower1) + (250007283/100000000000000 : ℝ)*(upper3) + (13742637/12500000000000 : ℝ)*(lower4) + (244880993/100000000000000 : ℝ)*(upper5) + (1265947912410933/50000000000000 : ℝ)*(major0) + (1265947912410933/50000000000000 : ℝ)*(major1) + (1265947912410933/50000000000000 : ℝ)*(major2) + (1080724911/20000000000000 : ℝ)*(sp2) + (3583923439825181/100000000000000 : ℝ)*(sp4) + (3583921678058311/100000000000000 : ℝ)*(sp5) + (358391587468237/10000000000000 : ℝ)*(sp6) + (739933907162011/50000000000000 : ℝ)*(sp7) + (739933907162011/50000000000000 : ℝ)*(f.failure) + (3583923439825181/100000000000000 : ℝ)*(f.sum) + (25241928843583/7538750000000000000000000000 : ℝ)*base65 + (3980242706376416897/603100000000000000000000000000000 : ℝ)*base68 + (3702222980380983103/603100000000000000000000000000000 : ℝ)*base69 + (251675081973883103/603100000000000000000000000000000 : ℝ)*base71 + (13255811539907/30155000000000000000000000000 : ℝ)*base73 + (5906674948318316897/603100000000000000000000000000000 : ℝ)*base76 + (1087143698068616897/603100000000000000000000000000000 : ℝ)*base78 + (5040917781738316897/603100000000000000000000000000000 : ℝ)*base80 + (52209615061943/7538750000000000000000000000 : ℝ)*base81 + (13308553/5000000000000000000000 : ℝ)*base89 + (13308553/5000000000000000000000 : ℝ)*base91 + (13308553/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1599_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2047/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2069/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16361/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1599_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1599_s5_0 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-866185041/5000000000 : ℝ)*x 0 + (27314083/50000000 : ℝ)*x 1 + (161865731/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866185041/5000000000 : ℝ)^4715 ≤ (1704258737/16000000000 : ℝ)^3691 := by
    have hnat : (866185041 : ℕ)^4715*16000000000^3691 ≤ 1704258737^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866185041 5000000000 1704258737 16000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27314083/50000000 : ℝ)^4715 ≤ (11548024710663/25000000000000 : ℝ)^3691 := by
    have hnat : (27314083 : ℕ)^4715*25000000000000^3691 ≤ 11548024710663^3691*50000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27314083 50000000 11548024710663 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161865731/312500000 : ℝ)^4715 ≤ (43156284043439/100000000000000 : ℝ)^3691 := by
    have hnat : (161865731 : ℕ)^4715*100000000000000^3691 ≤ 43156284043439^3691*312500000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161865731 312500000 43156284043439 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-866185041/5000000000 : ℝ), (27314083/50000000 : ℝ), (161865731/312500000 : ℝ)] ![(1704258737/16000000000 : ℝ), (11548024710663/25000000000000 : ℝ), (43156284043439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-866185041/5000000000 : ℝ)|^4715 ≤ (1704258737/16000000000 : ℝ)^3691
        have hw : |(-866185041/5000000000 : ℝ)|=(866185041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27314083/50000000 : ℝ)|^4715 ≤ (11548024710663/25000000000000 : ℝ)^3691
        have hw : |(27314083/50000000 : ℝ)|=(27314083/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161865731/312500000 : ℝ)|^4715 ≤ (43156284043439/100000000000000 : ℝ)^3691
        have hw : |(161865731/312500000 : ℝ)|=(161865731/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s5_1 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214203803/400000000 : ℝ)*x 0 + (-469607087/2500000000 : ℝ)*x 1 + (5179704889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214203803/400000000 : ℝ)^4715 ≤ (11257932578037/25000000000000 : ℝ)^3691 := by
    have hnat : (214203803 : ℕ)^4715*25000000000000^3691 ≤ 11257932578037^3691*400000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214203803 400000000 11257932578037 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469607087/2500000000 : ℝ)^4715 ≤ (11811969693517/100000000000000 : ℝ)^3691 := by
    have hnat : (469607087 : ℕ)^4715*100000000000000^3691 ≤ 11811969693517^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469607087 2500000000 11811969693517 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179704889/10000000000 : ℝ)^4715 ≤ (21578149988239/50000000000000 : ℝ)^3691 := by
    have hnat : (5179704889 : ℕ)^4715*50000000000000^3691 ≤ 21578149988239^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179704889 10000000000 21578149988239 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214203803/400000000 : ℝ), (-469607087/2500000000 : ℝ), (5179704889/10000000000 : ℝ)] ![(11257932578037/25000000000000 : ℝ), (11811969693517/100000000000000 : ℝ), (21578149988239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214203803/400000000 : ℝ)|^4715 ≤ (11257932578037/25000000000000 : ℝ)^3691
        have hw : |(214203803/400000000 : ℝ)|=(214203803/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-469607087/2500000000 : ℝ)|^4715 ≤ (11811969693517/100000000000000 : ℝ)^3691
        have hw : |(-469607087/2500000000 : ℝ)|=(469607087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179704889/10000000000 : ℝ)|^4715 ≤ (21578149988239/50000000000000 : ℝ)^3691
        have hw : |(5179704889/10000000000 : ℝ)|=(5179704889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s5_2 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669386751/1250000000 : ℝ)*x 0 + (323731629/625000000 : ℝ)*x 1 + (-1878428217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669386751/1250000000 : ℝ)^4715 ≤ (4503171885033/10000000000000 : ℝ)^3691 := by
    have hnat : (669386751 : ℕ)^4715*10000000000000^3691 ≤ 4503171885033^3691*1250000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669386751 1250000000 4503171885033 10000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323731629/625000000 : ℝ)^4715 ≤ (10789078120593/25000000000000 : ℝ)^3691 := by
    have hnat : (323731629 : ℕ)^4715*25000000000000^3691 ≤ 10789078120593^3691*625000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323731629 625000000 10789078120593 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1878428217/10000000000 : ℝ)^4715 ≤ (1476496080153/12500000000000 : ℝ)^3691 := by
    have hnat : (1878428217 : ℕ)^4715*12500000000000^3691 ≤ 1476496080153^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878428217 10000000000 1476496080153 12500000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669386751/1250000000 : ℝ), (323731629/625000000 : ℝ), (-1878428217/10000000000 : ℝ)] ![(4503171885033/10000000000000 : ℝ), (10789078120593/25000000000000 : ℝ), (1476496080153/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669386751/1250000000 : ℝ)|^4715 ≤ (4503171885033/10000000000000 : ℝ)^3691
        have hw : |(669386751/1250000000 : ℝ)|=(669386751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323731629/625000000 : ℝ)|^4715 ≤ (10789078120593/25000000000000 : ℝ)^3691
        have hw : |(323731629/625000000 : ℝ)|=(323731629/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1878428217/10000000000 : ℝ)|^4715 ≤ (1476496080153/12500000000000 : ℝ)^3691
        have hw : |(-1878428217/10000000000 : ℝ)|=(1878428217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s5_3 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055427301/2500000000 : ℝ)*x 0 + (3889799153/10000000000 : ℝ)*x 1 + (457543199/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055427301/2500000000 : ℝ)^4715 ≤ (33234331159693/100000000000000 : ℝ)^3691 := by
    have hnat : (1055427301 : ℕ)^4715*100000000000000^3691 ≤ 33234331159693^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055427301 2500000000 33234331159693 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3889799153/10000000000 : ℝ)^4715 ≤ (29933673829839/100000000000000 : ℝ)^3691 := by
    have hnat : (3889799153 : ℕ)^4715*100000000000000^3691 ≤ 29933673829839^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3889799153 10000000000 29933673829839 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457543199/1000000000 : ℝ)^4715 ≤ (9207998749549/25000000000000 : ℝ)^3691 := by
    have hnat : (457543199 : ℕ)^4715*25000000000000^3691 ≤ 9207998749549^3691*1000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457543199 1000000000 9207998749549 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055427301/2500000000 : ℝ), (3889799153/10000000000 : ℝ), (457543199/1000000000 : ℝ)] ![(33234331159693/100000000000000 : ℝ), (29933673829839/100000000000000 : ℝ), (9207998749549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055427301/2500000000 : ℝ)|^4715 ≤ (33234331159693/100000000000000 : ℝ)^3691
        have hw : |(1055427301/2500000000 : ℝ)|=(1055427301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3889799153/10000000000 : ℝ)|^4715 ≤ (29933673829839/100000000000000 : ℝ)^3691
        have hw : |(3889799153/10000000000 : ℝ)|=(3889799153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(457543199/1000000000 : ℝ)|^4715 ≤ (9207998749549/25000000000000 : ℝ)^3691
        have hw : |(457543199/1000000000 : ℝ)|=(457543199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s5_4 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-433110939/2500000000 : ℝ)*x 0 + (1036359541/2000000000 : ℝ)*x 1 + (2730349589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433110939/2500000000 : ℝ)^4715 ≤ (426087830963/4000000000000 : ℝ)^3691 := by
    have hnat : (433110939 : ℕ)^4715*4000000000000^3691 ≤ 426087830963^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433110939 2500000000 426087830963 4000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036359541/2000000000 : ℝ)^4715 ≤ (5397321965091/12500000000000 : ℝ)^3691 := by
    have hnat : (1036359541 : ℕ)^4715*12500000000000^3691 ≤ 5397321965091^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036359541 2000000000 5397321965091 12500000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730349589/5000000000 : ℝ)^4715 ≤ (23084614246751/50000000000000 : ℝ)^3691 := by
    have hnat : (2730349589 : ℕ)^4715*50000000000000^3691 ≤ 23084614246751^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730349589 5000000000 23084614246751 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-433110939/2500000000 : ℝ), (1036359541/2000000000 : ℝ), (2730349589/5000000000 : ℝ)] ![(426087830963/4000000000000 : ℝ), (5397321965091/12500000000000 : ℝ), (23084614246751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-433110939/2500000000 : ℝ)|^4715 ≤ (426087830963/4000000000000 : ℝ)^3691
        have hw : |(-433110939/2500000000 : ℝ)|=(433110939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036359541/2000000000 : ℝ)|^4715 ≤ (5397321965091/12500000000000 : ℝ)^3691
        have hw : |(1036359541/2000000000 : ℝ)|=(1036359541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730349589/5000000000 : ℝ)|^4715 ≤ (23084614246751/50000000000000 : ℝ)^3691
        have hw : |(2730349589/5000000000 : ℝ)|=(2730349589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s5_5 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280065107/10000000000 : ℝ)*x 0 + (-399358457/2500000000 : ℝ)*x 1 + (2730349589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280065107/10000000000 : ℝ)^4715 ≤ (8845464566281/20000000000000 : ℝ)^3691 := by
    have hnat : (5280065107 : ℕ)^4715*20000000000000^3691 ≤ 8845464566281^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280065107 10000000000 8845464566281 20000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399358457/2500000000 : ℝ)^4715 ≤ (9603448659177/100000000000000 : ℝ)^3691 := by
    have hnat : (399358457 : ℕ)^4715*100000000000000^3691 ≤ 9603448659177^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399358457 2500000000 9603448659177 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730349589/5000000000 : ℝ)^4715 ≤ (23084614246751/50000000000000 : ℝ)^3691 := by
    have hnat : (2730349589 : ℕ)^4715*50000000000000^3691 ≤ 23084614246751^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730349589 5000000000 23084614246751 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280065107/10000000000 : ℝ), (-399358457/2500000000 : ℝ), (2730349589/5000000000 : ℝ)] ![(8845464566281/20000000000000 : ℝ), (9603448659177/100000000000000 : ℝ), (23084614246751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280065107/10000000000 : ℝ)|^4715 ≤ (8845464566281/20000000000000 : ℝ)^3691
        have hw : |(5280065107/10000000000 : ℝ)|=(5280065107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-399358457/2500000000 : ℝ)|^4715 ≤ (9603448659177/100000000000000 : ℝ)^3691
        have hw : |(-399358457/2500000000 : ℝ)|=(399358457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730349589/5000000000 : ℝ)|^4715 ≤ (23084614246751/50000000000000 : ℝ)^3691
        have hw : |(2730349589/5000000000 : ℝ)|=(2730349589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s5_6 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280065107/10000000000 : ℝ)*x 0 + (2730349589/5000000000 : ℝ)*x 1 + (-399358457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280065107/10000000000 : ℝ)^4715 ≤ (8845464566281/20000000000000 : ℝ)^3691 := by
    have hnat : (5280065107 : ℕ)^4715*20000000000000^3691 ≤ 8845464566281^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280065107 10000000000 8845464566281 20000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730349589/5000000000 : ℝ)^4715 ≤ (23084614246751/50000000000000 : ℝ)^3691 := by
    have hnat : (2730349589 : ℕ)^4715*50000000000000^3691 ≤ 23084614246751^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730349589 5000000000 23084614246751 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399358457/2500000000 : ℝ)^4715 ≤ (9603448659177/100000000000000 : ℝ)^3691 := by
    have hnat : (399358457 : ℕ)^4715*100000000000000^3691 ≤ 9603448659177^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399358457 2500000000 9603448659177 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280065107/10000000000 : ℝ), (2730349589/5000000000 : ℝ), (-399358457/2500000000 : ℝ)] ![(8845464566281/20000000000000 : ℝ), (23084614246751/50000000000000 : ℝ), (9603448659177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280065107/10000000000 : ℝ)|^4715 ≤ (8845464566281/20000000000000 : ℝ)^3691
        have hw : |(5280065107/10000000000 : ℝ)|=(5280065107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730349589/5000000000 : ℝ)|^4715 ≤ (23084614246751/50000000000000 : ℝ)^3691
        have hw : |(2730349589/5000000000 : ℝ)|=(2730349589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-399358457/2500000000 : ℝ)|^4715 ≤ (9603448659177/100000000000000 : ℝ)^3691
        have hw : |(-399358457/2500000000 : ℝ)|=(399358457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s5_7 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263867891/625000000 : ℝ)*x 0 + (1142590213/2500000000 : ℝ)*x 1 + (3894921041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263867891/625000000 : ℝ)^4715 ≤ (830902791253/2500000000000 : ℝ)^3691 := by
    have hnat : (263867891 : ℕ)^4715*2500000000000^3691 ≤ 830902791253^3691*625000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263867891 625000000 830902791253 2500000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142590213/2500000000 : ℝ)^4715 ≤ (36779855190347/100000000000000 : ℝ)^3691 := by
    have hnat : (1142590213 : ℕ)^4715*100000000000000^3691 ≤ 36779855190347^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142590213 2500000000 36779855190347 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3894921041/10000000000 : ℝ)^4715 ≤ (5996806630201/20000000000000 : ℝ)^3691 := by
    have hnat : (3894921041 : ℕ)^4715*20000000000000^3691 ≤ 5996806630201^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3894921041 10000000000 5996806630201 20000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263867891/625000000 : ℝ), (1142590213/2500000000 : ℝ), (3894921041/10000000000 : ℝ)] ![(830902791253/2500000000000 : ℝ), (36779855190347/100000000000000 : ℝ), (5996806630201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263867891/625000000 : ℝ)|^4715 ≤ (830902791253/2500000000000 : ℝ)^3691
        have hw : |(263867891/625000000 : ℝ)|=(263867891/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1142590213/2500000000 : ℝ)|^4715 ≤ (36779855190347/100000000000000 : ℝ)^3691
        have hw : |(1142590213/2500000000 : ℝ)|=(1142590213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3894921041/10000000000 : ℝ)|^4715 ≤ (5996806630201/20000000000000 : ℝ)^3691
        have hw : |(3894921041/10000000000 : ℝ)|=(3894921041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1599_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16361/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10361/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16359/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16361/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16361/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16361/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16361/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16361/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16361/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (10359/100000 : ℝ) ^ (4711/1024 : ℝ) ≤ (368803541609609/12500000000000000000 : ℝ) := by
    have hpowers : (10359/100000 : ℝ)^4711 ≤ (368803541609609/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10359 : ℕ)^4711*12500000000000000000^1024 ≤ 368803541609609^1024*100000^4711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10359 100000 368803541609609 12500000000000000000 4711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10359/100000 : ℝ)) (X := (368803541609609/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16361/100000 : ℝ) ^ (4711/1024 : ℝ) ≤ (60395507605509/250000000000000000 : ℝ) := by
    have hpowers : (16361/100000 : ℝ)^4711 ≤ (60395507605509/250000000000000000 : ℝ)^1024 := by
      have hnat : (16361 : ℕ)^4711*250000000000000000^1024 ≤ 60395507605509^1024*100000^4711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16361 100000 60395507605509 250000000000000000 4711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16361/100000 : ℝ)) (X := (60395507605509/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250368803541609609/6250000000000000000 : ℝ) ≤ (1000012826019323/1000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (6250368803541609609/6250000000000000000 : ℝ)^1024 ≤ (1000012826019323/1000000000000000 : ℝ)^4711 := by
      have hnat : (6250368803541609609 : ℕ)^1024*1000000000000000^4711 ≤ 1000012826019323^4711*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250368803541609609 6250000000000000000 1000012826019323 1000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000012826019323/1000000000000000 : ℝ)) (X := (6250368803541609609/6250000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503388578921885059/12500000000000000000 : ℝ) ≤ (2500147295129879/2500000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (12503388578921885059/12500000000000000000 : ℝ)^1024 ≤ (2500147295129879/2500000000000000 : ℝ)^4711 := by
      have hnat : (12503388578921885059 : ℕ)^1024*2500000000000000^4711 ≤ 2500147295129879^4711*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503388578921885059 12500000000000000000 2500147295129879 2500000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500147295129879/2500000000000000 : ℝ)) (X := (12503388578921885059/12500000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (125060395507605509/125000000000000000 : ℝ) ≤ (5000525050422901/5000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (125060395507605509/125000000000000000 : ℝ)^1024 ≤ (5000525050422901/5000000000000000 : ℝ)^4711 := by
      have hnat : (125060395507605509 : ℕ)^1024*5000000000000000^4711 ≤ 5000525050422901^4711*125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125060395507605509 125000000000000000 5000525050422901 5000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000525050422901/5000000000000000 : ℝ)) (X := (125060395507605509/125000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(368803541609609/12500000000000000000 : ℝ) ≤ ((7501402558794971639/7502500000000000000 : ℝ)+2*(230460163143/300100000000000 : ℝ)*(10359/100000 : ℝ))^(4711/1024 : ℝ) := by
    rw [show (7501402558794971639/7502500000000000000 : ℝ)+2*(230460163143/300100000000000 : ℝ)*(10359/100000 : ℝ)=(1000012826019323/1000000000000000 : ℝ) by norm_num, show 1+2*(368803541609609/12500000000000000000 : ℝ)=(6250368803541609609/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(60395507605509/250000000000000000 : ℝ)+(368803541609609/12500000000000000000 : ℝ) ≤ ((7501402558794971639/7502500000000000000 : ℝ)+(230460163143/300100000000000 : ℝ)*((16361/100000 : ℝ)+(10359/100000 : ℝ)))^(4711/1024 : ℝ) := by
    rw [show (7501402558794971639/7502500000000000000 : ℝ)+(230460163143/300100000000000 : ℝ)*((16361/100000 : ℝ)+(10359/100000 : ℝ))=(2500147295129879/2500000000000000 : ℝ) by norm_num, show 1+(60395507605509/250000000000000000 : ℝ)+(368803541609609/12500000000000000000 : ℝ)=(12503388578921885059/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(60395507605509/250000000000000000 : ℝ) ≤ ((7501402558794971639/7502500000000000000 : ℝ)+2*(230460163143/300100000000000 : ℝ)*(16361/100000 : ℝ))^(4711/1024 : ℝ) := by
    rw [show (7501402558794971639/7502500000000000000 : ℝ)+2*(230460163143/300100000000000 : ℝ)*(16361/100000 : ℝ)=(5000525050422901/5000000000000000 : ℝ) by norm_num, show 1+2*(60395507605509/250000000000000000 : ℝ)=(125060395507605509/125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7501402558794971639/7502500000000000000 : ℝ)*(X 1 0+X 2 0)+(230460163143/300100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (10359/100000 : ℝ)) (hi := (16361/100000 : ℝ)) (c := (7501402558794971639/7502500000000000000 : ℝ)) (alpha := (230460163143/300100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7501402558794971639/7502500000000000000 : ℝ)*(X 0 1+X 2 1)+(230460163143/300100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (10359/100000 : ℝ)) (hi := (16361/100000 : ℝ)) (c := (7501402558794971639/7502500000000000000 : ℝ)) (alpha := (230460163143/300100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7501402558794971639/7502500000000000000 : ℝ)*(X 0 2+X 1 2)+(230460163143/300100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (10359/100000 : ℝ)) (hi := (16361/100000 : ℝ)) (c := (7501402558794971639/7502500000000000000 : ℝ)) (alpha := (230460163143/300100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-866185041/5000000000 : ℝ)*X 0 0+(27314083/50000000 : ℝ)*X 0 1+(161865731/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214203803/400000000 : ℝ)*X 1 0+(-469607087/2500000000 : ℝ)*X 1 1+(5179704889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669386751/1250000000 : ℝ)*X 2 0+(323731629/625000000 : ℝ)*X 2 1+(-1878428217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1055427301/2500000000 : ℝ)*X 0 0+(3889799153/10000000000 : ℝ)*X 0 1+(457543199/1000000000 : ℝ)*X 0 2+(1055427301/2500000000 : ℝ)*X 1 0+(3889799153/10000000000 : ℝ)*X 1 1+(457543199/1000000000 : ℝ)*X 1 2+(1055427301/2500000000 : ℝ)*X 2 0+(3889799153/10000000000 : ℝ)*X 2 1+(457543199/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-433110939/2500000000 : ℝ)*X 0 0+(1036359541/2000000000 : ℝ)*X 0 1+(2730349589/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280065107/10000000000 : ℝ)*X 1 0+(-399358457/2500000000 : ℝ)*X 1 1+(2730349589/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280065107/10000000000 : ℝ)*X 2 0+(2730349589/5000000000 : ℝ)*X 2 1+(-399358457/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((263867891/625000000 : ℝ)*X 0 0+(1142590213/2500000000 : ℝ)*X 0 1+(3894921041/10000000000 : ℝ)*X 0 2+(263867891/625000000 : ℝ)*X 1 0+(1142590213/2500000000 : ℝ)*X 1 1+(3894921041/10000000000 : ℝ)*X 1 2+(263867891/625000000 : ℝ)*X 2 0+(1142590213/2500000000 : ℝ)*X 2 1+(3894921041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112211928864342212244600633/46890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (258670951/100000000000000 : ℝ)*(base8) + (405699023/50000000000000 : ℝ)*(base21) + (59966997/25000000000000 : ℝ)*(base29) + (331169241/100000000000000 : ℝ)*(lower3) + (115373417/100000000000000 : ℝ)*(lower5) + (155960113737613/6250000000000 : ℝ)*(major0) + (623840514917449/25000000000000 : ℝ)*(major1) + (623840514917449/25000000000000 : ℝ)*(major2) + (1766089315405739/50000000000000 : ℝ)*(sp0) + (220763100382147/6250000000000 : ℝ)*(sp1) + (1766104397358153/50000000000000 : ℝ)*(sp2) + (729255240438921/50000000000000 : ℝ)*(sp3) + (30956499911/100000000000000 : ℝ)*(sp4) + (1856355423/50000000000000 : ℝ)*(sp7) + (91157137099293/6250000000000 : ℝ)*(f.failure) + (176610492299117/5000000000000 : ℝ)*(f.sum) + (10131476342083/3751250000000000000000000000 : ℝ)*base66 + (77815159230658589/187562500000000000000000000000000 : ℝ)*base68 + (412028112738596089/187562500000000000000000000000000 : ℝ)*base70 + (61872297405976457/46890625000000000000000000000000 : ℝ)*base71 + (8637178243731/3751250000000000000000000000 : ℝ)*base74 + (1378428696072503911/187562500000000000000000000000000 : ℝ)*base75 + (247630537686476457/46890625000000000000000000000000 : ℝ)*base77 + (414168944259503911/187562500000000000000000000000000 : ℝ)*base79 + (18527662181817/7502500000000000000000000000 : ℝ)*base82 + (1851361/625000000000000000000 : ℝ)*base90 + (1851361/625000000000000000000 : ℝ)*base92 + (1851361/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (493175823750226983951650001/93781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81640561/10000000000000 : ℝ)*(base19) + (442276007/50000000000000 : ℝ)*(base23) + (260166783/100000000000000 : ℝ)*(lower1) + (110424279/100000000000000 : ℝ)*(upper3) + (15328977/50000000000000 : ℝ)*(lower4) + (108950209/100000000000000 : ℝ)*(upper5) + (1266499709747003/50000000000000 : ℝ)*(major0) + (1266499709747003/50000000000000 : ℝ)*(major1) + (1266499709747003/50000000000000 : ℝ)*(major2) + (177391319/25000000000000 : ℝ)*(sp2) + (3585485809310771/100000000000000 : ℝ)*(sp4) + (89637124822629/2500000000000 : ℝ)*(sp5) + (1792742107596741/50000000000000 : ℝ)*(sp6) + (74025642719213/5000000000000 : ℝ)*(sp7) + (74025642719213/5000000000000 : ℝ)*(f.failure) + (3585485809310771/100000000000000 : ℝ)*(f.sum) + (3310010406281/7502500000000000000000000000 : ℝ)*base66 + (568500705873402083/375125000000000000000000000000000 : ℝ)*base68 + (734499424148722917/375125000000000000000000000000000 : ℝ)*base69 + (53083684324027083/375125000000000000000000000000000 : ℝ)*base72 + (11825365582171/7502500000000000000000000000 : ℝ)*base74 + (10931029880631527083/375125000000000000000000000000000 : ℝ)*base76 + (1357860963406777083/375125000000000000000000000000000 : ℝ)*base78 + (5958976021611527083/375125000000000000000000000000000 : ℝ)*base80 + (23306258511251/7502500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (1262799/500000000000000000000 : ℝ)*base89 + (1262799/500000000000000000000 : ℝ)*base91 + (1262799/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1599_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16361/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1599_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1599_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16543/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1599_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1599_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1599_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16543/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1599_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
