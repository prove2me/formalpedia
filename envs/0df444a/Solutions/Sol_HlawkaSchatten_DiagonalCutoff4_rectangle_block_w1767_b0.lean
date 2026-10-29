-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1767_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:30:19.004245+00:00
-- url     : https://prove2.me/submissions/859bbfae-c178-424a-bf99-d00a3ce74697

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
theorem support_rectangle_w1767_s0_0 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-13752299/125000000 : ℝ)*x 0 + (5581739757/10000000000 : ℝ)*x 1 + (1000225109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13752299/125000000 : ℝ)^6047 ≤ (876932730033/12500000000000 : ℝ)^5023 := by
    have hnat : (13752299 : ℕ)^6047*12500000000000^5023 ≤ 876932730033^5023*125000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13752299 125000000 876932730033 12500000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5581739757/10000000000 : ℝ)^6047 ≤ (24780808419813/50000000000000 : ℝ)^5023 := by
    have hnat : (5581739757 : ℕ)^6047*50000000000000^5023 ≤ 24780808419813^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5581739757 10000000000 24780808419813 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000225109/2000000000 : ℝ)^6047 ≤ (2171146065831/5000000000000 : ℝ)^5023 := by
    have hnat : (1000225109 : ℕ)^6047*5000000000000^5023 ≤ 2171146065831^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000225109 2000000000 2171146065831 5000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13752299/125000000 : ℝ), (5581739757/10000000000 : ℝ), (1000225109/2000000000 : ℝ)] ![(876932730033/12500000000000 : ℝ), (24780808419813/50000000000000 : ℝ), (2171146065831/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13752299/125000000 : ℝ)|^6047 ≤ (876932730033/12500000000000 : ℝ)^5023
        have hw : |(-13752299/125000000 : ℝ)|=(13752299/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5581739757/10000000000 : ℝ)|^6047 ≤ (24780808419813/50000000000000 : ℝ)^5023
        have hw : |(5581739757/10000000000 : ℝ)|=(5581739757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1000225109/2000000000 : ℝ)|^6047 ≤ (2171146065831/5000000000000 : ℝ)^5023
        have hw : |(1000225109/2000000000 : ℝ)|=(1000225109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s0_1 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334553119/625000000 : ℝ)*x 0 + (-704647279/5000000000 : ℝ)*x 1 + (5001125019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334553119/625000000 : ℝ)^6047 ≤ (47125265609287/100000000000000 : ℝ)^5023 := by
    have hnat : (334553119 : ℕ)^6047*100000000000000^5023 ≤ 47125265609287^5023*625000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334553119 625000000 47125265609287 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (704647279/5000000000 : ℝ)^6047 ≤ (9451818552287/100000000000000 : ℝ)^5023 := by
    have hnat : (704647279 : ℕ)^6047*100000000000000^5023 ≤ 9451818552287^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704647279 5000000000 9451818552287 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5001125019/10000000000 : ℝ)^6047 ≤ (8684583163701/20000000000000 : ℝ)^5023 := by
    have hnat : (5001125019 : ℕ)^6047*20000000000000^5023 ≤ 8684583163701^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001125019 10000000000 8684583163701 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334553119/625000000 : ℝ), (-704647279/5000000000 : ℝ), (5001125019/10000000000 : ℝ)] ![(47125265609287/100000000000000 : ℝ), (9451818552287/100000000000000 : ℝ), (8684583163701/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334553119/625000000 : ℝ)|^6047 ≤ (47125265609287/100000000000000 : ℝ)^5023
        have hw : |(334553119/625000000 : ℝ)|=(334553119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-704647279/5000000000 : ℝ)|^6047 ≤ (9451818552287/100000000000000 : ℝ)^5023
        have hw : |(-704647279/5000000000 : ℝ)|=(704647279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5001125019/10000000000 : ℝ)|^6047 ≤ (8684583163701/20000000000000 : ℝ)^5023
        have hw : |(5001125019/10000000000 : ℝ)|=(5001125019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s0_2 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352846389/10000000000 : ℝ)*x 0 + (5001127371/10000000000 : ℝ)*x 1 + (-5505063/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352846389/10000000000 : ℝ)^6047 ≤ (9425045671093/20000000000000 : ℝ)^5023 := by
    have hnat : (5352846389 : ℕ)^6047*20000000000000^5023 ≤ 9425045671093^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352846389 10000000000 9425045671093 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5001127371/10000000000 : ℝ)^6047 ≤ (43422940403233/100000000000000 : ℝ)^5023 := by
    have hnat : (5001127371 : ℕ)^6047*100000000000000^5023 ≤ 43422940403233^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001127371 10000000000 43422940403233 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505063/39062500 : ℝ)^6047 ≤ (9451831228517/100000000000000 : ℝ)^5023 := by
    have hnat : (5505063 : ℕ)^6047*100000000000000^5023 ≤ 9451831228517^5023*39062500^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505063 39062500 9451831228517 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352846389/10000000000 : ℝ), (5001127371/10000000000 : ℝ), (-5505063/39062500 : ℝ)] ![(9425045671093/20000000000000 : ℝ), (43422940403233/100000000000000 : ℝ), (9451831228517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352846389/10000000000 : ℝ)|^6047 ≤ (9425045671093/20000000000000 : ℝ)^5023
        have hw : |(5352846389/10000000000 : ℝ)|=(5352846389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5001127371/10000000000 : ℝ)|^6047 ≤ (43422940403233/100000000000000 : ℝ)^5023
        have hw : |(5001127371/10000000000 : ℝ)|=(5001127371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5505063/39062500 : ℝ)|^6047 ≤ (9451831228517/100000000000000 : ℝ)^5023
        have hw : |(-5505063/39062500 : ℝ)|=(5505063/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s0_3 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3953070997/10000000000 : ℝ)*x 0 + (2998924509/10000000000 : ℝ)*x 1 + (2519689461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3953070997/10000000000 : ℝ)^6047 ≤ (8179086724671/25000000000000 : ℝ)^5023 := by
    have hnat : (3953070997 : ℕ)^6047*25000000000000^5023 ≤ 8179086724671^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3953070997 10000000000 8179086724671 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2998924509/10000000000 : ℝ)^6047 ≤ (23460569963519/100000000000000 : ℝ)^5023 := by
    have hnat : (2998924509 : ℕ)^6047*100000000000000^5023 ≤ 23460569963519^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2998924509 10000000000 23460569963519 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2519689461/5000000000 : ℝ)^6047 ≤ (43823083127943/100000000000000 : ℝ)^5023 := by
    have hnat : (2519689461 : ℕ)^6047*100000000000000^5023 ≤ 43823083127943^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519689461 5000000000 43823083127943 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3953070997/10000000000 : ℝ), (2998924509/10000000000 : ℝ), (2519689461/5000000000 : ℝ)] ![(8179086724671/25000000000000 : ℝ), (23460569963519/100000000000000 : ℝ), (43823083127943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3953070997/10000000000 : ℝ)|^6047 ≤ (8179086724671/25000000000000 : ℝ)^5023
        have hw : |(3953070997/10000000000 : ℝ)|=(3953070997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2998924509/10000000000 : ℝ)|^6047 ≤ (23460569963519/100000000000000 : ℝ)^5023
        have hw : |(2998924509/10000000000 : ℝ)|=(2998924509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2519689461/5000000000 : ℝ)|^6047 ≤ (43823083127943/100000000000000 : ℝ)^5023
        have hw : |(2519689461/5000000000 : ℝ)|=(2519689461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s0_4 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1101239941/10000000000 : ℝ)*x 0 + (626941013/1250000000 : ℝ)*x 1 + (1113377899/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101239941/10000000000 : ℝ)^6047 ≤ (7023569262597/100000000000000 : ℝ)^5023 := by
    have hnat : (1101239941 : ℕ)^6047*100000000000000^5023 ≤ 7023569262597^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101239941 10000000000 7023569262597 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626941013/1250000000 : ℝ)^6047 ≤ (4357351095983/10000000000000 : ℝ)^5023 := by
    have hnat : (626941013 : ℕ)^6047*10000000000000^5023 ≤ 4357351095983^5023*1250000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626941013 1250000000 4357351095983 10000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113377899/2000000000 : ℝ)^6047 ≤ (49402919767927/100000000000000 : ℝ)^5023 := by
    have hnat : (1113377899 : ℕ)^6047*100000000000000^5023 ≤ 49402919767927^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113377899 2000000000 49402919767927 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1101239941/10000000000 : ℝ), (626941013/1250000000 : ℝ), (1113377899/2000000000 : ℝ)] ![(7023569262597/100000000000000 : ℝ), (4357351095983/10000000000000 : ℝ), (49402919767927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1101239941/10000000000 : ℝ)|^6047 ≤ (7023569262597/100000000000000 : ℝ)^5023
        have hw : |(-1101239941/10000000000 : ℝ)|=(1101239941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(626941013/1250000000 : ℝ)|^6047 ≤ (4357351095983/10000000000000 : ℝ)^5023
        have hw : |(626941013/1250000000 : ℝ)|=(626941013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1113377899/2000000000 : ℝ)|^6047 ≤ (49402919767927/100000000000000 : ℝ)^5023
        have hw : |(1113377899/2000000000 : ℝ)|=(1113377899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s0_5 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039842317/2000000000 : ℝ)*x 0 + (-843532199/10000000000 : ℝ)*x 1 + (1113377899/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039842317/2000000000 : ℝ)^6047 ≤ (11375431586383/25000000000000 : ℝ)^5023 := by
    have hnat : (1039842317 : ℕ)^6047*25000000000000^5023 ≤ 11375431586383^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039842317 2000000000 11375431586383 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (843532199/10000000000 : ℝ)^6047 ≤ (5095353877679/100000000000000 : ℝ)^5023 := by
    have hnat : (843532199 : ℕ)^6047*100000000000000^5023 ≤ 5095353877679^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843532199 10000000000 5095353877679 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113377899/2000000000 : ℝ)^6047 ≤ (49402919767927/100000000000000 : ℝ)^5023 := by
    have hnat : (1113377899 : ℕ)^6047*100000000000000^5023 ≤ 49402919767927^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113377899 2000000000 49402919767927 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039842317/2000000000 : ℝ), (-843532199/10000000000 : ℝ), (1113377899/2000000000 : ℝ)] ![(11375431586383/25000000000000 : ℝ), (5095353877679/100000000000000 : ℝ), (49402919767927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039842317/2000000000 : ℝ)|^6047 ≤ (11375431586383/25000000000000 : ℝ)^5023
        have hw : |(1039842317/2000000000 : ℝ)|=(1039842317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-843532199/10000000000 : ℝ)|^6047 ≤ (5095353877679/100000000000000 : ℝ)^5023
        have hw : |(-843532199/10000000000 : ℝ)|=(843532199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1113377899/2000000000 : ℝ)|^6047 ≤ (49402919767927/100000000000000 : ℝ)^5023
        have hw : |(1113377899/2000000000 : ℝ)|=(1113377899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s0_6 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199211891/10000000000 : ℝ)*x 0 + (5566889417/10000000000 : ℝ)*x 1 + (-843531869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199211891/10000000000 : ℝ)^6047 ≤ (11375432392371/25000000000000 : ℝ)^5023 := by
    have hnat : (5199211891 : ℕ)^6047*25000000000000^5023 ≤ 11375432392371^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199211891 10000000000 11375432392371 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5566889417/10000000000 : ℝ)^6047 ≤ (3087682433413/6250000000000 : ℝ)^5023 := by
    have hnat : (5566889417 : ℕ)^6047*6250000000000^5023 ≤ 3087682433413^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5566889417 10000000000 3087682433413 6250000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (843531869/10000000000 : ℝ)^6047 ≤ (5095351477943/100000000000000 : ℝ)^5023 := by
    have hnat : (843531869 : ℕ)^6047*100000000000000^5023 ≤ 5095351477943^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843531869 10000000000 5095351477943 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199211891/10000000000 : ℝ), (5566889417/10000000000 : ℝ), (-843531869/10000000000 : ℝ)] ![(11375432392371/25000000000000 : ℝ), (3087682433413/6250000000000 : ℝ), (5095351477943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199211891/10000000000 : ℝ)|^6047 ≤ (11375432392371/25000000000000 : ℝ)^5023
        have hw : |(5199211891/10000000000 : ℝ)|=(5199211891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5566889417/10000000000 : ℝ)|^6047 ≤ (3087682433413/6250000000000 : ℝ)^5023
        have hw : |(5566889417/10000000000 : ℝ)|=(5566889417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-843531869/10000000000 : ℝ)|^6047 ≤ (5095351477943/100000000000000 : ℝ)^5023
        have hw : |(-843531869/10000000000 : ℝ)|=(843531869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s0_7 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3956778697/10000000000 : ℝ)*x 0 + (4988767729/10000000000 : ℝ)*x 1 + (3051111717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3956778697/10000000000 : ℝ)^6047 ≤ (2047080729869/6250000000000 : ℝ)^5023 := by
    have hnat : (3956778697 : ℕ)^6047*6250000000000^5023 ≤ 2047080729869^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3956778697 10000000000 2047080729869 6250000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4988767729/10000000000 : ℝ)^6047 ≤ (43293781453041/100000000000000 : ℝ)^5023 := by
    have hnat : (4988767729 : ℕ)^6047*100000000000000^5023 ≤ 43293781453041^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988767729 10000000000 43293781453041 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3051111717/10000000000 : ℝ)^6047 ≤ (11976463429799/50000000000000 : ℝ)^5023 := by
    have hnat : (3051111717 : ℕ)^6047*50000000000000^5023 ≤ 11976463429799^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3051111717 10000000000 11976463429799 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3956778697/10000000000 : ℝ), (4988767729/10000000000 : ℝ), (3051111717/10000000000 : ℝ)] ![(2047080729869/6250000000000 : ℝ), (43293781453041/100000000000000 : ℝ), (11976463429799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3956778697/10000000000 : ℝ)|^6047 ≤ (2047080729869/6250000000000 : ℝ)^5023
        have hw : |(3956778697/10000000000 : ℝ)|=(3956778697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4988767729/10000000000 : ℝ)|^6047 ≤ (43293781453041/100000000000000 : ℝ)^5023
        have hw : |(4988767729/10000000000 : ℝ)|=(4988767729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3051111717/10000000000 : ℝ)|^6047 ≤ (11976463429799/50000000000000 : ℝ)^5023
        have hw : |(3051111717/10000000000 : ℝ)|=(3051111717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1767_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3669/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9973/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (6031/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^6031 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^6031*1^1024 ≤ 0^1024*1^6031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 6031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (6031/1024 : ℝ) ≤ (453182623982547531/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^6031 ≤ (453182623982547531/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^6031*100000000000000000000^1024 ≤ 453182623982547531^1024*5^6031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 453182623982547531 100000000000000000000 6031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (453182623982547531/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^6031 := by
      have hnat : (1 : ℕ)^1024*1^6031 ≤ 1^6031*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100453182623982547531/100000000000000000000 : ℝ) ≤ (2001536025309041/2000000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (100453182623982547531/100000000000000000000 : ℝ)^1024 ≤ (2001536025309041/2000000000000000 : ℝ)^6031 := by
      have hnat : (100453182623982547531 : ℕ)^1024*2000000000000000^6031 ≤ 2001536025309041^6031*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100453182623982547531 100000000000000000000 2001536025309041 2000000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001536025309041/2000000000000000 : ℝ)) (X := (100453182623982547531/100000000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50453182623982547531/50000000000000000000 : ℝ) ≤ (1001536025309041/1000000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (50453182623982547531/50000000000000000000 : ℝ)^1024 ≤ (1001536025309041/1000000000000000 : ℝ)^6031 := by
      have hnat : (50453182623982547531 : ℕ)^1024*1000000000000000^6031 ≤ 1001536025309041^6031*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50453182623982547531 50000000000000000000 1001536025309041 1000000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001536025309041/1000000000000000 : ℝ)) (X := (50453182623982547531/50000000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1536025309041/800000000000000 : ℝ)*(0 : ℝ))^(6031/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1536025309041/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(453182623982547531/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1536025309041/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(6031/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1536025309041/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2001536025309041/2000000000000000 : ℝ) by norm_num, show 1+(453182623982547531/100000000000000000000 : ℝ)+(0 : ℝ)=(100453182623982547531/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(453182623982547531/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1536025309041/800000000000000 : ℝ)*(2/5 : ℝ))^(6031/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1536025309041/800000000000000 : ℝ)*(2/5 : ℝ)=(1001536025309041/1000000000000000 : ℝ) by norm_num, show 1+2*(453182623982547531/100000000000000000000 : ℝ)=(50453182623982547531/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1536025309041/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1536025309041/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1536025309041/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1536025309041/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1536025309041/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1536025309041/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-13752299/125000000 : ℝ)*X 0 0+(5581739757/10000000000 : ℝ)*X 0 1+(1000225109/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334553119/625000000 : ℝ)*X 1 0+(-704647279/5000000000 : ℝ)*X 1 1+(5001125019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352846389/10000000000 : ℝ)*X 2 0+(5001127371/10000000000 : ℝ)*X 2 1+(-5505063/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3953070997/10000000000 : ℝ)*X 0 0+(2998924509/10000000000 : ℝ)*X 0 1+(2519689461/5000000000 : ℝ)*X 0 2+(3953070997/10000000000 : ℝ)*X 1 0+(2998924509/10000000000 : ℝ)*X 1 1+(2519689461/5000000000 : ℝ)*X 1 2+(3953070997/10000000000 : ℝ)*X 2 0+(2998924509/10000000000 : ℝ)*X 2 1+(2519689461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1101239941/10000000000 : ℝ)*X 0 0+(626941013/1250000000 : ℝ)*X 0 1+(1113377899/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1039842317/2000000000 : ℝ)*X 1 0+(-843532199/10000000000 : ℝ)*X 1 1+(1113377899/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5199211891/10000000000 : ℝ)*X 2 0+(5566889417/10000000000 : ℝ)*X 2 1+(-843531869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3956778697/10000000000 : ℝ)*X 0 0+(4988767729/10000000000 : ℝ)*X 0 1+(3051111717/10000000000 : ℝ)*X 0 2+(3956778697/10000000000 : ℝ)*X 1 0+(4988767729/10000000000 : ℝ)*X 1 1+(3051111717/10000000000 : ℝ)*X 1 2+(3956778697/10000000000 : ℝ)*X 2 0+(4988767729/10000000000 : ℝ)*X 2 1+(3051111717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24024738784954927460907/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4881789/1000000000000 : ℝ)*(base1) + (520545921/25000000000000 : ℝ)*(base19) + (2700671/312500000000 : ℝ)*(base23) + (25239607/5000000000000 : ℝ)*(upper3) + (138276171909703/12500000000000 : ℝ)*(major0) + (138276171909703/12500000000000 : ℝ)*(major1) + (138276171909703/12500000000000 : ℝ)*(major2) + (861162770712459/50000000000000 : ℝ)*(sp0) + (430581632388239/25000000000000 : ℝ)*(sp1) + (1722324716802737/100000000000000 : ℝ)*(sp2) + (490087500582527/100000000000000 : ℝ)*(sp3) + (1779245311/50000000000000 : ℝ)*(sp4) + (3030719183/100000000000000 : ℝ)*(sp6) + (914863663/50000000000000 : ℝ)*(sp7) + (490089818488753/100000000000000 : ℝ)*(f.failure) + (5382276911677/312500000000 : ℝ)*(f.sum) + (171237370177/5000000000000000000000000000 : ℝ)*base66 + (57088503585177/10000000000000000000000000000 : ℝ)*base68 + (65367486835177/10000000000000000000000000000 : ℝ)*base70 + (58123877125177/10000000000000000000000000000 : ℝ)*base72 + (766795720177/5000000000000000000000000000 : ℝ)*base74 + (28966086475177/10000000000000000000000000000 : ℝ)*base76 + (50360432345177/10000000000000000000000000000 : ℝ)*base78 + (53763454825177/10000000000000000000000000000 : ℝ)*base80 + (1580924840177/5000000000000000000000000000 : ℝ)*base82 + (134685673/10000000000000000000000 : ℝ)*base89 + (134685673/10000000000000000000000 : ℝ)*base91 + (134685673/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (209567261283226815423903/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (352542129/25000000000000 : ℝ)*(base19) + (1569048881/100000000000000 : ℝ)*(base23) + (51045593/25000000000000 : ℝ)*(base32) + (148345903/50000000000000 : ℝ)*(upper3) + (35966569/20000000000000 : ℝ)*(upper5) + (582444643980713/50000000000000 : ℝ)*(major0) + (582444643980713/50000000000000 : ℝ)*(major1) + (582444643980713/50000000000000 : ℝ)*(major2) + (5805445439/100000000000000 : ℝ)*(sp1) + (7569930743/100000000000000 : ℝ)*(sp2) + (1813691134584109/100000000000000 : ℝ)*(sp4) + (906841959485077/50000000000000 : ℝ)*(sp5) + (362736399120897/20000000000000 : ℝ)*(sp6) + (645108609847/125000000000 : ℝ)*(sp7) + (129021773014993/25000000000000 : ℝ)*(f.failure) + (1813691134584109/100000000000000 : ℝ)*(f.sum) + (9469524093767/20000000000000000000000000000 : ℝ)*base66 + (20975479086233/40000000000000000000000000000 : ℝ)*base67 + (221591302326233/40000000000000000000000000000 : ℝ)*base69 + (69989902686233/40000000000000000000000000000 : ℝ)*base71 + (21619052686233/20000000000000000000000000000 : ℝ)*base73 + (7293877686233/40000000000000000000000000000 : ℝ)*base75 + (90735945953767/40000000000000000000000000000 : ℝ)*base78 + (84391376606233/40000000000000000000000000000 : ℝ)*base79 + (64567395906233/20000000000000000000000000000 : ℝ)*base81 + (2394487/2500000000000000000000 : ℝ)*base90 + (2394487/2500000000000000000000 : ℝ)*base92 + (2394487/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1767_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9973/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1767_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1767_s1_0 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-283283653/2500000000 : ℝ)*x 0 + (5476631531/10000000000 : ℝ)*x 1 + (2541997241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283283653/2500000000 : ℝ)^6047 ≤ (227161769147/3125000000000 : ℝ)^5023 := by
    have hnat : (283283653 : ℕ)^6047*3125000000000^5023 ≤ 227161769147^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283283653 2500000000 227161769147 3125000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476631531/10000000000 : ℝ)^6047 ≤ (24220121052461/50000000000000 : ℝ)^5023 := by
    have hnat : (5476631531 : ℕ)^6047*50000000000000^5023 ≤ 24220121052461^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476631531 10000000000 24220121052461 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541997241/5000000000 : ℝ)^6047 ≤ (5536322657783/12500000000000 : ℝ)^5023 := by
    have hnat : (2541997241 : ℕ)^6047*12500000000000^5023 ≤ 5536322657783^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541997241 5000000000 5536322657783 12500000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-283283653/2500000000 : ℝ), (5476631531/10000000000 : ℝ), (2541997241/5000000000 : ℝ)] ![(227161769147/3125000000000 : ℝ), (24220121052461/50000000000000 : ℝ), (5536322657783/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-283283653/2500000000 : ℝ)|^6047 ≤ (227161769147/3125000000000 : ℝ)^5023
        have hw : |(-283283653/2500000000 : ℝ)|=(283283653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476631531/10000000000 : ℝ)|^6047 ≤ (24220121052461/50000000000000 : ℝ)^5023
        have hw : |(5476631531/10000000000 : ℝ)|=(5476631531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541997241/5000000000 : ℝ)|^6047 ≤ (5536322657783/12500000000000 : ℝ)^5023
        have hw : |(2541997241/5000000000 : ℝ)|=(2541997241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s1_1 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5324985299/10000000000 : ℝ)*x 0 + (-1338015537/10000000000 : ℝ)*x 1 + (317749671/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5324985299/10000000000 : ℝ)^6047 ≤ (2341504937109/5000000000000 : ℝ)^5023 := by
    have hnat : (5324985299 : ℕ)^6047*5000000000000^5023 ≤ 2341504937109^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5324985299 10000000000 2341504937109 5000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1338015537/10000000000 : ℝ)^6047 ≤ (8879317319/100000000000 : ℝ)^5023 := by
    have hnat : (1338015537 : ℕ)^6047*100000000000^5023 ≤ 8879317319^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338015537 10000000000 8879317319 100000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317749671/625000000 : ℝ)^6047 ≤ (22145291963079/50000000000000 : ℝ)^5023 := by
    have hnat : (317749671 : ℕ)^6047*50000000000000^5023 ≤ 22145291963079^5023*625000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317749671 625000000 22145291963079 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5324985299/10000000000 : ℝ), (-1338015537/10000000000 : ℝ), (317749671/625000000 : ℝ)] ![(2341504937109/5000000000000 : ℝ), (8879317319/100000000000 : ℝ), (22145291963079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5324985299/10000000000 : ℝ)|^6047 ≤ (2341504937109/5000000000000 : ℝ)^5023
        have hw : |(5324985299/10000000000 : ℝ)|=(5324985299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1338015537/10000000000 : ℝ)|^6047 ≤ (8879317319/100000000000 : ℝ)^5023
        have hw : |(-1338015537/10000000000 : ℝ)|=(1338015537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317749671/625000000 : ℝ)|^6047 ≤ (22145291963079/50000000000000 : ℝ)^5023
        have hw : |(317749671/625000000 : ℝ)|=(317749671/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s1_2 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1331246553/2500000000 : ℝ)*x 0 + (1270998479/2500000000 : ℝ)*x 1 + (-334503851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1331246553/2500000000 : ℝ)^6047 ≤ (23415054204173/50000000000000 : ℝ)^5023 := by
    have hnat : (1331246553 : ℕ)^6047*50000000000000^5023 ≤ 23415054204173^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331246553 2500000000 23415054204173 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270998479/2500000000 : ℝ)^6047 ≤ (44290575326187/100000000000000 : ℝ)^5023 := by
    have hnat : (1270998479 : ℕ)^6047*100000000000000^5023 ≤ 44290575326187^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270998479 2500000000 44290575326187 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334503851/2500000000 : ℝ)^6047 ≤ (8879316256457/100000000000000 : ℝ)^5023 := by
    have hnat : (334503851 : ℕ)^6047*100000000000000^5023 ≤ 8879316256457^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334503851 2500000000 8879316256457 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1331246553/2500000000 : ℝ), (1270998479/2500000000 : ℝ), (-334503851/2500000000 : ℝ)] ![(23415054204173/50000000000000 : ℝ), (44290575326187/100000000000000 : ℝ), (8879316256457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1331246553/2500000000 : ℝ)|^6047 ≤ (23415054204173/50000000000000 : ℝ)^5023
        have hw : |(1331246553/2500000000 : ℝ)|=(1331246553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270998479/2500000000 : ℝ)|^6047 ≤ (44290575326187/100000000000000 : ℝ)^5023
        have hw : |(1270998479/2500000000 : ℝ)|=(1270998479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-334503851/2500000000 : ℝ)|^6047 ≤ (8879316256457/100000000000000 : ℝ)^5023
        have hw : |(-334503851/2500000000 : ℝ)|=(334503851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s1_3 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3986749529/10000000000 : ℝ)*x 0 + (3326912527/10000000000 : ℝ)*x 1 + (4706766157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3986749529/10000000000 : ℝ)^6047 ≤ (33052189872833/100000000000000 : ℝ)^5023 := by
    have hnat : (3986749529 : ℕ)^6047*100000000000000^5023 ≤ 33052189872833^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3986749529 10000000000 33052189872833 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3326912527/10000000000 : ℝ)^6047 ≤ (207679534287/781250000000 : ℝ)^5023 := by
    have hnat : (3326912527 : ℕ)^6047*781250000000^5023 ≤ 207679534287^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3326912527 10000000000 207679534287 781250000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4706766157/10000000000 : ℝ)^6047 ≤ (40364829723821/100000000000000 : ℝ)^5023 := by
    have hnat : (4706766157 : ℕ)^6047*100000000000000^5023 ≤ 40364829723821^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4706766157 10000000000 40364829723821 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3986749529/10000000000 : ℝ), (3326912527/10000000000 : ℝ), (4706766157/10000000000 : ℝ)] ![(33052189872833/100000000000000 : ℝ), (207679534287/781250000000 : ℝ), (40364829723821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3986749529/10000000000 : ℝ)|^6047 ≤ (33052189872833/100000000000000 : ℝ)^5023
        have hw : |(3986749529/10000000000 : ℝ)|=(3986749529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3326912527/10000000000 : ℝ)|^6047 ≤ (207679534287/781250000000 : ℝ)^5023
        have hw : |(3326912527/10000000000 : ℝ)|=(3326912527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4706766157/10000000000 : ℝ)|^6047 ≤ (40364829723821/100000000000000 : ℝ)^5023
        have hw : |(4706766157/10000000000 : ℝ)|=(4706766157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s1_4 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-283364889/2500000000 : ℝ)*x 0 + (318162621/625000000 : ℝ)*x 1 + (1093977227/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283364889/2500000000 : ℝ)^6047 ≤ (1454337239323/20000000000000 : ℝ)^5023 := by
    have hnat : (283364889 : ℕ)^6047*20000000000000^5023 ≤ 1454337239323^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283364889 2500000000 1454337239323 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (318162621/625000000 : ℝ)^6047 ≤ (11089971972107/25000000000000 : ℝ)^5023 := by
    have hnat : (318162621 : ℕ)^6047*25000000000000^5023 ≤ 11089971972107^5023*625000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318162621 625000000 11089971972107 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093977227/2000000000 : ℝ)^6047 ≤ (9673685179091/20000000000000 : ℝ)^5023 := by
    have hnat : (1093977227 : ℕ)^6047*20000000000000^5023 ≤ 9673685179091^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093977227 2000000000 9673685179091 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-283364889/2500000000 : ℝ), (318162621/625000000 : ℝ), (1093977227/2000000000 : ℝ)] ![(1454337239323/20000000000000 : ℝ), (11089971972107/25000000000000 : ℝ), (9673685179091/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-283364889/2500000000 : ℝ)|^6047 ≤ (1454337239323/20000000000000 : ℝ)^5023
        have hw : |(-283364889/2500000000 : ℝ)|=(283364889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(318162621/625000000 : ℝ)|^6047 ≤ (11089971972107/25000000000000 : ℝ)^5023
        have hw : |(318162621/625000000 : ℝ)|=(318162621/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093977227/2000000000 : ℝ)|^6047 ≤ (9673685179091/20000000000000 : ℝ)^5023
        have hw : |(1093977227/2000000000 : ℝ)|=(1093977227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s1_5 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208859517/400000000 : ℝ)*x 0 + (-476061799/5000000000 : ℝ)*x 1 + (1093977167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208859517/400000000 : ℝ)^6047 ≤ (22868263802933/50000000000000 : ℝ)^5023 := by
    have hnat : (208859517 : ℕ)^6047*50000000000000^5023 ≤ 22868263802933^5023*400000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208859517 400000000 22868263802933 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (476061799/5000000000 : ℝ)^6047 ≤ (147376242147/2500000000000 : ℝ)^5023 := by
    have hnat : (476061799 : ℕ)^6047*2500000000000^5023 ≤ 147376242147^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476061799 5000000000 147376242147 2500000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093977167/2000000000 : ℝ)^6047 ≤ (24184211350923/50000000000000 : ℝ)^5023 := by
    have hnat : (1093977167 : ℕ)^6047*50000000000000^5023 ≤ 24184211350923^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093977167 2000000000 24184211350923 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208859517/400000000 : ℝ), (-476061799/5000000000 : ℝ), (1093977167/2000000000 : ℝ)] ![(22868263802933/50000000000000 : ℝ), (147376242147/2500000000000 : ℝ), (24184211350923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208859517/400000000 : ℝ)|^6047 ≤ (22868263802933/50000000000000 : ℝ)^5023
        have hw : |(208859517/400000000 : ℝ)|=(208859517/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-476061799/5000000000 : ℝ)|^6047 ≤ (147376242147/2500000000000 : ℝ)^5023
        have hw : |(-476061799/5000000000 : ℝ)|=(476061799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093977167/2000000000 : ℝ)|^6047 ≤ (24184211350923/50000000000000 : ℝ)^5023
        have hw : |(1093977167/2000000000 : ℝ)|=(1093977167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s1_6 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2610744033/5000000000 : ℝ)*x 0 + (2734942919/5000000000 : ℝ)*x 1 + (-952123393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2610744033/5000000000 : ℝ)^6047 ≤ (11434132273177/25000000000000 : ℝ)^5023 := by
    have hnat : (2610744033 : ℕ)^6047*25000000000000^5023 ≤ 11434132273177^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610744033 5000000000 11434132273177 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734942919/5000000000 : ℝ)^6047 ≤ (24184211366891/50000000000000 : ℝ)^5023 := by
    have hnat : (2734942919 : ℕ)^6047*50000000000000^5023 ≤ 24184211366891^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734942919 5000000000 24184211366891 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (952123393/10000000000 : ℝ)^6047 ≤ (47160385263/800000000000 : ℝ)^5023 := by
    have hnat : (952123393 : ℕ)^6047*800000000000^5023 ≤ 47160385263^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952123393 10000000000 47160385263 800000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2610744033/5000000000 : ℝ), (2734942919/5000000000 : ℝ), (-952123393/10000000000 : ℝ)] ![(11434132273177/25000000000000 : ℝ), (24184211366891/50000000000000 : ℝ), (47160385263/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2610744033/5000000000 : ℝ)|^6047 ≤ (11434132273177/25000000000000 : ℝ)^5023
        have hw : |(2610744033/5000000000 : ℝ)|=(2610744033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734942919/5000000000 : ℝ)|^6047 ≤ (24184211366891/50000000000000 : ℝ)^5023
        have hw : |(2734942919/5000000000 : ℝ)|=(2734942919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-952123393/10000000000 : ℝ)|^6047 ≤ (47160385263/800000000000 : ℝ)^5023
        have hw : |(-952123393/10000000000 : ℝ)|=(952123393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s1_7 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3987892377/10000000000 : ℝ)*x 0 + (2341772189/5000000000 : ℝ)*x 1 + (3350620731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3987892377/10000000000 : ℝ)^6047 ≤ (33063596552337/100000000000000 : ℝ)^5023 := by
    have hnat : (3987892377 : ℕ)^6047*100000000000000^5023 ≤ 33063596552337^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3987892377 10000000000 33063596552337 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2341772189/5000000000 : ℝ)^6047 ≤ (8025040734271/20000000000000 : ℝ)^5023 := by
    have hnat : (2341772189 : ℕ)^6047*20000000000000^5023 ≤ 8025040734271^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341772189 5000000000 8025040734271 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3350620731/10000000000 : ℝ)^6047 ≤ (3351399968959/12500000000000 : ℝ)^5023 := by
    have hnat : (3350620731 : ℕ)^6047*12500000000000^5023 ≤ 3351399968959^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3350620731 10000000000 3351399968959 12500000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3987892377/10000000000 : ℝ), (2341772189/5000000000 : ℝ), (3350620731/10000000000 : ℝ)] ![(33063596552337/100000000000000 : ℝ), (8025040734271/20000000000000 : ℝ), (3351399968959/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3987892377/10000000000 : ℝ)|^6047 ≤ (33063596552337/100000000000000 : ℝ)^5023
        have hw : |(3987892377/10000000000 : ℝ)|=(3987892377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2341772189/5000000000 : ℝ)|^6047 ≤ (8025040734271/20000000000000 : ℝ)^5023
        have hw : |(2341772189/5000000000 : ℝ)|=(2341772189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3350620731/10000000000 : ℝ)|^6047 ≤ (3351399968959/12500000000000 : ℝ)^5023
        have hw : |(3350620731/10000000000 : ℝ)|=(3350620731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1767_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9973/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3669/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2299/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8841/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9973/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3669/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9973/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3669/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9973/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3669/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9973/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3669/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9973/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3669/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9973/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3669/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3669/50000 : ℝ) ^ (6031/1024 : ℝ) ≤ (10414094670887/50000000000000000000 : ℝ) := by
    have hpowers : (3669/50000 : ℝ)^6031 ≤ (10414094670887/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3669 : ℕ)^6031*50000000000000000000^1024 ≤ 10414094670887^1024*50000^6031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3669 50000 10414094670887 50000000000000000000 6031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3669/50000 : ℝ)) (X := (10414094670887/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9973/50000 : ℝ) ^ (6031/1024 : ℝ) ≤ (300924040450227/4000000000000000000 : ℝ) := by
    have hpowers : (9973/50000 : ℝ)^6031 ≤ (300924040450227/4000000000000000000 : ℝ)^1024 := by
      have hnat : (9973 : ℕ)^6031*4000000000000000000^1024 ≤ 300924040450227^1024*50000^6031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9973 50000 300924040450227 4000000000000000000 6031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9973/50000 : ℝ)) (X := (300924040450227/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000010414094670887/25000000000000000000 : ℝ) ≤ (10000000707281121/10000000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (25000010414094670887/25000000000000000000 : ℝ)^1024 ≤ (10000000707281121/10000000000000000 : ℝ)^6031 := by
      have hnat : (25000010414094670887 : ℕ)^1024*10000000000000000^6031 ≤ 10000000707281121^6031*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000010414094670887 25000000000000000000 10000000707281121 10000000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000707281121/10000000000000000 : ℝ)) (X := (25000010414094670887/25000000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100007543929200597449/100000000000000000000 : ℝ) ≤ (10000128083926427/10000000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (100007543929200597449/100000000000000000000 : ℝ)^1024 ≤ (10000128083926427/10000000000000000 : ℝ)^6031 := by
      have hnat : (100007543929200597449 : ℕ)^1024*10000000000000000^6031 ≤ 10000128083926427^6031*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100007543929200597449 100000000000000000000 10000128083926427 10000000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000128083926427/10000000000000000 : ℝ)) (X := (100007543929200597449/100000000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000300924040450227/2000000000000000000 : ℝ) ≤ (10000255460571733/10000000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (2000300924040450227/2000000000000000000 : ℝ)^1024 ≤ (10000255460571733/10000000000000000 : ℝ)^6031 := by
      have hnat : (2000300924040450227 : ℕ)^1024*10000000000000000^6031 ≤ 10000255460571733^6031*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000300924040450227 2000000000000000000 10000255460571733 10000000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000255460571733/10000000000000000 : ℝ)) (X := (2000300924040450227/2000000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10414094670887/50000000000000000000 : ℝ) ≤ ((15759767442219232839/15760000000000000000 : ℝ)+2*(63688322653/630400000000000 : ℝ)*(3669/50000 : ℝ))^(6031/1024 : ℝ) := by
    rw [show (15759767442219232839/15760000000000000000 : ℝ)+2*(63688322653/630400000000000 : ℝ)*(3669/50000 : ℝ)=(10000000707281121/10000000000000000 : ℝ) by norm_num, show 1+2*(10414094670887/50000000000000000000 : ℝ)=(25000010414094670887/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(300924040450227/4000000000000000000 : ℝ)+(10414094670887/50000000000000000000 : ℝ) ≤ ((15759767442219232839/15760000000000000000 : ℝ)+(63688322653/630400000000000 : ℝ)*((9973/50000 : ℝ)+(3669/50000 : ℝ)))^(6031/1024 : ℝ) := by
    rw [show (15759767442219232839/15760000000000000000 : ℝ)+(63688322653/630400000000000 : ℝ)*((9973/50000 : ℝ)+(3669/50000 : ℝ))=(10000128083926427/10000000000000000 : ℝ) by norm_num, show 1+(300924040450227/4000000000000000000 : ℝ)+(10414094670887/50000000000000000000 : ℝ)=(100007543929200597449/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(300924040450227/4000000000000000000 : ℝ) ≤ ((15759767442219232839/15760000000000000000 : ℝ)+2*(63688322653/630400000000000 : ℝ)*(9973/50000 : ℝ))^(6031/1024 : ℝ) := by
    rw [show (15759767442219232839/15760000000000000000 : ℝ)+2*(63688322653/630400000000000 : ℝ)*(9973/50000 : ℝ)=(10000255460571733/10000000000000000 : ℝ) by norm_num, show 1+2*(300924040450227/4000000000000000000 : ℝ)=(2000300924040450227/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15759767442219232839/15760000000000000000 : ℝ)*(X 1 0+X 2 0)+(63688322653/630400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (3669/50000 : ℝ)) (hi := (9973/50000 : ℝ)) (c := (15759767442219232839/15760000000000000000 : ℝ)) (alpha := (63688322653/630400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15759767442219232839/15760000000000000000 : ℝ)*(X 0 1+X 2 1)+(63688322653/630400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (3669/50000 : ℝ)) (hi := (9973/50000 : ℝ)) (c := (15759767442219232839/15760000000000000000 : ℝ)) (alpha := (63688322653/630400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15759767442219232839/15760000000000000000 : ℝ)*(X 0 2+X 1 2)+(63688322653/630400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (3669/50000 : ℝ)) (hi := (9973/50000 : ℝ)) (c := (15759767442219232839/15760000000000000000 : ℝ)) (alpha := (63688322653/630400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-283283653/2500000000 : ℝ)*X 0 0+(5476631531/10000000000 : ℝ)*X 0 1+(2541997241/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5324985299/10000000000 : ℝ)*X 1 0+(-1338015537/10000000000 : ℝ)*X 1 1+(317749671/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1331246553/2500000000 : ℝ)*X 2 0+(1270998479/2500000000 : ℝ)*X 2 1+(-334503851/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3986749529/10000000000 : ℝ)*X 0 0+(3326912527/10000000000 : ℝ)*X 0 1+(4706766157/10000000000 : ℝ)*X 0 2+(3986749529/10000000000 : ℝ)*X 1 0+(3326912527/10000000000 : ℝ)*X 1 1+(4706766157/10000000000 : ℝ)*X 1 2+(3986749529/10000000000 : ℝ)*X 2 0+(3326912527/10000000000 : ℝ)*X 2 1+(4706766157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-283364889/2500000000 : ℝ)*X 0 0+(318162621/625000000 : ℝ)*X 0 1+(1093977227/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((208859517/400000000 : ℝ)*X 1 0+(-476061799/5000000000 : ℝ)*X 1 1+(1093977167/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2610744033/5000000000 : ℝ)*X 2 0+(2734942919/5000000000 : ℝ)*X 2 1+(-952123393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3987892377/10000000000 : ℝ)*X 0 0+(2341772189/5000000000 : ℝ)*X 0 1+(3350620731/10000000000 : ℝ)*X 0 2+(3987892377/10000000000 : ℝ)*X 1 0+(2341772189/5000000000 : ℝ)*X 1 1+(3350620731/10000000000 : ℝ)*X 1 2+(3987892377/10000000000 : ℝ)*X 2 0+(2341772189/5000000000 : ℝ)*X 2 1+(3350620731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (913624936940680708326502323/78800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (327693837/25000000000000 : ℝ)*(base19) + (433502579/25000000000000 : ℝ)*(base23) + (46375341/20000000000000 : ℝ)*(upper3) + (7160069/100000000000000 : ℝ)*(upper4) + (345734943/100000000000000 : ℝ)*(upper5) + (163581307227827/10000000000000 : ℝ)*(major0) + (163581307227827/10000000000000 : ℝ)*(major1) + (163581307227827/10000000000000 : ℝ)*(major2) + (1273445216578723/50000000000000 : ℝ)*(sp0) + (1273450744176267/50000000000000 : ℝ)*(sp1) + (1273450532558783/50000000000000 : ℝ)*(sp2) + (181179691725187/25000000000000 : ℝ)*(sp3) + (12365970437/100000000000000 : ℝ)*(sp4) + (4192053731/100000000000000 : ℝ)*(sp7) + (724722958954479/100000000000000 : ℝ)*(f.failure) + (1273451399563941/50000000000000 : ℝ)*(f.sum) + (6845067981929/3152000000000000000000000000 : ℝ)*base66 + (295330480731585853/157600000000000000000000000000000 : ℝ)*base67 + (453522049352385853/157600000000000000000000000000000 : ℝ)*base69 + (1015150581626785853/157600000000000000000000000000000 : ℝ)*base71 + (8079814813881/3152000000000000000000000000 : ℝ)*base74 + (1446266977169185853/157600000000000000000000000000000 : ℝ)*base75 + (1042005255049185853/157600000000000000000000000000000 : ℝ)*base77 + (1618109423286785853/157600000000000000000000000000000 : ℝ)*base79 + (405199309237/630400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (82693961/10000000000000000000000 : ℝ)*base90 + (82693961/10000000000000000000000 : ℝ)*base92 + (82693961/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7705767793683217828691663187/788000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61703117/5000000000000 : ℝ)*(base19) + (726363407/50000000000000 : ℝ)*(base23) + (91537301/50000000000000 : ℝ)*(upper3) + (12781547/25000000000000 : ℝ)*(lower4) + (155627741/100000000000000 : ℝ)*(upper5) + (1693387724836489/100000000000000 : ℝ)*(major0) + (1693387724836489/100000000000000 : ℝ)*(major1) + (1693387724836489/100000000000000 : ℝ)*(major2) + (7693190919/100000000000000 : ℝ)*(sp1) + (10193076357/100000000000000 : ℝ)*(sp2) + (2636544560451521/100000000000000 : ℝ)*(sp4) + (1318267816599131/50000000000000 : ℝ)*(sp5) + (52730658292967/2000000000000 : ℝ)*(sp6) + (750230563258347/100000000000000 : ℝ)*(sp7) + (750230563258347/100000000000000 : ℝ)*(f.failure) + (2636544560451521/100000000000000 : ℝ)*(f.sum) + (99267703542043/31520000000000000000000000000 : ℝ)*base66 + (4369396996955187271/1576000000000000000000000000000000 : ℝ)*base67 + (7774525969035187271/1576000000000000000000000000000000 : ℝ)*base69 + (959435868772812729/1576000000000000000000000000000000 : ℝ)*base72 + (22696041535077/31520000000000000000000000000 : ℝ)*base73 + (7393354894291187271/1576000000000000000000000000000000 : ℝ)*base75 + (7298024558099187271/1576000000000000000000000000000000 : ℝ)*base77 + (3336875252900812729/1576000000000000000000000000000000 : ℝ)*base80 + (26238609259237/31520000000000000000000000000 : ℝ)*base81 + (58294573/10000000000000000000000 : ℝ)*base90 + (58294573/10000000000000000000000 : ℝ)*base92 + (58294573/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1767_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9973/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3669/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2299/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8841/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1767_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1767_s2_0 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-283403523/2500000000 : ℝ)*x 0 + (5475085737/10000000000 : ℝ)*x 1 + (1271302683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283403523/2500000000 : ℝ)^6047 ≤ (7272879749297/100000000000000 : ℝ)^5023 := by
    have hnat : (283403523 : ℕ)^6047*100000000000000^5023 ≤ 7272879749297^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283403523 2500000000 7272879749297 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475085737/10000000000 : ℝ)^6047 ≤ (48423782905987/100000000000000 : ℝ)^5023 := by
    have hnat : (5475085737 : ℕ)^6047*100000000000000^5023 ≤ 48423782905987^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475085737 10000000000 48423782905987 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1271302683/2500000000 : ℝ)^6047 ≤ (886066746439/2000000000000 : ℝ)^5023 := by
    have hnat : (1271302683 : ℕ)^6047*2000000000000^5023 ≤ 886066746439^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271302683 2500000000 886066746439 2000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-283403523/2500000000 : ℝ), (5475085737/10000000000 : ℝ), (1271302683/2500000000 : ℝ)] ![(7272879749297/100000000000000 : ℝ), (48423782905987/100000000000000 : ℝ), (886066746439/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-283403523/2500000000 : ℝ)|^6047 ≤ (7272879749297/100000000000000 : ℝ)^5023
        have hw : |(-283403523/2500000000 : ℝ)|=(283403523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475085737/10000000000 : ℝ)|^6047 ≤ (48423782905987/100000000000000 : ℝ)^5023
        have hw : |(5475085737/10000000000 : ℝ)|=(5475085737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1271302683/2500000000 : ℝ)|^6047 ≤ (886066746439/2000000000000 : ℝ)^5023
        have hw : |(1271302683/2500000000 : ℝ)|=(1271302683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s2_1 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2662276017/5000000000 : ℝ)*x 0 + (-1336993259/10000000000 : ℝ)*x 1 + (5085210737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2662276017/5000000000 : ℝ)^6047 ≤ (46825511692369/100000000000000 : ℝ)^5023 := by
    have hnat : (2662276017 : ℕ)^6047*100000000000000^5023 ≤ 46825511692369^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2662276017 5000000000 46825511692369 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1336993259/10000000000 : ℝ)^6047 ≤ (2217787730941/25000000000000 : ℝ)^5023 := by
    have hnat : (1336993259 : ℕ)^6047*25000000000000^5023 ≤ 2217787730941^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336993259 10000000000 2217787730941 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5085210737/10000000000 : ℝ)^6047 ≤ (5537917171799/12500000000000 : ℝ)^5023 := by
    have hnat : (5085210737 : ℕ)^6047*12500000000000^5023 ≤ 5537917171799^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085210737 10000000000 5537917171799 12500000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2662276017/5000000000 : ℝ), (-1336993259/10000000000 : ℝ), (5085210737/10000000000 : ℝ)] ![(46825511692369/100000000000000 : ℝ), (2217787730941/25000000000000 : ℝ), (5537917171799/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2662276017/5000000000 : ℝ)|^6047 ≤ (46825511692369/100000000000000 : ℝ)^5023
        have hw : |(2662276017/5000000000 : ℝ)|=(2662276017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1336993259/10000000000 : ℝ)|^6047 ≤ (2217787730941/25000000000000 : ℝ)^5023
        have hw : |(-1336993259/10000000000 : ℝ)|=(1336993259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5085210737/10000000000 : ℝ)|^6047 ≤ (5537917171799/12500000000000 : ℝ)^5023
        have hw : |(5085210737/10000000000 : ℝ)|=(5085210737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s2_2 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1064910407/2000000000 : ℝ)*x 0 + (5085210733/10000000000 : ℝ)*x 1 + (-668496631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064910407/2000000000 : ℝ)^6047 ≤ (46825511702957/100000000000000 : ℝ)^5023 := by
    have hnat : (1064910407 : ℕ)^6047*100000000000000^5023 ≤ 46825511702957^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064910407 2000000000 46825511702957 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085210733/10000000000 : ℝ)^6047 ≤ (44303337332439/100000000000000 : ℝ)^5023 := by
    have hnat : (5085210733 : ℕ)^6047*100000000000000^5023 ≤ 44303337332439^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085210733 10000000000 44303337332439 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (668496631/5000000000 : ℝ)^6047 ≤ (8871150947727/100000000000000 : ℝ)^5023 := by
    have hnat : (668496631 : ℕ)^6047*100000000000000^5023 ≤ 8871150947727^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668496631 5000000000 8871150947727 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064910407/2000000000 : ℝ), (5085210733/10000000000 : ℝ), (-668496631/5000000000 : ℝ)] ![(46825511702957/100000000000000 : ℝ), (44303337332439/100000000000000 : ℝ), (8871150947727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064910407/2000000000 : ℝ)|^6047 ≤ (46825511702957/100000000000000 : ℝ)^5023
        have hw : |(1064910407/2000000000 : ℝ)|=(1064910407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085210733/10000000000 : ℝ)|^6047 ≤ (44303337332439/100000000000000 : ℝ)^5023
        have hw : |(5085210733/10000000000 : ℝ)|=(5085210733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-668496631/5000000000 : ℝ)|^6047 ≤ (8871150947727/100000000000000 : ℝ)^5023
        have hw : |(-668496631/5000000000 : ℝ)|=(668496631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s2_3 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3987145531/10000000000 : ℝ)*x 0 + (3331740833/10000000000 : ℝ)*x 1 + (4701883557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3987145531/10000000000 : ℝ)^6047 ≤ (165280711317/500000000000 : ℝ)^5023 := by
    have hnat : (3987145531 : ℕ)^6047*500000000000^5023 ≤ 165280711317^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3987145531 10000000000 165280711317 500000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3331740833/10000000000 : ℝ)^6047 ≤ (13314715855533/50000000000000 : ℝ)^5023 := by
    have hnat : (3331740833 : ℕ)^6047*50000000000000^5023 ≤ 13314715855533^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3331740833 10000000000 13314715855533 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4701883557/10000000000 : ℝ)^6047 ≤ (40314426013959/100000000000000 : ℝ)^5023 := by
    have hnat : (4701883557 : ℕ)^6047*100000000000000^5023 ≤ 40314426013959^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4701883557 10000000000 40314426013959 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3987145531/10000000000 : ℝ), (3331740833/10000000000 : ℝ), (4701883557/10000000000 : ℝ)] ![(165280711317/500000000000 : ℝ), (13314715855533/50000000000000 : ℝ), (40314426013959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3987145531/10000000000 : ℝ)|^6047 ≤ (165280711317/500000000000 : ℝ)^5023
        have hw : |(3987145531/10000000000 : ℝ)|=(3987145531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3331740833/10000000000 : ℝ)|^6047 ≤ (13314715855533/50000000000000 : ℝ)^5023
        have hw : |(3331740833/10000000000 : ℝ)|=(3331740833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4701883557/10000000000 : ℝ)|^6047 ≤ (40314426013959/100000000000000 : ℝ)^5023
        have hw : |(4701883557/10000000000 : ℝ)|=(4701883557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s2_4 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-283483139/2500000000 : ℝ)*x 0 + (5091725781/10000000000 : ℝ)*x 1 + (1367108847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283483139/2500000000 : ℝ)^6047 ≤ (7275339498011/100000000000000 : ℝ)^5023 := by
    have hnat : (283483139 : ℕ)^6047*100000000000000^5023 ≤ 7275339498011^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283483139 2500000000 7275339498011 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5091725781/10000000000 : ℝ)^6047 ≤ (693307467209/1562500000000 : ℝ)^5023 := by
    have hnat : (5091725781 : ℕ)^6047*1562500000000^5023 ≤ 693307467209^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091725781 10000000000 693307467209 1562500000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367108847/2500000000 : ℝ)^6047 ≤ (12088245646289/25000000000000 : ℝ)^5023 := by
    have hnat : (1367108847 : ℕ)^6047*25000000000000^5023 ≤ 12088245646289^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367108847 2500000000 12088245646289 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-283483139/2500000000 : ℝ), (5091725781/10000000000 : ℝ), (1367108847/2500000000 : ℝ)] ![(7275339498011/100000000000000 : ℝ), (693307467209/1562500000000 : ℝ), (12088245646289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-283483139/2500000000 : ℝ)|^6047 ≤ (7275339498011/100000000000000 : ℝ)^5023
        have hw : |(-283483139/2500000000 : ℝ)|=(283483139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5091725781/10000000000 : ℝ)|^6047 ≤ (693307467209/1562500000000 : ℝ)^5023
        have hw : |(5091725781/10000000000 : ℝ)|=(5091725781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367108847/2500000000 : ℝ)|^6047 ≤ (12088245646289/25000000000000 : ℝ)^5023
        have hw : |(1367108847/2500000000 : ℝ)|=(1367108847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s2_5 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5221789129/10000000000 : ℝ)*x 0 + (-476884407/5000000000 : ℝ)*x 1 + (5468435277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5221789129/10000000000 : ℝ)^6047 ≤ (45739703814267/100000000000000 : ℝ)^5023 := by
    have hnat : (5221789129 : ℕ)^6047*100000000000000^5023 ≤ 45739703814267^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221789129 10000000000 45739703814267 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (476884407/5000000000 : ℝ)^6047 ≤ (295365738183/5000000000000 : ℝ)^5023 := by
    have hnat : (476884407 : ℕ)^6047*5000000000000^5023 ≤ 295365738183^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476884407 5000000000 295365738183 5000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468435277/10000000000 : ℝ)^6047 ≤ (9670596280717/20000000000000 : ℝ)^5023 := by
    have hnat : (5468435277 : ℕ)^6047*20000000000000^5023 ≤ 9670596280717^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468435277 10000000000 9670596280717 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5221789129/10000000000 : ℝ), (-476884407/5000000000 : ℝ), (5468435277/10000000000 : ℝ)] ![(45739703814267/100000000000000 : ℝ), (295365738183/5000000000000 : ℝ), (9670596280717/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5221789129/10000000000 : ℝ)|^6047 ≤ (45739703814267/100000000000000 : ℝ)^5023
        have hw : |(5221789129/10000000000 : ℝ)|=(5221789129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-476884407/5000000000 : ℝ)|^6047 ≤ (295365738183/5000000000000 : ℝ)^5023
        have hw : |(-476884407/5000000000 : ℝ)|=(476884407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468435277/10000000000 : ℝ)|^6047 ≤ (9670596280717/20000000000000 : ℝ)^5023
        have hw : |(5468435277/10000000000 : ℝ)|=(5468435277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s2_6 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044357841/2000000000 : ℝ)*x 0 + (21873741/40000000 : ℝ)*x 1 + (-476884373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044357841/2000000000 : ℝ)^6047 ≤ (9147940923139/20000000000000 : ℝ)^5023 := by
    have hnat : (1044357841 : ℕ)^6047*20000000000000^5023 ≤ 9147940923139^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044357841 2000000000 9147940923139 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21873741/40000000 : ℝ)^6047 ≤ (3022061319761/6250000000000 : ℝ)^5023 := by
    have hnat : (21873741 : ℕ)^6047*6250000000000^5023 ≤ 3022061319761^5023*40000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21873741 40000000 3022061319761 6250000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476884373/5000000000 : ℝ)^6047 ≤ (738414282079/12500000000000 : ℝ)^5023 := by
    have hnat : (476884373 : ℕ)^6047*12500000000000^5023 ≤ 738414282079^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476884373 5000000000 738414282079 12500000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044357841/2000000000 : ℝ), (21873741/40000000 : ℝ), (-476884373/5000000000 : ℝ)] ![(9147940923139/20000000000000 : ℝ), (3022061319761/6250000000000 : ℝ), (738414282079/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044357841/2000000000 : ℝ)|^6047 ≤ (9147940923139/20000000000000 : ℝ)^5023
        have hw : |(1044357841/2000000000 : ℝ)|=(1044357841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21873741/40000000 : ℝ)|^6047 ≤ (3022061319761/6250000000000 : ℝ)^5023
        have hw : |(21873741/40000000 : ℝ)|=(21873741/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-476884373/5000000000 : ℝ)|^6047 ≤ (738414282079/12500000000000 : ℝ)^5023
        have hw : |(-476884373/5000000000 : ℝ)|=(476884373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s2_7 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3988264973/10000000000 : ℝ)*x 0 + (935797473/2000000000 : ℝ)*x 1 + (3355112583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3988264973/10000000000 : ℝ)^6047 ≤ (33067315548911/100000000000000 : ℝ)^5023 := by
    have hnat : (3988264973 : ℕ)^6047*100000000000000^5023 ≤ 33067315548911^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3988264973 10000000000 33067315548911 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935797473/2000000000 : ℝ)^6047 ≤ (5009776017251/12500000000000 : ℝ)^5023 := by
    have hnat : (935797473 : ℕ)^6047*12500000000000^5023 ≤ 5009776017251^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935797473 2000000000 5009776017251 12500000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3355112583/10000000000 : ℝ)^6047 ≤ (6713619072807/25000000000000 : ℝ)^5023 := by
    have hnat : (3355112583 : ℕ)^6047*25000000000000^5023 ≤ 6713619072807^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3355112583 10000000000 6713619072807 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3988264973/10000000000 : ℝ), (935797473/2000000000 : ℝ), (3355112583/10000000000 : ℝ)] ![(33067315548911/100000000000000 : ℝ), (5009776017251/12500000000000 : ℝ), (6713619072807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3988264973/10000000000 : ℝ)|^6047 ≤ (33067315548911/100000000000000 : ℝ)^5023
        have hw : |(3988264973/10000000000 : ℝ)|=(3988264973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(935797473/2000000000 : ℝ)|^6047 ≤ (5009776017251/12500000000000 : ℝ)^5023
        have hw : |(935797473/2000000000 : ℝ)|=(935797473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3355112583/10000000000 : ℝ)|^6047 ≤ (6713619072807/25000000000000 : ℝ)^5023
        have hw : |(3355112583/10000000000 : ℝ)|=(3355112583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1767_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8841/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (9223/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17649/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8841/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2299/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8841/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2299/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8841/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2299/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8841/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2299/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8841/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2299/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8841/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2299/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2299/25000 : ℝ) ^ (6031/1024 : ℝ) ≤ (3934886897963/5000000000000000000 : ℝ) := by
    have hpowers : (2299/25000 : ℝ)^6031 ≤ (3934886897963/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2299 : ℕ)^6031*5000000000000000000^1024 ≤ 3934886897963^1024*25000^6031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2299 25000 3934886897963 5000000000000000000 6031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2299/25000 : ℝ)) (X := (3934886897963/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8841/50000 : ℝ) ^ (6031/1024 : ℝ) ≤ (3700193233851893/100000000000000000000 : ℝ) := by
    have hpowers : (8841/50000 : ℝ)^6031 ≤ (3700193233851893/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8841 : ℕ)^6031*100000000000000000000^1024 ≤ 3700193233851893^1024*50000^6031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8841 50000 3700193233851893 100000000000000000000 6031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8841/50000 : ℝ)) (X := (3700193233851893/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500003934886897963/2500000000000000000 : ℝ) ≤ (2500000668101733/2500000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (2500003934886897963/2500000000000000000 : ℝ)^1024 ≤ (2500000668101733/2500000000000000 : ℝ)^6031 := by
      have hnat : (2500003934886897963 : ℕ)^1024*2500000000000000^6031 ≤ 2500000668101733^6031*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500003934886897963 2500000000000000000 2500000668101733 2500000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000668101733/2500000000000000 : ℝ)) (X := (2500003934886897963/2500000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100003778890971811153/100000000000000000000 : ℝ) ≤ (1250008020070587/1250000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (100003778890971811153/100000000000000000000 : ℝ)^1024 ≤ (1250008020070587/1250000000000000 : ℝ)^6031 := by
      have hnat : (100003778890971811153 : ℕ)^1024*1250000000000000^6031 ≤ 1250008020070587^6031*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100003778890971811153 100000000000000000000 1250008020070587 1250000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250008020070587/1250000000000000 : ℝ)) (X := (100003778890971811153/100000000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50003700193233851893/50000000000000000000 : ℝ) ≤ (500006282436123/500000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (50003700193233851893/50000000000000000000 : ℝ)^1024 ≤ (500006282436123/500000000000000 : ℝ)^6031 := by
      have hnat : (50003700193233851893 : ℕ)^1024*500000000000000^6031 ≤ 500006282436123^6031*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003700193233851893 50000000000000000000 500006282436123 500000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500006282436123/500000000000000 : ℝ)) (X := (50003700193233851893/50000000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3934886897963/5000000000000000000 : ℝ) ≤ ((10607361473480953683/10607500000000000000 : ℝ)+2*(15372039441/212150000000000 : ℝ)*(2299/25000 : ℝ))^(6031/1024 : ℝ) := by
    rw [show (10607361473480953683/10607500000000000000 : ℝ)+2*(15372039441/212150000000000 : ℝ)*(2299/25000 : ℝ)=(2500000668101733/2500000000000000 : ℝ) by norm_num, show 1+2*(3934886897963/5000000000000000000 : ℝ)=(2500003934886897963/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3700193233851893/100000000000000000000 : ℝ)+(3934886897963/5000000000000000000 : ℝ) ≤ ((10607361473480953683/10607500000000000000 : ℝ)+(15372039441/212150000000000 : ℝ)*((8841/50000 : ℝ)+(2299/25000 : ℝ)))^(6031/1024 : ℝ) := by
    rw [show (10607361473480953683/10607500000000000000 : ℝ)+(15372039441/212150000000000 : ℝ)*((8841/50000 : ℝ)+(2299/25000 : ℝ))=(1250008020070587/1250000000000000 : ℝ) by norm_num, show 1+(3700193233851893/100000000000000000000 : ℝ)+(3934886897963/5000000000000000000 : ℝ)=(100003778890971811153/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3700193233851893/100000000000000000000 : ℝ) ≤ ((10607361473480953683/10607500000000000000 : ℝ)+2*(15372039441/212150000000000 : ℝ)*(8841/50000 : ℝ))^(6031/1024 : ℝ) := by
    rw [show (10607361473480953683/10607500000000000000 : ℝ)+2*(15372039441/212150000000000 : ℝ)*(8841/50000 : ℝ)=(500006282436123/500000000000000 : ℝ) by norm_num, show 1+2*(3700193233851893/100000000000000000000 : ℝ)=(50003700193233851893/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10607361473480953683/10607500000000000000 : ℝ)*(X 1 0+X 2 0)+(15372039441/212150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (2299/25000 : ℝ)) (hi := (8841/50000 : ℝ)) (c := (10607361473480953683/10607500000000000000 : ℝ)) (alpha := (15372039441/212150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10607361473480953683/10607500000000000000 : ℝ)*(X 0 1+X 2 1)+(15372039441/212150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (2299/25000 : ℝ)) (hi := (8841/50000 : ℝ)) (c := (10607361473480953683/10607500000000000000 : ℝ)) (alpha := (15372039441/212150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10607361473480953683/10607500000000000000 : ℝ)*(X 0 2+X 1 2)+(15372039441/212150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (2299/25000 : ℝ)) (hi := (8841/50000 : ℝ)) (c := (10607361473480953683/10607500000000000000 : ℝ)) (alpha := (15372039441/212150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-283403523/2500000000 : ℝ)*X 0 0+(5475085737/10000000000 : ℝ)*X 0 1+(1271302683/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2662276017/5000000000 : ℝ)*X 1 0+(-1336993259/10000000000 : ℝ)*X 1 1+(5085210737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1064910407/2000000000 : ℝ)*X 2 0+(5085210733/10000000000 : ℝ)*X 2 1+(-668496631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3987145531/10000000000 : ℝ)*X 0 0+(3331740833/10000000000 : ℝ)*X 0 1+(4701883557/10000000000 : ℝ)*X 0 2+(3987145531/10000000000 : ℝ)*X 1 0+(3331740833/10000000000 : ℝ)*X 1 1+(4701883557/10000000000 : ℝ)*X 1 2+(3987145531/10000000000 : ℝ)*X 2 0+(3331740833/10000000000 : ℝ)*X 2 1+(4701883557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-283483139/2500000000 : ℝ)*X 0 0+(5091725781/10000000000 : ℝ)*X 0 1+(1367108847/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5221789129/10000000000 : ℝ)*X 1 0+(-476884407/5000000000 : ℝ)*X 1 1+(5468435277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1044357841/2000000000 : ℝ)*X 2 0+(21873741/40000000 : ℝ)*X 2 1+(-476884373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3988264973/10000000000 : ℝ)*X 0 0+(935797473/2000000000 : ℝ)*X 0 1+(3355112583/10000000000 : ℝ)*X 0 2+(3988264973/10000000000 : ℝ)*X 1 0+(935797473/2000000000 : ℝ)*X 1 1+(3355112583/10000000000 : ℝ)*X 1 2+(3988264973/10000000000 : ℝ)*X 2 0+(935797473/2000000000 : ℝ)*X 2 1+(3355112583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6701042610262086041407628493/530375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (334919573/20000000000000 : ℝ)*(base19) + (396409837/25000000000000 : ℝ)*(base23) + (1190573/2500000000000 : ℝ)*(lower2) + (149952889/50000000000000 : ℝ)*(upper3) + (58870917/25000000000000 : ℝ)*(upper5) + (1647405672166357/100000000000000 : ℝ)*(major0) + (1647405672166357/100000000000000 : ℝ)*(major1) + (1647405672166357/100000000000000 : ℝ)*(major2) + (6412345872617/250000000000 : ℝ)*(sp0) + (1282475179245867/50000000000000 : ℝ)*(sp1) + (641237611862563/25000000000000 : ℝ)*(sp2) + (364927335669257/50000000000000 : ℝ)*(sp3) + (13684042799/100000000000000 : ℝ)*(sp4) + (4218753359/100000000000000 : ℝ)*(sp7) + (729858890091873/100000000000000 : ℝ)*(f.failure) + (2564952033089599/100000000000000 : ℝ)*(f.sum) + (72543071424481/21215000000000000000000000000 : ℝ)*base66 + (996769152512307169/1060750000000000000000000000000000 : ℝ)*base68 + (3751977528515557169/1060750000000000000000000000000000 : ℝ)*base70 + (1861190074841942831/1060750000000000000000000000000000 : ℝ)*base71 + (5351520192309/21215000000000000000000000000 : ℝ)*base73 + (4125025375214942831/1060750000000000000000000000000000 : ℝ)*base75 + (7055448822896057169/1060750000000000000000000000000000 : ℝ)*base78 + (4977511546905057169/1060750000000000000000000000000000 : ℝ)*base80 + (49832905560891/21215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (36914407/10000000000000000000000 : ℝ)*base90 + (36914407/10000000000000000000000 : ℝ)*base92 + (36914407/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120628095956358944776257/10607500000000000000000000000 : ℝ) := by norm_num
    linear_combination (662964599/50000000000000 : ℝ)*(base19) + (1503646089/100000000000000 : ℝ)*(base23) + (351030043/100000000000000 : ℝ)*(lower1) + (220357791/100000000000000 : ℝ)*(upper3) + (62452501/100000000000000 : ℝ)*(lower4) + (63213531/25000000000000 : ℝ)*(upper5) + (852477786279979/50000000000000 : ℝ)*(major0) + (852477786279979/50000000000000 : ℝ)*(major1) + (852477786279979/50000000000000 : ℝ)*(major2) + (989939917/100000000000000 : ℝ)*(sp2) + (2654555237741777/100000000000000 : ℝ)*(sp4) + (2654553911812579/100000000000000 : ℝ)*(sp5) + (265455274415577/10000000000000 : ℝ)*(sp6) + (151071105662541/20000000000000 : ℝ)*(sp7) + (151071105662541/20000000000000 : ℝ)*(f.failure) + (2654555237741777/100000000000000 : ℝ)*(f.sum) + (66233532245939/21215000000000000000000000000 : ℝ)*base66 + (921737427939587343/530375000000000000000000000000000 : ℝ)*base68 + (2721702100317037657/530375000000000000000000000000000 : ℝ)*base69 + (5060471268694837343/530375000000000000000000000000000 : ℝ)*base72 + (111210839911129/21215000000000000000000000000 : ℝ)*base74 + (1236563379733087343/530375000000000000000000000000000 : ℝ)*base76 + (2095936812839912657/530375000000000000000000000000000 : ℝ)*base77 + (1761552307031412657/530375000000000000000000000000000 : ℝ)*base79 + (121988109172359/21215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (11503781/2000000000000000000000 : ℝ)*base89 + (11503781/2000000000000000000000 : ℝ)*base91 + (11503781/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1767_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8841/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17649/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1767_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1767_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17649/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1767_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1767_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1767_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17649/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1767_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
