-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1212_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:07:19.960382+00:00
-- url     : https://prove2.me/submissions/e923f8de-c4fb-446d-a974-a52a692f7e25

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
theorem support_rectangle_w1212_s3_0 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130750639/10000000000 : ℝ)*x 0 + (5422356331/10000000000 : ℝ)*x 1 + (5238232673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130750639/10000000000 : ℝ)^8405 ≤ (6474103713809/50000000000000 : ℝ)^6357 := by
    have hnat : (2130750639 : ℕ)^8405*50000000000000^6357 ≤ 6474103713809^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130750639 10000000000 6474103713809 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422356331/10000000000 : ℝ)^8405 ≤ (2225988283569/5000000000000 : ℝ)^6357 := by
    have hnat : (5422356331 : ℕ)^8405*5000000000000^6357 ≤ 2225988283569^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422356331 10000000000 2225988283569 5000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238232673/10000000000 : ℝ)^8405 ≤ (42532026885033/100000000000000 : ℝ)^6357 := by
    have hnat : (5238232673 : ℕ)^8405*100000000000000^6357 ≤ 42532026885033^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238232673 10000000000 42532026885033 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130750639/10000000000 : ℝ), (5422356331/10000000000 : ℝ), (5238232673/10000000000 : ℝ)] ![(6474103713809/50000000000000 : ℝ), (2225988283569/5000000000000 : ℝ), (42532026885033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130750639/10000000000 : ℝ)|^8405 ≤ (6474103713809/50000000000000 : ℝ)^6357
        have hw : |(-2130750639/10000000000 : ℝ)|=(2130750639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422356331/10000000000 : ℝ)|^8405 ≤ (2225988283569/5000000000000 : ℝ)^6357
        have hw : |(5422356331/10000000000 : ℝ)|=(5422356331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238232673/10000000000 : ℝ)|^8405 ≤ (42532026885033/100000000000000 : ℝ)^6357
        have hw : |(5238232673/10000000000 : ℝ)|=(5238232673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s3_1 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2676080329/5000000000 : ℝ)*x 0 + (-2224732433/10000000000 : ℝ)*x 1 + (5238232741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676080329/5000000000 : ℝ)^8405 ≤ (43759349380653/100000000000000 : ℝ)^6357 := by
    have hnat : (2676080329 : ℕ)^8405*100000000000000^6357 ≤ 43759349380653^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676080329 5000000000 43759349380653 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2224732433/10000000000 : ℝ)^8405 ≤ (171357787239/1250000000000 : ℝ)^6357 := by
    have hnat : (2224732433 : ℕ)^8405*1250000000000^6357 ≤ 171357787239^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224732433 10000000000 171357787239 1250000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238232741/10000000000 : ℝ)^8405 ≤ (42532027615037/100000000000000 : ℝ)^6357 := by
    have hnat : (5238232741 : ℕ)^8405*100000000000000^6357 ≤ 42532027615037^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238232741 10000000000 42532027615037 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676080329/5000000000 : ℝ), (-2224732433/10000000000 : ℝ), (5238232741/10000000000 : ℝ)] ![(43759349380653/100000000000000 : ℝ), (171357787239/1250000000000 : ℝ), (42532027615037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676080329/5000000000 : ℝ)|^8405 ≤ (43759349380653/100000000000000 : ℝ)^6357
        have hw : |(2676080329/5000000000 : ℝ)|=(2676080329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2224732433/10000000000 : ℝ)|^8405 ≤ (171357787239/1250000000000 : ℝ)^6357
        have hw : |(-2224732433/10000000000 : ℝ)|=(2224732433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238232741/10000000000 : ℝ)|^8405 ≤ (42532027615037/100000000000000 : ℝ)^6357
        have hw : |(5238232741/10000000000 : ℝ)|=(5238232741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s3_2 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338040151/2500000000 : ℝ)*x 0 + (5238232921/10000000000 : ℝ)*x 1 + (-556183067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338040151/2500000000 : ℝ)^8405 ≤ (43759348796911/100000000000000 : ℝ)^6357 := by
    have hnat : (1338040151 : ℕ)^8405*100000000000000^6357 ≤ 43759348796911^6357*2500000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338040151 2500000000 43759348796911 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238232921/10000000000 : ℝ)^8405 ≤ (42532029547403/100000000000000 : ℝ)^6357 := by
    have hnat : (5238232921 : ℕ)^8405*100000000000000^6357 ≤ 42532029547403^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238232921 10000000000 42532029547403 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556183067/2500000000 : ℝ)^8405 ≤ (13708621634853/100000000000000 : ℝ)^6357 := by
    have hnat : (556183067 : ℕ)^8405*100000000000000^6357 ≤ 13708621634853^6357*2500000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556183067 2500000000 13708621634853 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338040151/2500000000 : ℝ), (5238232921/10000000000 : ℝ), (-556183067/2500000000 : ℝ)] ![(43759348796911/100000000000000 : ℝ), (42532029547403/100000000000000 : ℝ), (13708621634853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338040151/2500000000 : ℝ)|^8405 ≤ (43759348796911/100000000000000 : ℝ)^6357
        have hw : |(1338040151/2500000000 : ℝ)|=(1338040151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238232921/10000000000 : ℝ)|^8405 ≤ (42532029547403/100000000000000 : ℝ)^6357
        have hw : |(5238232921/10000000000 : ℝ)|=(5238232921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-556183067/2500000000 : ℝ)|^8405 ≤ (13708621634853/100000000000000 : ℝ)^6357
        have hw : |(-556183067/2500000000 : ℝ)|=(556183067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s3_3 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870610741/2000000000 : ℝ)*x 0 + (521406691/1250000000 : ℝ)*x 1 + (56782481/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870610741/2000000000 : ℝ)^8405 ≤ (33298622459057/100000000000000 : ℝ)^6357 := by
    have hnat : (870610741 : ℕ)^8405*100000000000000^6357 ≤ 33298622459057^6357*2000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870610741 2000000000 33298622459057 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521406691/1250000000 : ℝ)^8405 ≤ (15736203015113/50000000000000 : ℝ)^6357 := by
    have hnat : (521406691 : ℕ)^8405*50000000000000^6357 ≤ 15736203015113^6357*1250000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521406691 1250000000 15736203015113 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56782481/125000000 : ℝ)^8405 ≤ (35228971492893/100000000000000 : ℝ)^6357 := by
    have hnat : (56782481 : ℕ)^8405*100000000000000^6357 ≤ 35228971492893^6357*125000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56782481 125000000 35228971492893 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870610741/2000000000 : ℝ), (521406691/1250000000 : ℝ), (56782481/125000000 : ℝ)] ![(33298622459057/100000000000000 : ℝ), (15736203015113/50000000000000 : ℝ), (35228971492893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870610741/2000000000 : ℝ)|^8405 ≤ (33298622459057/100000000000000 : ℝ)^6357
        have hw : |(870610741/2000000000 : ℝ)|=(870610741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521406691/1250000000 : ℝ)|^8405 ≤ (15736203015113/50000000000000 : ℝ)^6357
        have hw : |(521406691/1250000000 : ℝ)|=(521406691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56782481/125000000 : ℝ)|^8405 ≤ (35228971492893/100000000000000 : ℝ)^6357
        have hw : |(56782481/125000000 : ℝ)|=(56782481/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s3_4 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-106538287/500000000 : ℝ)*x 0 + (1047782883/2000000000 : ℝ)*x 1 + (5421670929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106538287/500000000 : ℝ)^8405 ≤ (12948328757767/100000000000000 : ℝ)^6357 := by
    have hnat : (106538287 : ℕ)^8405*100000000000000^6357 ≤ 12948328757767^6357*500000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106538287 500000000 12948328757767 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047782883/2000000000 : ℝ)^8405 ≤ (5317418223429/12500000000000 : ℝ)^6357 := by
    have hnat : (1047782883 : ℕ)^8405*12500000000000^6357 ≤ 5317418223429^6357*2000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047782883 2000000000 5317418223429 12500000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421670929/10000000000 : ℝ)^8405 ≤ (22256162716533/50000000000000 : ℝ)^6357 := by
    have hnat : (5421670929 : ℕ)^8405*50000000000000^6357 ≤ 22256162716533^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421670929 10000000000 22256162716533 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106538287/500000000 : ℝ), (1047782883/2000000000 : ℝ), (5421670929/10000000000 : ℝ)] ![(12948328757767/100000000000000 : ℝ), (5317418223429/12500000000000 : ℝ), (22256162716533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106538287/500000000 : ℝ)|^8405 ≤ (12948328757767/100000000000000 : ℝ)^6357
        have hw : |(-106538287/500000000 : ℝ)|=(106538287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047782883/2000000000 : ℝ)|^8405 ≤ (5317418223429/12500000000000 : ℝ)^6357
        have hw : |(1047782883/2000000000 : ℝ)|=(1047782883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421670929/10000000000 : ℝ)|^8405 ≤ (22256162716533/50000000000000 : ℝ)^6357
        have hw : |(5421670929/10000000000 : ℝ)|=(5421670929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s3_5 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530528201/1000000000 : ℝ)*x 0 + (-2041294323/10000000000 : ℝ)*x 1 + (338854413/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530528201/1000000000 : ℝ)^8405 ≤ (4325330581729/10000000000000 : ℝ)^6357 := by
    have hnat : (530528201 : ℕ)^8405*10000000000000^6357 ≤ 4325330581729^6357*1000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530528201 1000000000 4325330581729 10000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2041294323/10000000000 : ℝ)^8405 ≤ (6117186114207/50000000000000 : ℝ)^6357 := by
    have hnat : (2041294323 : ℕ)^8405*50000000000000^6357 ≤ 6117186114207^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041294323 10000000000 6117186114207 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338854413/625000000 : ℝ)^8405 ≤ (11128080487147/25000000000000 : ℝ)^6357 := by
    have hnat : (338854413 : ℕ)^8405*25000000000000^6357 ≤ 11128080487147^6357*625000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338854413 625000000 11128080487147 25000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530528201/1000000000 : ℝ), (-2041294323/10000000000 : ℝ), (338854413/625000000 : ℝ)] ![(4325330581729/10000000000000 : ℝ), (6117186114207/50000000000000 : ℝ), (11128080487147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530528201/1000000000 : ℝ)|^8405 ≤ (4325330581729/10000000000000 : ℝ)^6357
        have hw : |(530528201/1000000000 : ℝ)|=(530528201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2041294323/10000000000 : ℝ)|^8405 ≤ (6117186114207/50000000000000 : ℝ)^6357
        have hw : |(-2041294323/10000000000 : ℝ)|=(2041294323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338854413/625000000 : ℝ)|^8405 ≤ (11128080487147/25000000000000 : ℝ)^6357
        have hw : |(338854413/625000000 : ℝ)|=(338854413/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s3_6 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530528187/1000000000 : ℝ)*x 0 + (2710835299/5000000000 : ℝ)*x 1 + (-2041294527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530528187/1000000000 : ℝ)^8405 ≤ (5406663038521/12500000000000 : ℝ)^6357 := by
    have hnat : (530528187 : ℕ)^8405*12500000000000^6357 ≤ 5406663038521^6357*1000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530528187 1000000000 5406663038521 12500000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710835299/5000000000 : ℝ)^8405 ≤ (22256160920019/50000000000000 : ℝ)^6357 := by
    have hnat : (2710835299 : ℕ)^8405*50000000000000^6357 ≤ 22256160920019^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710835299 5000000000 22256160920019 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2041294527/10000000000 : ℝ)^8405 ≤ (12234373844973/100000000000000 : ℝ)^6357 := by
    have hnat : (2041294527 : ℕ)^8405*100000000000000^6357 ≤ 12234373844973^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041294527 10000000000 12234373844973 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530528187/1000000000 : ℝ), (2710835299/5000000000 : ℝ), (-2041294527/10000000000 : ℝ)] ![(5406663038521/12500000000000 : ℝ), (22256160920019/50000000000000 : ℝ), (12234373844973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530528187/1000000000 : ℝ)|^8405 ≤ (5406663038521/12500000000000 : ℝ)^6357
        have hw : |(530528187/1000000000 : ℝ)|=(530528187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710835299/5000000000 : ℝ)|^8405 ≤ (22256160920019/50000000000000 : ℝ)^6357
        have hw : |(2710835299/5000000000 : ℝ)|=(2710835299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2041294527/10000000000 : ℝ)|^8405 ≤ (12234373844973/100000000000000 : ℝ)^6357
        have hw : |(-2041294527/10000000000 : ℝ)|=(2041294527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s3_7 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353084311/10000000000 : ℝ)*x 0 + (4541223043/10000000000 : ℝ)*x 1 + (4172636107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353084311/10000000000 : ℝ)^8405 ≤ (2081183250299/6250000000000 : ℝ)^6357 := by
    have hnat : (4353084311 : ℕ)^8405*6250000000000^6357 ≤ 2081183250299^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353084311 10000000000 2081183250299 6250000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4541223043/10000000000 : ℝ)^8405 ≤ (35214868845801/100000000000000 : ℝ)^6357 := by
    have hnat : (4541223043 : ℕ)^8405*100000000000000^6357 ≤ 35214868845801^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541223043 10000000000 35214868845801 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172636107/10000000000 : ℝ)^8405 ≤ (49197186147/156250000000 : ℝ)^6357 := by
    have hnat : (4172636107 : ℕ)^8405*156250000000^6357 ≤ 49197186147^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172636107 10000000000 49197186147 156250000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353084311/10000000000 : ℝ), (4541223043/10000000000 : ℝ), (4172636107/10000000000 : ℝ)] ![(2081183250299/6250000000000 : ℝ), (35214868845801/100000000000000 : ℝ), (49197186147/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353084311/10000000000 : ℝ)|^8405 ≤ (2081183250299/6250000000000 : ℝ)^6357
        have hw : |(4353084311/10000000000 : ℝ)|=(4353084311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4541223043/10000000000 : ℝ)|^8405 ≤ (35214868845801/100000000000000 : ℝ)^6357
        have hw : |(4541223043/10000000000 : ℝ)|=(4541223043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172636107/10000000000 : ℝ)|^8405 ≤ (49197186147/156250000000 : ℝ)^6357
        have hw : |(4172636107/10000000000 : ℝ)|=(4172636107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1212_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16303/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3/32 : ℝ)*pair X i i ≤ pair X i h) :
    (677/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14729/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16303/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3/32 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16303/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3/32 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16303/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3/32 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16303/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3/32 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16303/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3/32 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16303/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3/32 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3/32 : ℝ) ^ (2101/512 : ℝ) ≤ (755749872820437/12500000000000000000 : ℝ) := by
    have hpowers : (3/32 : ℝ)^2101 ≤ (755749872820437/12500000000000000000 : ℝ)^512 := by
      have hnat : (3 : ℕ)^2101*12500000000000000000^512 ≤ 755749872820437^512*32^2101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 32 755749872820437 12500000000000000000 2101 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3/32 : ℝ)) (X := (755749872820437/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16303/100000 : ℝ) ^ (2101/512 : ℝ) ≤ (11710016061285381/20000000000000000000 : ℝ) := by
    have hpowers : (16303/100000 : ℝ)^2101 ≤ (11710016061285381/20000000000000000000 : ℝ)^512 := by
      have hnat : (16303 : ℕ)^2101*20000000000000000000^512 ≤ 11710016061285381^512*100000^2101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16303 100000 11710016061285381 20000000000000000000 2101 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16303/100000 : ℝ)) (X := (11710016061285381/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250755749872820437/6250000000000000000 : ℝ) ≤ (5000147330316089/5000000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (6250755749872820437/6250000000000000000 : ℝ)^512 ≤ (5000147330316089/5000000000000000 : ℝ)^2101 := by
      have hnat : (6250755749872820437 : ℕ)^512*5000000000000000^2101 ≤ 5000147330316089^2101*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250755749872820437 6250000000000000000 5000147330316089 5000000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000147330316089/5000000000000000 : ℝ)) (X := (6250755749872820437/6250000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100064596079288990401/100000000000000000000 : ℝ) ≤ (10001573779951877/10000000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (100064596079288990401/100000000000000000000 : ℝ)^512 ≤ (10001573779951877/10000000000000000 : ℝ)^2101 := by
      have hnat : (100064596079288990401 : ℕ)^512*10000000000000000^2101 ≤ 10001573779951877^2101*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100064596079288990401 100000000000000000000 10001573779951877 10000000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001573779951877/10000000000000000 : ℝ)) (X := (100064596079288990401/100000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10011710016061285381/10000000000000000000 : ℝ) ≤ (1250356612408947/1250000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (10011710016061285381/10000000000000000000 : ℝ)^512 ≤ (1250356612408947/1250000000000000 : ℝ)^2101 := by
      have hnat : (10011710016061285381 : ℕ)^512*1250000000000000^2101 ≤ 1250356612408947^2101*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10011710016061285381 10000000000000000000 1250356612408947 1250000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250356612408947/1250000000000000 : ℝ)) (X := (10011710016061285381/10000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(755749872820437/12500000000000000000 : ℝ) ≤ ((34629028960807686467/34640000000000000000 : ℝ)+2*(1279119319699/692800000000000 : ℝ)*(3/32 : ℝ))^(2101/512 : ℝ) := by
    rw [show (34629028960807686467/34640000000000000000 : ℝ)+2*(1279119319699/692800000000000 : ℝ)*(3/32 : ℝ)=(5000147330316089/5000000000000000 : ℝ) by norm_num, show 1+2*(755749872820437/12500000000000000000 : ℝ)=(6250755749872820437/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11710016061285381/20000000000000000000 : ℝ)+(755749872820437/12500000000000000000 : ℝ) ≤ ((34629028960807686467/34640000000000000000 : ℝ)+(1279119319699/692800000000000 : ℝ)*((16303/100000 : ℝ)+(3/32 : ℝ)))^(2101/512 : ℝ) := by
    rw [show (34629028960807686467/34640000000000000000 : ℝ)+(1279119319699/692800000000000 : ℝ)*((16303/100000 : ℝ)+(3/32 : ℝ))=(10001573779951877/10000000000000000 : ℝ) by norm_num, show 1+(11710016061285381/20000000000000000000 : ℝ)+(755749872820437/12500000000000000000 : ℝ)=(100064596079288990401/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11710016061285381/20000000000000000000 : ℝ) ≤ ((34629028960807686467/34640000000000000000 : ℝ)+2*(1279119319699/692800000000000 : ℝ)*(16303/100000 : ℝ))^(2101/512 : ℝ) := by
    rw [show (34629028960807686467/34640000000000000000 : ℝ)+2*(1279119319699/692800000000000 : ℝ)*(16303/100000 : ℝ)=(1250356612408947/1250000000000000 : ℝ) by norm_num, show 1+2*(11710016061285381/20000000000000000000 : ℝ)=(10011710016061285381/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34629028960807686467/34640000000000000000 : ℝ)*(X 1 0+X 2 0)+(1279119319699/692800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (3/32 : ℝ)) (hi := (16303/100000 : ℝ)) (c := (34629028960807686467/34640000000000000000 : ℝ)) (alpha := (1279119319699/692800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34629028960807686467/34640000000000000000 : ℝ)*(X 0 1+X 2 1)+(1279119319699/692800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (3/32 : ℝ)) (hi := (16303/100000 : ℝ)) (c := (34629028960807686467/34640000000000000000 : ℝ)) (alpha := (1279119319699/692800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34629028960807686467/34640000000000000000 : ℝ)*(X 0 2+X 1 2)+(1279119319699/692800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (3/32 : ℝ)) (hi := (16303/100000 : ℝ)) (c := (34629028960807686467/34640000000000000000 : ℝ)) (alpha := (1279119319699/692800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2130750639/10000000000 : ℝ)*X 0 0+(5422356331/10000000000 : ℝ)*X 0 1+(5238232673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676080329/5000000000 : ℝ)*X 1 0+(-2224732433/10000000000 : ℝ)*X 1 1+(5238232741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338040151/2500000000 : ℝ)*X 2 0+(5238232921/10000000000 : ℝ)*X 2 1+(-556183067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870610741/2000000000 : ℝ)*X 0 0+(521406691/1250000000 : ℝ)*X 0 1+(56782481/125000000 : ℝ)*X 0 2+(870610741/2000000000 : ℝ)*X 1 0+(521406691/1250000000 : ℝ)*X 1 1+(56782481/125000000 : ℝ)*X 1 2+(870610741/2000000000 : ℝ)*X 2 0+(521406691/1250000000 : ℝ)*X 2 1+(56782481/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-106538287/500000000 : ℝ)*X 0 0+(1047782883/2000000000 : ℝ)*X 0 1+(5421670929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530528201/1000000000 : ℝ)*X 1 0+(-2041294323/10000000000 : ℝ)*X 1 1+(338854413/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530528187/1000000000 : ℝ)*X 2 0+(2710835299/5000000000 : ℝ)*X 2 1+(-2041294527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353084311/10000000000 : ℝ)*X 0 0+(4541223043/10000000000 : ℝ)*X 0 1+(4172636107/10000000000 : ℝ)*X 0 2+(4353084311/10000000000 : ℝ)*X 1 0+(4541223043/10000000000 : ℝ)*X 1 1+(4172636107/10000000000 : ℝ)*X 1 2+(4353084311/10000000000 : ℝ)*X 2 0+(4541223043/10000000000 : ℝ)*X 2 1+(4172636107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9296389633980445174805077947/866000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30012249/1562500000000 : ℝ)*(base19) + (830120259/50000000000000 : ℝ)*(base23) + (110118473/100000000000000 : ℝ)*(lower2) + (17466329/10000000000000 : ℝ)*(upper3) + (24173467/12500000000000 : ℝ)*(upper5) + (2031041554853853/50000000000000 : ℝ)*(major0) + (2031041554853853/50000000000000 : ℝ)*(major1) + (2031041554853853/50000000000000 : ℝ)*(major2) + (5431172184669607/100000000000000 : ℝ)*(sp0) + (54312126160969/1000000000000 : ℝ)*(sp1) + (2715606438320159/50000000000000 : ℝ)*(sp2) + (1346466195483257/50000000000000 : ℝ)*(sp3) + (4235221123/10000000000000 : ℝ)*(sp4) + (378674787/2000000000000 : ℝ)*(sp7) + (336618915588233/12500000000000 : ℝ)*(f.failure) + (1357803634220209/25000000000000 : ℝ)*(f.sum) + (113658628844207/17320000000000000000000000000 : ℝ)*base65 + (3320677558444742649/1732000000000000000000000000000000 : ℝ)*base68 + (9570938237188742649/1732000000000000000000000000000000 : ℝ)*base70 + (20178376871303257351/1732000000000000000000000000000000 : ℝ)*base71 + (116657368698807/17320000000000000000000000000 : ℝ)*base73 + (32771610917503257351/1732000000000000000000000000000000 : ℝ)*base75 + (9471374788999257351/1732000000000000000000000000000000 : ℝ)*base77 + (29601357684503257351/1732000000000000000000000000000000 : ℝ)*base79 + (51669572925527/17320000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (234947/39062500000000000000 : ℝ)*base90 + (234947/39062500000000000000 : ℝ)*base92 + (234947/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (125263053438354680609528517/43300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (782762103/100000000000000 : ℝ)*(base19) + (380700033/50000000000000 : ℝ)*(base23) + (19071809/20000000000000 : ℝ)*(lower4) + (28463019/25000000000000 : ℝ)*(upper5) + (102310424061283/2500000000000 : ℝ)*(major0) + (102310424061283/2500000000000 : ℝ)*(major1) + (102310424061283/2500000000000 : ℝ)*(major2) + (5437972481/100000000000000 : ℝ)*(sp0) + (7699707631/50000000000000 : ℝ)*(sp1) + (8981252717/100000000000000 : ℝ)*(sp2) + (1367941821986909/25000000000000 : ℝ)*(sp4) + (170992391991961/3125000000000 : ℝ)*(sp5) + (2735881491633667/50000000000000 : ℝ)*(sp6) + (169566318909509/6250000000000 : ℝ)*(sp7) + (169566318909509/6250000000000 : ℝ)*(f.failure) + (5471772725920117/100000000000000 : ℝ)*(f.sum) + (6532601138007/866000000000000000000000000 : ℝ)*base65 + (594609340955192839/86600000000000000000000000000000 : ℝ)*base68 + (486820748779607161/86600000000000000000000000000000 : ℝ)*base69 + (9099151071392839/86600000000000000000000000000000 : ℝ)*base72 + (1893085753717/866000000000000000000000000 : ℝ)*base73 + (705885771413007161/86600000000000000000000000000000 : ℝ)*base75 + (407088174937407161/86600000000000000000000000000000 : ℝ)*base77 + (395051827214007161/86600000000000000000000000000000 : ℝ)*base79 + (2884876251173/866000000000000000000000000 : ℝ)*base81 + (98881/19531250000000000000 : ℝ)*base90 + (98881/19531250000000000000 : ℝ)*base92 + (98881/19531250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1212_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16303/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3/32 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (677/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1212_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1212_s4_0 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133237917/10000000000 : ℝ)*x 0 + (5398736361/10000000000 : ℝ)*x 1 + (5260223479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133237917/10000000000 : ℝ)^8405 ≤ (6484097694211/50000000000000 : ℝ)^6357 := by
    have hnat : (2133237917 : ℕ)^8405*50000000000000^6357 ≤ 6484097694211^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133237917 10000000000 6484097694211 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398736361/10000000000 : ℝ)^8405 ≤ (5532942361299/12500000000000 : ℝ)^6357 := by
    have hnat : (5398736361 : ℕ)^8405*12500000000000^6357 ≤ 5532942361299^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398736361 10000000000 5532942361299 12500000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260223479/10000000000 : ℝ)^8405 ≤ (42768265702799/100000000000000 : ℝ)^6357 := by
    have hnat : (5260223479 : ℕ)^8405*100000000000000^6357 ≤ 42768265702799^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260223479 10000000000 42768265702799 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133237917/10000000000 : ℝ), (5398736361/10000000000 : ℝ), (5260223479/10000000000 : ℝ)] ![(6484097694211/50000000000000 : ℝ), (5532942361299/12500000000000 : ℝ), (42768265702799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133237917/10000000000 : ℝ)|^8405 ≤ (6484097694211/50000000000000 : ℝ)^6357
        have hw : |(-2133237917/10000000000 : ℝ)|=(2133237917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398736361/10000000000 : ℝ)|^8405 ≤ (5532942361299/12500000000000 : ℝ)^6357
        have hw : |(5398736361/10000000000 : ℝ)|=(5398736361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260223479/10000000000 : ℝ)|^8405 ≤ (42768265702799/100000000000000 : ℝ)^6357
        have hw : |(5260223479/10000000000 : ℝ)|=(5260223479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s4_1 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668277763/1250000000 : ℝ)*x 0 + (-2203581509/10000000000 : ℝ)*x 1 + (5260223487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668277763/1250000000 : ℝ)^8405 ≤ (21847582431417/50000000000000 : ℝ)^6357 := by
    have hnat : (668277763 : ℕ)^8405*50000000000000^6357 ≤ 21847582431417^6357*1250000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668277763 1250000000 21847582431417 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2203581509/10000000000 : ℝ)^8405 ≤ (6768284671353/50000000000000 : ℝ)^6357 := by
    have hnat : (2203581509 : ℕ)^8405*50000000000000^6357 ≤ 6768284671353^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203581509 10000000000 6768284671353 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260223487/10000000000 : ℝ)^8405 ≤ (21384132894399/50000000000000 : ℝ)^6357 := by
    have hnat : (5260223487 : ℕ)^8405*50000000000000^6357 ≤ 21384132894399^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260223487 10000000000 21384132894399 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668277763/1250000000 : ℝ), (-2203581509/10000000000 : ℝ), (5260223487/10000000000 : ℝ)] ![(21847582431417/50000000000000 : ℝ), (6768284671353/50000000000000 : ℝ), (21384132894399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668277763/1250000000 : ℝ)|^8405 ≤ (21847582431417/50000000000000 : ℝ)^6357
        have hw : |(668277763/1250000000 : ℝ)|=(668277763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2203581509/10000000000 : ℝ)|^8405 ≤ (6768284671353/50000000000000 : ℝ)^6357
        have hw : |(-2203581509/10000000000 : ℝ)|=(2203581509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260223487/10000000000 : ℝ)|^8405 ≤ (21384132894399/50000000000000 : ℝ)^6357
        have hw : |(5260223487/10000000000 : ℝ)|=(5260223487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s4_2 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673111017/5000000000 : ℝ)*x 0 + (5260223557/10000000000 : ℝ)*x 1 + (-2203581509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673111017/5000000000 : ℝ)^8405 ≤ (21847582053201/50000000000000 : ℝ)^6357 := by
    have hnat : (2673111017 : ℕ)^8405*50000000000000^6357 ≤ 21847582053201^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673111017 5000000000 21847582053201 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260223557/10000000000 : ℝ)^8405 ≤ (42768266541289/100000000000000 : ℝ)^6357 := by
    have hnat : (5260223557 : ℕ)^8405*100000000000000^6357 ≤ 42768266541289^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260223557 10000000000 42768266541289 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203581509/10000000000 : ℝ)^8405 ≤ (6768284671353/50000000000000 : ℝ)^6357 := by
    have hnat : (2203581509 : ℕ)^8405*50000000000000^6357 ≤ 6768284671353^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203581509 10000000000 6768284671353 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673111017/5000000000 : ℝ), (5260223557/10000000000 : ℝ), (-2203581509/10000000000 : ℝ)] ![(21847582053201/50000000000000 : ℝ), (42768266541289/100000000000000 : ℝ), (6768284671353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673111017/5000000000 : ℝ)|^8405 ≤ (21847582053201/50000000000000 : ℝ)^6357
        have hw : |(2673111017/5000000000 : ℝ)|=(2673111017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260223557/10000000000 : ℝ)|^8405 ≤ (42768266541289/100000000000000 : ℝ)^6357
        have hw : |(5260223557/10000000000 : ℝ)|=(5260223557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2203581509/10000000000 : ℝ)|^8405 ≤ (6768284671353/50000000000000 : ℝ)^6357
        have hw : |(-2203581509/10000000000 : ℝ)|=(2203581509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s4_3 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177271279/5000000000 : ℝ)*x 0 + (2108528501/5000000000 : ℝ)*x 1 + (562051657/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177271279/5000000000 : ℝ)^8405 ≤ (16656840683761/50000000000000 : ℝ)^6357 := by
    have hnat : (2177271279 : ℕ)^8405*50000000000000^6357 ≤ 16656840683761^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177271279 5000000000 16656840683761 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108528501/5000000000 : ℝ)^8405 ≤ (1596506986763/5000000000000 : ℝ)^6357 := by
    have hnat : (2108528501 : ℕ)^8405*5000000000000^6357 ≤ 1596506986763^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108528501 5000000000 1596506986763 5000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562051657/1250000000 : ℝ)^8405 ≤ (17378089439641/50000000000000 : ℝ)^6357 := by
    have hnat : (562051657 : ℕ)^8405*50000000000000^6357 ≤ 17378089439641^6357*1250000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562051657 1250000000 17378089439641 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177271279/5000000000 : ℝ), (2108528501/5000000000 : ℝ), (562051657/1250000000 : ℝ)] ![(16656840683761/50000000000000 : ℝ), (1596506986763/5000000000000 : ℝ), (17378089439641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177271279/5000000000 : ℝ)|^8405 ≤ (16656840683761/50000000000000 : ℝ)^6357
        have hw : |(2177271279/5000000000 : ℝ)|=(2177271279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2108528501/5000000000 : ℝ)|^8405 ≤ (1596506986763/5000000000000 : ℝ)^6357
        have hw : |(2108528501/5000000000 : ℝ)|=(2108528501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562051657/1250000000 : ℝ)|^8405 ≤ (17378089439641/50000000000000 : ℝ)^6357
        have hw : |(562051657/1250000000 : ℝ)|=(562051657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s4_4 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133244407/10000000000 : ℝ)*x 0 + (1052121979/2000000000 : ℝ)*x 1 + (2699174173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133244407/10000000000 : ℝ)^8405 ≤ (2593649510479/20000000000000 : ℝ)^6357 := by
    have hnat : (2133244407 : ℕ)^8405*20000000000000^6357 ≤ 2593649510479^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133244407 10000000000 2593649510479 20000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052121979/2000000000 : ℝ)^8405 ≤ (21386209835607/50000000000000 : ℝ)^6357 := by
    have hnat : (1052121979 : ℕ)^8405*50000000000000^6357 ≤ 21386209835607^6357*2000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052121979 2000000000 21386209835607 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699174173/5000000000 : ℝ)^8405 ≤ (44259332757341/100000000000000 : ℝ)^6357 := by
    have hnat : (2699174173 : ℕ)^8405*100000000000000^6357 ≤ 44259332757341^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699174173 5000000000 44259332757341 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133244407/10000000000 : ℝ), (1052121979/2000000000 : ℝ), (2699174173/5000000000 : ℝ)] ![(2593649510479/20000000000000 : ℝ), (21386209835607/50000000000000 : ℝ), (44259332757341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133244407/10000000000 : ℝ)|^8405 ≤ (2593649510479/20000000000000 : ℝ)^6357
        have hw : |(-2133244407/10000000000 : ℝ)|=(2133244407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052121979/2000000000 : ℝ)|^8405 ≤ (21386209835607/50000000000000 : ℝ)^6357
        have hw : |(1052121979/2000000000 : ℝ)|=(1052121979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699174173/5000000000 : ℝ)|^8405 ≤ (44259332757341/100000000000000 : ℝ)^6357
        have hw : |(2699174173/5000000000 : ℝ)|=(2699174173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s4_5 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655477023/5000000000 : ℝ)*x 0 + (-2065457203/10000000000 : ℝ)*x 1 + (5398348249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655477023/5000000000 : ℝ)^8405 ≤ (21657228867799/50000000000000 : ℝ)^6357 := by
    have hnat : (2655477023 : ℕ)^8405*50000000000000^6357 ≤ 21657228867799^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655477023 5000000000 21657228867799 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065457203/10000000000 : ℝ)^8405 ≤ (12426210548483/100000000000000 : ℝ)^6357 := by
    have hnat : (2065457203 : ℕ)^8405*100000000000000^6357 ≤ 12426210548483^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065457203 10000000000 12426210548483 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398348249/10000000000 : ℝ)^8405 ≤ (44259331705861/100000000000000 : ℝ)^6357 := by
    have hnat : (5398348249 : ℕ)^8405*100000000000000^6357 ≤ 44259331705861^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398348249 10000000000 44259331705861 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655477023/5000000000 : ℝ), (-2065457203/10000000000 : ℝ), (5398348249/10000000000 : ℝ)] ![(21657228867799/50000000000000 : ℝ), (12426210548483/100000000000000 : ℝ), (44259331705861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655477023/5000000000 : ℝ)|^8405 ≤ (21657228867799/50000000000000 : ℝ)^6357
        have hw : |(2655477023/5000000000 : ℝ)|=(2655477023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2065457203/10000000000 : ℝ)|^8405 ≤ (12426210548483/100000000000000 : ℝ)^6357
        have hw : |(-2065457203/10000000000 : ℝ)|=(2065457203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398348249/10000000000 : ℝ)|^8405 ≤ (44259331705861/100000000000000 : ℝ)^6357
        have hw : |(5398348249/10000000000 : ℝ)|=(5398348249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s4_6 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310954307/10000000000 : ℝ)*x 0 + (2699174087/5000000000 : ℝ)*x 1 + (-2065456951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310954307/10000000000 : ℝ)^8405 ≤ (43314460550001/100000000000000 : ℝ)^6357 := by
    have hnat : (5310954307 : ℕ)^8405*100000000000000^6357 ≤ 43314460550001^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310954307 10000000000 43314460550001 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699174087/5000000000 : ℝ)^8405 ≤ (2212966544643/5000000000000 : ℝ)^6357 := by
    have hnat : (2699174087 : ℕ)^8405*5000000000000^6357 ≤ 2212966544643^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699174087 5000000000 2212966544643 5000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065456951/10000000000 : ℝ)^8405 ≤ (12426208543971/100000000000000 : ℝ)^6357 := by
    have hnat : (2065456951 : ℕ)^8405*100000000000000^6357 ≤ 12426208543971^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065456951 10000000000 12426208543971 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310954307/10000000000 : ℝ), (2699174087/5000000000 : ℝ), (-2065456951/10000000000 : ℝ)] ![(43314460550001/100000000000000 : ℝ), (2212966544643/5000000000000 : ℝ), (12426208543971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310954307/10000000000 : ℝ)|^8405 ≤ (43314460550001/100000000000000 : ℝ)^6357
        have hw : |(5310954307/10000000000 : ℝ)|=(5310954307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699174087/5000000000 : ℝ)|^8405 ≤ (2212966544643/5000000000000 : ℝ)^6357
        have hw : |(2699174087/5000000000 : ℝ)|=(2699174087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2065456951/10000000000 : ℝ)|^8405 ≤ (12426208543971/100000000000000 : ℝ)^6357
        have hw : |(-2065456951/10000000000 : ℝ)|=(2065456951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s4_7 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177277729/5000000000 : ℝ)*x 0 + (561954217/1250000000 : ℝ)*x 1 + (2108919859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177277729/5000000000 : ℝ)^8405 ≤ (33313811850997/100000000000000 : ℝ)^6357 := by
    have hnat : (2177277729 : ℕ)^8405*100000000000000^6357 ≤ 33313811850997^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177277729 5000000000 33313811850997 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561954217/1250000000 : ℝ)^8405 ≤ (434352654997/1250000000000 : ℝ)^6357 := by
    have hnat : (561954217 : ℕ)^8405*1250000000000^6357 ≤ 434352654997^6357*1250000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561954217 1250000000 434352654997 1250000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108919859/5000000000 : ℝ)^8405 ≤ (15968987864221/50000000000000 : ℝ)^6357 := by
    have hnat : (2108919859 : ℕ)^8405*50000000000000^6357 ≤ 15968987864221^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108919859 5000000000 15968987864221 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177277729/5000000000 : ℝ), (561954217/1250000000 : ℝ), (2108919859/5000000000 : ℝ)] ![(33313811850997/100000000000000 : ℝ), (434352654997/1250000000000 : ℝ), (15968987864221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177277729/5000000000 : ℝ)|^8405 ≤ (33313811850997/100000000000000 : ℝ)^6357
        have hw : |(2177277729/5000000000 : ℝ)|=(2177277729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561954217/1250000000 : ℝ)|^8405 ≤ (434352654997/1250000000000 : ℝ)^6357
        have hw : |(561954217/1250000000 : ℝ)|=(561954217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2108919859/5000000000 : ℝ)|^8405 ≤ (15968987864221/50000000000000 : ℝ)^6357
        have hw : |(2108919859/5000000000 : ℝ)|=(2108919859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1212_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (677/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5651/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (677/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (677/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (677/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (677/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (677/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (677/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (677/6250 : ℝ) ^ (2101/512 : ℝ) ≤ (5468671954601921/50000000000000000000 : ℝ) := by
    have hpowers : (677/6250 : ℝ)^2101 ≤ (5468671954601921/50000000000000000000 : ℝ)^512 := by
      have hnat : (677 : ℕ)^2101*50000000000000000000^512 ≤ 5468671954601921^512*6250^2101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        677 6250 5468671954601921 50000000000000000000 2101 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (677/6250 : ℝ)) (X := (5468671954601921/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14729/100000 : ℝ) ^ (2101/512 : ℝ) ≤ (38599882621181763/100000000000000000000 : ℝ) := by
    have hpowers : (14729/100000 : ℝ)^2101 ≤ (38599882621181763/100000000000000000000 : ℝ)^512 := by
      have hnat : (14729 : ℕ)^2101*100000000000000000000^512 ≤ 38599882621181763^512*100000^2101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14729 100000 38599882621181763 100000000000000000000 2101 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14729/100000 : ℝ)) (X := (38599882621181763/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005468671954601921/25000000000000000000 : ℝ) ≤ (10000533027788321/10000000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (25005468671954601921/25000000000000000000 : ℝ)^512 ≤ (10000533027788321/10000000000000000 : ℝ)^2101 := by
      have hnat : (25005468671954601921 : ℕ)^512*10000000000000000^2101 ≤ 10000533027788321^2101*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005468671954601921 25000000000000000000 10000533027788321 10000000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000533027788321/10000000000000000 : ℝ)) (X := (25005468671954601921/25000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009907445306077121/20000000000000000000 : ℝ) ≤ (5000603481917759/5000000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (20009907445306077121/20000000000000000000 : ℝ)^512 ≤ (5000603481917759/5000000000000000 : ℝ)^2101 := by
      have hnat : (20009907445306077121 : ℕ)^512*5000000000000000^2101 ≤ 5000603481917759^2101*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009907445306077121 20000000000000000000 5000603481917759 5000000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000603481917759/5000000000000000 : ℝ)) (X := (20009907445306077121/20000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038599882621181763/50000000000000000000 : ℝ) ≤ (2000376179976543/2000000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (50038599882621181763/50000000000000000000 : ℝ)^512 ≤ (2000376179976543/2000000000000000 : ℝ)^2101 := by
      have hnat : (50038599882621181763 : ℕ)^512*2000000000000000^2101 ≤ 2000376179976543^2101*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038599882621181763 50000000000000000000 2000376179976543 2000000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000376179976543/2000000000000000 : ℝ)) (X := (50038599882621181763/50000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5468671954601921/50000000000000000000 : ℝ) ≤ ((38957477058764611129/38970000000000000000 : ℝ)+2*(673936047197/389700000000000 : ℝ)*(677/6250 : ℝ))^(2101/512 : ℝ) := by
    rw [show (38957477058764611129/38970000000000000000 : ℝ)+2*(673936047197/389700000000000 : ℝ)*(677/6250 : ℝ)=(10000533027788321/10000000000000000 : ℝ) by norm_num, show 1+2*(5468671954601921/50000000000000000000 : ℝ)=(25005468671954601921/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38599882621181763/100000000000000000000 : ℝ)+(5468671954601921/50000000000000000000 : ℝ) ≤ ((38957477058764611129/38970000000000000000 : ℝ)+(673936047197/389700000000000 : ℝ)*((14729/100000 : ℝ)+(677/6250 : ℝ)))^(2101/512 : ℝ) := by
    rw [show (38957477058764611129/38970000000000000000 : ℝ)+(673936047197/389700000000000 : ℝ)*((14729/100000 : ℝ)+(677/6250 : ℝ))=(5000603481917759/5000000000000000 : ℝ) by norm_num, show 1+(38599882621181763/100000000000000000000 : ℝ)+(5468671954601921/50000000000000000000 : ℝ)=(20009907445306077121/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38599882621181763/100000000000000000000 : ℝ) ≤ ((38957477058764611129/38970000000000000000 : ℝ)+2*(673936047197/389700000000000 : ℝ)*(14729/100000 : ℝ))^(2101/512 : ℝ) := by
    rw [show (38957477058764611129/38970000000000000000 : ℝ)+2*(673936047197/389700000000000 : ℝ)*(14729/100000 : ℝ)=(2000376179976543/2000000000000000 : ℝ) by norm_num, show 1+2*(38599882621181763/100000000000000000000 : ℝ)=(50038599882621181763/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38957477058764611129/38970000000000000000 : ℝ)*(X 1 0+X 2 0)+(673936047197/389700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (677/6250 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (38957477058764611129/38970000000000000000 : ℝ)) (alpha := (673936047197/389700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38957477058764611129/38970000000000000000 : ℝ)*(X 0 1+X 2 1)+(673936047197/389700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (677/6250 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (38957477058764611129/38970000000000000000 : ℝ)) (alpha := (673936047197/389700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38957477058764611129/38970000000000000000 : ℝ)*(X 0 2+X 1 2)+(673936047197/389700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (677/6250 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (38957477058764611129/38970000000000000000 : ℝ)) (alpha := (673936047197/389700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2133237917/10000000000 : ℝ)*X 0 0+(5398736361/10000000000 : ℝ)*X 0 1+(5260223479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668277763/1250000000 : ℝ)*X 1 0+(-2203581509/10000000000 : ℝ)*X 1 1+(5260223487/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673111017/5000000000 : ℝ)*X 2 0+(5260223557/10000000000 : ℝ)*X 2 1+(-2203581509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177271279/5000000000 : ℝ)*X 0 0+(2108528501/5000000000 : ℝ)*X 0 1+(562051657/1250000000 : ℝ)*X 0 2+(2177271279/5000000000 : ℝ)*X 1 0+(2108528501/5000000000 : ℝ)*X 1 1+(562051657/1250000000 : ℝ)*X 1 2+(2177271279/5000000000 : ℝ)*X 2 0+(2108528501/5000000000 : ℝ)*X 2 1+(562051657/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2133244407/10000000000 : ℝ)*X 0 0+(1052121979/2000000000 : ℝ)*X 0 1+(2699174173/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655477023/5000000000 : ℝ)*X 1 0+(-2065457203/10000000000 : ℝ)*X 1 1+(5398348249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310954307/10000000000 : ℝ)*X 2 0+(2699174087/5000000000 : ℝ)*X 2 1+(-2065456951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177277729/5000000000 : ℝ)*X 0 0+(561954217/1250000000 : ℝ)*X 0 1+(2108919859/5000000000 : ℝ)*X 0 2+(2177277729/5000000000 : ℝ)*X 1 0+(561954217/1250000000 : ℝ)*X 1 1+(2108919859/5000000000 : ℝ)*X 1 2+(2177277729/5000000000 : ℝ)*X 2 0+(561954217/1250000000 : ℝ)*X 2 1+(2108919859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15643582245944516392931/6495000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48744673/12500000000000 : ℝ)*(base19) + (280595069/100000000000000 : ℝ)*(base23) + (12961511/25000000000000 : ℝ)*(lower2) + (1438833/5000000000000 : ℝ)*(upper3) + (21957757/50000000000000 : ℝ)*(lower4) + (5399619813440687/100000000000000 : ℝ)*(major0) + (5399619813440687/100000000000000 : ℝ)*(major1) + (5399619813440687/100000000000000 : ℝ)*(major2) + (721955874513573/10000000000000 : ℝ)*(sp0) + (7219570071394567/100000000000000 : ℝ)*(sp1) + (3609785090378441/50000000000000 : ℝ)*(sp2) + (715932742656021/20000000000000 : ℝ)*(sp3) + (11716216221/100000000000000 : ℝ)*(sp4) + (5371964053/100000000000000 : ℝ)*(sp7) + (1789834542622079/50000000000000 : ℝ)*(f.failure) + (7219570461351951/100000000000000 : ℝ)*(f.sum) + (20555807027611/4871250000000000000000000000 : ℝ)*base65 + (2417329193397277153/433000000000000000000000000000000 : ℝ)*base68 + (99599555411722847/433000000000000000000000000000000 : ℝ)*base69 + (6236069163465722847/433000000000000000000000000000000 : ℝ)*base71 + (548266140379/1217812500000000000000000000 : ℝ)*base73 + (2574638751557277153/433000000000000000000000000000000 : ℝ)*base76 + (544444797805722847/433000000000000000000000000000000 : ℝ)*base77 + (5536177943314277153/433000000000000000000000000000000 : ℝ)*base80 + (112729545307721/19485000000000000000000000000 : ℝ)*base82 + (1046011/156250000000000000000 : ℝ)*base90 + (1046011/156250000000000000000 : ℝ)*base92 + (1046011/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (194234755491290823873389851/27062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27971269/10000000000000 : ℝ)*(base19) + (20978629/2500000000000 : ℝ)*(base23) + (2576201/6250000000000 : ℝ)*(upper3) + (31002413/50000000000000 : ℝ)*(lower4) + (40482343/20000000000000 : ℝ)*(upper5) + (1357491881191143/25000000000000 : ℝ)*(major0) + (1357491881191143/25000000000000 : ℝ)*(major1) + (1357491881191143/25000000000000 : ℝ)*(major2) + (1235940621/100000000000000 : ℝ)*(sp1) + (14170548519/100000000000000 : ℝ)*(sp2) + (1815036689918369/25000000000000 : ℝ)*(sp4) + (7260145244020167/100000000000000 : ℝ)*(sp5) + (7260131749979797/100000000000000 : ℝ)*(sp6) + (449973506326683/12500000000000 : ℝ)*(sp7) + (449973506326683/12500000000000 : ℝ)*(f.failure) + (1815036689918369/25000000000000 : ℝ)*(f.sum) + (1318390098391/811875000000000000000000000 : ℝ)*base65 + (917687534924903383/108250000000000000000000000000000 : ℝ)*base67 + (1126970797101903383/108250000000000000000000000000000 : ℝ)*base69 + (425912953429403383/108250000000000000000000000000000 : ℝ)*base71 + (10648911757601/3247500000000000000000000000 : ℝ)*base74 + (1050975799111403383/108250000000000000000000000000000 : ℝ)*base75 + (194150738707346617/108250000000000000000000000000000 : ℝ)*base78 + (3936513984461653383/108250000000000000000000000000000 : ℝ)*base79 + (7585147253801/3247500000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base85 + (447753/39062500000000000000 : ℝ)*base89 + (447753/39062500000000000000 : ℝ)*base91 + (447753/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1212_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (677/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1212_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1212_s5_0 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066866933/5000000000 : ℝ)*x 0 + (1078627357/2000000000 : ℝ)*x 1 + (5265497513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066866933/5000000000 : ℝ)^8405 ≤ (6486090885789/50000000000000 : ℝ)^6357 := by
    have hnat : (1066866933 : ℕ)^8405*50000000000000^6357 ≤ 6486090885789^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066866933 5000000000 6486090885789 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078627357/2000000000 : ℝ)^8405 ≤ (44202848199669/100000000000000 : ℝ)^6357 := by
    have hnat : (1078627357 : ℕ)^8405*100000000000000^6357 ≤ 44202848199669^6357*2000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078627357 2000000000 44202848199669 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265497513/10000000000 : ℝ)^8405 ≤ (42824970002981/100000000000000 : ℝ)^6357 := by
    have hnat : (5265497513 : ℕ)^8405*100000000000000^6357 ≤ 42824970002981^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265497513 10000000000 42824970002981 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066866933/5000000000 : ℝ), (1078627357/2000000000 : ℝ), (5265497513/10000000000 : ℝ)] ![(6486090885789/50000000000000 : ℝ), (44202848199669/100000000000000 : ℝ), (42824970002981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066866933/5000000000 : ℝ)|^8405 ≤ (6486090885789/50000000000000 : ℝ)^6357
        have hw : |(-1066866933/5000000000 : ℝ)|=(1066866933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078627357/2000000000 : ℝ)|^8405 ≤ (44202848199669/100000000000000 : ℝ)^6357
        have hw : |(1078627357/2000000000 : ℝ)|=(1078627357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265497513/10000000000 : ℝ)|^8405 ≤ (42824970002981/100000000000000 : ℝ)^6357
        have hw : |(5265497513/10000000000 : ℝ)|=(5265497513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s5_1 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344809973/10000000000 : ℝ)*x 0 + (-2198476803/10000000000 : ℝ)*x 1 + (658187189/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344809973/10000000000 : ℝ)^8405 ≤ (21839952890559/50000000000000 : ℝ)^6357 := by
    have hnat : (5344809973 : ℕ)^8405*50000000000000^6357 ≤ 21839952890559^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344809973 10000000000 21839952890559 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198476803/10000000000 : ℝ)^8405 ≤ (6747562103819/50000000000000 : ℝ)^6357 := by
    have hnat : (2198476803 : ℕ)^8405*50000000000000^6357 ≤ 6747562103819^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198476803 10000000000 6747562103819 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658187189/1250000000 : ℝ)^8405 ≤ (10706242498057/25000000000000 : ℝ)^6357 := by
    have hnat : (658187189 : ℕ)^8405*25000000000000^6357 ≤ 10706242498057^6357*1250000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658187189 1250000000 10706242498057 25000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344809973/10000000000 : ℝ), (-2198476803/10000000000 : ℝ), (658187189/1250000000 : ℝ)] ![(21839952890559/50000000000000 : ℝ), (6747562103819/50000000000000 : ℝ), (10706242498057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344809973/10000000000 : ℝ)|^8405 ≤ (21839952890559/50000000000000 : ℝ)^6357
        have hw : |(5344809973/10000000000 : ℝ)|=(5344809973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2198476803/10000000000 : ℝ)|^8405 ≤ (6747562103819/50000000000000 : ℝ)^6357
        have hw : |(-2198476803/10000000000 : ℝ)|=(2198476803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658187189/1250000000 : ℝ)|^8405 ≤ (10706242498057/25000000000000 : ℝ)^6357
        have hw : |(658187189/1250000000 : ℝ)|=(658187189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s5_2 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672404989/5000000000 : ℝ)*x 0 + (5265497507/10000000000 : ℝ)*x 1 + (-2198476803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672404989/5000000000 : ℝ)^8405 ≤ (5459988229393/12500000000000 : ℝ)^6357 := by
    have hnat : (2672404989 : ℕ)^8405*12500000000000^6357 ≤ 5459988229393^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672404989 5000000000 5459988229393 12500000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265497507/10000000000 : ℝ)^8405 ≤ (42824969938461/100000000000000 : ℝ)^6357 := by
    have hnat : (5265497507 : ℕ)^8405*100000000000000^6357 ≤ 42824969938461^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265497507 10000000000 42824969938461 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198476803/10000000000 : ℝ)^8405 ≤ (6747562103819/50000000000000 : ℝ)^6357 := by
    have hnat : (2198476803 : ℕ)^8405*50000000000000^6357 ≤ 6747562103819^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198476803 10000000000 6747562103819 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672404989/5000000000 : ℝ), (5265497507/10000000000 : ℝ), (-2198476803/10000000000 : ℝ)] ![(5459988229393/12500000000000 : ℝ), (42824969938461/100000000000000 : ℝ), (6747562103819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672404989/5000000000 : ℝ)|^8405 ≤ (5459988229393/12500000000000 : ℝ)^6357
        have hw : |(2672404989/5000000000 : ℝ)|=(2672404989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265497507/10000000000 : ℝ)|^8405 ≤ (42824969938461/100000000000000 : ℝ)^6357
        have hw : |(5265497507/10000000000 : ℝ)|=(5265497507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2198476803/10000000000 : ℝ)|^8405 ≤ (6747562103819/50000000000000 : ℝ)^6357
        have hw : |(-2198476803/10000000000 : ℝ)|=(2198476803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s5_3 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (68044303/156250000 : ℝ)*x 0 + (1056996103/2500000000 : ℝ)*x 1 + (2242705353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68044303/156250000 : ℝ)^8405 ≤ (16658321706761/50000000000000 : ℝ)^6357 := by
    have hnat : (68044303 : ℕ)^8405*50000000000000^6357 ≤ 16658321706761^6357*156250000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68044303 156250000 16658321706761 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056996103/2500000000 : ℝ)^8405 ≤ (32039579518531/100000000000000 : ℝ)^6357 := by
    have hnat : (1056996103 : ℕ)^8405*100000000000000^6357 ≤ 32039579518531^6357*2500000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056996103 2500000000 32039579518531 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242705353/5000000000 : ℝ)^8405 ≤ (8660944264359/25000000000000 : ℝ)^6357 := by
    have hnat : (2242705353 : ℕ)^8405*25000000000000^6357 ≤ 8660944264359^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242705353 5000000000 8660944264359 25000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68044303/156250000 : ℝ), (1056996103/2500000000 : ℝ), (2242705353/5000000000 : ℝ)] ![(16658321706761/50000000000000 : ℝ), (32039579518531/100000000000000 : ℝ), (8660944264359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68044303/156250000 : ℝ)|^8405 ≤ (16658321706761/50000000000000 : ℝ)^6357
        have hw : |(68044303/156250000 : ℝ)|=(68044303/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056996103/2500000000 : ℝ)|^8405 ≤ (32039579518531/100000000000000 : ℝ)^6357
        have hw : |(1056996103/2500000000 : ℝ)|=(1056996103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242705353/5000000000 : ℝ)|^8405 ≤ (8660944264359/25000000000000 : ℝ)^6357
        have hw : |(2242705353/5000000000 : ℝ)|=(2242705353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s5_4 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133738911/10000000000 : ℝ)*x 0 + (5265825911/10000000000 : ℝ)*x 1 + (1348201791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133738911/10000000000 : ℝ)^8405 ≤ (12972222324263/100000000000000 : ℝ)^6357 := by
    have hnat : (2133738911 : ℕ)^8405*100000000000000^6357 ≤ 12972222324263^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133738911 10000000000 12972222324263 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265825911/10000000000 : ℝ)^8405 ≤ (42828501412053/100000000000000 : ℝ)^6357 := by
    have hnat : (5265825911 : ℕ)^8405*100000000000000^6357 ≤ 42828501412053^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265825911 10000000000 42828501412053 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348201791/2500000000 : ℝ)^8405 ≤ (8839855250673/20000000000000 : ℝ)^6357 := by
    have hnat : (1348201791 : ℕ)^8405*20000000000000^6357 ≤ 8839855250673^6357*2500000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348201791 2500000000 8839855250673 20000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133738911/10000000000 : ℝ), (5265825911/10000000000 : ℝ), (1348201791/2500000000 : ℝ)] ![(12972222324263/100000000000000 : ℝ), (42828501412053/100000000000000 : ℝ), (8839855250673/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133738911/10000000000 : ℝ)|^8405 ≤ (12972222324263/100000000000000 : ℝ)^6357
        have hw : |(-2133738911/10000000000 : ℝ)|=(2133738911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265825911/10000000000 : ℝ)|^8405 ≤ (42828501412053/100000000000000 : ℝ)^6357
        have hw : |(5265825911/10000000000 : ℝ)|=(5265825911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348201791/2500000000 : ℝ)|^8405 ≤ (8839855250673/20000000000000 : ℝ)^6357
        have hw : |(1348201791/2500000000 : ℝ)|=(1348201791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s5_5 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656154731/5000000000 : ℝ)*x 0 + (-2071167093/10000000000 : ℝ)*x 1 + (5392807179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656154731/5000000000 : ℝ)^8405 ≤ (21664536998557/50000000000000 : ℝ)^6357 := by
    have hnat : (2656154731 : ℕ)^8405*50000000000000^6357 ≤ 21664536998557^6357*5000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656154731 5000000000 21664536998557 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071167093/10000000000 : ℝ)^8405 ≤ (12471649571599/100000000000000 : ℝ)^6357 := by
    have hnat : (2071167093 : ℕ)^8405*100000000000000^6357 ≤ 12471649571599^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071167093 10000000000 12471649571599 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392807179/10000000000 : ℝ)^8405 ≤ (44199276415911/100000000000000 : ℝ)^6357 := by
    have hnat : (5392807179 : ℕ)^8405*100000000000000^6357 ≤ 44199276415911^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392807179 10000000000 44199276415911 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656154731/5000000000 : ℝ), (-2071167093/10000000000 : ℝ), (5392807179/10000000000 : ℝ)] ![(21664536998557/50000000000000 : ℝ), (12471649571599/100000000000000 : ℝ), (44199276415911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656154731/5000000000 : ℝ)|^8405 ≤ (21664536998557/50000000000000 : ℝ)^6357
        have hw : |(2656154731/5000000000 : ℝ)|=(2656154731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2071167093/10000000000 : ℝ)|^8405 ≤ (12471649571599/100000000000000 : ℝ)^6357
        have hw : |(-2071167093/10000000000 : ℝ)|=(2071167093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392807179/10000000000 : ℝ)|^8405 ≤ (44199276415911/100000000000000 : ℝ)^6357
        have hw : |(5392807179/10000000000 : ℝ)|=(5392807179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s5_6 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664038677/1250000000 : ℝ)*x 0 + (5392807219/10000000000 : ℝ)*x 1 + (-2071167101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664038677/1250000000 : ℝ)^8405 ≤ (5416134187631/12500000000000 : ℝ)^6357 := by
    have hnat : (664038677 : ℕ)^8405*12500000000000^6357 ≤ 5416134187631^6357*1250000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664038677 1250000000 5416134187631 12500000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392807219/10000000000 : ℝ)^8405 ≤ (5524909606171/12500000000000 : ℝ)^6357 := by
    have hnat : (5392807219 : ℕ)^8405*12500000000000^6357 ≤ 5524909606171^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392807219 10000000000 5524909606171 12500000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2071167101/10000000000 : ℝ)^8405 ≤ (12471649635291/100000000000000 : ℝ)^6357 := by
    have hnat : (2071167101 : ℕ)^8405*100000000000000^6357 ≤ 12471649635291^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071167101 10000000000 12471649635291 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664038677/1250000000 : ℝ), (5392807219/10000000000 : ℝ), (-2071167101/10000000000 : ℝ)] ![(5416134187631/12500000000000 : ℝ), (5524909606171/12500000000000 : ℝ), (12471649635291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664038677/1250000000 : ℝ)|^8405 ≤ (5416134187631/12500000000000 : ℝ)^6357
        have hw : |(664038677/1250000000 : ℝ)|=(664038677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392807219/10000000000 : ℝ)|^8405 ≤ (5524909606171/12500000000000 : ℝ)^6357
        have hw : |(5392807219/10000000000 : ℝ)|=(5392807219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2071167101/10000000000 : ℝ)|^8405 ≤ (12471649635291/100000000000000 : ℝ)^6357
        have hw : |(-2071167101/10000000000 : ℝ)|=(2071167101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1212_s5_7 (p : ℝ) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (544355703/1250000000 : ℝ)*x 0 + (4484748341/10000000000 : ℝ)*x 1 + (4228649147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544355703/1250000000 : ℝ)^8405 ≤ (16658373456207/50000000000000 : ℝ)^6357 := by
    have hnat : (544355703 : ℕ)^8405*50000000000000^6357 ≤ 16658373456207^6357*1250000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544355703 1250000000 16658373456207 50000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484748341/10000000000 : ℝ)^8405 ≤ (34637013182469/100000000000000 : ℝ)^6357 := by
    have hnat : (4484748341 : ℕ)^8405*100000000000000^6357 ≤ 34637013182469^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484748341 10000000000 34637013182469 100000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228649147/10000000000 : ℝ)^8405 ≤ (640924797809/2000000000000 : ℝ)^6357 := by
    have hnat : (4228649147 : ℕ)^8405*2000000000000^6357 ≤ 640924797809^6357*10000000000^8405 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228649147 10000000000 640924797809 2000000000000 8405 6357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8405/2048 : ℝ)) 8405 6357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544355703/1250000000 : ℝ), (4484748341/10000000000 : ℝ), (4228649147/10000000000 : ℝ)] ![(16658373456207/50000000000000 : ℝ), (34637013182469/100000000000000 : ℝ), (640924797809/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544355703/1250000000 : ℝ)|^8405 ≤ (16658373456207/50000000000000 : ℝ)^6357
        have hw : |(544355703/1250000000 : ℝ)|=(544355703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484748341/10000000000 : ℝ)|^8405 ≤ (34637013182469/100000000000000 : ℝ)^6357
        have hw : |(4484748341/10000000000 : ℝ)|=(4484748341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228649147/10000000000 : ℝ)|^8405 ≤ (640924797809/2000000000000 : ℝ)^6357
        have hw : |(4228649147/10000000000 : ℝ)|=(4228649147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1212_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5707/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7059/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5651/50000 : ℝ) ^ (2101/512 : ℝ) ≤ (13019910271897821/100000000000000000000 : ℝ) := by
    have hpowers : (5651/50000 : ℝ)^2101 ≤ (13019910271897821/100000000000000000000 : ℝ)^512 := by
      have hnat : (5651 : ℕ)^2101*100000000000000000000^512 ≤ 13019910271897821^512*50000^2101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5651 50000 13019910271897821 100000000000000000000 2101 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5651/50000 : ℝ)) (X := (13019910271897821/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (2101/512 : ℝ) ≤ (4194683217186317/12500000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^2101 ≤ (4194683217186317/12500000000000000000 : ℝ)^512 := by
      have hnat : (2847 : ℕ)^2101*12500000000000000000^512 ≤ 4194683217186317^512*20000^2101 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 4194683217186317 12500000000000000000 2101 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (4194683217186317/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013019910271897821/50000000000000000000 : ℝ) ≤ (10000634510969659/10000000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (50013019910271897821/50000000000000000000 : ℝ)^512 ≤ (10000634510969659/10000000000000000 : ℝ)^2101 := by
      have hnat : (50013019910271897821 : ℕ)^512*10000000000000000^2101 ≤ 10000634510969659^2101*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013019910271897821 50000000000000000000 10000634510969659 10000000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000634510969659/10000000000000000 : ℝ)) (X := (50013019910271897821/50000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046577376009388357/100000000000000000000 : ℝ) ≤ (10001134860413561/10000000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (100046577376009388357/100000000000000000000 : ℝ)^512 ≤ (10001134860413561/10000000000000000 : ℝ)^2101 := by
      have hnat : (100046577376009388357 : ℕ)^512*10000000000000000^2101 ≤ 10001134860413561^2101*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046577376009388357 100000000000000000000 10001134860413561 10000000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001134860413561/10000000000000000 : ℝ)) (X := (100046577376009388357/100000000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254194683217186317/6250000000000000000 : ℝ) ≤ (10001635209857463/10000000000000000 : ℝ) ^ (2101/512 : ℝ) := by
    have hpowers : (6254194683217186317/6250000000000000000 : ℝ)^512 ≤ (10001635209857463/10000000000000000 : ℝ)^2101 := by
      have hnat : (6254194683217186317 : ℕ)^512*10000000000000000^2101 ≤ 10001635209857463^2101*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254194683217186317 6250000000000000000 10001635209857463 10000000000000000 512 2101 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001635209857463/10000000000000000 : ℝ)) (X := (6254194683217186317/6250000000000000000 : ℝ)) (by norm_num) 2101 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13019910271897821/100000000000000000000 : ℝ) ≤ ((4188650160263435577/4190000000000000000 : ℝ)+2*(35739245993/20950000000000 : ℝ)*(5651/50000 : ℝ))^(2101/512 : ℝ) := by
    rw [show (4188650160263435577/4190000000000000000 : ℝ)+2*(35739245993/20950000000000 : ℝ)*(5651/50000 : ℝ)=(10000634510969659/10000000000000000 : ℝ) by norm_num, show 1+2*(13019910271897821/100000000000000000000 : ℝ)=(50013019910271897821/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4194683217186317/12500000000000000000 : ℝ)+(13019910271897821/100000000000000000000 : ℝ) ≤ ((4188650160263435577/4190000000000000000 : ℝ)+(35739245993/20950000000000 : ℝ)*((2847/20000 : ℝ)+(5651/50000 : ℝ)))^(2101/512 : ℝ) := by
    rw [show (4188650160263435577/4190000000000000000 : ℝ)+(35739245993/20950000000000 : ℝ)*((2847/20000 : ℝ)+(5651/50000 : ℝ))=(10001134860413561/10000000000000000 : ℝ) by norm_num, show 1+(4194683217186317/12500000000000000000 : ℝ)+(13019910271897821/100000000000000000000 : ℝ)=(100046577376009388357/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4194683217186317/12500000000000000000 : ℝ) ≤ ((4188650160263435577/4190000000000000000 : ℝ)+2*(35739245993/20950000000000 : ℝ)*(2847/20000 : ℝ))^(2101/512 : ℝ) := by
    rw [show (4188650160263435577/4190000000000000000 : ℝ)+2*(35739245993/20950000000000 : ℝ)*(2847/20000 : ℝ)=(10001635209857463/10000000000000000 : ℝ) by norm_num, show 1+2*(4194683217186317/12500000000000000000 : ℝ)=(6254194683217186317/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4188650160263435577/4190000000000000000 : ℝ)*(X 1 0+X 2 0)+(35739245993/20950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (4188650160263435577/4190000000000000000 : ℝ)) (alpha := (35739245993/20950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4188650160263435577/4190000000000000000 : ℝ)*(X 0 1+X 2 1)+(35739245993/20950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (4188650160263435577/4190000000000000000 : ℝ)) (alpha := (35739245993/20950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4188650160263435577/4190000000000000000 : ℝ)*(X 0 2+X 1 2)+(35739245993/20950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2101/512 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (4188650160263435577/4190000000000000000 : ℝ)) (alpha := (35739245993/20950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1066866933/5000000000 : ℝ)*X 0 0+(1078627357/2000000000 : ℝ)*X 0 1+(5265497513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344809973/10000000000 : ℝ)*X 1 0+(-2198476803/10000000000 : ℝ)*X 1 1+(658187189/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672404989/5000000000 : ℝ)*X 2 0+(5265497507/10000000000 : ℝ)*X 2 1+(-2198476803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((68044303/156250000 : ℝ)*X 0 0+(1056996103/2500000000 : ℝ)*X 0 1+(2242705353/5000000000 : ℝ)*X 0 2+(68044303/156250000 : ℝ)*X 1 0+(1056996103/2500000000 : ℝ)*X 1 1+(2242705353/5000000000 : ℝ)*X 1 2+(68044303/156250000 : ℝ)*X 2 0+(1056996103/2500000000 : ℝ)*X 2 1+(2242705353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2133738911/10000000000 : ℝ)*X 0 0+(5265825911/10000000000 : ℝ)*X 0 1+(1348201791/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656154731/5000000000 : ℝ)*X 1 0+(-2071167093/10000000000 : ℝ)*X 1 1+(5392807179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664038677/1250000000 : ℝ)*X 2 0+(5392807219/10000000000 : ℝ)*X 2 1+(-2071167101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((544355703/1250000000 : ℝ)*X 0 0+(4484748341/10000000000 : ℝ)*X 0 1+(4228649147/10000000000 : ℝ)*X 0 2+(544355703/1250000000 : ℝ)*X 1 0+(4484748341/10000000000 : ℝ)*X 1 1+(4228649147/10000000000 : ℝ)*X 1 2+(544355703/1250000000 : ℝ)*X 2 0+(4484748341/10000000000 : ℝ)*X 2 1+(4228649147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1212_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (604238631383704162294041723/104750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (220179573/20000000000000 : ℝ)*(base19) + (1045993051/100000000000000 : ℝ)*(base23) + (33262901/100000000000000 : ℝ)*(lower2) + (67346651/50000000000000 : ℝ)*(upper3) + (45062887/50000000000000 : ℝ)*(upper5) + (5859639857351633/100000000000000 : ℝ)*(major0) + (5859639857351633/100000000000000 : ℝ)*(major1) + (5859639857351633/100000000000000 : ℝ)*(major2) + (3917305302559191/50000000000000 : ℝ)*(sp0) + (3917319901928051/50000000000000 : ℝ)*(sp1) + (1958659964690229/25000000000000 : ℝ)*(sp2) + (388462216698807/10000000000000 : ℝ)*(sp3) + (6059927117/20000000000000 : ℝ)*(sp4) + (131605453/800000000000 : ℝ)*(sp7) + (60697478401089/1562500000000 : ℝ)*(f.failure) + (7834640904753967/100000000000000 : ℝ)*(f.sum) + (14578153956303/2095000000000000000000000000 : ℝ)*base65 + (1304464003184952759/419000000000000000000000000000000 : ℝ)*base68 + (5813487431773952759/419000000000000000000000000000000 : ℝ)*base70 + (5769794733988952759/419000000000000000000000000000000 : ℝ)*base72 + (13505645174533/2095000000000000000000000000 : ℝ)*base73 + (876872722015952759/419000000000000000000000000000000 : ℝ)*base76 + (208288152226952759/419000000000000000000000000000000 : ℝ)*base78 + (1748993633482047241/419000000000000000000000000000000 : ℝ)*base79 + (6933268393173/2095000000000000000000000000 : ℝ)*base81 + (106567/39062500000000000000 : ℝ)*base89 + (106567/39062500000000000000 : ℝ)*base91 + (106567/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (472877169681100426824757929/52375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (885838813/50000000000000 : ℝ)*(base19) + (375293713/20000000000000 : ℝ)*(base23) + (208812083/100000000000000 : ℝ)*(upper3) + (7871057/10000000000000 : ℝ)*(lower4) + (94499133/50000000000000 : ℝ)*(upper5) + (2944977781296859/50000000000000 : ℝ)*(major0) + (2944977781296859/50000000000000 : ℝ)*(major1) + (2944977781296859/50000000000000 : ℝ)*(major2) + (9728196411/20000000000000 : ℝ)*(sp1) + (13174317677/25000000000000 : ℝ)*(sp2) + (7875174459571743/100000000000000 : ℝ)*(sp4) + (3937562023456031/50000000000000 : ℝ)*(sp5) + (787511988583247/10000000000000 : ℝ)*(sp6) + (61011505697807/1562500000000 : ℝ)*(sp7) + (61011505697807/1562500000000 : ℝ)*(f.failure) + (7875174459571743/100000000000000 : ℝ)*(f.sum) + (8248296080443/2095000000000000000000000000 : ℝ)*base65 + (650342256866852643/209500000000000000000000000000000 : ℝ)*base67 + (2816025944069647357/209500000000000000000000000000000 : ℝ)*base70 + (557376779498147357/209500000000000000000000000000000 : ℝ)*base72 + (5410179556433/2095000000000000000000000000 : ℝ)*base73 + (2512685322626647357/209500000000000000000000000000000 : ℝ)*base76 + (1802329855955647357/209500000000000000000000000000000 : ℝ)*base78 + (4056262329356647357/209500000000000000000000000000000 : ℝ)*base80 + (5441299907529/1047500000000000000000000000 : ℝ)*base81 + (121527/19531250000000000000 : ℝ)*base90 + (121527/19531250000000000000 : ℝ)*base92 + (121527/19531250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1212_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1212_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1212_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16303/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3/32 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1212_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1212_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1212_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2101/512 : ℝ) ≤ p) (hpb : p ≤ (8405/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4713791/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16303/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3/32 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1212_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
