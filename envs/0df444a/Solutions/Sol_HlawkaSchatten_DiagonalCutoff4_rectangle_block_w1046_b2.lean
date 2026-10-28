-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1046_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:51:26.666369+00:00
-- url     : https://prove2.me/submissions/09ea8898-0d0c-4ac4-aa10-dffc5dec137f

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
theorem support_rectangle_w1046_s6_0 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213598373/10000000000 : ℝ)*x 0 + (5395329349/10000000000 : ℝ)*x 1 + (2631745641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213598373/10000000000 : ℝ)^8239 ≤ (13441746459589/100000000000000 : ℝ)^6191 := by
    have hnat : (2213598373 : ℕ)^8239*100000000000000^6191 ≤ 13441746459589^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213598373 10000000000 13441746459589 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395329349/10000000000 : ℝ)^8239 ≤ (43991498672491/100000000000000 : ℝ)^6191 := by
    have hnat : (5395329349 : ℕ)^8239*100000000000000^6191 ≤ 43991498672491^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395329349 10000000000 43991498672491 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631745641/5000000000 : ℝ)^8239 ≤ (10641688714377/25000000000000 : ℝ)^6191 := by
    have hnat : (2631745641 : ℕ)^8239*25000000000000^6191 ≤ 10641688714377^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631745641 5000000000 10641688714377 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213598373/10000000000 : ℝ), (5395329349/10000000000 : ℝ), (2631745641/5000000000 : ℝ)] ![(13441746459589/100000000000000 : ℝ), (43991498672491/100000000000000 : ℝ), (10641688714377/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213598373/10000000000 : ℝ)|^8239 ≤ (13441746459589/100000000000000 : ℝ)^6191
        have hw : |(-2213598373/10000000000 : ℝ)|=(2213598373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395329349/10000000000 : ℝ)|^8239 ≤ (43991498672491/100000000000000 : ℝ)^6191
        have hw : |(5395329349/10000000000 : ℝ)|=(5395329349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631745641/5000000000 : ℝ)|^8239 ≤ (10641688714377/25000000000000 : ℝ)^6191
        have hw : |(2631745641/5000000000 : ℝ)|=(2631745641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s6_1 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668147211/1250000000 : ℝ)*x 0 + (-1140251671/5000000000 : ℝ)*x 1 + (5263491273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668147211/1250000000 : ℝ)^8239 ≤ (43448148015467/100000000000000 : ℝ)^6191 := by
    have hnat : (668147211 : ℕ)^8239*100000000000000^6191 ≤ 43448148015467^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668147211 1250000000 43448148015467 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140251671/5000000000 : ℝ)^8239 ≤ (218517143839/1562500000000 : ℝ)^6191 := by
    have hnat : (1140251671 : ℕ)^8239*1562500000000^6191 ≤ 218517143839^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140251671 5000000000 218517143839 1562500000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263491273/10000000000 : ℝ)^8239 ≤ (21283377380323/50000000000000 : ℝ)^6191 := by
    have hnat : (5263491273 : ℕ)^8239*50000000000000^6191 ≤ 21283377380323^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263491273 10000000000 21283377380323 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668147211/1250000000 : ℝ), (-1140251671/5000000000 : ℝ), (5263491273/10000000000 : ℝ)] ![(43448148015467/100000000000000 : ℝ), (218517143839/1562500000000 : ℝ), (21283377380323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668147211/1250000000 : ℝ)|^8239 ≤ (43448148015467/100000000000000 : ℝ)^6191
        have hw : |(668147211/1250000000 : ℝ)|=(668147211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1140251671/5000000000 : ℝ)|^8239 ≤ (218517143839/1562500000000 : ℝ)^6191
        have hw : |(-1140251671/5000000000 : ℝ)|=(1140251671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263491273/10000000000 : ℝ)|^8239 ≤ (21283377380323/50000000000000 : ℝ)^6191
        have hw : |(5263491273/10000000000 : ℝ)|=(5263491273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s6_2 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345177513/10000000000 : ℝ)*x 0 + (526349139/1000000000 : ℝ)*x 1 + (-114025171/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345177513/10000000000 : ℝ)^8239 ≤ (21724073061211/50000000000000 : ℝ)^6191 := by
    have hnat : (5345177513 : ℕ)^8239*50000000000000^6191 ≤ 21724073061211^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345177513 10000000000 21724073061211 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526349139/1000000000 : ℝ)^8239 ≤ (851335120397/2000000000000 : ℝ)^6191 := by
    have hnat : (526349139 : ℕ)^8239*2000000000000^6191 ≤ 851335120397^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526349139 1000000000 851335120397 2000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114025171/500000000 : ℝ)^8239 ≤ (13985097842261/100000000000000 : ℝ)^6191 := by
    have hnat : (114025171 : ℕ)^8239*100000000000000^6191 ≤ 13985097842261^6191*500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114025171 500000000 13985097842261 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345177513/10000000000 : ℝ), (526349139/1000000000 : ℝ), (-114025171/500000000 : ℝ)] ![(21724073061211/50000000000000 : ℝ), (851335120397/2000000000000 : ℝ), (13985097842261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345177513/10000000000 : ℝ)|^8239 ≤ (21724073061211/50000000000000 : ℝ)^6191
        have hw : |(5345177513/10000000000 : ℝ)|=(5345177513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526349139/1000000000 : ℝ)|^8239 ≤ (851335120397/2000000000000 : ℝ)^6191
        have hw : |(526349139/1000000000 : ℝ)|=(526349139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114025171/500000000 : ℝ)|^8239 ≤ (13985097842261/100000000000000 : ℝ)^6191
        have hw : |(-114025171/500000000 : ℝ)|=(114025171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s6_3 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378345327/10000000000 : ℝ)*x 0 + (425159063/1000000000 : ℝ)*x 1 + (4508949597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378345327/10000000000 : ℝ)^8239 ≤ (4164514519217/12500000000000 : ℝ)^6191 := by
    have hnat : (4378345327 : ℕ)^8239*12500000000000^6191 ≤ 4164514519217^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378345327 10000000000 4164514519217 12500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425159063/1000000000 : ℝ)^8239 ≤ (32038725095521/100000000000000 : ℝ)^6191 := by
    have hnat : (425159063 : ℕ)^8239*100000000000000^6191 ≤ 32038725095521^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425159063 1000000000 32038725095521 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508949597/10000000000 : ℝ)^8239 ≤ (135332651293/390625000000 : ℝ)^6191 := by
    have hnat : (4508949597 : ℕ)^8239*390625000000^6191 ≤ 135332651293^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508949597 10000000000 135332651293 390625000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378345327/10000000000 : ℝ), (425159063/1000000000 : ℝ), (4508949597/10000000000 : ℝ)] ![(4164514519217/12500000000000 : ℝ), (32038725095521/100000000000000 : ℝ), (135332651293/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378345327/10000000000 : ℝ)|^8239 ≤ (4164514519217/12500000000000 : ℝ)^6191
        have hw : |(4378345327/10000000000 : ℝ)|=(4378345327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(425159063/1000000000 : ℝ)|^8239 ≤ (32038725095521/100000000000000 : ℝ)^6191
        have hw : |(425159063/1000000000 : ℝ)|=(425159063/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508949597/10000000000 : ℝ)|^8239 ≤ (135332651293/390625000000 : ℝ)^6191
        have hw : |(4508949597/10000000000 : ℝ)|=(4508949597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s6_4 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213603661/10000000000 : ℝ)*x 0 + (657978033/1250000000 : ℝ)*x 1 + (84296799/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213603661/10000000000 : ℝ)^8239 ≤ (1680223649059/12500000000000 : ℝ)^6191 := by
    have hnat : (2213603661 : ℕ)^8239*12500000000000^6191 ≤ 1680223649059^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213603661 10000000000 1680223649059 12500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657978033/1250000000 : ℝ)^8239 ≤ (21285169295209/50000000000000 : ℝ)^6191 := by
    have hnat : (657978033 : ℕ)^8239*50000000000000^6191 ≤ 21285169295209^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657978033 1250000000 21285169295209 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84296799/156250000 : ℝ)^8239 ≤ (43987872208373/100000000000000 : ℝ)^6191 := by
    have hnat : (84296799 : ℕ)^8239*100000000000000^6191 ≤ 43987872208373^6191*156250000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84296799 156250000 43987872208373 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213603661/10000000000 : ℝ), (657978033/1250000000 : ℝ), (84296799/156250000 : ℝ)] ![(1680223649059/12500000000000 : ℝ), (21285169295209/50000000000000 : ℝ), (43987872208373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213603661/10000000000 : ℝ)|^8239 ≤ (1680223649059/12500000000000 : ℝ)^6191
        have hw : |(-2213603661/10000000000 : ℝ)|=(2213603661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657978033/1250000000 : ℝ)|^8239 ≤ (21285169295209/50000000000000 : ℝ)^6191
        have hw : |(657978033/1250000000 : ℝ)|=(657978033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84296799/156250000 : ℝ)|^8239 ≤ (43987872208373/100000000000000 : ℝ)^6191
        have hw : |(84296799/156250000 : ℝ)|=(84296799/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s6_5 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656011741/5000000000 : ℝ)*x 0 + (-214899949/1000000000 : ℝ)*x 1 + (337187201/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656011741/5000000000 : ℝ)^8239 ≤ (8617974842799/20000000000000 : ℝ)^6191 := by
    have hnat : (2656011741 : ℕ)^8239*20000000000000^6191 ≤ 8617974842799^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656011741 5000000000 8617974842799 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214899949/1000000000 : ℝ)^8239 ≤ (6461126346737/50000000000000 : ℝ)^6191 := by
    have hnat : (214899949 : ℕ)^8239*50000000000000^6191 ≤ 6461126346737^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214899949 1000000000 6461126346737 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337187201/625000000 : ℝ)^8239 ≤ (1759514923057/4000000000000 : ℝ)^6191 := by
    have hnat : (337187201 : ℕ)^8239*4000000000000^6191 ≤ 1759514923057^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337187201 625000000 1759514923057 4000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656011741/5000000000 : ℝ), (-214899949/1000000000 : ℝ), (337187201/625000000 : ℝ)] ![(8617974842799/20000000000000 : ℝ), (6461126346737/50000000000000 : ℝ), (1759514923057/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656011741/5000000000 : ℝ)|^8239 ≤ (8617974842799/20000000000000 : ℝ)^6191
        have hw : |(2656011741/5000000000 : ℝ)|=(2656011741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-214899949/1000000000 : ℝ)|^8239 ≤ (6461126346737/50000000000000 : ℝ)^6191
        have hw : |(-214899949/1000000000 : ℝ)|=(214899949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337187201/625000000 : ℝ)|^8239 ≤ (1759514923057/4000000000000 : ℝ)^6191
        have hw : |(337187201/625000000 : ℝ)|=(337187201/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s6_6 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332001469/625000000 : ℝ)*x 0 + (1078999027/2000000000 : ℝ)*x 1 + (-214899957/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332001469/625000000 : ℝ)^8239 ≤ (43089874451489/100000000000000 : ℝ)^6191 := by
    have hnat : (332001469 : ℕ)^8239*100000000000000^6191 ≤ 43089874451489^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332001469 625000000 43089874451489 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078999027/2000000000 : ℝ)^8239 ≤ (43987872197523/100000000000000 : ℝ)^6191 := by
    have hnat : (1078999027 : ℕ)^8239*100000000000000^6191 ≤ 43987872197523^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078999027 2000000000 43987872197523 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214899957/1000000000 : ℝ)^8239 ≤ (12922253333659/100000000000000 : ℝ)^6191 := by
    have hnat : (214899957 : ℕ)^8239*100000000000000^6191 ≤ 12922253333659^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214899957 1000000000 12922253333659 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332001469/625000000 : ℝ), (1078999027/2000000000 : ℝ), (-214899957/1000000000 : ℝ)] ![(43089874451489/100000000000000 : ℝ), (43987872197523/100000000000000 : ℝ), (12922253333659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332001469/625000000 : ℝ)|^8239 ≤ (43089874451489/100000000000000 : ℝ)^6191
        have hw : |(332001469/625000000 : ℝ)|=(332001469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078999027/2000000000 : ℝ)|^8239 ≤ (43987872197523/100000000000000 : ℝ)^6191
        have hw : |(1078999027/2000000000 : ℝ)|=(1078999027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214899957/1000000000 : ℝ)|^8239 ≤ (12922253333659/100000000000000 : ℝ)^6191
        have hw : |(-214899957/1000000000 : ℝ)|=(214899957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s6_7 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (547294471/1250000000 : ℝ)*x 0 + (2254149623/5000000000 : ℝ)*x 1 + (2126121587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547294471/1250000000 : ℝ)^8239 ≤ (6663244376849/20000000000000 : ℝ)^6191 := by
    have hnat : (547294471 : ℕ)^8239*20000000000000^6191 ≤ 6663244376849^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547294471 1250000000 6663244376849 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254149623/5000000000 : ℝ)^8239 ≤ (34638508781853/100000000000000 : ℝ)^6191 := by
    have hnat : (2254149623 : ℕ)^8239*100000000000000^6191 ≤ 34638508781853^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254149623 5000000000 34638508781853 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126121587/5000000000 : ℝ)^8239 ≤ (32045269321823/100000000000000 : ℝ)^6191 := by
    have hnat : (2126121587 : ℕ)^8239*100000000000000^6191 ≤ 32045269321823^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126121587 5000000000 32045269321823 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547294471/1250000000 : ℝ), (2254149623/5000000000 : ℝ), (2126121587/5000000000 : ℝ)] ![(6663244376849/20000000000000 : ℝ), (34638508781853/100000000000000 : ℝ), (32045269321823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547294471/1250000000 : ℝ)|^8239 ≤ (6663244376849/20000000000000 : ℝ)^6191
        have hw : |(547294471/1250000000 : ℝ)|=(547294471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254149623/5000000000 : ℝ)|^8239 ≤ (34638508781853/100000000000000 : ℝ)^6191
        have hw : |(2254149623/5000000000 : ℝ)|=(2254149623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2126121587/5000000000 : ℝ)|^8239 ≤ (32045269321823/100000000000000 : ℝ)^6191
        have hw : |(2126121587/5000000000 : ℝ)|=(2126121587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1046_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11211/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14003/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5583/50000 : ℝ) ^ (4119/1024 : ℝ) ≤ (7399040191690263/50000000000000000000 : ℝ) := by
    have hpowers : (5583/50000 : ℝ)^4119 ≤ (7399040191690263/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5583 : ℕ)^4119*50000000000000000000^1024 ≤ 7399040191690263^1024*50000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5583 50000 7399040191690263 50000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5583/50000 : ℝ)) (X := (7399040191690263/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14051/100000 : ℝ) ^ (4119/1024 : ℝ) ≤ (18649004120219851/50000000000000000000 : ℝ) := by
    have hpowers : (14051/100000 : ℝ)^4119 ≤ (18649004120219851/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14051 : ℕ)^4119*50000000000000000000^1024 ≤ 18649004120219851^1024*100000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14051 100000 18649004120219851 50000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14051/100000 : ℝ)) (X := (18649004120219851/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007399040191690263/25000000000000000000 : ℝ) ≤ (1000073569068621/1000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (25007399040191690263/25000000000000000000 : ℝ)^1024 ≤ (1000073569068621/1000000000000000 : ℝ)^4119 := by
      have hnat : (25007399040191690263 : ℕ)^1024*1000000000000000^4119 ≤ 1000073569068621^4119*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007399040191690263 25000000000000000000 1000073569068621 1000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000073569068621/1000000000000000 : ℝ)) (X := (25007399040191690263/25000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013024022155955057/25000000000000000000 : ℝ) ≤ (2000258975269521/2000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (25013024022155955057/25000000000000000000 : ℝ)^1024 ≤ (2000258975269521/2000000000000000 : ℝ)^4119 := by
      have hnat : (25013024022155955057 : ℕ)^1024*2000000000000000^4119 ≤ 2000258975269521^4119*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013024022155955057 25000000000000000000 2000258975269521 2000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000258975269521/2000000000000000 : ℝ)) (X := (25013024022155955057/25000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018649004120219851/25000000000000000000 : ℝ) ≤ (10001854062009/10000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (25018649004120219851/25000000000000000000 : ℝ)^1024 ≤ (10001854062009/10000000000000 : ℝ)^4119 := by
      have hnat : (25018649004120219851 : ℕ)^1024*10000000000000^4119 ≤ 10001854062009^4119*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018649004120219851 25000000000000000000 10001854062009 10000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001854062009/10000000000000 : ℝ)) (X := (25018649004120219851/25000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7399040191690263/50000000000000000000 : ℝ) ≤ ((2883963473343944271/2885000000000000000 : ℝ)+2*(111837132279/57700000000000 : ℝ)*(5583/50000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (2883963473343944271/2885000000000000000 : ℝ)+2*(111837132279/57700000000000 : ℝ)*(5583/50000 : ℝ)=(1000073569068621/1000000000000000 : ℝ) by norm_num, show 1+2*(7399040191690263/50000000000000000000 : ℝ)=(25007399040191690263/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18649004120219851/50000000000000000000 : ℝ)+(7399040191690263/50000000000000000000 : ℝ) ≤ ((2883963473343944271/2885000000000000000 : ℝ)+(111837132279/57700000000000 : ℝ)*((14051/100000 : ℝ)+(5583/50000 : ℝ)))^(4119/1024 : ℝ) := by
    rw [show (2883963473343944271/2885000000000000000 : ℝ)+(111837132279/57700000000000 : ℝ)*((14051/100000 : ℝ)+(5583/50000 : ℝ))=(2000258975269521/2000000000000000 : ℝ) by norm_num, show 1+(18649004120219851/50000000000000000000 : ℝ)+(7399040191690263/50000000000000000000 : ℝ)=(25013024022155955057/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18649004120219851/50000000000000000000 : ℝ) ≤ ((2883963473343944271/2885000000000000000 : ℝ)+2*(111837132279/57700000000000 : ℝ)*(14051/100000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (2883963473343944271/2885000000000000000 : ℝ)+2*(111837132279/57700000000000 : ℝ)*(14051/100000 : ℝ)=(10001854062009/10000000000000 : ℝ) by norm_num, show 1+2*(18649004120219851/50000000000000000000 : ℝ)=(25018649004120219851/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2883963473343944271/2885000000000000000 : ℝ)*(X 1 0+X 2 0)+(111837132279/57700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (2883963473343944271/2885000000000000000 : ℝ)) (alpha := (111837132279/57700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2883963473343944271/2885000000000000000 : ℝ)*(X 0 1+X 2 1)+(111837132279/57700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (2883963473343944271/2885000000000000000 : ℝ)) (alpha := (111837132279/57700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2883963473343944271/2885000000000000000 : ℝ)*(X 0 2+X 1 2)+(111837132279/57700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (2883963473343944271/2885000000000000000 : ℝ)) (alpha := (111837132279/57700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2213598373/10000000000 : ℝ)*X 0 0+(5395329349/10000000000 : ℝ)*X 0 1+(2631745641/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668147211/1250000000 : ℝ)*X 1 0+(-1140251671/5000000000 : ℝ)*X 1 1+(5263491273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345177513/10000000000 : ℝ)*X 2 0+(526349139/1000000000 : ℝ)*X 2 1+(-114025171/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378345327/10000000000 : ℝ)*X 0 0+(425159063/1000000000 : ℝ)*X 0 1+(4508949597/10000000000 : ℝ)*X 0 2+(4378345327/10000000000 : ℝ)*X 1 0+(425159063/1000000000 : ℝ)*X 1 1+(4508949597/10000000000 : ℝ)*X 1 2+(4378345327/10000000000 : ℝ)*X 2 0+(425159063/1000000000 : ℝ)*X 2 1+(4508949597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2213603661/10000000000 : ℝ)*X 0 0+(657978033/1250000000 : ℝ)*X 0 1+(84296799/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656011741/5000000000 : ℝ)*X 1 0+(-214899949/1000000000 : ℝ)*X 1 1+(337187201/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332001469/625000000 : ℝ)*X 2 0+(1078999027/2000000000 : ℝ)*X 2 1+(-214899957/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((547294471/1250000000 : ℝ)*X 0 0+(2254149623/5000000000 : ℝ)*X 0 1+(2126121587/5000000000 : ℝ)*X 0 2+(547294471/1250000000 : ℝ)*X 1 0+(2254149623/5000000000 : ℝ)*X 1 1+(2126121587/5000000000 : ℝ)*X 1 2+(547294471/1250000000 : ℝ)*X 2 0+(2254149623/5000000000 : ℝ)*X 2 1+(2126121587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112011751994511053644695213/18031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (685392191/50000000000000 : ℝ)*(base19) + (543146979/50000000000000 : ℝ)*(base23) + (19325347/100000000000000 : ℝ)*(lower2) + (120759327/50000000000000 : ℝ)*(upper3) + (46184929/100000000000000 : ℝ)*(upper5) + (716924887766733/12500000000000 : ℝ)*(major0) + (716924887766733/12500000000000 : ℝ)*(major1) + (716924887766733/12500000000000 : ℝ)*(major2) + (7585104326764969/100000000000000 : ℝ)*(sp0) + (7585133443904033/100000000000000 : ℝ)*(sp1) + (7585133728394457/100000000000000 : ℝ)*(sp2) + (3885641804725113/100000000000000 : ℝ)*(sp3) + (15243961723/50000000000000 : ℝ)*(sp4) + (21377784519/100000000000000 : ℝ)*(sp7) + (60713487226713/1562500000000 : ℝ)*(f.failure) + (1517026962937683/20000000000000 : ℝ)*(f.sum) + (2012220611389/721250000000000000000000000 : ℝ)*base65 + (125529827321774143/36062500000000000000000000000000 : ℝ)*base67 + (221269313529024143/36062500000000000000000000000000 : ℝ)*base69 + (121449879867649143/36062500000000000000000000000000 : ℝ)*base71 + (31364251763/1442500000000000000000000000 : ℝ)*base73 + (176546581040586643/36062500000000000000000000000000 : ℝ)*base75 + (325367819977086643/36062500000000000000000000000000 : ℝ)*base77 + (289861003072711643/36062500000000000000000000000000 : ℝ)*base79 + (13653028045161/2885000000000000000000000000 : ℝ)*base81 + (183897/39062500000000000000 : ℝ)*base90 + (183897/39062500000000000000 : ℝ)*base92 + (183897/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49287931329958616415408957/36062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (483300227/100000000000000 : ℝ)*(base19) + (527161679/100000000000000 : ℝ)*(base23) + (1605599/4000000000000 : ℝ)*(upper3) + (5933481/20000000000000 : ℝ)*(lower4) + (35380411/25000000000000 : ℝ)*(upper5) + (2882259978627289/50000000000000 : ℝ)*(major0) + (2882259978627289/50000000000000 : ℝ)*(major1) + (2882259978627289/50000000000000 : ℝ)*(major2) + (9254824811/50000000000000 : ℝ)*(sp1) + (23060349/200000000000 : ℝ)*(sp2) + (1524729532207607/20000000000000 : ℝ)*(sp4) + (1905907167022047/25000000000000 : ℝ)*(sp5) + (7623635603701857/100000000000000 : ℝ)*(sp6) + (3905392207913227/100000000000000 : ℝ)*(sp7) + (3905392207913227/100000000000000 : ℝ)*(f.failure) + (1524729532207607/20000000000000 : ℝ)*(f.sum) + (10208217101623/2885000000000000000000000000 : ℝ)*base66 + (1161100247251138681/144250000000000000000000000000000 : ℝ)*base68 + (1531065748639138681/144250000000000000000000000000000 : ℝ)*base70 + (1145074044266638681/144250000000000000000000000000000 : ℝ)*base72 + (434966260121/360625000000000000000000000 : ℝ)*base74 + (4744214253728638681/144250000000000000000000000000000 : ℝ)*base76 + (118036529370361319/144250000000000000000000000000000 : ℝ)*base77 + (2083310613634888681/144250000000000000000000000000000 : ℝ)*base80 + (1525082232591/1442500000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (15162963/2500000000000000000000 : ℝ)*base90 + (15162963/2500000000000000000000 : ℝ)*base92 + (15162963/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1046_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1046_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1046_s7_0 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213646573/10000000000 : ℝ)*x 0 + (674351793/1250000000 : ℝ)*x 1 + (657996789/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213646573/10000000000 : ℝ)^8239 ≤ (13442135970093/100000000000000 : ℝ)^6191 := by
    have hnat : (2213646573 : ℕ)^8239*100000000000000^6191 ≤ 13442135970093^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213646573 10000000000 13442135970093 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674351793/1250000000 : ℝ)^8239 ≤ (175943642037/400000000000 : ℝ)^6191 := by
    have hnat : (674351793 : ℕ)^8239*400000000000^6191 ≤ 175943642037^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674351793 1250000000 175943642037 400000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657996789/1250000000 : ℝ)^8239 ≤ (42571953512899/100000000000000 : ℝ)^6191 := by
    have hnat : (657996789 : ℕ)^8239*100000000000000^6191 ≤ 42571953512899^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657996789 1250000000 42571953512899 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213646573/10000000000 : ℝ), (674351793/1250000000 : ℝ), (657996789/1250000000 : ℝ)] ![(13442135970093/100000000000000 : ℝ), (175943642037/400000000000 : ℝ), (42571953512899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213646573/10000000000 : ℝ)|^8239 ≤ (13442135970093/100000000000000 : ℝ)^6191
        have hw : |(-2213646573/10000000000 : ℝ)|=(2213646573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674351793/1250000000 : ℝ)|^8239 ≤ (175943642037/400000000000 : ℝ)^6191
        have hw : |(674351793/1250000000 : ℝ)|=(674351793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657996789/1250000000 : ℝ)|^8239 ≤ (42571953512899/100000000000000 : ℝ)^6191
        have hw : |(657996789/1250000000 : ℝ)|=(657996789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s7_1 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345048321/10000000000 : ℝ)*x 0 + (-2280037383/10000000000 : ℝ)*x 1 + (657996827/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345048321/10000000000 : ℝ)^8239 ≤ (21723374303351/50000000000000 : ℝ)^6191 := by
    have hnat : (5345048321 : ℕ)^8239*50000000000000^6191 ≤ 21723374303351^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345048321 10000000000 21723374303351 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2280037383/10000000000 : ℝ)^8239 ≤ (2796258919637/20000000000000 : ℝ)^6191 := by
    have hnat : (2280037383 : ℕ)^8239*20000000000000^6191 ≤ 2796258919637^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280037383 10000000000 2796258919637 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657996827/1250000000 : ℝ)^8239 ≤ (42571956784777/100000000000000 : ℝ)^6191 := by
    have hnat : (657996827 : ℕ)^8239*100000000000000^6191 ≤ 42571956784777^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657996827 1250000000 42571956784777 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345048321/10000000000 : ℝ), (-2280037383/10000000000 : ℝ), (657996827/1250000000 : ℝ)] ![(21723374303351/50000000000000 : ℝ), (2796258919637/20000000000000 : ℝ), (42571956784777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345048321/10000000000 : ℝ)|^8239 ≤ (21723374303351/50000000000000 : ℝ)^6191
        have hw : |(5345048321/10000000000 : ℝ)|=(5345048321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2280037383/10000000000 : ℝ)|^8239 ≤ (2796258919637/20000000000000 : ℝ)^6191
        have hw : |(-2280037383/10000000000 : ℝ)|=(2280037383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657996827/1250000000 : ℝ)|^8239 ≤ (42571956784777/100000000000000 : ℝ)^6191
        have hw : |(657996827/1250000000 : ℝ)|=(657996827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s7_2 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069009689/2000000000 : ℝ)*x 0 + (1315993603/2500000000 : ℝ)*x 1 + (-2280037487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069009689/2000000000 : ℝ)^8239 ≤ (43446749948049/100000000000000 : ℝ)^6191 := by
    have hnat : (1069009689 : ℕ)^8239*100000000000000^6191 ≤ 43446749948049^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069009689 2000000000 43446749948049 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315993603/2500000000 : ℝ)^8239 ≤ (1702878183567/4000000000000 : ℝ)^6191 := by
    have hnat : (1315993603 : ℕ)^8239*4000000000000^6191 ≤ 1702878183567^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315993603 2500000000 1702878183567 4000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2280037487/10000000000 : ℝ)^8239 ≤ (13981295446881/100000000000000 : ℝ)^6191 := by
    have hnat : (2280037487 : ℕ)^8239*100000000000000^6191 ≤ 13981295446881^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280037487 10000000000 13981295446881 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069009689/2000000000 : ℝ), (1315993603/2500000000 : ℝ), (-2280037487/10000000000 : ℝ)] ![(43446749948049/100000000000000 : ℝ), (1702878183567/4000000000000 : ℝ), (13981295446881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069009689/2000000000 : ℝ)|^8239 ≤ (43446749948049/100000000000000 : ℝ)^6191
        have hw : |(1069009689/2000000000 : ℝ)|=(1069009689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315993603/2500000000 : ℝ)|^8239 ≤ (1702878183567/4000000000000 : ℝ)^6191
        have hw : |(1315993603/2500000000 : ℝ)|=(1315993603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2280037487/10000000000 : ℝ)|^8239 ≤ (13981295446881/100000000000000 : ℝ)^6191
        have hw : |(-2280037487/10000000000 : ℝ)|=(2280037487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s7_3 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378371049/10000000000 : ℝ)*x 0 + (2126280851/5000000000 : ℝ)*x 1 + (4507971679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378371049/10000000000 : ℝ)^8239 ≤ (6663275325407/20000000000000 : ℝ)^6191 := by
    have hnat : (4378371049 : ℕ)^8239*20000000000000^6191 ≤ 6663275325407^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378371049 10000000000 6663275325407 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126280851/5000000000 : ℝ)^8239 ≤ (4006057986587/12500000000000 : ℝ)^6191 := by
    have hnat : (2126280851 : ℕ)^8239*12500000000000^6191 ≤ 4006057986587^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126280851 5000000000 4006057986587 12500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507971679/10000000000 : ℝ)^8239 ≤ (34635159473949/100000000000000 : ℝ)^6191 := by
    have hnat : (4507971679 : ℕ)^8239*100000000000000^6191 ≤ 34635159473949^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507971679 10000000000 34635159473949 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378371049/10000000000 : ℝ), (2126280851/5000000000 : ℝ), (4507971679/10000000000 : ℝ)] ![(6663275325407/20000000000000 : ℝ), (4006057986587/12500000000000 : ℝ), (34635159473949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378371049/10000000000 : ℝ)|^8239 ≤ (6663275325407/20000000000000 : ℝ)^6191
        have hw : |(4378371049/10000000000 : ℝ)|=(4378371049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126280851/5000000000 : ℝ)|^8239 ≤ (4006057986587/12500000000000 : ℝ)^6191
        have hw : |(2126280851/5000000000 : ℝ)|=(2126280851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507971679/10000000000 : ℝ)|^8239 ≤ (34635159473949/100000000000000 : ℝ)^6191
        have hw : |(4507971679/10000000000 : ℝ)|=(4507971679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s7_4 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213651541/10000000000 : ℝ)*x 0 + (5264302521/10000000000 : ℝ)*x 1 + (2697242541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213651541/10000000000 : ℝ)^8239 ≤ (1344217611731/10000000000000 : ℝ)^6191 := by
    have hnat : (2213651541 : ℕ)^8239*10000000000000^6191 ≤ 1344217611731^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213651541 10000000000 1344217611731 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264302521/10000000000 : ℝ)^8239 ≤ (42575485982893/100000000000000 : ℝ)^6191 := by
    have hnat : (5264302521 : ℕ)^8239*100000000000000^6191 ≤ 42575485982893^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264302521 10000000000 42575485982893 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697242541/5000000000 : ℝ)^8239 ≤ (4398233787951/10000000000000 : ℝ)^6191 := by
    have hnat : (2697242541 : ℕ)^8239*10000000000000^6191 ≤ 4398233787951^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697242541 5000000000 4398233787951 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213651541/10000000000 : ℝ), (5264302521/10000000000 : ℝ), (2697242541/5000000000 : ℝ)] ![(1344217611731/10000000000000 : ℝ), (42575485982893/100000000000000 : ℝ), (4398233787951/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213651541/10000000000 : ℝ)|^8239 ≤ (1344217611731/10000000000000 : ℝ)^6191
        have hw : |(-2213651541/10000000000 : ℝ)|=(2213651541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264302521/10000000000 : ℝ)|^8239 ≤ (42575485982893/100000000000000 : ℝ)^6191
        have hw : |(5264302521/10000000000 : ℝ)|=(5264302521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697242541/5000000000 : ℝ)|^8239 ≤ (4398233787951/10000000000000 : ℝ)^6191
        have hw : |(2697242541/5000000000 : ℝ)|=(2697242541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s7_5 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664018159/1250000000 : ℝ)*x 0 + (-268690859/1250000000 : ℝ)*x 1 + (2697242541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664018159/1250000000 : ℝ)^8239 ≤ (1077279724027/2500000000000 : ℝ)^6191 := by
    have hnat : (664018159 : ℕ)^8239*2500000000000^6191 ≤ 1077279724027^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664018159 1250000000 1077279724027 2500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268690859/1250000000 : ℝ)^8239 ≤ (3231618285349/25000000000000 : ℝ)^6191 := by
    have hnat : (268690859 : ℕ)^8239*25000000000000^6191 ≤ 3231618285349^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268690859 1250000000 3231618285349 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697242541/5000000000 : ℝ)^8239 ≤ (4398233787951/10000000000000 : ℝ)^6191 := by
    have hnat : (2697242541 : ℕ)^8239*10000000000000^6191 ≤ 4398233787951^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697242541 5000000000 4398233787951 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664018159/1250000000 : ℝ), (-268690859/1250000000 : ℝ), (2697242541/5000000000 : ℝ)] ![(1077279724027/2500000000000 : ℝ), (3231618285349/25000000000000 : ℝ), (4398233787951/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664018159/1250000000 : ℝ)|^8239 ≤ (1077279724027/2500000000000 : ℝ)^6191
        have hw : |(664018159/1250000000 : ℝ)|=(664018159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-268690859/1250000000 : ℝ)|^8239 ≤ (3231618285349/25000000000000 : ℝ)^6191
        have hw : |(-268690859/1250000000 : ℝ)|=(268690859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697242541/5000000000 : ℝ)|^8239 ≤ (4398233787951/10000000000000 : ℝ)^6191
        have hw : |(2697242541/5000000000 : ℝ)|=(2697242541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s7_6 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664018159/1250000000 : ℝ)*x 0 + (2697242541/5000000000 : ℝ)*x 1 + (-268690859/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664018159/1250000000 : ℝ)^8239 ≤ (1077279724027/2500000000000 : ℝ)^6191 := by
    have hnat : (664018159 : ℕ)^8239*2500000000000^6191 ≤ 1077279724027^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664018159 1250000000 1077279724027 2500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697242541/5000000000 : ℝ)^8239 ≤ (4398233787951/10000000000000 : ℝ)^6191 := by
    have hnat : (2697242541 : ℕ)^8239*10000000000000^6191 ≤ 4398233787951^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697242541 5000000000 4398233787951 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268690859/1250000000 : ℝ)^8239 ≤ (3231618285349/25000000000000 : ℝ)^6191 := by
    have hnat : (268690859 : ℕ)^8239*25000000000000^6191 ≤ 3231618285349^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268690859 1250000000 3231618285349 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664018159/1250000000 : ℝ), (2697242541/5000000000 : ℝ), (-268690859/1250000000 : ℝ)] ![(1077279724027/2500000000000 : ℝ), (4398233787951/10000000000000 : ℝ), (3231618285349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664018159/1250000000 : ℝ)|^8239 ≤ (1077279724027/2500000000000 : ℝ)^6191
        have hw : |(664018159/1250000000 : ℝ)|=(664018159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697242541/5000000000 : ℝ)|^8239 ≤ (4398233787951/10000000000000 : ℝ)^6191
        have hw : |(2697242541/5000000000 : ℝ)|=(2697242541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-268690859/1250000000 : ℝ)|^8239 ≤ (3231618285349/25000000000000 : ℝ)^6191
        have hw : |(-268690859/1250000000 : ℝ)|=(268690859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s7_7 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094595247/2500000000 : ℝ)*x 0 + (4507331441/10000000000 : ℝ)*x 1 + (850640869/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094595247/2500000000 : ℝ)^8239 ≤ (4164559659281/12500000000000 : ℝ)^6191 := by
    have hnat : (1094595247 : ℕ)^8239*12500000000000^6191 ≤ 4164559659281^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094595247 2500000000 4164559659281 12500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507331441/10000000000 : ℝ)^8239 ≤ (17314306699629/50000000000000 : ℝ)^6191 := by
    have hnat : (4507331441 : ℕ)^8239*50000000000000^6191 ≤ 17314306699629^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507331441 10000000000 17314306699629 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850640869/2000000000 : ℝ)^8239 ≤ (32054909308351/100000000000000 : ℝ)^6191 := by
    have hnat : (850640869 : ℕ)^8239*100000000000000^6191 ≤ 32054909308351^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850640869 2000000000 32054909308351 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094595247/2500000000 : ℝ), (4507331441/10000000000 : ℝ), (850640869/2000000000 : ℝ)] ![(4164559659281/12500000000000 : ℝ), (17314306699629/50000000000000 : ℝ), (32054909308351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094595247/2500000000 : ℝ)|^8239 ≤ (4164559659281/12500000000000 : ℝ)^6191
        have hw : |(1094595247/2500000000 : ℝ)|=(1094595247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507331441/10000000000 : ℝ)|^8239 ≤ (17314306699629/50000000000000 : ℝ)^6191
        have hw : |(4507331441/10000000000 : ℝ)|=(4507331441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850640869/2000000000 : ℝ)|^8239 ≤ (32054909308351/100000000000000 : ℝ)^6191
        have hw : |(850640869/2000000000 : ℝ)|=(850640869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1046_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11221/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13993/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11211/100000 : ℝ) ^ (4119/1024 : ℝ) ≤ (15039435361787427/100000000000000000000 : ℝ) := by
    have hpowers : (11211/100000 : ℝ)^4119 ≤ (15039435361787427/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11211 : ℕ)^4119*100000000000000000000^1024 ≤ 15039435361787427^1024*100000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11211 100000 15039435361787427 100000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11211/100000 : ℝ)) (X := (15039435361787427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14003/100000 : ℝ) ^ (4119/1024 : ℝ) ≤ (1471525091511359/4000000000000000000 : ℝ) := by
    have hpowers : (14003/100000 : ℝ)^4119 ≤ (1471525091511359/4000000000000000000 : ℝ)^1024 := by
      have hnat : (14003 : ℕ)^4119*4000000000000000000^1024 ≤ 1471525091511359^1024*100000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14003 100000 1471525091511359 4000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14003/100000 : ℝ)) (X := (1471525091511359/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015039435361787427/50000000000000000000 : ℝ) ≤ (10000747688360521/10000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50015039435361787427/50000000000000000000 : ℝ)^1024 ≤ (10000747688360521/10000000000000000 : ℝ)^4119 := by
      have hnat : (50015039435361787427 : ℕ)^1024*10000000000000000^4119 ≤ 10000747688360521^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015039435361787427 50000000000000000000 10000747688360521 10000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000747688360521/10000000000000000 : ℝ)) (X := (50015039435361787427/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025913781324785701/50000000000000000000 : ℝ) ≤ (10001288203288921/10000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50025913781324785701/50000000000000000000 : ℝ)^1024 ≤ (10001288203288921/10000000000000000 : ℝ)^4119 := by
      have hnat : (50025913781324785701 : ℕ)^1024*10000000000000000^4119 ≤ 10001288203288921^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025913781324785701 50000000000000000000 10001288203288921 10000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001288203288921/10000000000000000 : ℝ)) (X := (50025913781324785701/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001471525091511359/2000000000000000000 : ℝ) ≤ (10001828718217321/10000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (2001471525091511359/2000000000000000000 : ℝ)^1024 ≤ (10001828718217321/10000000000000000 : ℝ)^4119 := by
      have hnat : (2001471525091511359 : ℕ)^1024*10000000000000000^4119 ≤ 10001828718217321^4119*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001471525091511359 2000000000000000000 10001828718217321 10000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001828718217321/10000000000000000 : ℝ)) (X := (2001471525091511359/2000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15039435361787427/100000000000000000000 : ℝ) ≤ ((3488746015022248729/3490000000000000000 : ℝ)+2*(1351287321/698000000000 : ℝ)*(11211/100000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (3488746015022248729/3490000000000000000 : ℝ)+2*(1351287321/698000000000 : ℝ)*(11211/100000 : ℝ)=(10000747688360521/10000000000000000 : ℝ) by norm_num, show 1+2*(15039435361787427/100000000000000000000 : ℝ)=(50015039435361787427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1471525091511359/4000000000000000000 : ℝ)+(15039435361787427/100000000000000000000 : ℝ) ≤ ((3488746015022248729/3490000000000000000 : ℝ)+(1351287321/698000000000 : ℝ)*((14003/100000 : ℝ)+(11211/100000 : ℝ)))^(4119/1024 : ℝ) := by
    rw [show (3488746015022248729/3490000000000000000 : ℝ)+(1351287321/698000000000 : ℝ)*((14003/100000 : ℝ)+(11211/100000 : ℝ))=(10001288203288921/10000000000000000 : ℝ) by norm_num, show 1+(1471525091511359/4000000000000000000 : ℝ)+(15039435361787427/100000000000000000000 : ℝ)=(50025913781324785701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1471525091511359/4000000000000000000 : ℝ) ≤ ((3488746015022248729/3490000000000000000 : ℝ)+2*(1351287321/698000000000 : ℝ)*(14003/100000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (3488746015022248729/3490000000000000000 : ℝ)+2*(1351287321/698000000000 : ℝ)*(14003/100000 : ℝ)=(10001828718217321/10000000000000000 : ℝ) by norm_num, show 1+2*(1471525091511359/4000000000000000000 : ℝ)=(2001471525091511359/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3488746015022248729/3490000000000000000 : ℝ)*(X 1 0+X 2 0)+(1351287321/698000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (3488746015022248729/3490000000000000000 : ℝ)) (alpha := (1351287321/698000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3488746015022248729/3490000000000000000 : ℝ)*(X 0 1+X 2 1)+(1351287321/698000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (3488746015022248729/3490000000000000000 : ℝ)) (alpha := (1351287321/698000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3488746015022248729/3490000000000000000 : ℝ)*(X 0 2+X 1 2)+(1351287321/698000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (3488746015022248729/3490000000000000000 : ℝ)) (alpha := (1351287321/698000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2213646573/10000000000 : ℝ)*X 0 0+(674351793/1250000000 : ℝ)*X 0 1+(657996789/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345048321/10000000000 : ℝ)*X 1 0+(-2280037383/10000000000 : ℝ)*X 1 1+(657996827/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069009689/2000000000 : ℝ)*X 2 0+(1315993603/2500000000 : ℝ)*X 2 1+(-2280037487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378371049/10000000000 : ℝ)*X 0 0+(2126280851/5000000000 : ℝ)*X 0 1+(4507971679/10000000000 : ℝ)*X 0 2+(4378371049/10000000000 : ℝ)*X 1 0+(2126280851/5000000000 : ℝ)*X 1 1+(4507971679/10000000000 : ℝ)*X 1 2+(4378371049/10000000000 : ℝ)*X 2 0+(2126280851/5000000000 : ℝ)*X 2 1+(4507971679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2213651541/10000000000 : ℝ)*X 0 0+(5264302521/10000000000 : ℝ)*X 0 1+(2697242541/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664018159/1250000000 : ℝ)*X 1 0+(-268690859/1250000000 : ℝ)*X 1 1+(2697242541/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664018159/1250000000 : ℝ)*X 2 0+(2697242541/5000000000 : ℝ)*X 2 1+(-268690859/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1094595247/2500000000 : ℝ)*X 0 0+(4507331441/10000000000 : ℝ)*X 0 1+(850640869/2000000000 : ℝ)*X 0 2+(1094595247/2500000000 : ℝ)*X 1 0+(4507331441/10000000000 : ℝ)*X 1 1+(850640869/2000000000 : ℝ)*X 1 2+(1094595247/2500000000 : ℝ)*X 2 0+(4507331441/10000000000 : ℝ)*X 2 1+(850640869/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (350537328490216647347000667/43625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (976461113/50000000000000 : ℝ)*(base19) + (2065779451/100000000000000 : ℝ)*(base23) + (67432851/20000000000000 : ℝ)*(upper3) + (17225541/50000000000000 : ℝ)*(upper4) + (80555563/50000000000000 : ℝ)*(upper5) + (2889596141186041/50000000000000 : ℝ)*(major0) + (2889596141186041/50000000000000 : ℝ)*(major1) + (2889596141186041/50000000000000 : ℝ)*(major2) + (7642988929829313/100000000000000 : ℝ)*(sp0) + (1910762453532659/25000000000000 : ℝ)*(sp1) + (7643049701273411/100000000000000 : ℝ)*(sp2) + (1957650354042339/50000000000000 : ℝ)*(sp3) + (62837223549/100000000000000 : ℝ)*(sp4) + (31821765289/100000000000000 : ℝ)*(sp7) + (1957666264924983/50000000000000 : ℝ)*(f.failure) + (3821525883526431/50000000000000 : ℝ)*(f.sum) + (4417981469/5453125000000000000000000 : ℝ)*base65 + (2623430435727208111/174500000000000000000000000000000 : ℝ)*base68 + (2609441230534708111/174500000000000000000000000000000 : ℝ)*base70 + (1372394667974791889/174500000000000000000000000000000 : ℝ)*base71 + (1180783624913/349000000000000000000000000 : ℝ)*base74 + (1292966482333708111/174500000000000000000000000000000 : ℝ)*base76 + (2459439269480708111/174500000000000000000000000000000 : ℝ)*base78 + (2699272782836708111/174500000000000000000000000000000 : ℝ)*base80 + (182436373837/34900000000000000000000000 : ℝ)*base82 + (14642527/1250000000000000000000 : ℝ)*base90 + (14642527/1250000000000000000000 : ℝ)*base92 + (14642527/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (812164814998129430682603153/87250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (870595809/50000000000000 : ℝ)*(base19) + (473394223/25000000000000 : ℝ)*(base23) + (186839843/100000000000000 : ℝ)*(upper3) + (34663817/50000000000000 : ℝ)*(lower4) + (38059423/20000000000000 : ℝ)*(upper5) + (5808278673548819/100000000000000 : ℝ)*(major0) + (5808278673548819/100000000000000 : ℝ)*(major1) + (5808278673548819/100000000000000 : ℝ)*(major2) + (23563955161/50000000000000 : ℝ)*(sp1) + (50659805039/100000000000000 : ℝ)*(sp2) + (3840759415232293/50000000000000 : ℝ)*(sp4) + (3840734980681323/50000000000000 : ℝ)*(sp5) + (3840733138541327/50000000000000 : ℝ)*(sp6) + (2459398878969/62500000000 : ℝ)*(sp7) + (2459398878969/62500000000 : ℝ)*(f.failure) + (3840759415232293/50000000000000 : ℝ)*(f.sum) + (336613156717/43625000000000000000000000 : ℝ)*base66 + (1147238977756798949/349000000000000000000000000000000 : ℝ)*base68 + (1569754552510798949/349000000000000000000000000000000 : ℝ)*base70 + (1281997149988798949/349000000000000000000000000000000 : ℝ)*base72 + (1018384485487/87250000000000000000000000 : ℝ)*base74 + (2988483970438798949/349000000000000000000000000000000 : ℝ)*base76 + (4296815211969798949/349000000000000000000000000000000 : ℝ)*base78 + (7226105694133201051/349000000000000000000000000000000 : ℝ)*base79 + (2211824299941/349000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5041/390625000000000000 : ℝ)*base89 + (5041/390625000000000000 : ℝ)*base91 + (5041/390625000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1046_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1046_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1046_s8_0 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-221365431/1000000000 : ℝ)*x 0 + (1348676593/2500000000 : ℝ)*x 1 + (2632038677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221365431/1000000000 : ℝ)^8239 ≤ (13442198494063/100000000000000 : ℝ)^6191 := by
    have hnat : (221365431 : ℕ)^8239*100000000000000^6191 ≤ 13442198494063^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221365431 1000000000 13442198494063 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348676593/2500000000 : ℝ)^8239 ≤ (43984738960163/100000000000000 : ℝ)^6191 := by
    have hnat : (1348676593 : ℕ)^8239*100000000000000^6191 ≤ 43984738960163^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348676593 2500000000 43984738960163 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632038677/5000000000 : ℝ)^8239 ≤ (42573062532451/100000000000000 : ℝ)^6191 := by
    have hnat : (2632038677 : ℕ)^8239*100000000000000^6191 ≤ 42573062532451^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632038677 5000000000 42573062532451 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221365431/1000000000 : ℝ), (1348676593/2500000000 : ℝ), (2632038677/5000000000 : ℝ)] ![(13442198494063/100000000000000 : ℝ), (43984738960163/100000000000000 : ℝ), (42573062532451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221365431/1000000000 : ℝ)|^8239 ≤ (13442198494063/100000000000000 : ℝ)^6191
        have hw : |(-221365431/1000000000 : ℝ)|=(221365431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348676593/2500000000 : ℝ)|^8239 ≤ (43984738960163/100000000000000 : ℝ)^6191
        have hw : |(1348676593/2500000000 : ℝ)|=(1348676593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632038677/5000000000 : ℝ)|^8239 ≤ (42573062532451/100000000000000 : ℝ)^6191
        have hw : |(2632038677/5000000000 : ℝ)|=(2632038677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s8_1 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672510969/5000000000 : ℝ)*x 0 + (-569984211/2500000000 : ℝ)*x 1 + (2632038681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672510969/5000000000 : ℝ)^8239 ≤ (217232316069/500000000000 : ℝ)^6191 := by
    have hnat : (2672510969 : ℕ)^8239*500000000000^6191 ≤ 217232316069^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672510969 5000000000 217232316069 500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569984211/2500000000 : ℝ)^8239 ≤ (6990237075611/50000000000000 : ℝ)^6191 := by
    have hnat : (569984211 : ℕ)^8239*50000000000000^6191 ≤ 6990237075611^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569984211 2500000000 6990237075611 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632038681/5000000000 : ℝ)^8239 ≤ (42573062618553/100000000000000 : ℝ)^6191 := by
    have hnat : (2632038681 : ℕ)^8239*100000000000000^6191 ≤ 42573062618553^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632038681 5000000000 42573062618553 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672510969/5000000000 : ℝ), (-569984211/2500000000 : ℝ), (2632038681/5000000000 : ℝ)] ![(217232316069/500000000000 : ℝ), (6990237075611/50000000000000 : ℝ), (42573062618553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672510969/5000000000 : ℝ)|^8239 ≤ (217232316069/500000000000 : ℝ)^6191
        have hw : |(2672510969/5000000000 : ℝ)|=(2672510969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-569984211/2500000000 : ℝ)|^8239 ≤ (6990237075611/50000000000000 : ℝ)^6191
        have hw : |(-569984211/2500000000 : ℝ)|=(569984211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632038681/5000000000 : ℝ)|^8239 ≤ (42573062618553/100000000000000 : ℝ)^6191
        have hw : |(2632038681/5000000000 : ℝ)|=(2632038681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s8_2 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345021927/10000000000 : ℝ)*x 0 + (5264077383/10000000000 : ℝ)*x 1 + (-2279936831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345021927/10000000000 : ℝ)^8239 ≤ (4344646309481/10000000000000 : ℝ)^6191 := by
    have hnat : (5345021927 : ℕ)^8239*10000000000000^6191 ≤ 4344646309481^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345021927 10000000000 4344646309481 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264077383/10000000000 : ℝ)^8239 ≤ (42573062844573/100000000000000 : ℝ)^6191 := by
    have hnat : (5264077383 : ℕ)^8239*100000000000000^6191 ≤ 42573062844573^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264077383 10000000000 42573062844573 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2279936831/10000000000 : ℝ)^8239 ≤ (13980474045137/100000000000000 : ℝ)^6191 := by
    have hnat : (2279936831 : ℕ)^8239*100000000000000^6191 ≤ 13980474045137^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279936831 10000000000 13980474045137 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345021927/10000000000 : ℝ), (5264077383/10000000000 : ℝ), (-2279936831/10000000000 : ℝ)] ![(4344646309481/10000000000000 : ℝ), (42573062844573/100000000000000 : ℝ), (13980474045137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345021927/10000000000 : ℝ)|^8239 ≤ (4344646309481/10000000000000 : ℝ)^6191
        have hw : |(5345021927/10000000000 : ℝ)|=(5345021927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264077383/10000000000 : ℝ)|^8239 ≤ (42573062844573/100000000000000 : ℝ)^6191
        have hw : |(5264077383/10000000000 : ℝ)|=(5264077383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2279936831/10000000000 : ℝ)|^8239 ≤ (13980474045137/100000000000000 : ℝ)^6191
        have hw : |(-2279936831/10000000000 : ℝ)|=(2279936831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s8_3 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (109459409/250000000 : ℝ)*x 0 + (265797923/625000000 : ℝ)*x 1 + (4507765267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109459409/250000000 : ℝ)^8239 ≤ (33316430408829/100000000000000 : ℝ)^6191 := by
    have hnat : (109459409 : ℕ)^8239*100000000000000^6191 ≤ 33316430408829^6191*250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109459409 250000000 33316430408829 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265797923/625000000 : ℝ)^8239 ≤ (4006315071997/12500000000000 : ℝ)^6191 := by
    have hnat : (265797923 : ℕ)^8239*12500000000000^6191 ≤ 4006315071997^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265797923 625000000 4006315071997 12500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507765267/10000000000 : ℝ)^8239 ≤ (692660979867/2000000000000 : ℝ)^6191 := by
    have hnat : (4507765267 : ℕ)^8239*2000000000000^6191 ≤ 692660979867^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507765267 10000000000 692660979867 2000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109459409/250000000 : ℝ), (265797923/625000000 : ℝ), (4507765267/10000000000 : ℝ)] ![(33316430408829/100000000000000 : ℝ), (4006315071997/12500000000000 : ℝ), (692660979867/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109459409/250000000 : ℝ)|^8239 ≤ (33316430408829/100000000000000 : ℝ)^6191
        have hw : |(109459409/250000000 : ℝ)|=(109459409/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(265797923/625000000 : ℝ)|^8239 ≤ (4006315071997/12500000000000 : ℝ)^6191
        have hw : |(265797923/625000000 : ℝ)|=(265797923/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507765267/10000000000 : ℝ)|^8239 ≤ (692660979867/2000000000000 : ℝ)^6191
        have hw : |(4507765267/10000000000 : ℝ)|=(4507765267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s8_4 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-138353713/625000000 : ℝ)*x 0 + (329025269/625000000 : ℝ)*x 1 + (5394378259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138353713/625000000 : ℝ)^8239 ≤ (336055992297/2500000000000 : ℝ)^6191 := by
    have hnat : (138353713 : ℕ)^8239*2500000000000^6191 ≤ 336055992297^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138353713 625000000 336055992297 2500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329025269/625000000 : ℝ)^8239 ≤ (532207268433/1250000000000 : ℝ)^6191 := by
    have hnat : (329025269 : ℕ)^8239*1250000000000^6191 ≤ 532207268433^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329025269 625000000 532207268433 1250000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394378259/10000000000 : ℝ)^8239 ≤ (43981178820997/100000000000000 : ℝ)^6191 := by
    have hnat : (5394378259 : ℕ)^8239*100000000000000^6191 ≤ 43981178820997^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394378259 10000000000 43981178820997 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-138353713/625000000 : ℝ), (329025269/625000000 : ℝ), (5394378259/10000000000 : ℝ)] ![(336055992297/2500000000000 : ℝ), (532207268433/1250000000000 : ℝ), (43981178820997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-138353713/625000000 : ℝ)|^8239 ≤ (336055992297/2500000000000 : ℝ)^6191
        have hw : |(-138353713/625000000 : ℝ)|=(138353713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329025269/625000000 : ℝ)|^8239 ≤ (532207268433/1250000000000 : ℝ)^6191
        have hw : |(329025269/625000000 : ℝ)|=(329025269/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394378259/10000000000 : ℝ)|^8239 ≤ (43981178820997/100000000000000 : ℝ)^6191
        have hw : |(5394378259/10000000000 : ℝ)|=(5394378259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s8_5 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656085927/5000000000 : ℝ)*x 0 + (-2149635941/10000000000 : ℝ)*x 1 + (2697189093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656085927/5000000000 : ℝ)^8239 ≤ (43091475920341/100000000000000 : ℝ)^6191 := by
    have hnat : (2656085927 : ℕ)^8239*100000000000000^6191 ≤ 43091475920341^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656085927 5000000000 43091475920341 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149635941/10000000000 : ℝ)^8239 ≤ (3231836506003/25000000000000 : ℝ)^6191 := by
    have hnat : (2149635941 : ℕ)^8239*25000000000000^6191 ≤ 3231836506003^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149635941 10000000000 3231836506003 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697189093/5000000000 : ℝ)^8239 ≤ (4398117802893/10000000000000 : ℝ)^6191 := by
    have hnat : (2697189093 : ℕ)^8239*10000000000000^6191 ≤ 4398117802893^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697189093 5000000000 4398117802893 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656085927/5000000000 : ℝ), (-2149635941/10000000000 : ℝ), (2697189093/5000000000 : ℝ)] ![(43091475920341/100000000000000 : ℝ), (3231836506003/25000000000000 : ℝ), (4398117802893/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656085927/5000000000 : ℝ)|^8239 ≤ (43091475920341/100000000000000 : ℝ)^6191
        have hw : |(2656085927/5000000000 : ℝ)|=(2656085927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2149635941/10000000000 : ℝ)|^8239 ≤ (3231836506003/25000000000000 : ℝ)^6191
        have hw : |(-2149635941/10000000000 : ℝ)|=(2149635941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697189093/5000000000 : ℝ)|^8239 ≤ (4398117802893/10000000000000 : ℝ)^6191
        have hw : |(2697189093/5000000000 : ℝ)|=(2697189093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s8_6 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212486869/400000000 : ℝ)*x 0 + (2697189073/5000000000 : ℝ)*x 1 + (-2149636171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212486869/400000000 : ℝ)^8239 ≤ (43091474527753/100000000000000 : ℝ)^6191 := by
    have hnat : (212486869 : ℕ)^8239*100000000000000^6191 ≤ 43091474527753^6191*400000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212486869 400000000 43091474527753 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697189073/5000000000 : ℝ)^8239 ≤ (1099529439873/2500000000000 : ℝ)^6191 := by
    have hnat : (2697189073 : ℕ)^8239*2500000000000^6191 ≤ 1099529439873^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697189073 5000000000 1099529439873 2500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149636171/10000000000 : ℝ)^8239 ≤ (517093914589/4000000000000 : ℝ)^6191 := by
    have hnat : (2149636171 : ℕ)^8239*4000000000000^6191 ≤ 517093914589^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149636171 10000000000 517093914589 4000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212486869/400000000 : ℝ), (2697189073/5000000000 : ℝ), (-2149636171/10000000000 : ℝ)] ![(43091474527753/100000000000000 : ℝ), (1099529439873/2500000000000 : ℝ), (517093914589/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212486869/400000000 : ℝ)|^8239 ≤ (43091474527753/100000000000000 : ℝ)^6191
        have hw : |(212486869/400000000 : ℝ)|=(212486869/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697189073/5000000000 : ℝ)|^8239 ≤ (1099529439873/2500000000000 : ℝ)^6191
        have hw : |(2697189073/5000000000 : ℝ)|=(2697189073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2149636171/10000000000 : ℝ)|^8239 ≤ (517093914589/4000000000000 : ℝ)^6191
        have hw : |(-2149636171/10000000000 : ℝ)|=(2149636171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s8_7 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189193/5000000 : ℝ)*x 0 + (4507127181/10000000000 : ℝ)*x 1 + (4253407501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189193/5000000 : ℝ)^8239 ≤ (33316528028259/100000000000000 : ℝ)^6191 := by
    have hnat : (2189193 : ℕ)^8239*100000000000000^6191 ≤ 33316528028259^6191*5000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189193 5000000 33316528028259 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507127181/10000000000 : ℝ)^8239 ≤ (6925305003993/20000000000000 : ℝ)^6191 := by
    have hnat : (4507127181 : ℕ)^8239*20000000000000^6191 ≤ 6925305003993^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507127181 10000000000 6925305003993 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4253407501/10000000000 : ℝ)^8239 ≤ (8014236734307/25000000000000 : ℝ)^6191 := by
    have hnat : (4253407501 : ℕ)^8239*25000000000000^6191 ≤ 8014236734307^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253407501 10000000000 8014236734307 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189193/5000000 : ℝ), (4507127181/10000000000 : ℝ), (4253407501/10000000000 : ℝ)] ![(33316528028259/100000000000000 : ℝ), (6925305003993/20000000000000 : ℝ), (8014236734307/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189193/5000000 : ℝ)|^8239 ≤ (33316528028259/100000000000000 : ℝ)^6191
        have hw : |(2189193/5000000 : ℝ)|=(2189193/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507127181/10000000000 : ℝ)|^8239 ≤ (6925305003993/20000000000000 : ℝ)^6191
        have hw : |(4507127181/10000000000 : ℝ)|=(4507127181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4253407501/10000000000 : ℝ)|^8239 ≤ (8014236734307/25000000000000 : ℝ)^6191
        have hw : |(4253407501/10000000000 : ℝ)|=(4253407501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1046_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11223/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1399/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13993/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13993/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13993/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13993/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13993/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13993/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11221/100000 : ℝ) ^ (4119/1024 : ℝ) ≤ (15093469023046269/100000000000000000000 : ℝ) := by
    have hpowers : (11221/100000 : ℝ)^4119 ≤ (15093469023046269/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11221 : ℕ)^4119*100000000000000000000^1024 ≤ 15093469023046269^1024*100000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11221 100000 15093469023046269 100000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11221/100000 : ℝ)) (X := (15093469023046269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13993/100000 : ℝ) ^ (4119/1024 : ℝ) ≤ (36682564779534333/100000000000000000000 : ℝ) := by
    have hpowers : (13993/100000 : ℝ)^4119 ≤ (36682564779534333/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13993 : ℕ)^4119*100000000000000000000^1024 ≤ 36682564779534333^1024*100000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13993 100000 36682564779534333 100000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13993/100000 : ℝ)) (X := (36682564779534333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015093469023046269/50000000000000000000 : ℝ) ≤ (10000750374349579/10000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50015093469023046269/50000000000000000000 : ℝ)^1024 ≤ (10000750374349579/10000000000000000 : ℝ)^4119 := by
      have hnat : (50015093469023046269 : ℕ)^1024*10000000000000000^4119 ≤ 10000750374349579^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015093469023046269 50000000000000000000 10000750374349579 10000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000750374349579/10000000000000000 : ℝ)) (X := (50015093469023046269/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025888016901290301/50000000000000000000 : ℝ) ≤ (2000257384551883/2000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50025888016901290301/50000000000000000000 : ℝ)^1024 ≤ (2000257384551883/2000000000000000 : ℝ)^4119 := by
      have hnat : (50025888016901290301 : ℕ)^1024*2000000000000000^4119 ≤ 2000257384551883^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025888016901290301 50000000000000000000 2000257384551883 2000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000257384551883/2000000000000000 : ℝ)) (X := (50025888016901290301/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036682564779534333/50000000000000000000 : ℝ) ≤ (10001823471169251/10000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50036682564779534333/50000000000000000000 : ℝ)^1024 ≤ (10001823471169251/10000000000000000 : ℝ)^4119 := by
      have hnat : (50036682564779534333 : ℕ)^1024*10000000000000000^4119 ≤ 10001823471169251^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036682564779534333 50000000000000000000 10001823471169251 10000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001823471169251/10000000000000000 : ℝ)) (X := (50036682564779534333/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15093469023046269/100000000000000000000 : ℝ) ≤ ((989644243510124767/990000000000000000 : ℝ)+2*(134137102459/69300000000000 : ℝ)*(11221/100000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (989644243510124767/990000000000000000 : ℝ)+2*(134137102459/69300000000000 : ℝ)*(11221/100000 : ℝ)=(10000750374349579/10000000000000000 : ℝ) by norm_num, show 1+2*(15093469023046269/100000000000000000000 : ℝ)=(50015093469023046269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36682564779534333/100000000000000000000 : ℝ)+(15093469023046269/100000000000000000000 : ℝ) ≤ ((989644243510124767/990000000000000000 : ℝ)+(134137102459/69300000000000 : ℝ)*((13993/100000 : ℝ)+(11221/100000 : ℝ)))^(4119/1024 : ℝ) := by
    rw [show (989644243510124767/990000000000000000 : ℝ)+(134137102459/69300000000000 : ℝ)*((13993/100000 : ℝ)+(11221/100000 : ℝ))=(2000257384551883/2000000000000000 : ℝ) by norm_num, show 1+(36682564779534333/100000000000000000000 : ℝ)+(15093469023046269/100000000000000000000 : ℝ)=(50025888016901290301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36682564779534333/100000000000000000000 : ℝ) ≤ ((989644243510124767/990000000000000000 : ℝ)+2*(134137102459/69300000000000 : ℝ)*(13993/100000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (989644243510124767/990000000000000000 : ℝ)+2*(134137102459/69300000000000 : ℝ)*(13993/100000 : ℝ)=(10001823471169251/10000000000000000 : ℝ) by norm_num, show 1+2*(36682564779534333/100000000000000000000 : ℝ)=(50036682564779534333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (989644243510124767/990000000000000000 : ℝ)*(X 1 0+X 2 0)+(134137102459/69300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (13993/100000 : ℝ)) (c := (989644243510124767/990000000000000000 : ℝ)) (alpha := (134137102459/69300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (989644243510124767/990000000000000000 : ℝ)*(X 0 1+X 2 1)+(134137102459/69300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (13993/100000 : ℝ)) (c := (989644243510124767/990000000000000000 : ℝ)) (alpha := (134137102459/69300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (989644243510124767/990000000000000000 : ℝ)*(X 0 2+X 1 2)+(134137102459/69300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (13993/100000 : ℝ)) (c := (989644243510124767/990000000000000000 : ℝ)) (alpha := (134137102459/69300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-221365431/1000000000 : ℝ)*X 0 0+(1348676593/2500000000 : ℝ)*X 0 1+(2632038677/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672510969/5000000000 : ℝ)*X 1 0+(-569984211/2500000000 : ℝ)*X 1 1+(2632038681/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345021927/10000000000 : ℝ)*X 2 0+(5264077383/10000000000 : ℝ)*X 2 1+(-2279936831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((109459409/250000000 : ℝ)*X 0 0+(265797923/625000000 : ℝ)*X 0 1+(4507765267/10000000000 : ℝ)*X 0 2+(109459409/250000000 : ℝ)*X 1 0+(265797923/625000000 : ℝ)*X 1 1+(4507765267/10000000000 : ℝ)*X 1 2+(109459409/250000000 : ℝ)*X 2 0+(265797923/625000000 : ℝ)*X 2 1+(4507765267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-138353713/625000000 : ℝ)*X 0 0+(329025269/625000000 : ℝ)*X 0 1+(5394378259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656085927/5000000000 : ℝ)*X 1 0+(-2149635941/10000000000 : ℝ)*X 1 1+(2697189093/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212486869/400000000 : ℝ)*X 2 0+(2697189073/5000000000 : ℝ)*X 2 1+(-2149636171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189193/5000000 : ℝ)*X 0 0+(4507127181/10000000000 : ℝ)*X 0 1+(4253407501/10000000000 : ℝ)*X 0 2+(2189193/5000000 : ℝ)*X 1 0+(4507127181/10000000000 : ℝ)*X 1 1+(4253407501/10000000000 : ℝ)*X 1 2+(2189193/5000000 : ℝ)*X 2 0+(4507127181/10000000000 : ℝ)*X 2 1+(4253407501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4129230100239737894231/385000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2209148627/100000000000000 : ℝ)*(base19) + (80444901/4000000000000 : ℝ)*(base23) + (4871223/5000000000000 : ℝ)*(lower2) + (34458569/12500000000000 : ℝ)*(upper3) + (19638261/12500000000000 : ℝ)*(upper5) + (2894260477950339/50000000000000 : ℝ)*(major0) + (2894260477950339/50000000000000 : ℝ)*(major1) + (2894260477950339/50000000000000 : ℝ)*(major2) + (7655329353982957/100000000000000 : ℝ)*(sp0) + (7655386752360587/100000000000000 : ℝ)*(sp1) + (7655386950386689/100000000000000 : ℝ)*(sp2) + (980405109158887/25000000000000 : ℝ)*(sp3) + (29803763129/50000000000000 : ℝ)*(sp4) + (32156147481/100000000000000 : ℝ)*(sp7) + (392165259278303/10000000000000 : ℝ)*(f.failure) + (1531077792301843/20000000000000 : ℝ)*(f.sum) + (227674900069/72187500000000000000000000 : ℝ)*base65 + (946597216837740697/115500000000000000000000000000000 : ℝ)*base67 + (1040474085070259303/115500000000000000000000000000000 : ℝ)*base70 + (653828824799759303/115500000000000000000000000000000 : ℝ)*base72 + (2648688571699/1155000000000000000000000000 : ℝ)*base73 + (3173514436672740697/115500000000000000000000000000000 : ℝ)*base75 + (1004067802003259303/115500000000000000000000000000000 : ℝ)*base78 + (1229151975747240697/115500000000000000000000000000000 : ℝ)*base79 + (357502007707/144375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1630393/250000000000000000000 : ℝ)*base89 + (1630393/250000000000000000000 : ℝ)*base91 + (1630393/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33728511717454738548536021/10500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (345537423/100000000000000 : ℝ)*(base19) + (236308151/100000000000000 : ℝ)*(base23) + (80779077/100000000000000 : ℝ)*(upper2) + (23598937/100000000000000 : ℝ)*(lower3) + (5817602516438399/100000000000000 : ℝ)*(major0) + (5817602516438399/100000000000000 : ℝ)*(major1) + (5817602516438399/100000000000000 : ℝ)*(major2) + (2404199721/100000000000000 : ℝ)*(sp0) + (2423656843/20000000000000 : ℝ)*(sp1) + (77863419/100000000000000 : ℝ)*(sp2) + (961730940627273/12500000000000 : ℝ)*(sp4) + (7693837465396267/100000000000000 : ℝ)*(sp5) + (1538769923009267/20000000000000 : ℝ)*(sp6) + (49266937457303/1250000000000 : ℝ)*(sp7) + (49266937457303/1250000000000 : ℝ)*(f.failure) + (1538769985843581/20000000000000 : ℝ)*(f.sum) + (14640767069771/3465000000000000000000000000 : ℝ)*base65 + (3602757961451803769/693000000000000000000000000000000 : ℝ)*base68 + (1498706387057803769/693000000000000000000000000000000 : ℝ)*base70 + (4813169797248196231/693000000000000000000000000000000 : ℝ)*base71 + (1091115197287/433125000000000000000000000 : ℝ)*base73 + (705632060243803769/693000000000000000000000000000000 : ℝ)*base76 + (5776516997448196231/693000000000000000000000000000000 : ℝ)*base77 + (7244584700078803769/693000000000000000000000000000000 : ℝ)*base80 + (14258929793951/3465000000000000000000000000 : ℝ)*base81 + (508107/31250000000000000000 : ℝ)*base90 + (508107/31250000000000000000 : ℝ)*base92 + (508107/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1046_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1046_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1046_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1046_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1046_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1046_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1046_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
