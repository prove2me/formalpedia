-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1329_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:01:48.22+00:00
-- url     : https://prove2.me/submissions/66ecdea7-aa95-41f4-8d00-9d610921ec53

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
theorem support_rectangle_w1329_s6_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-256906299/1250000000 : ℝ)*x 0 + (1082679509/2000000000 : ℝ)*x 1 + (5244183179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256906299/1250000000 : ℝ)^4289 ≤ (6256463608043/50000000000000 : ℝ)^3265 := by
    have hnat : (256906299 : ℕ)^4289*50000000000000^3265 ≤ 6256463608043^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256906299 1250000000 6256463608043 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082679509/2000000000 : ℝ)^4289 ≤ (2232791944861/5000000000000 : ℝ)^3265 := by
    have hnat : (1082679509 : ℕ)^4289*5000000000000^3265 ≤ 2232791944861^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082679509 2000000000 2232791944861 5000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244183179/10000000000 : ℝ)^4289 ≤ (42831233876141/100000000000000 : ℝ)^3265 := by
    have hnat : (5244183179 : ℕ)^4289*100000000000000^3265 ≤ 42831233876141^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244183179 10000000000 42831233876141 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256906299/1250000000 : ℝ), (1082679509/2000000000 : ℝ), (5244183179/10000000000 : ℝ)] ![(6256463608043/50000000000000 : ℝ), (2232791944861/5000000000000 : ℝ), (42831233876141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256906299/1250000000 : ℝ)|^4289 ≤ (6256463608043/50000000000000 : ℝ)^3265
        have hw : |(-256906299/1250000000 : ℝ)|=(256906299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082679509/2000000000 : ℝ)|^4289 ≤ (2232791944861/5000000000000 : ℝ)^3265
        have hw : |(1082679509/2000000000 : ℝ)|=(1082679509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244183179/10000000000 : ℝ)|^4289 ≤ (42831233876141/100000000000000 : ℝ)^3265
        have hw : |(5244183179/10000000000 : ℝ)|=(5244183179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s6_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668652933/1250000000 : ℝ)*x 0 + (-535369303/2500000000 : ℝ)*x 1 + (5244183181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668652933/1250000000 : ℝ)^4289 ≤ (8792345062193/20000000000000 : ℝ)^3265 := by
    have hnat : (668652933 : ℕ)^4289*20000000000000^3265 ≤ 8792345062193^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668652933 1250000000 8792345062193 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535369303/2500000000 : ℝ)^4289 ≤ (6603520387443/50000000000000 : ℝ)^3265 := by
    have hnat : (535369303 : ℕ)^4289*50000000000000^3265 ≤ 6603520387443^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535369303 2500000000 6603520387443 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244183181/10000000000 : ℝ)^4289 ≤ (42831233897599/100000000000000 : ℝ)^3265 := by
    have hnat : (5244183181 : ℕ)^4289*100000000000000^3265 ≤ 42831233897599^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244183181 10000000000 42831233897599 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668652933/1250000000 : ℝ), (-535369303/2500000000 : ℝ), (5244183181/10000000000 : ℝ)] ![(8792345062193/20000000000000 : ℝ), (6603520387443/50000000000000 : ℝ), (42831233897599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668652933/1250000000 : ℝ)|^4289 ≤ (8792345062193/20000000000000 : ℝ)^3265
        have hw : |(668652933/1250000000 : ℝ)|=(668652933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535369303/2500000000 : ℝ)|^4289 ≤ (6603520387443/50000000000000 : ℝ)^3265
        have hw : |(-535369303/2500000000 : ℝ)|=(535369303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244183181/10000000000 : ℝ)|^4289 ≤ (42831233897599/100000000000000 : ℝ)^3265
        have hw : |(5244183181/10000000000 : ℝ)|=(5244183181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s6_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213968939/400000000 : ℝ)*x 0 + (1311045793/2500000000 : ℝ)*x 1 + (-2141477209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213968939/400000000 : ℝ)^4289 ≤ (43961725429719/100000000000000 : ℝ)^3265 := by
    have hnat : (213968939 : ℕ)^4289*100000000000000^3265 ≤ 43961725429719^3265*400000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213968939 400000000 43961725429719 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311045793/2500000000 : ℝ)^4289 ≤ (42831233801039/100000000000000 : ℝ)^3265 := by
    have hnat : (1311045793 : ℕ)^4289*100000000000000^3265 ≤ 42831233801039^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311045793 2500000000 42831233801039 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2141477209/10000000000 : ℝ)^4289 ≤ (13207040750581/100000000000000 : ℝ)^3265 := by
    have hnat : (2141477209 : ℕ)^4289*100000000000000^3265 ≤ 13207040750581^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141477209 10000000000 13207040750581 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213968939/400000000 : ℝ), (1311045793/2500000000 : ℝ), (-2141477209/10000000000 : ℝ)] ![(43961725429719/100000000000000 : ℝ), (42831233801039/100000000000000 : ℝ), (13207040750581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213968939/400000000 : ℝ)|^4289 ≤ (43961725429719/100000000000000 : ℝ)^3265
        have hw : |(213968939/400000000 : ℝ)|=(213968939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311045793/2500000000 : ℝ)|^4289 ≤ (42831233801039/100000000000000 : ℝ)^3265
        have hw : |(1311045793/2500000000 : ℝ)|=(1311045793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2141477209/10000000000 : ℝ)|^4289 ≤ (13207040750581/100000000000000 : ℝ)^3265
        have hw : |(-2141477209/10000000000 : ℝ)|=(2141477209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s6_3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4330027753/10000000000 : ℝ)*x 0 + (20785271/50000000 : ℝ)*x 1 + (4509753141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330027753/10000000000 : ℝ)^4289 ≤ (8325752139877/25000000000000 : ℝ)^3265 := by
    have hnat : (4330027753 : ℕ)^4289*25000000000000^3265 ≤ 8325752139877^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330027753 10000000000 8325752139877 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20785271/50000000 : ℝ)^4289 ≤ (3945805579489/12500000000000 : ℝ)^3265 := by
    have hnat : (20785271 : ℕ)^4289*12500000000000^3265 ≤ 3945805579489^3265*50000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20785271 50000000 3945805579489 12500000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509753141/10000000000 : ℝ)^4289 ≤ (4391318348879/12500000000000 : ℝ)^3265 := by
    have hnat : (4509753141 : ℕ)^4289*12500000000000^3265 ≤ 4391318348879^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509753141 10000000000 4391318348879 12500000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330027753/10000000000 : ℝ), (20785271/50000000 : ℝ), (4509753141/10000000000 : ℝ)] ![(8325752139877/25000000000000 : ℝ), (3945805579489/12500000000000 : ℝ), (4391318348879/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330027753/10000000000 : ℝ)|^4289 ≤ (8325752139877/25000000000000 : ℝ)^3265
        have hw : |(4330027753/10000000000 : ℝ)|=(4330027753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20785271/50000000 : ℝ)|^4289 ≤ (3945805579489/12500000000000 : ℝ)^3265
        have hw : |(20785271/50000000 : ℝ)|=(20785271/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509753141/10000000000 : ℝ)|^4289 ≤ (4391318348879/12500000000000 : ℝ)^3265
        have hw : |(4509753141/10000000000 : ℝ)|=(4509753141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s6_4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2055263919/10000000000 : ℝ)*x 0 + (1048957579/2000000000 : ℝ)*x 1 + (338299301/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055263919/10000000000 : ℝ)^4289 ≤ (6256517700783/50000000000000 : ℝ)^3265 := by
    have hnat : (2055263919 : ℕ)^4289*50000000000000^3265 ≤ 6256517700783^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055263919 10000000000 6256517700783 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048957579/2000000000 : ℝ)^4289 ≤ (42837721936861/100000000000000 : ℝ)^3265 := by
    have hnat : (1048957579 : ℕ)^4289*100000000000000^3265 ≤ 42837721936861^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048957579 2000000000 42837721936861 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338299301/625000000 : ℝ)^4289 ≤ (44649242640873/100000000000000 : ℝ)^3265 := by
    have hnat : (338299301 : ℕ)^4289*100000000000000^3265 ≤ 44649242640873^3265*625000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338299301 625000000 44649242640873 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2055263919/10000000000 : ℝ), (1048957579/2000000000 : ℝ), (338299301/625000000 : ℝ)] ![(6256517700783/50000000000000 : ℝ), (42837721936861/100000000000000 : ℝ), (44649242640873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2055263919/10000000000 : ℝ)|^4289 ≤ (6256517700783/50000000000000 : ℝ)^3265
        have hw : |(-2055263919/10000000000 : ℝ)|=(2055263919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048957579/2000000000 : ℝ)|^4289 ≤ (42837721936861/100000000000000 : ℝ)^3265
        have hw : |(1048957579/2000000000 : ℝ)|=(1048957579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338299301/625000000 : ℝ)|^4289 ≤ (44649242640873/100000000000000 : ℝ)^3265
        have hw : |(338299301/625000000 : ℝ)|=(338299301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s6_5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165803277/312500000 : ℝ)*x 0 + (-986435527/5000000000 : ℝ)*x 1 + (1353197041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165803277/312500000 : ℝ)^4289 ≤ (1739700221061/4000000000000 : ℝ)^3265 := by
    have hnat : (165803277 : ℕ)^4289*4000000000000^3265 ≤ 1739700221061^3265*312500000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165803277 312500000 1739700221061 4000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (986435527/5000000000 : ℝ)^4289 ≤ (2964564721047/25000000000000 : ℝ)^3265 := by
    have hnat : (986435527 : ℕ)^4289*25000000000000^3265 ≤ 2964564721047^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986435527 5000000000 2964564721047 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353197041/2500000000 : ℝ)^4289 ≤ (11162308893963/25000000000000 : ℝ)^3265 := by
    have hnat : (1353197041 : ℕ)^4289*25000000000000^3265 ≤ 11162308893963^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353197041 2500000000 11162308893963 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165803277/312500000 : ℝ), (-986435527/5000000000 : ℝ), (1353197041/2500000000 : ℝ)] ![(1739700221061/4000000000000 : ℝ), (2964564721047/25000000000000 : ℝ), (11162308893963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165803277/312500000 : ℝ)|^4289 ≤ (1739700221061/4000000000000 : ℝ)^3265
        have hw : |(165803277/312500000 : ℝ)|=(165803277/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-986435527/5000000000 : ℝ)|^4289 ≤ (2964564721047/25000000000000 : ℝ)^3265
        have hw : |(-986435527/5000000000 : ℝ)|=(986435527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353197041/2500000000 : ℝ)|^4289 ≤ (11162308893963/25000000000000 : ℝ)^3265
        have hw : |(1353197041/2500000000 : ℝ)|=(1353197041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s6_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305705317/10000000000 : ℝ)*x 0 + (270639393/500000000 : ℝ)*x 1 + (-1972870853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305705317/10000000000 : ℝ)^4289 ≤ (10873127601133/25000000000000 : ℝ)^3265 := by
    have hnat : (5305705317 : ℕ)^4289*25000000000000^3265 ≤ 10873127601133^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305705317 10000000000 10873127601133 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270639393/500000000 : ℝ)^4289 ≤ (11162308070433/25000000000000 : ℝ)^3265 := by
    have hnat : (270639393 : ℕ)^4289*25000000000000^3265 ≤ 11162308070433^3265*500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270639393 500000000 11162308070433 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1972870853/10000000000 : ℝ)^4289 ≤ (741141081071/6250000000000 : ℝ)^3265 := by
    have hnat : (1972870853 : ℕ)^4289*6250000000000^3265 ≤ 741141081071^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972870853 10000000000 741141081071 6250000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305705317/10000000000 : ℝ), (270639393/500000000 : ℝ), (-1972870853/10000000000 : ℝ)] ![(10873127601133/25000000000000 : ℝ), (11162308070433/25000000000000 : ℝ), (741141081071/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305705317/10000000000 : ℝ)|^4289 ≤ (10873127601133/25000000000000 : ℝ)^3265
        have hw : |(5305705317/10000000000 : ℝ)|=(5305705317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270639393/500000000 : ℝ)|^4289 ≤ (11162308070433/25000000000000 : ℝ)^3265
        have hw : |(270639393/500000000 : ℝ)|=(270639393/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1972870853/10000000000 : ℝ)|^4289 ≤ (741141081071/6250000000000 : ℝ)^3265
        have hw : |(-1972870853/10000000000 : ℝ)|=(1972870853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s6_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (866010749/2000000000 : ℝ)*x 0 + (35222589/78125000 : ℝ)*x 1 + (4158322147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866010749/2000000000 : ℝ)^4289 ≤ (33303271166181/100000000000000 : ℝ)^3265 := by
    have hnat : (866010749 : ℕ)^4289*100000000000000^3265 ≤ 33303271166181^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866010749 2000000000 33303271166181 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35222589/78125000 : ℝ)^4289 ≤ (35117635819793/100000000000000 : ℝ)^3265 := by
    have hnat : (35222589 : ℕ)^4289*100000000000000^3265 ≤ 35117635819793^3265*78125000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35222589 78125000 35117635819793 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4158322147/10000000000 : ℝ)^4289 ≤ (31579093010361/100000000000000 : ℝ)^3265 := by
    have hnat : (4158322147 : ℕ)^4289*100000000000000^3265 ≤ 31579093010361^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158322147 10000000000 31579093010361 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866010749/2000000000 : ℝ), (35222589/78125000 : ℝ), (4158322147/10000000000 : ℝ)] ![(33303271166181/100000000000000 : ℝ), (35117635819793/100000000000000 : ℝ), (31579093010361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866010749/2000000000 : ℝ)|^4289 ≤ (33303271166181/100000000000000 : ℝ)^3265
        have hw : |(866010749/2000000000 : ℝ)|=(866010749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35222589/78125000 : ℝ)|^4289 ≤ (35117635819793/100000000000000 : ℝ)^3265
        have hw : |(35222589/78125000 : ℝ)|=(35222589/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4158322147/10000000000 : ℝ)|^4289 ≤ (31579093010361/100000000000000 : ℝ)^3265
        have hw : |(4158322147/10000000000 : ℝ)|=(4158322147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s6_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-6414653/2000000000 : ℝ)*x 0 + (1437475353/2500000000 : ℝ)*x 1 + (6043892257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6414653/2000000000 : ℝ)^4289 ≤ (1655184333/3125000000000 : ℝ)^3265 := by
    have hnat : (6414653 : ℕ)^4289*3125000000000^3265 ≤ 1655184333^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6414653 2000000000 1655184333 3125000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1437475353/2500000000 : ℝ)^4289 ≤ (48337349466799/100000000000000 : ℝ)^3265 := by
    have hnat : (1437475353 : ℕ)^4289*100000000000000^3265 ≤ 48337349466799^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437475353 2500000000 48337349466799 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6043892257/10000000000 : ℝ)^4289 ≤ (25804842311711/50000000000000 : ℝ)^3265 := by
    have hnat : (6043892257 : ℕ)^4289*50000000000000^3265 ≤ 25804842311711^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6043892257 10000000000 25804842311711 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6414653/2000000000 : ℝ), (1437475353/2500000000 : ℝ), (6043892257/10000000000 : ℝ)] ![(1655184333/3125000000000 : ℝ), (48337349466799/100000000000000 : ℝ), (25804842311711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6414653/2000000000 : ℝ)|^4289 ≤ (1655184333/3125000000000 : ℝ)^3265
        have hw : |(-6414653/2000000000 : ℝ)|=(6414653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1437475353/2500000000 : ℝ)|^4289 ≤ (48337349466799/100000000000000 : ℝ)^3265
        have hw : |(1437475353/2500000000 : ℝ)|=(1437475353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6043892257/10000000000 : ℝ)|^4289 ≤ (25804842311711/50000000000000 : ℝ)^3265
        have hw : |(6043892257/10000000000 : ℝ)|=(6043892257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s6_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (50287097/500000000 : ℝ)*x 0 + (-4294146183/10000000000 : ℝ)*x 1 + (139273583/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50287097/500000000 : ℝ)^4289 ≤ (2446848166197/50000000000000 : ℝ)^3265 := by
    have hnat : (50287097 : ℕ)^4289*50000000000000^3265 ≤ 2446848166197^3265*500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50287097 500000000 2446848166197 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4294146183/10000000000 : ℝ)^4289 ≤ (16470478138147/50000000000000 : ℝ)^3265 := by
    have hnat : (4294146183 : ℕ)^4289*50000000000000^3265 ≤ 16470478138147^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4294146183 10000000000 16470478138147 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139273583/200000000 : ℝ)^4289 ≤ (62165347377541/100000000000000 : ℝ)^3265 := by
    have hnat : (139273583 : ℕ)^4289*100000000000000^3265 ≤ 62165347377541^3265*200000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139273583 200000000 62165347377541 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(50287097/500000000 : ℝ), (-4294146183/10000000000 : ℝ), (139273583/200000000 : ℝ)] ![(2446848166197/50000000000000 : ℝ), (16470478138147/50000000000000 : ℝ), (62165347377541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(50287097/500000000 : ℝ)|^4289 ≤ (2446848166197/50000000000000 : ℝ)^3265
        have hw : |(50287097/500000000 : ℝ)|=(50287097/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4294146183/10000000000 : ℝ)|^4289 ≤ (16470478138147/50000000000000 : ℝ)^3265
        have hw : |(-4294146183/10000000000 : ℝ)|=(4294146183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(139273583/200000000 : ℝ)|^4289 ≤ (62165347377541/100000000000000 : ℝ)^3265
        have hw : |(139273583/200000000 : ℝ)|=(139273583/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s6_10 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1414580669/10000000000 : ℝ)*x 0 + (1422606799/2500000000 : ℝ)*x 1 + (5413613391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1414580669/10000000000 : ℝ)^4289 ≤ (3830095492741/50000000000000 : ℝ)^3265 := by
    have hnat : (1414580669 : ℕ)^4289*50000000000000^3265 ≤ 3830095492741^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414580669 10000000000 3830095492741 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1422606799/2500000000 : ℝ)^4289 ≤ (23840815557061/50000000000000 : ℝ)^3265 := by
    have hnat : (1422606799 : ℕ)^4289*50000000000000^3265 ≤ 23840815557061^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422606799 2500000000 23840815557061 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413613391/10000000000 : ℝ)^4289 ≤ (22329088942389/50000000000000 : ℝ)^3265 := by
    have hnat : (5413613391 : ℕ)^4289*50000000000000^3265 ≤ 22329088942389^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413613391 10000000000 22329088942389 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1414580669/10000000000 : ℝ), (1422606799/2500000000 : ℝ), (5413613391/10000000000 : ℝ)] ![(3830095492741/50000000000000 : ℝ), (23840815557061/50000000000000 : ℝ), (22329088942389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1414580669/10000000000 : ℝ)|^4289 ≤ (3830095492741/50000000000000 : ℝ)^3265
        have hw : |(1414580669/10000000000 : ℝ)|=(1414580669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1422606799/2500000000 : ℝ)|^4289 ≤ (23840815557061/50000000000000 : ℝ)^3265
        have hw : |(1422606799/2500000000 : ℝ)|=(1422606799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413613391/10000000000 : ℝ)|^4289 ≤ (22329088942389/50000000000000 : ℝ)^3265
        have hw : |(5413613391/10000000000 : ℝ)|=(5413613391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1329_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11117/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14699/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11109/100000 : ℝ) ^ (67/16 : ℝ) ≤ (10087044188300009/100000000000000000000 : ℝ) := by
    have hpowers : (11109/100000 : ℝ)^67 ≤ (10087044188300009/100000000000000000000 : ℝ)^16 := by
      have hnat : (11109 : ℕ)^67*100000000000000000000^16 ≤ 10087044188300009^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11109 100000 10087044188300009 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11109/100000 : ℝ)) (X := (10087044188300009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hpowhi : (3677/25000 : ℝ) ^ (67/16 : ℝ) ≤ (32668619964485633/100000000000000000000 : ℝ) := by
    have hpowers : (3677/25000 : ℝ)^67 ≤ (32668619964485633/100000000000000000000 : ℝ)^16 := by
      have hnat : (3677 : ℕ)^67*100000000000000000000^16 ≤ 32668619964485633^16*25000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3677 25000 32668619964485633 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3677/25000 : ℝ)) (X := (32668619964485633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010087044188300009/50000000000000000000 : ℝ) ≤ (1250060216535981/1250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50010087044188300009/50000000000000000000 : ℝ)^16 ≤ (1250060216535981/1250000000000000 : ℝ)^67 := by
      have hnat : (50010087044188300009 : ℕ)^16*1250000000000000^67 ≤ 1250060216535981^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010087044188300009 50000000000000000000 1250060216535981 1250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250060216535981/1250000000000000 : ℝ)) (X := (50010087044188300009/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021377832076392821/50000000000000000000 : ℝ) ≤ (10001020864678377/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50021377832076392821/50000000000000000000 : ℝ)^16 ≤ (10001020864678377/10000000000000000 : ℝ)^67 := by
      have hnat : (50021377832076392821 : ℕ)^16*10000000000000000^67 ≤ 10001020864678377^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021377832076392821 50000000000000000000 10001020864678377 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001020864678377/10000000000000000 : ℝ)) (X := (50021377832076392821/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032668619964485633/50000000000000000000 : ℝ) ≤ (5000779998534453/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50032668619964485633/50000000000000000000 : ℝ)^16 ≤ (5000779998534453/5000000000000000 : ℝ)^67 := by
      have hnat : (50032668619964485633 : ℕ)^16*5000000000000000^67 ≤ 5000779998534453^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032668619964485633 50000000000000000000 5000779998534453 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000779998534453/5000000000000000 : ℝ)) (X := (50032668619964485633/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10087044188300009/100000000000000000000 : ℝ) ≤ ((3597975531105119163/3599000000000000000 : ℝ)+2*(539132390529/359900000000000 : ℝ)*(11109/100000 : ℝ))^(67/16 : ℝ) := by
    rw [show (3597975531105119163/3599000000000000000 : ℝ)+2*(539132390529/359900000000000 : ℝ)*(11109/100000 : ℝ)=(1250060216535981/1250000000000000 : ℝ) by norm_num, show 1+2*(10087044188300009/100000000000000000000 : ℝ)=(50010087044188300009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32668619964485633/100000000000000000000 : ℝ)+(10087044188300009/100000000000000000000 : ℝ) ≤ ((3597975531105119163/3599000000000000000 : ℝ)+(539132390529/359900000000000 : ℝ)*((3677/25000 : ℝ)+(11109/100000 : ℝ)))^(67/16 : ℝ) := by
    rw [show (3597975531105119163/3599000000000000000 : ℝ)+(539132390529/359900000000000 : ℝ)*((3677/25000 : ℝ)+(11109/100000 : ℝ))=(10001020864678377/10000000000000000 : ℝ) by norm_num, show 1+(32668619964485633/100000000000000000000 : ℝ)+(10087044188300009/100000000000000000000 : ℝ)=(50021377832076392821/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32668619964485633/100000000000000000000 : ℝ) ≤ ((3597975531105119163/3599000000000000000 : ℝ)+2*(539132390529/359900000000000 : ℝ)*(3677/25000 : ℝ))^(67/16 : ℝ) := by
    rw [show (3597975531105119163/3599000000000000000 : ℝ)+2*(539132390529/359900000000000 : ℝ)*(3677/25000 : ℝ)=(5000779998534453/5000000000000000 : ℝ) by norm_num, show 1+2*(32668619964485633/100000000000000000000 : ℝ)=(50032668619964485633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3597975531105119163/3599000000000000000 : ℝ)*(X 1 0+X 2 0)+(539132390529/359900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (3597975531105119163/3599000000000000000 : ℝ)) (alpha := (539132390529/359900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3597975531105119163/3599000000000000000 : ℝ)*(X 0 1+X 2 1)+(539132390529/359900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (3597975531105119163/3599000000000000000 : ℝ)) (alpha := (539132390529/359900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3597975531105119163/3599000000000000000 : ℝ)*(X 0 2+X 1 2)+(539132390529/359900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (3597975531105119163/3599000000000000000 : ℝ)) (alpha := (539132390529/359900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-256906299/1250000000 : ℝ)*X 0 0+(1082679509/2000000000 : ℝ)*X 0 1+(5244183179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668652933/1250000000 : ℝ)*X 1 0+(-535369303/2500000000 : ℝ)*X 1 1+(5244183181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213968939/400000000 : ℝ)*X 2 0+(1311045793/2500000000 : ℝ)*X 2 1+(-2141477209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4330027753/10000000000 : ℝ)*X 0 0+(20785271/50000000 : ℝ)*X 0 1+(4509753141/10000000000 : ℝ)*X 0 2+(4330027753/10000000000 : ℝ)*X 1 0+(20785271/50000000 : ℝ)*X 1 1+(4509753141/10000000000 : ℝ)*X 1 2+(4330027753/10000000000 : ℝ)*X 2 0+(20785271/50000000 : ℝ)*X 2 1+(4509753141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2055263919/10000000000 : ℝ)*X 0 0+(1048957579/2000000000 : ℝ)*X 0 1+(338299301/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165803277/312500000 : ℝ)*X 1 0+(-986435527/5000000000 : ℝ)*X 1 1+(1353197041/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305705317/10000000000 : ℝ)*X 2 0+(270639393/500000000 : ℝ)*X 2 1+(-1972870853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((866010749/2000000000 : ℝ)*X 0 0+(35222589/78125000 : ℝ)*X 0 1+(4158322147/10000000000 : ℝ)*X 0 2+(866010749/2000000000 : ℝ)*X 1 0+(35222589/78125000 : ℝ)*X 1 1+(4158322147/10000000000 : ℝ)*X 1 2+(866010749/2000000000 : ℝ)*X 2 0+(35222589/78125000 : ℝ)*X 2 1+(4158322147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-6414653/2000000000 : ℝ)*X 0 0+(1437475353/2500000000 : ℝ)*X 0 1+(6043892257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s6_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((50287097/500000000 : ℝ)*X 1 0+(-4294146183/10000000000 : ℝ)*X 1 1+(139273583/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s6_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1414580669/10000000000 : ℝ)*X 0 0+(1422606799/2500000000 : ℝ)*X 0 1+(5413613391/10000000000 : ℝ)*X 0 2+(1414580669/10000000000 : ℝ)*X 1 0+(1422606799/2500000000 : ℝ)*X 1 1+(5413613391/10000000000 : ℝ)*X 1 2+(1414580669/10000000000 : ℝ)*X 2 0+(1422606799/2500000000 : ℝ)*X 2 1+(5413613391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s6_10 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (360307802196777184187274903/22493750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (402147281/50000000000000 : ℝ)*(lower2) + (135919657/100000000000000 : ℝ)*(lower3) + (42260329/20000000000000 : ℝ)*(lower4) + (546558121703173/12500000000000 : ℝ)*(major0) + (546558121703173/12500000000000 : ℝ)*(major1) + (546558121703173/12500000000000 : ℝ)*(major2) + (5909649676998869/100000000000000 : ℝ)*(sp0) + (738706618052627/12500000000000 : ℝ)*(sp1) + (2954827147351287/50000000000000 : ℝ)*(sp2) + (177204685729417/6250000000000 : ℝ)*(sp3) + (61599721/100000000000000 : ℝ)*(sp7) + (923540741/20000000000000 : ℝ)*(sp8) + (675140779/50000000000000 : ℝ)*(sp9) + (4267007/5000000000000 : ℝ)*(sp10) + (708818779652633/25000000000000 : ℝ)*(f.failure) + (2954827147351287/50000000000000 : ℝ)*(f.sum) + (14500886212281/4498750000000000000000000000 : ℝ)*base66 + (117000187255413301/44987500000000000000000000000000 : ℝ)*base68 + (257153036905561699/44987500000000000000000000000000 : ℝ)*base69 + (761497662499936699/44987500000000000000000000000000 : ℝ)*base71 + (1837650672517/8997500000000000000000000000 : ℝ)*base74 + (158958332091311699/44987500000000000000000000000000 : ℝ)*base75 + (435739500986238301/44987500000000000000000000000000 : ℝ)*base78 + (183229442617874199/44987500000000000000000000000000 : ℝ)*base79 + (9785146756701/17995000000000000000000000000 : ℝ)*base81 + (18734301/2500000000000000000000 : ℝ)*base90 + (18734301/2500000000000000000000 : ℝ)*base92 + (18734301/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1465334698344512217794313/44987500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67410697/25000000000000 : ℝ)*(lower2) + (22819661/3125000000000 : ℝ)*(lower3) + (765502567/100000000000000 : ℝ)*(lower5) + (1101019070001983/25000000000000 : ℝ)*(major0) + (1101019070001983/25000000000000 : ℝ)*(major1) + (1101019070001983/25000000000000 : ℝ)*(major2) + (3669628563/25000000000000 : ℝ)*(sp0) + (188166647/6250000000000 : ℝ)*(sp3) + (5952355427454209/100000000000000 : ℝ)*(sp4) + (2976189724342351/50000000000000 : ℝ)*(sp5) + (2976189724342351/50000000000000 : ℝ)*(sp6) + (1427883355014557/50000000000000 : ℝ)*(sp7) + (9342716241/100000000000000 : ℝ)*(sp8) + (677909991/20000000000000 : ℝ)*(sp10) + (142788655512271/5000000000000 : ℝ)*(f.failure) + (2976189724342351/50000000000000 : ℝ)*(f.sum) + (111546508971167/17995000000000000000000000000 : ℝ)*base66 + (1063245897725245229/89975000000000000000000000000000 : ℝ)*base67 + (164058218349029771/89975000000000000000000000000000 : ℝ)*base70 + (3176242476595229/89975000000000000000000000000000 : ℝ)*base71 + (22633775169293/4498750000000000000000000000 : ℝ)*base74 + (92557001329445229/89975000000000000000000000000000 : ℝ)*base75 + (919442703813254771/89975000000000000000000000000000 : ℝ)*base78 + (176292679106070229/89975000000000000000000000000000 : ℝ)*base79 + (165787142846027/17995000000000000000000000000 : ℝ)*base82 + (1564587/500000000000000000000 : ℝ)*base90 + (1564587/500000000000000000000 : ℝ)*base92 + (1564587/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1329_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1329_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1329_s7_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2055260033/10000000000 : ℝ)*x 0 + (676665533/1250000000 : ℝ)*x 1 + (2622125003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055260033/10000000000 : ℝ)^4289 ≤ (12513004322311/100000000000000 : ℝ)^3265 := by
    have hnat : (2055260033 : ℕ)^4289*100000000000000^3265 ≤ 12513004322311^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055260033 10000000000 12513004322311 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676665533/1250000000 : ℝ)^4289 ≤ (11163761200923/25000000000000 : ℝ)^3265 := by
    have hnat : (676665533 : ℕ)^4289*25000000000000^3265 ≤ 11163761200923^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676665533 1250000000 11163761200923 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622125003/5000000000 : ℝ)^4289 ≤ (10707987714607/25000000000000 : ℝ)^3265 := by
    have hnat : (2622125003 : ℕ)^4289*25000000000000^3265 ≤ 10707987714607^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622125003 5000000000 10707987714607 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2055260033/10000000000 : ℝ), (676665533/1250000000 : ℝ), (2622125003/5000000000 : ℝ)] ![(12513004322311/100000000000000 : ℝ), (11163761200923/25000000000000 : ℝ), (10707987714607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2055260033/10000000000 : ℝ)|^4289 ≤ (12513004322311/100000000000000 : ℝ)^3265
        have hw : |(-2055260033/10000000000 : ℝ)|=(2055260033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676665533/1250000000 : ℝ)|^4289 ≤ (11163761200923/25000000000000 : ℝ)^3265
        have hw : |(676665533/1250000000 : ℝ)|=(676665533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622125003/5000000000 : ℝ)|^4289 ≤ (10707987714607/25000000000000 : ℝ)^3265
        have hw : |(2622125003/5000000000 : ℝ)|=(2622125003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s7_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349204031/10000000000 : ℝ)*x 0 + (-2141415209/10000000000 : ℝ)*x 1 + (2622124777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349204031/10000000000 : ℝ)^4289 ≤ (686898679927/1562500000000 : ℝ)^3265 := by
    have hnat : (5349204031 : ℕ)^4289*1562500000000^3265 ≤ 686898679927^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349204031 10000000000 686898679927 1562500000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2141415209/10000000000 : ℝ)^4289 ≤ (13206538460457/100000000000000 : ℝ)^3265 := by
    have hnat : (2141415209 : ℕ)^4289*100000000000000^3265 ≤ 13206538460457^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141415209 10000000000 13206538460457 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622124777/5000000000 : ℝ)^4289 ≤ (42831946008941/100000000000000 : ℝ)^3265 := by
    have hnat : (2622124777 : ℕ)^4289*100000000000000^3265 ≤ 42831946008941^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622124777 5000000000 42831946008941 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349204031/10000000000 : ℝ), (-2141415209/10000000000 : ℝ), (2622124777/5000000000 : ℝ)] ![(686898679927/1562500000000 : ℝ), (13206538460457/100000000000000 : ℝ), (42831946008941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349204031/10000000000 : ℝ)|^4289 ≤ (686898679927/1562500000000 : ℝ)^3265
        have hw : |(5349204031/10000000000 : ℝ)|=(5349204031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2141415209/10000000000 : ℝ)|^4289 ≤ (13206538460457/100000000000000 : ℝ)^3265
        have hw : |(-2141415209/10000000000 : ℝ)|=(2141415209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622124777/5000000000 : ℝ)|^4289 ≤ (42831946008941/100000000000000 : ℝ)^3265
        have hw : |(2622124777/5000000000 : ℝ)|=(2622124777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s7_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069840969/2000000000 : ℝ)*x 0 + (5244249643/10000000000 : ℝ)*x 1 + (-2141414007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069840969/2000000000 : ℝ)^4289 ≤ (2198076215157/5000000000000 : ℝ)^3265 := by
    have hnat : (1069840969 : ℕ)^4289*5000000000000^3265 ≤ 2198076215157^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069840969 2000000000 2198076215157 5000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244249643/10000000000 : ℝ)^4289 ≤ (21415973481909/50000000000000 : ℝ)^3265 := by
    have hnat : (5244249643 : ℕ)^4289*50000000000000^3265 ≤ 21415973481909^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244249643 10000000000 21415973481909 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2141414007/10000000000 : ℝ)^4289 ≤ (2641305744511/20000000000000 : ℝ)^3265 := by
    have hnat : (2141414007 : ℕ)^4289*20000000000000^3265 ≤ 2641305744511^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141414007 10000000000 2641305744511 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069840969/2000000000 : ℝ), (5244249643/10000000000 : ℝ), (-2141414007/10000000000 : ℝ)] ![(2198076215157/5000000000000 : ℝ), (21415973481909/50000000000000 : ℝ), (2641305744511/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069840969/2000000000 : ℝ)|^4289 ≤ (2198076215157/5000000000000 : ℝ)^3265
        have hw : |(1069840969/2000000000 : ℝ)|=(1069840969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244249643/10000000000 : ℝ)|^4289 ≤ (21415973481909/50000000000000 : ℝ)^3265
        have hw : |(5244249643/10000000000 : ℝ)|=(5244249643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2141414007/10000000000 : ℝ)|^4289 ≤ (2641305744511/20000000000000 : ℝ)^3265
        have hw : |(-2141414007/10000000000 : ℝ)|=(2141414007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s7_3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4330032871/10000000000 : ℝ)*x 0 + (83143993/200000000 : ℝ)*x 1 + (140925197/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330032871/10000000000 : ℝ)^4289 ≤ (33303060268493/100000000000000 : ℝ)^3265 := by
    have hnat : (4330032871 : ℕ)^4289*100000000000000^3265 ≤ 33303060268493^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330032871 10000000000 33303060268493 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83143993/200000000 : ℝ)^4289 ≤ (15783947753709/50000000000000 : ℝ)^3265 := by
    have hnat : (83143993 : ℕ)^4289*50000000000000^3265 ≤ 15783947753709^3265*200000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83143993 200000000 15783947753709 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140925197/312500000 : ℝ)^4289 ≤ (35129044208673/100000000000000 : ℝ)^3265 := by
    have hnat : (140925197 : ℕ)^4289*100000000000000^3265 ≤ 35129044208673^3265*312500000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140925197 312500000 35129044208673 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330032871/10000000000 : ℝ), (83143993/200000000 : ℝ), (140925197/312500000 : ℝ)] ![(33303060268493/100000000000000 : ℝ), (15783947753709/50000000000000 : ℝ), (35129044208673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330032871/10000000000 : ℝ)|^4289 ≤ (33303060268493/100000000000000 : ℝ)^3265
        have hw : |(4330032871/10000000000 : ℝ)|=(4330032871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(83143993/200000000 : ℝ)|^4289 ≤ (15783947753709/50000000000000 : ℝ)^3265
        have hw : |(83143993/200000000 : ℝ)|=(83143993/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140925197/312500000 : ℝ)|^4289 ≤ (35129044208673/100000000000000 : ℝ)^3265
        have hw : |(140925197/312500000 : ℝ)|=(140925197/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s7_4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411054557/2000000000 : ℝ)*x 0 + (5244853959/10000000000 : ℝ)*x 1 + (2706358429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411054557/2000000000 : ℝ)^4289 ≤ (3128276577421/25000000000000 : ℝ)^3265 := by
    have hnat : (411054557 : ℕ)^4289*25000000000000^3265 ≤ 3128276577421^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411054557 2000000000 3128276577421 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244853959/10000000000 : ℝ)^4289 ≤ (42838430758589/100000000000000 : ℝ)^3265 := by
    have hnat : (5244853959 : ℕ)^4289*100000000000000^3265 ≤ 42838430758589^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244853959 10000000000 42838430758589 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706358429/5000000000 : ℝ)^4289 ≤ (2790528931951/6250000000000 : ℝ)^3265 := by
    have hnat : (2706358429 : ℕ)^4289*6250000000000^3265 ≤ 2790528931951^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706358429 5000000000 2790528931951 6250000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411054557/2000000000 : ℝ), (5244853959/10000000000 : ℝ), (2706358429/5000000000 : ℝ)] ![(3128276577421/25000000000000 : ℝ), (42838430758589/100000000000000 : ℝ), (2790528931951/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411054557/2000000000 : ℝ)|^4289 ≤ (3128276577421/25000000000000 : ℝ)^3265
        have hw : |(-411054557/2000000000 : ℝ)|=(411054557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244853959/10000000000 : ℝ)|^4289 ≤ (42838430758589/100000000000000 : ℝ)^3265
        have hw : |(5244853959/10000000000 : ℝ)|=(5244853959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706358429/5000000000 : ℝ)|^4289 ≤ (2790528931951/6250000000000 : ℝ)^3265
        have hw : |(2706358429/5000000000 : ℝ)|=(2706358429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s7_5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305721057/10000000000 : ℝ)*x 0 + (-1972947047/10000000000 : ℝ)*x 1 + (2706358349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305721057/10000000000 : ℝ)^4289 ≤ (43492679896507/100000000000000 : ℝ)^3265 := by
    have hnat : (5305721057 : ℕ)^4289*100000000000000^3265 ≤ 43492679896507^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305721057 10000000000 43492679896507 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972947047/10000000000 : ℝ)^4289 ≤ (11858858911889/100000000000000 : ℝ)^3265 := by
    have hnat : (1972947047 : ℕ)^4289*100000000000000^3265 ≤ 11858858911889^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972947047 10000000000 11858858911889 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706358349/5000000000 : ℝ)^4289 ≤ (11162115294369/25000000000000 : ℝ)^3265 := by
    have hnat : (2706358349 : ℕ)^4289*25000000000000^3265 ≤ 11162115294369^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706358349 5000000000 11162115294369 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305721057/10000000000 : ℝ), (-1972947047/10000000000 : ℝ), (2706358349/5000000000 : ℝ)] ![(43492679896507/100000000000000 : ℝ), (11858858911889/100000000000000 : ℝ), (11162115294369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305721057/10000000000 : ℝ)|^4289 ≤ (43492679896507/100000000000000 : ℝ)^3265
        have hw : |(5305721057/10000000000 : ℝ)|=(5305721057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1972947047/10000000000 : ℝ)|^4289 ≤ (11858858911889/100000000000000 : ℝ)^3265
        have hw : |(-1972947047/10000000000 : ℝ)|=(1972947047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706358349/5000000000 : ℝ)|^4289 ≤ (11162115294369/25000000000000 : ℝ)^3265
        have hw : |(2706358349/5000000000 : ℝ)|=(2706358349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s7_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305721043/10000000000 : ℝ)*x 0 + (84573697/156250000 : ℝ)*x 1 + (-493236797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305721043/10000000000 : ℝ)^4289 ≤ (5436584968219/12500000000000 : ℝ)^3265 := by
    have hnat : (5305721043 : ℕ)^4289*12500000000000^3265 ≤ 5436584968219^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305721043 10000000000 5436584968219 12500000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84573697/156250000 : ℝ)^4289 ≤ (44648460202247/100000000000000 : ℝ)^3265 := by
    have hnat : (84573697 : ℕ)^4289*100000000000000^3265 ≤ 44648460202247^3265*156250000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84573697 156250000 44648460202247 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493236797/2500000000 : ℝ)^4289 ≤ (11858860025207/100000000000000 : ℝ)^3265 := by
    have hnat : (493236797 : ℕ)^4289*100000000000000^3265 ≤ 11858860025207^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493236797 2500000000 11858860025207 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305721043/10000000000 : ℝ), (84573697/156250000 : ℝ), (-493236797/2500000000 : ℝ)] ![(5436584968219/12500000000000 : ℝ), (44648460202247/100000000000000 : ℝ), (11858860025207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305721043/10000000000 : ℝ)|^4289 ≤ (5436584968219/12500000000000 : ℝ)^3265
        have hw : |(5305721043/10000000000 : ℝ)|=(5305721043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84573697/156250000 : ℝ)|^4289 ≤ (44648460202247/100000000000000 : ℝ)^3265
        have hw : |(84573697/156250000 : ℝ)|=(84573697/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-493236797/2500000000 : ℝ)|^4289 ≤ (11858860025207/100000000000000 : ℝ)^3265
        have hw : |(-493236797/2500000000 : ℝ)|=(493236797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_s7_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (866011681/2000000000 : ℝ)*x 0 + (1127086811/2500000000 : ℝ)*x 1 + (166338611/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866011681/2000000000 : ℝ)^4289 ≤ (6660663649583/20000000000000 : ℝ)^3265 := by
    have hnat : (866011681 : ℕ)^4289*20000000000000^3265 ≤ 6660663649583^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866011681 2000000000 6660663649583 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127086811/2500000000 : ℝ)^4289 ≤ (35116160883269/100000000000000 : ℝ)^3265 := by
    have hnat : (1127086811 : ℕ)^4289*100000000000000^3265 ≤ 35116160883269^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127086811 2500000000 35116160883269 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166338611/400000000 : ℝ)^4289 ≤ (31580520856227/100000000000000 : ℝ)^3265 := by
    have hnat : (166338611 : ℕ)^4289*100000000000000^3265 ≤ 31580520856227^3265*400000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166338611 400000000 31580520856227 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866011681/2000000000 : ℝ), (1127086811/2500000000 : ℝ), (166338611/400000000 : ℝ)] ![(6660663649583/20000000000000 : ℝ), (35116160883269/100000000000000 : ℝ), (31580520856227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866011681/2000000000 : ℝ)|^4289 ≤ (6660663649583/20000000000000 : ℝ)^3265
        have hw : |(866011681/2000000000 : ℝ)|=(866011681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127086811/2500000000 : ℝ)|^4289 ≤ (35116160883269/100000000000000 : ℝ)^3265
        have hw : |(1127086811/2500000000 : ℝ)|=(1127086811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166338611/400000000 : ℝ)|^4289 ≤ (31580520856227/100000000000000 : ℝ)^3265
        have hw : |(166338611/400000000 : ℝ)|=(166338611/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1329_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11119/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7349/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11117/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11117/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11117/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11117/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11117/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11117/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11117/100000 : ℝ) ^ (67/16 : ℝ) ≤ (2529374333965761/25000000000000000000 : ℝ) := by
    have hpowers : (11117/100000 : ℝ)^67 ≤ (2529374333965761/25000000000000000000 : ℝ)^16 := by
      have hnat : (11117 : ℕ)^67*25000000000000000000^16 ≤ 2529374333965761^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11117 100000 2529374333965761 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11117/100000 : ℝ)) (X := (2529374333965761/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hpowhi : (14699/100000 : ℝ) ^ (67/16 : ℝ) ≤ (16292496056382549/50000000000000000000 : ℝ) := by
    have hpowers : (14699/100000 : ℝ)^67 ≤ (16292496056382549/50000000000000000000 : ℝ)^16 := by
      have hnat : (14699 : ℕ)^67*50000000000000000000^16 ≤ 16292496056382549^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14699 100000 16292496056382549 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14699/100000 : ℝ)) (X := (16292496056382549/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502529374333965761/12500000000000000000 : ℝ) ≤ (2000096637308577/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (12502529374333965761/12500000000000000000 : ℝ)^16 ≤ (2000096637308577/2000000000000000 : ℝ)^67 := by
      have hnat : (12502529374333965761 : ℕ)^16*2000000000000000^67 ≤ 2000096637308577^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502529374333965761 12500000000000000000 2000096637308577 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000096637308577/2000000000000000 : ℝ)) (X := (12502529374333965761/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021351244724314071/50000000000000000000 : ℝ) ≤ (5000509797623779/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50021351244724314071/50000000000000000000 : ℝ)^16 ≤ (5000509797623779/5000000000000000 : ℝ)^67 := by
      have hnat : (50021351244724314071 : ℕ)^16*5000000000000000^67 ≤ 5000509797623779^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021351244724314071 50000000000000000000 5000509797623779 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000509797623779/5000000000000000 : ℝ)) (X := (50021351244724314071/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016292496056382549/25000000000000000000 : ℝ) ≤ (10001556003952231/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (25016292496056382549/25000000000000000000 : ℝ)^16 ≤ (10001556003952231/10000000000000000 : ℝ)^67 := by
      have hnat : (25016292496056382549 : ℕ)^16*10000000000000000^67 ≤ 10001556003952231^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016292496056382549 25000000000000000000 10001556003952231 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001556003952231/10000000000000000 : ℝ)) (X := (25016292496056382549/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2529374333965761/25000000000000000000 : ℝ) ≤ ((8952451065764228647/8955000000000000000 : ℝ)+2*(536408704673/358200000000000 : ℝ)*(11117/100000 : ℝ))^(67/16 : ℝ) := by
    rw [show (8952451065764228647/8955000000000000000 : ℝ)+2*(536408704673/358200000000000 : ℝ)*(11117/100000 : ℝ)=(2000096637308577/2000000000000000 : ℝ) by norm_num, show 1+2*(2529374333965761/25000000000000000000 : ℝ)=(12502529374333965761/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16292496056382549/50000000000000000000 : ℝ)+(2529374333965761/25000000000000000000 : ℝ) ≤ ((8952451065764228647/8955000000000000000 : ℝ)+(536408704673/358200000000000 : ℝ)*((14699/100000 : ℝ)+(11117/100000 : ℝ)))^(67/16 : ℝ) := by
    rw [show (8952451065764228647/8955000000000000000 : ℝ)+(536408704673/358200000000000 : ℝ)*((14699/100000 : ℝ)+(11117/100000 : ℝ))=(5000509797623779/5000000000000000 : ℝ) by norm_num, show 1+(16292496056382549/50000000000000000000 : ℝ)+(2529374333965761/25000000000000000000 : ℝ)=(50021351244724314071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16292496056382549/50000000000000000000 : ℝ) ≤ ((8952451065764228647/8955000000000000000 : ℝ)+2*(536408704673/358200000000000 : ℝ)*(14699/100000 : ℝ))^(67/16 : ℝ) := by
    rw [show (8952451065764228647/8955000000000000000 : ℝ)+2*(536408704673/358200000000000 : ℝ)*(14699/100000 : ℝ)=(10001556003952231/10000000000000000 : ℝ) by norm_num, show 1+2*(16292496056382549/50000000000000000000 : ℝ)=(25016292496056382549/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8952451065764228647/8955000000000000000 : ℝ)*(X 1 0+X 2 0)+(536408704673/358200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (11117/100000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (8952451065764228647/8955000000000000000 : ℝ)) (alpha := (536408704673/358200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8952451065764228647/8955000000000000000 : ℝ)*(X 0 1+X 2 1)+(536408704673/358200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (11117/100000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (8952451065764228647/8955000000000000000 : ℝ)) (alpha := (536408704673/358200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8952451065764228647/8955000000000000000 : ℝ)*(X 0 2+X 1 2)+(536408704673/358200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (11117/100000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (8952451065764228647/8955000000000000000 : ℝ)) (alpha := (536408704673/358200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2055260033/10000000000 : ℝ)*X 0 0+(676665533/1250000000 : ℝ)*X 0 1+(2622125003/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349204031/10000000000 : ℝ)*X 1 0+(-2141415209/10000000000 : ℝ)*X 1 1+(2622124777/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069840969/2000000000 : ℝ)*X 2 0+(5244249643/10000000000 : ℝ)*X 2 1+(-2141414007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4330032871/10000000000 : ℝ)*X 0 0+(83143993/200000000 : ℝ)*X 0 1+(140925197/312500000 : ℝ)*X 0 2+(4330032871/10000000000 : ℝ)*X 1 0+(83143993/200000000 : ℝ)*X 1 1+(140925197/312500000 : ℝ)*X 1 2+(4330032871/10000000000 : ℝ)*X 2 0+(83143993/200000000 : ℝ)*X 2 1+(140925197/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-411054557/2000000000 : ℝ)*X 0 0+(5244853959/10000000000 : ℝ)*X 0 1+(2706358429/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305721057/10000000000 : ℝ)*X 1 0+(-1972947047/10000000000 : ℝ)*X 1 1+(2706358349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305721043/10000000000 : ℝ)*X 2 0+(84573697/156250000 : ℝ)*X 2 1+(-493236797/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((866011681/2000000000 : ℝ)*X 0 0+(1127086811/2500000000 : ℝ)*X 0 1+(166338611/400000000 : ℝ)*X 0 2+(866011681/2000000000 : ℝ)*X 1 0+(1127086811/2500000000 : ℝ)*X 1 1+(166338611/400000000 : ℝ)*X 1 2+(866011681/2000000000 : ℝ)*X 2 0+(1127086811/2500000000 : ℝ)*X 2 1+(166338611/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (435809724249115727747308657/74625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (393900367/100000000000000 : ℝ)*(base19) + (347748061/25000000000000 : ℝ)*(base23) + (4527523/4000000000000 : ℝ)*(lower2) + (27041519/12500000000000 : ℝ)*(upper5) + (2188064821816723/50000000000000 : ℝ)*(major0) + (2188064821816723/50000000000000 : ℝ)*(major1) + (2188064821816723/50000000000000 : ℝ)*(major2) + (2957287219986363/50000000000000 : ℝ)*(sp0) + (739321162096469/12500000000000 : ℝ)*(sp1) + (1478651567366003/25000000000000 : ℝ)*(sp2) + (354705017393371/12500000000000 : ℝ)*(sp3) + (3322048353/10000000000000 : ℝ)*(sp4) + (37969784137/100000000000000 : ℝ)*(sp5) + (2823249277/25000000000000 : ℝ)*(sp7) + (2837651432144077/100000000000000 : ℝ)*(f.failure) + (5914607660456257/100000000000000 : ℝ)*(f.sum) + (39010239815279/8955000000000000000000000000 : ℝ)*base65 + (1406374207119412927/149250000000000000000000000000000 : ℝ)*base67 + (1781686379005912927/149250000000000000000000000000000 : ℝ)*base69 + (1761494806046662927/149250000000000000000000000000000 : ℝ)*base71 + (1477139973181/559687500000000000000000000 : ℝ)*base74 + (2803521558159412927/149250000000000000000000000000000 : ℝ)*base75 + (1458109402960912927/149250000000000000000000000000000 : ℝ)*base77 + (2098367536405912927/149250000000000000000000000000000 : ℝ)*base79 + (27180612924539/8955000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (38489569/10000000000000000000000 : ℝ)*base90 + (38489569/10000000000000000000000 : ℝ)*base92 + (38489569/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (188270299724157649508029597/37312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (441663149/20000000000000 : ℝ)*(base19) + (64005189/2500000000000 : ℝ)*(base23) + (3570037/500000000000 : ℝ)*(lower1) + (190497121/100000000000000 : ℝ)*(upper2) + (50923611/25000000000000 : ℝ)*(upper3) + (23886979/10000000000000 : ℝ)*(upper5) + (2203820311753649/50000000000000 : ℝ)*(major0) + (2203820311753649/50000000000000 : ℝ)*(major1) + (2203820311753649/50000000000000 : ℝ)*(major2) + (130707649/12500000000000 : ℝ)*(sp2) + (1489299177656331/25000000000000 : ℝ)*(sp4) + (5957194502309579/100000000000000 : ℝ)*(sp5) + (1489298276189143/25000000000000 : ℝ)*(sp6) + (714521092049229/25000000000000 : ℝ)*(sp7) + (714521092049229/25000000000000 : ℝ)*(f.failure) + (1489299177656331/25000000000000 : ℝ)*(f.sum) + (6693560565577/8955000000000000000000000000 : ℝ)*base65 + (1196219367220669301/149250000000000000000000000000000 : ℝ)*base67 + (2671981476424669301/149250000000000000000000000000000 : ℝ)*base69 + (2422677247842919301/149250000000000000000000000000000 : ℝ)*base71 + (1088396753621/279843750000000000000000000 : ℝ)*base73 + (1638677642462830699/149250000000000000000000000000000 : ℝ)*base76 + (1901091059017669301/149250000000000000000000000000000 : ℝ)*base77 + (306772273207669301/149250000000000000000000000000000 : ℝ)*base79 + (48820135557323/8955000000000000000000000000 : ℝ)*base82 + (44850913/2500000000000000000000 : ℝ)*base90 + (44850913/2500000000000000000000 : ℝ)*base92 + (44850913/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1329_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11119/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1329_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1329_box_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1886958049/10000000000 : ℝ)*x 0 + (336905249/625000000 : ℝ)*x 1 + (1347621017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1886958049/10000000000 : ℝ)^4289 ≤ (1118458798891/10000000000000 : ℝ)^3265 := by
    have hnat : (1886958049 : ℕ)^4289*10000000000000^3265 ≤ 1118458798891^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886958049 10000000000 1118458798891 10000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336905249/625000000 : ℝ)^4289 ≤ (1387740798371/3125000000000 : ℝ)^3265 := by
    have hnat : (336905249 : ℕ)^4289*3125000000000^3265 ≤ 1387740798371^3265*625000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336905249 625000000 1387740798371 3125000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347621017/2500000000 : ℝ)^4289 ≤ (2775481653557/6250000000000 : ℝ)^3265 := by
    have hnat : (1347621017 : ℕ)^4289*6250000000000^3265 ≤ 2775481653557^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347621017 2500000000 2775481653557 6250000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1886958049/10000000000 : ℝ), (336905249/625000000 : ℝ), (1347621017/2500000000 : ℝ)] ![(1118458798891/10000000000000 : ℝ), (1387740798371/3125000000000 : ℝ), (2775481653557/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1886958049/10000000000 : ℝ)|^4289 ≤ (1118458798891/10000000000000 : ℝ)^3265
        have hw : |(-1886958049/10000000000 : ℝ)|=(1886958049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336905249/625000000 : ℝ)|^4289 ≤ (1387740798371/3125000000000 : ℝ)^3265
        have hw : |(336905249/625000000 : ℝ)|=(336905249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347621017/2500000000 : ℝ)|^4289 ≤ (2775481653557/6250000000000 : ℝ)^3265
        have hw : |(1347621017/2500000000 : ℝ)|=(1347621017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5284978107/10000000000 : ℝ)*x 0 + (-507859909/2500000000 : ℝ)*x 1 + (84226313/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284978107/10000000000 : ℝ)^4289 ≤ (21634725975817/50000000000000 : ℝ)^3265 := by
    have hnat : (5284978107 : ℕ)^4289*50000000000000^3265 ≤ 21634725975817^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284978107 10000000000 21634725975817 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507859909/2500000000 : ℝ)^4289 ≤ (12322841975713/100000000000000 : ℝ)^3265 := by
    have hnat : (507859909 : ℕ)^4289*100000000000000^3265 ≤ 12322841975713^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507859909 2500000000 12322841975713 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84226313/156250000 : ℝ)^4289 ≤ (44407706067323/100000000000000 : ℝ)^3265 := by
    have hnat : (84226313 : ℕ)^4289*100000000000000^3265 ≤ 44407706067323^3265*156250000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84226313 156250000 44407706067323 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284978107/10000000000 : ℝ), (-507859909/2500000000 : ℝ), (84226313/156250000 : ℝ)] ![(21634725975817/50000000000000 : ℝ), (12322841975713/100000000000000 : ℝ), (44407706067323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284978107/10000000000 : ℝ)|^4289 ≤ (21634725975817/50000000000000 : ℝ)^3265
        have hw : |(5284978107/10000000000 : ℝ)|=(5284978107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507859909/2500000000 : ℝ)|^4289 ≤ (12322841975713/100000000000000 : ℝ)^3265
        have hw : |(-507859909/2500000000 : ℝ)|=(507859909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84226313/156250000 : ℝ)|^4289 ≤ (44407706067323/100000000000000 : ℝ)^3265
        have hw : |(84226313/156250000 : ℝ)|=(84226313/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5284978203/10000000000 : ℝ)*x 0 + (5390483867/10000000000 : ℝ)*x 1 + (-203143973/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284978203/10000000000 : ℝ)^4289 ≤ (10817363246029/25000000000000 : ℝ)^3265 := by
    have hnat : (5284978203 : ℕ)^4289*25000000000000^3265 ≤ 10817363246029^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284978203 10000000000 10817363246029 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390483867/10000000000 : ℝ)^4289 ≤ (4440770428171/10000000000000 : ℝ)^3265 := by
    have hnat : (5390483867 : ℕ)^4289*10000000000000^3265 ≤ 4440770428171^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390483867 10000000000 4440770428171 10000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203143973/1000000000 : ℝ)^4289 ≤ (12322842724757/100000000000000 : ℝ)^3265 := by
    have hnat : (203143973 : ℕ)^4289*100000000000000^3265 ≤ 12322842724757^3265*1000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203143973 1000000000 12322842724757 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284978203/10000000000 : ℝ), (5390483867/10000000000 : ℝ), (-203143973/1000000000 : ℝ)] ![(10817363246029/25000000000000 : ℝ), (4440770428171/10000000000000 : ℝ), (12322842724757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284978203/10000000000 : ℝ)|^4289 ≤ (10817363246029/25000000000000 : ℝ)^3265
        have hw : |(5284978203/10000000000 : ℝ)|=(5284978203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390483867/10000000000 : ℝ)|^4289 ≤ (4440770428171/10000000000000 : ℝ)^3265
        have hw : |(5390483867/10000000000 : ℝ)|=(5390483867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-203143973/1000000000 : ℝ)|^4289 ≤ (12322842724757/100000000000000 : ℝ)^3265
        have hw : |(-203143973/1000000000 : ℝ)|=(203143973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1119633843/2500000000 : ℝ)*x 0 + (266231251/625000000 : ℝ)*x 1 + (266231257/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119633843/2500000000 : ℝ)^4289 ≤ (34811441192211/100000000000000 : ℝ)^3265 := by
    have hnat : (1119633843 : ℕ)^4289*100000000000000^3265 ≤ 34811441192211^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119633843 2500000000 34811441192211 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266231251/625000000 : ℝ)^4289 ≤ (3259427891281/10000000000000 : ℝ)^3265 := by
    have hnat : (266231251 : ℕ)^4289*10000000000000^3265 ≤ 3259427891281^3265*625000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266231251 625000000 3259427891281 10000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266231257/625000000 : ℝ)^4289 ≤ (8148569969441/25000000000000 : ℝ)^3265 := by
    have hnat : (266231257 : ℕ)^4289*25000000000000^3265 ≤ 8148569969441^3265*625000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266231257 625000000 8148569969441 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1119633843/2500000000 : ℝ), (266231251/625000000 : ℝ), (266231257/625000000 : ℝ)] ![(34811441192211/100000000000000 : ℝ), (3259427891281/10000000000000 : ℝ), (8148569969441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1119633843/2500000000 : ℝ)|^4289 ≤ (34811441192211/100000000000000 : ℝ)^3265
        have hw : |(1119633843/2500000000 : ℝ)|=(1119633843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(266231251/625000000 : ℝ)|^4289 ≤ (3259427891281/10000000000000 : ℝ)^3265
        have hw : |(266231251/625000000 : ℝ)|=(266231251/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(266231257/625000000 : ℝ)|^4289 ≤ (8148569969441/25000000000000 : ℝ)^3265
        have hw : |(266231257/625000000 : ℝ)|=(266231257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1113155359/5000000000 : ℝ)*x 0 + (2632314339/5000000000 : ℝ)*x 1 + (5264628531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1113155359/5000000000 : ℝ)^4289 ≤ (13898550007947/100000000000000 : ℝ)^3265 := by
    have hnat : (1113155359 : ℕ)^4289*100000000000000^3265 ≤ 13898550007947^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113155359 5000000000 13898550007947 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632314339/5000000000 : ℝ)^4289 ≤ (43050725780433/100000000000000 : ℝ)^3265 := by
    have hnat : (2632314339 : ℕ)^4289*100000000000000^3265 ≤ 43050725780433^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632314339 5000000000 43050725780433 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264628531/10000000000 : ℝ)^4289 ≤ (43050724201357/100000000000000 : ℝ)^3265 := by
    have hnat : (5264628531 : ℕ)^4289*100000000000000^3265 ≤ 43050724201357^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264628531 10000000000 43050724201357 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1113155359/5000000000 : ℝ), (2632314339/5000000000 : ℝ), (5264628531/10000000000 : ℝ)] ![(13898550007947/100000000000000 : ℝ), (43050725780433/100000000000000 : ℝ), (43050724201357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1113155359/5000000000 : ℝ)|^4289 ≤ (13898550007947/100000000000000 : ℝ)^3265
        have hw : |(-1113155359/5000000000 : ℝ)|=(1113155359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632314339/5000000000 : ℝ)|^4289 ≤ (43050725780433/100000000000000 : ℝ)^3265
        have hw : |(2632314339/5000000000 : ℝ)|=(2632314339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264628531/10000000000 : ℝ)|^4289 ≤ (43050724201357/100000000000000 : ℝ)^3265
        have hw : |(5264628531/10000000000 : ℝ)|=(5264628531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373425283/10000000000 : ℝ)*x 0 + (-260231109/1250000000 : ℝ)*x 1 + (2632314303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373425283/10000000000 : ℝ)^4289 ≤ (22111594852443/50000000000000 : ℝ)^3265 := by
    have hnat : (5373425283 : ℕ)^4289*50000000000000^3265 ≤ 22111594852443^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373425283 10000000000 22111594852443 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260231109/1250000000 : ℝ)^4289 ≤ (6363042637043/50000000000000 : ℝ)^3265 := by
    have hnat : (260231109 : ℕ)^4289*50000000000000^3265 ≤ 6363042637043^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260231109 1250000000 6363042637043 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632314303/5000000000 : ℝ)^4289 ≤ (1345335156469/3125000000000 : ℝ)^3265 := by
    have hnat : (2632314303 : ℕ)^4289*3125000000000^3265 ≤ 1345335156469^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632314303 5000000000 1345335156469 3125000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373425283/10000000000 : ℝ), (-260231109/1250000000 : ℝ), (2632314303/5000000000 : ℝ)] ![(22111594852443/50000000000000 : ℝ), (6363042637043/50000000000000 : ℝ), (1345335156469/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373425283/10000000000 : ℝ)|^4289 ≤ (22111594852443/50000000000000 : ℝ)^3265
        have hw : |(5373425283/10000000000 : ℝ)|=(5373425283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260231109/1250000000 : ℝ)|^4289 ≤ (6363042637043/50000000000000 : ℝ)^3265
        have hw : |(-260231109/1250000000 : ℝ)|=(260231109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632314303/5000000000 : ℝ)|^4289 ≤ (1345335156469/3125000000000 : ℝ)^3265
        have hw : |(2632314303/5000000000 : ℝ)|=(2632314303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268671259/500000000 : ℝ)*x 0 + (1052925721/2000000000 : ℝ)*x 1 + (-2081849013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268671259/500000000 : ℝ)^4289 ≤ (22111594295669/50000000000000 : ℝ)^3265 := by
    have hnat : (268671259 : ℕ)^4289*50000000000000^3265 ≤ 22111594295669^3265*500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268671259 500000000 22111594295669 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052925721/2000000000 : ℝ)^4289 ≤ (21525362498133/50000000000000 : ℝ)^3265 := by
    have hnat : (1052925721 : ℕ)^4289*50000000000000^3265 ≤ 21525362498133^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052925721 2000000000 21525362498133 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081849013/10000000000 : ℝ)^4289 ≤ (3181521601581/25000000000000 : ℝ)^3265 := by
    have hnat : (2081849013 : ℕ)^4289*25000000000000^3265 ≤ 3181521601581^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081849013 10000000000 3181521601581 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268671259/500000000 : ℝ), (1052925721/2000000000 : ℝ), (-2081849013/10000000000 : ℝ)] ![(22111594295669/50000000000000 : ℝ), (21525362498133/50000000000000 : ℝ), (3181521601581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268671259/500000000 : ℝ)|^4289 ≤ (22111594295669/50000000000000 : ℝ)^3265
        have hw : |(268671259/500000000 : ℝ)|=(268671259/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052925721/2000000000 : ℝ)|^4289 ≤ (21525362498133/50000000000000 : ℝ)^3265
        have hw : |(1052925721/2000000000 : ℝ)|=(1052925721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2081849013/10000000000 : ℝ)|^4289 ≤ (3181521601581/25000000000000 : ℝ)^3265
        have hw : |(-2081849013/10000000000 : ℝ)|=(2081849013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (418062377/1000000000 : ℝ)*x 0 + (881720341/2000000000 : ℝ)*x 1 + (551075243/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418062377/1000000000 : ℝ)^4289 ≤ (6360351965449/20000000000000 : ℝ)^3265 := by
    have hnat : (418062377 : ℕ)^4289*20000000000000^3265 ≤ 6360351965449^3265*1000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418062377 1000000000 6360351965449 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881720341/2000000000 : ℝ)^4289 ≤ (34099118863791/100000000000000 : ℝ)^3265 := by
    have hnat : (881720341 : ℕ)^4289*100000000000000^3265 ≤ 34099118863791^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881720341 2000000000 34099118863791 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551075243/1250000000 : ℝ)^4289 ≤ (34099121292151/100000000000000 : ℝ)^3265 := by
    have hnat : (551075243 : ℕ)^4289*100000000000000^3265 ≤ 34099121292151^3265*1250000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551075243 1250000000 34099121292151 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418062377/1000000000 : ℝ), (881720341/2000000000 : ℝ), (551075243/1250000000 : ℝ)] ![(6360351965449/20000000000000 : ℝ), (34099118863791/100000000000000 : ℝ), (34099121292151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418062377/1000000000 : ℝ)|^4289 ≤ (6360351965449/20000000000000 : ℝ)^3265
        have hw : |(418062377/1000000000 : ℝ)|=(418062377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(881720341/2000000000 : ℝ)|^4289 ≤ (34099118863791/100000000000000 : ℝ)^3265
        have hw : |(881720341/2000000000 : ℝ)|=(881720341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551075243/1250000000 : ℝ)|^4289 ≤ (34099121292151/100000000000000 : ℝ)^3265
        have hw : |(551075243/1250000000 : ℝ)|=(551075243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1077541207/5000000000 : ℝ)*x 0 + (5178047723/10000000000 : ℝ)*x 1 + (1351127309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077541207/5000000000 : ℝ)^4289 ≤ (6658686420379/50000000000000 : ℝ)^3265 := by
    have hnat : (1077541207 : ℕ)^4289*50000000000000^3265 ≤ 6658686420379^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077541207 5000000000 6658686420379 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178047723/10000000000 : ℝ)^4289 ≤ (10530769962573/25000000000000 : ℝ)^3265 := by
    have hnat : (5178047723 : ℕ)^4289*25000000000000^3265 ≤ 10530769962573^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178047723 10000000000 10530769962573 25000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351127309/2500000000 : ℝ)^4289 ≤ (44559547284817/100000000000000 : ℝ)^3265 := by
    have hnat : (1351127309 : ℕ)^4289*100000000000000^3265 ≤ 44559547284817^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351127309 2500000000 44559547284817 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1077541207/5000000000 : ℝ), (5178047723/10000000000 : ℝ), (1351127309/2500000000 : ℝ)] ![(6658686420379/50000000000000 : ℝ), (10530769962573/25000000000000 : ℝ), (44559547284817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1077541207/5000000000 : ℝ)|^4289 ≤ (6658686420379/50000000000000 : ℝ)^3265
        have hw : |(-1077541207/5000000000 : ℝ)|=(1077541207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178047723/10000000000 : ℝ)|^4289 ≤ (10530769962573/25000000000000 : ℝ)^3265
        have hw : |(5178047723/10000000000 : ℝ)|=(5178047723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351127309/2500000000 : ℝ)|^4289 ≤ (44559547284817/100000000000000 : ℝ)^3265
        have hw : |(1351127309/2500000000 : ℝ)|=(1351127309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318778941/2500000000 : ℝ)*x 0 + (-405137621/2000000000 : ℝ)*x 1 + (2702255007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318778941/2500000000 : ℝ)^4289 ≤ (1726536533889/4000000000000 : ℝ)^3265 := by
    have hnat : (1318778941 : ℕ)^4289*4000000000000^3265 ≤ 1726536533889^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318778941 2500000000 1726536533889 4000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405137621/2000000000 : ℝ)^4289 ≤ (6138515460237/50000000000000 : ℝ)^3265 := by
    have hnat : (405137621 : ℕ)^4289*50000000000000^3265 ≤ 6138515460237^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405137621 2000000000 6138515460237 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702255007/5000000000 : ℝ)^4289 ≤ (22279777855559/50000000000000 : ℝ)^3265 := by
    have hnat : (2702255007 : ℕ)^4289*50000000000000^3265 ≤ 22279777855559^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702255007 5000000000 22279777855559 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318778941/2500000000 : ℝ), (-405137621/2000000000 : ℝ), (2702255007/5000000000 : ℝ)] ![(1726536533889/4000000000000 : ℝ), (6138515460237/50000000000000 : ℝ), (22279777855559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318778941/2500000000 : ℝ)|^4289 ≤ (1726536533889/4000000000000 : ℝ)^3265
        have hw : |(1318778941/2500000000 : ℝ)|=(1318778941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-405137621/2000000000 : ℝ)|^4289 ≤ (6138515460237/50000000000000 : ℝ)^3265
        have hw : |(-405137621/2000000000 : ℝ)|=(405137621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702255007/5000000000 : ℝ)|^4289 ≤ (22279777855559/50000000000000 : ℝ)^3265
        have hw : |(2702255007/5000000000 : ℝ)|=(2702255007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_10 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275116513/10000000000 : ℝ)*x 0 + (2702254641/5000000000 : ℝ)*x 1 + (-202568809/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275116513/10000000000 : ℝ)^4289 ≤ (8632684279603/20000000000000 : ℝ)^3265 := by
    have hnat : (5275116513 : ℕ)^4289*20000000000000^3265 ≤ 8632684279603^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275116513 10000000000 8632684279603 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702254641/5000000000 : ℝ)^4289 ≤ (4455954778303/10000000000000 : ℝ)^3265 := by
    have hnat : (2702254641 : ℕ)^4289*10000000000000^3265 ≤ 4455954778303^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702254641 5000000000 4455954778303 10000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202568809/1000000000 : ℝ)^4289 ≤ (12277030801051/100000000000000 : ℝ)^3265 := by
    have hnat : (202568809 : ℕ)^4289*100000000000000^3265 ≤ 12277030801051^3265*1000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202568809 1000000000 12277030801051 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275116513/10000000000 : ℝ), (2702254641/5000000000 : ℝ), (-202568809/1000000000 : ℝ)] ![(8632684279603/20000000000000 : ℝ), (4455954778303/10000000000000 : ℝ), (12277030801051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275116513/10000000000 : ℝ)|^4289 ≤ (8632684279603/20000000000000 : ℝ)^3265
        have hw : |(5275116513/10000000000 : ℝ)|=(5275116513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702254641/5000000000 : ℝ)|^4289 ≤ (4455954778303/10000000000000 : ℝ)^3265
        have hw : |(2702254641/5000000000 : ℝ)|=(2702254641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-202568809/1000000000 : ℝ)|^4289 ≤ (12277030801051/100000000000000 : ℝ)^3265
        have hw : |(-202568809/1000000000 : ℝ)|=(202568809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_11 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4511174779/10000000000 : ℝ)*x 0 + (2121546349/5000000000 : ℝ)*x 1 + (4243092989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4511174779/10000000000 : ℝ)^4289 ≤ (35145095199653/100000000000000 : ℝ)^3265 := by
    have hnat : (4511174779 : ℕ)^4289*100000000000000^3265 ≤ 35145095199653^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511174779 10000000000 35145095199653 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121546349/5000000000 : ℝ)^4289 ≤ (40534313667/125000000000 : ℝ)^3265 := by
    have hnat : (2121546349 : ℕ)^4289*125000000000^3265 ≤ 40534313667^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121546349 5000000000 40534313667 125000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243092989/10000000000 : ℝ)^4289 ≤ (6485490771007/20000000000000 : ℝ)^3265 := by
    have hnat : (4243092989 : ℕ)^4289*20000000000000^3265 ≤ 6485490771007^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243092989 10000000000 6485490771007 20000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4511174779/10000000000 : ℝ), (2121546349/5000000000 : ℝ), (4243092989/10000000000 : ℝ)] ![(35145095199653/100000000000000 : ℝ), (40534313667/125000000000 : ℝ), (6485490771007/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4511174779/10000000000 : ℝ)|^4289 ≤ (35145095199653/100000000000000 : ℝ)^3265
        have hw : |(4511174779/10000000000 : ℝ)|=(4511174779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2121546349/5000000000 : ℝ)|^4289 ≤ (40534313667/125000000000 : ℝ)^3265
        have hw : |(2121546349/5000000000 : ℝ)|=(2121546349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243092989/10000000000 : ℝ)|^4289 ≤ (6485490771007/20000000000000 : ℝ)^3265
        have hw : |(4243092989/10000000000 : ℝ)|=(4243092989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_12 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1958549507/10000000000 : ℝ)*x 0 + (68435373/125000000 : ℝ)*x 1 + (2626784997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1958549507/10000000000 : ℝ)^4289 ≤ (11745308026781/100000000000000 : ℝ)^3265 := by
    have hnat : (1958549507 : ℕ)^4289*100000000000000^3265 ≤ 11745308026781^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958549507 10000000000 11745308026781 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68435373/125000000 : ℝ)^4289 ≤ (45322719531233/100000000000000 : ℝ)^3265 := by
    have hnat : (68435373 : ℕ)^4289*100000000000000^3265 ≤ 45322719531233^3265*125000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68435373 125000000 45322719531233 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626784997/5000000000 : ℝ)^4289 ≤ (42931972424179/100000000000000 : ℝ)^3265 := by
    have hnat : (2626784997 : ℕ)^4289*100000000000000^3265 ≤ 42931972424179^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626784997 5000000000 42931972424179 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1958549507/10000000000 : ℝ), (68435373/125000000 : ℝ), (2626784997/5000000000 : ℝ)] ![(11745308026781/100000000000000 : ℝ), (45322719531233/100000000000000 : ℝ), (42931972424179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1958549507/10000000000 : ℝ)|^4289 ≤ (11745308026781/100000000000000 : ℝ)^3265
        have hw : |(-1958549507/10000000000 : ℝ)|=(1958549507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68435373/125000000 : ℝ)|^4289 ≤ (45322719531233/100000000000000 : ℝ)^3265
        have hw : |(68435373/125000000 : ℝ)|=(68435373/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626784997/5000000000 : ℝ)|^4289 ≤ (42931972424179/100000000000000 : ℝ)^3265
        have hw : |(2626784997/5000000000 : ℝ)|=(2626784997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381194277/10000000000 : ℝ)*x 0 + (-2086173643/10000000000 : ℝ)*x 1 + (1050714043/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381194277/10000000000 : ℝ)^4289 ≤ (22153600232881/50000000000000 : ℝ)^3265 := by
    have hnat : (5381194277 : ℕ)^4289*50000000000000^3265 ≤ 22153600232881^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381194277 10000000000 22153600232881 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2086173643/10000000000 : ℝ)^4289 ≤ (12760824728443/100000000000000 : ℝ)^3265 := by
    have hnat : (2086173643 : ℕ)^4289*100000000000000^3265 ≤ 12760824728443^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086173643 10000000000 12760824728443 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050714043/2000000000 : ℝ)^4289 ≤ (42931974796599/100000000000000 : ℝ)^3265 := by
    have hnat : (1050714043 : ℕ)^4289*100000000000000^3265 ≤ 42931974796599^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050714043 2000000000 42931974796599 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381194277/10000000000 : ℝ), (-2086173643/10000000000 : ℝ), (1050714043/2000000000 : ℝ)] ![(22153600232881/50000000000000 : ℝ), (12760824728443/100000000000000 : ℝ), (42931974796599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381194277/10000000000 : ℝ)|^4289 ≤ (22153600232881/50000000000000 : ℝ)^3265
        have hw : |(5381194277/10000000000 : ℝ)|=(5381194277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2086173643/10000000000 : ℝ)|^4289 ≤ (12760824728443/100000000000000 : ℝ)^3265
        have hw : |(-2086173643/10000000000 : ℝ)|=(2086173643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050714043/2000000000 : ℝ)|^4289 ≤ (42931974796599/100000000000000 : ℝ)^3265
        have hw : |(1050714043/2000000000 : ℝ)|=(1050714043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345298557/2500000000 : ℝ)*x 0 + (5253570079/10000000000 : ℝ)*x 1 + (-2086173889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345298557/2500000000 : ℝ)^4289 ≤ (1384599997993/3125000000000 : ℝ)^3265 := by
    have hnat : (1345298557 : ℕ)^4289*3125000000000^3265 ≤ 1384599997993^3265*2500000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345298557 2500000000 1384599997993 3125000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253570079/10000000000 : ℝ)^4289 ≤ (5366496667081/12500000000000 : ℝ)^3265 := by
    have hnat : (5253570079 : ℕ)^4289*12500000000000^3265 ≤ 5366496667081^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253570079 10000000000 5366496667081 12500000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086173889/10000000000 : ℝ)^4289 ≤ (12760826705123/100000000000000 : ℝ)^3265 := by
    have hnat : (2086173889 : ℕ)^4289*100000000000000^3265 ≤ 12760826705123^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086173889 10000000000 12760826705123 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345298557/2500000000 : ℝ), (5253570079/10000000000 : ℝ), (-2086173889/10000000000 : ℝ)] ![(1384599997993/3125000000000 : ℝ), (5366496667081/12500000000000 : ℝ), (12760826705123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345298557/2500000000 : ℝ)|^4289 ≤ (1384599997993/3125000000000 : ℝ)^3265
        have hw : |(1345298557/2500000000 : ℝ)|=(1345298557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253570079/10000000000 : ℝ)|^4289 ≤ (5366496667081/12500000000000 : ℝ)^3265
        have hw : |(5253570079/10000000000 : ℝ)|=(5253570079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2086173889/10000000000 : ℝ)|^4289 ≤ (12760826705123/100000000000000 : ℝ)^3265
        have hw : |(-2086173889/10000000000 : ℝ)|=(2086173889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1329_box_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4153999369/10000000000 : ℝ)*x 0 + (884335001/2000000000 : ℝ)*x 1 + (2210837503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4153999369/10000000000 : ℝ)^4289 ≤ (31535976213027/100000000000000 : ℝ)^3265 := by
    have hnat : (4153999369 : ℕ)^4289*100000000000000^3265 ≤ 31535976213027^3265*10000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153999369 10000000000 31535976213027 100000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884335001/2000000000 : ℝ)^4289 ≤ (2139500742377/6250000000000 : ℝ)^3265 := by
    have hnat : (884335001 : ℕ)^4289*6250000000000^3265 ≤ 2139500742377^3265*2000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884335001 2000000000 2139500742377 6250000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210837503/5000000000 : ℝ)^4289 ≤ (17116005944101/50000000000000 : ℝ)^3265 := by
    have hnat : (2210837503 : ℕ)^4289*50000000000000^3265 ≤ 17116005944101^3265*5000000000^4289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210837503 5000000000 17116005944101 50000000000000 4289 3265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4289/1024 : ℝ)) 4289 3265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4153999369/10000000000 : ℝ), (884335001/2000000000 : ℝ), (2210837503/5000000000 : ℝ)] ![(31535976213027/100000000000000 : ℝ), (2139500742377/6250000000000 : ℝ), (17116005944101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4153999369/10000000000 : ℝ)|^4289 ≤ (31535976213027/100000000000000 : ℝ)^3265
        have hw : |(4153999369/10000000000 : ℝ)|=(4153999369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(884335001/2000000000 : ℝ)|^4289 ≤ (2139500742377/6250000000000 : ℝ)^3265
        have hw : |(884335001/2000000000 : ℝ)|=(884335001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2210837503/5000000000 : ℝ)|^4289 ≤ (17116005944101/50000000000000 : ℝ)^3265
        have hw : |(2210837503/5000000000 : ℝ)|=(2210837503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1329_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11119/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1257/2000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14729/25000 : ℝ) ∧ (39939/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84301/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7349/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11119/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7349/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11119/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7349/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11119/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7349/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11119/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7349/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11119/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7349/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11119/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11119/100000 : ℝ) ^ (67/16 : ℝ) ≤ (10125121545503811/100000000000000000000 : ℝ) := by
    have hpowers : (11119/100000 : ℝ)^67 ≤ (10125121545503811/100000000000000000000 : ℝ)^16 := by
      have hnat : (11119 : ℕ)^67*100000000000000000000^16 ≤ 10125121545503811^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11119 100000 10125121545503811 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11119/100000 : ℝ)) (X := (10125121545503811/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hpowhi : (7349/50000 : ℝ) ^ (67/16 : ℝ) ≤ (4071963774788959/12500000000000000000 : ℝ) := by
    have hpowers : (7349/50000 : ℝ)^67 ≤ (4071963774788959/12500000000000000000 : ℝ)^16 := by
      have hnat : (7349 : ℕ)^67*12500000000000000000^16 ≤ 4071963774788959^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7349 50000 4071963774788959 12500000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7349/50000 : ℝ)) (X := (4071963774788959/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010125121545503811/50000000000000000000 : ℝ) ≤ (5000241775314071/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50010125121545503811/50000000000000000000 : ℝ)^16 ≤ (5000241775314071/5000000000000000 : ℝ)^67 := by
      have hnat : (50010125121545503811 : ℕ)^16*5000000000000000^67 ≤ 5000241775314071^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010125121545503811 50000000000000000000 5000241775314071 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000241775314071/5000000000000000 : ℝ)) (X := (50010125121545503811/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042700831743815483/100000000000000000000 : ℝ) ≤ (62506372222959/62500000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (100042700831743815483/100000000000000000000 : ℝ)^16 ≤ (62506372222959/62500000000000 : ℝ)^67 := by
      have hnat : (100042700831743815483 : ℕ)^16*62500000000000^67 ≤ 62506372222959^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042700831743815483 100000000000000000000 62506372222959 62500000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62506372222959/62500000000000 : ℝ)) (X := (100042700831743815483/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254071963774788959/6250000000000000000 : ℝ) ≤ (5000777780359369/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (6254071963774788959/6250000000000000000 : ℝ)^16 ≤ (5000777780359369/5000000000000000 : ℝ)^67 := by
      have hnat : (6254071963774788959 : ℕ)^16*5000000000000000^67 ≤ 5000777780359369^67*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254071963774788959 6250000000000000000 5000777780359369 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000777780359369/5000000000000000 : ℝ)) (X := (6254071963774788959/6250000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10125121545503811/100000000000000000000 : ℝ) ≤ ((17889905473750391647/17895000000000000000 : ℝ)+2*(268002522649/178950000000000 : ℝ)*(11119/100000 : ℝ))^(67/16 : ℝ) := by
    rw [show (17889905473750391647/17895000000000000000 : ℝ)+2*(268002522649/178950000000000 : ℝ)*(11119/100000 : ℝ)=(5000241775314071/5000000000000000 : ℝ) by norm_num, show 1+2*(10125121545503811/100000000000000000000 : ℝ)=(50010125121545503811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4071963774788959/12500000000000000000 : ℝ)+(10125121545503811/100000000000000000000 : ℝ) ≤ ((17889905473750391647/17895000000000000000 : ℝ)+(268002522649/178950000000000 : ℝ)*((7349/50000 : ℝ)+(11119/100000 : ℝ)))^(67/16 : ℝ) := by
    rw [show (17889905473750391647/17895000000000000000 : ℝ)+(268002522649/178950000000000 : ℝ)*((7349/50000 : ℝ)+(11119/100000 : ℝ))=(62506372222959/62500000000000 : ℝ) by norm_num, show 1+(4071963774788959/12500000000000000000 : ℝ)+(10125121545503811/100000000000000000000 : ℝ)=(100042700831743815483/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4071963774788959/12500000000000000000 : ℝ) ≤ ((17889905473750391647/17895000000000000000 : ℝ)+2*(268002522649/178950000000000 : ℝ)*(7349/50000 : ℝ))^(67/16 : ℝ) := by
    rw [show (17889905473750391647/17895000000000000000 : ℝ)+2*(268002522649/178950000000000 : ℝ)*(7349/50000 : ℝ)=(5000777780359369/5000000000000000 : ℝ) by norm_num, show 1+2*(4071963774788959/12500000000000000000 : ℝ)=(6254071963774788959/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17889905473750391647/17895000000000000000 : ℝ)*(X 1 0+X 2 0)+(268002522649/178950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (11119/100000 : ℝ)) (hi := (7349/50000 : ℝ)) (c := (17889905473750391647/17895000000000000000 : ℝ)) (alpha := (268002522649/178950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17889905473750391647/17895000000000000000 : ℝ)*(X 0 1+X 2 1)+(268002522649/178950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (11119/100000 : ℝ)) (hi := (7349/50000 : ℝ)) (c := (17889905473750391647/17895000000000000000 : ℝ)) (alpha := (268002522649/178950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17889905473750391647/17895000000000000000 : ℝ)*(X 0 2+X 1 2)+(268002522649/178950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (67/16 : ℝ)) (lo := (11119/100000 : ℝ)) (hi := (7349/50000 : ℝ)) (c := (17889905473750391647/17895000000000000000 : ℝ)) (alpha := (268002522649/178950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1886958049/10000000000 : ℝ)*X 0 0+(336905249/625000000 : ℝ)*X 0 1+(1347621017/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284978107/10000000000 : ℝ)*X 1 0+(-507859909/2500000000 : ℝ)*X 1 1+(84226313/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5284978203/10000000000 : ℝ)*X 2 0+(5390483867/10000000000 : ℝ)*X 2 1+(-203143973/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1119633843/2500000000 : ℝ)*X 0 0+(266231251/625000000 : ℝ)*X 0 1+(266231257/625000000 : ℝ)*X 0 2+(1119633843/2500000000 : ℝ)*X 1 0+(266231251/625000000 : ℝ)*X 1 1+(266231257/625000000 : ℝ)*X 1 2+(1119633843/2500000000 : ℝ)*X 2 0+(266231251/625000000 : ℝ)*X 2 1+(266231257/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1113155359/5000000000 : ℝ)*X 0 0+(2632314339/5000000000 : ℝ)*X 0 1+(5264628531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5373425283/10000000000 : ℝ)*X 1 0+(-260231109/1250000000 : ℝ)*X 1 1+(2632314303/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((268671259/500000000 : ℝ)*X 2 0+(1052925721/2000000000 : ℝ)*X 2 1+(-2081849013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((418062377/1000000000 : ℝ)*X 0 0+(881720341/2000000000 : ℝ)*X 0 1+(551075243/1250000000 : ℝ)*X 0 2+(418062377/1000000000 : ℝ)*X 1 0+(881720341/2000000000 : ℝ)*X 1 1+(551075243/1250000000 : ℝ)*X 1 2+(418062377/1000000000 : ℝ)*X 2 0+(881720341/2000000000 : ℝ)*X 2 1+(551075243/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1077541207/5000000000 : ℝ)*X 0 0+(5178047723/10000000000 : ℝ)*X 0 1+(1351127309/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1318778941/2500000000 : ℝ)*X 1 0+(-405137621/2000000000 : ℝ)*X 1 1+(2702255007/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275116513/10000000000 : ℝ)*X 2 0+(2702254641/5000000000 : ℝ)*X 2 1+(-202568809/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4511174779/10000000000 : ℝ)*X 0 0+(2121546349/5000000000 : ℝ)*X 0 1+(4243092989/10000000000 : ℝ)*X 0 2+(4511174779/10000000000 : ℝ)*X 1 0+(2121546349/5000000000 : ℝ)*X 1 1+(4243092989/10000000000 : ℝ)*X 1 2+(4511174779/10000000000 : ℝ)*X 2 0+(2121546349/5000000000 : ℝ)*X 2 1+(4243092989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1958549507/10000000000 : ℝ)*X 0 0+(68435373/125000000 : ℝ)*X 0 1+(2626784997/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5381194277/10000000000 : ℝ)*X 1 0+(-2086173643/10000000000 : ℝ)*X 1 1+(1050714043/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1345298557/2500000000 : ℝ)*X 2 0+(5253570079/10000000000 : ℝ)*X 2 1+(-2086173889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4153999369/10000000000 : ℝ)*X 0 0+(884335001/2000000000 : ℝ)*X 0 1+(2210837503/5000000000 : ℝ)*X 0 2+(4153999369/10000000000 : ℝ)*X 1 0+(884335001/2000000000 : ℝ)*X 1 1+(2210837503/5000000000 : ℝ)*X 1 2+(4153999369/10000000000 : ℝ)*X 2 0+(884335001/2000000000 : ℝ)*X 2 1+(2210837503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1329_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1257/2000 : ℝ) ≤ (-93722012825959625587468343393861/149125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10063831/100000000000000 : ℝ)*(upper0) + (6587377/12500000000000 : ℝ)*(upper2) + (2638629/100000000000000 : ℝ)*(upper3) + (20106543/100000000000000 : ℝ)*(lower4) + (1452981480158363/50000000000000 : ℝ)*(major0) + (1452981480158363/50000000000000 : ℝ)*(major1) + (1452981480158363/50000000000000 : ℝ)*(major2) + (1490639851/100000000000000 : ℝ)*(sp2) + (204775643/50000000000000 : ℝ)*(sp3) + (493567081297223/12500000000000 : ℝ)*(sp4) + (197425612838921/5000000000000 : ℝ)*(sp5) + (987133789934483/25000000000000 : ℝ)*(sp6) + (471084544755639/25000000000000 : ℝ)*(sp7) + (6098399841/25000000000000 : ℝ)*(sp13) + (942169294286921/50000000000000 : ℝ)*(f.failure) + (493567081297223/12500000000000 : ℝ)*(f.sum) + (8624833851913/4473750000000000000000000000 : ℝ)*base66 + (1407300592558093861/894750000000000000000000000000000 : ℝ)*base67 + (633158969758906139/894750000000000000000000000000000 : ℝ)*base70 + (935073567508906139/894750000000000000000000000000000 : ℝ)*base72 + (14540105126233/4473750000000000000000000000 : ℝ)*base74 + (159705421840093861/894750000000000000000000000000000 : ℝ)*base75 + (4501729119822343861/894750000000000000000000000000000 : ℝ)*base77 + (2970393835464343861/894750000000000000000000000000000 : ℝ)*base79 + (9420181783549/8947500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (36050637/5000000000000000000000 : ℝ)*base90 + (36050637/5000000000000000000000 : ℝ)*base92 + (36050637/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14729/25000 : ℝ) ≤ (2745691050682362917521465848559/4660156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (4055593/50000000000000 : ℝ)*(upper0) + (16540191/100000000000000 : ℝ)*(upper2) + (58697/1250000000000 : ℝ)*(upper5) + (23236087652687/781250000000 : ℝ)*(major0) + (23236087652687/781250000000 : ℝ)*(major1) + (23236087652687/781250000000 : ℝ)*(major2) + (4000198156876253/100000000000000 : ℝ)*(sp0) + (800039821174261/20000000000000 : ℝ)*(sp1) + (2000078041163477/50000000000000 : ℝ)*(sp2) + (482149198660877/25000000000000 : ℝ)*(sp3) + (636444593/50000000000000 : ℝ)*(sp5) + (1787925411/100000000000000 : ℝ)*(sp7) + (44296433537/100000000000000 : ℝ)*(sp10) + (1110942119/50000000000000 : ℝ)*(sp12) + (1928598582568919/100000000000000 : ℝ)*(f.failure) + (1000050094690123/25000000000000 : ℝ)*(f.sum) + (6059973174143/17895000000000000000000000000 : ℝ)*base65 + (3161234336756318669/55921875000000000000000000000000 : ℝ)*base68 + (23223302305013261/13980468750000000000000000000000 : ℝ)*base70 + (224283335711881169/55921875000000000000000000000000 : ℝ)*base72 + (1176113706820417/17895000000000000000000000000 : ℝ)*base74 + (1760766115983193/6990234375000000000000000000000 : ℝ)*base76 + (48178130145162419/55921875000000000000000000000000 : ℝ)*base78 + (425220123423818669/55921875000000000000000000000000 : ℝ)*base80 + (779964019211/8947500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (101562157/10000000000000000000000 : ℝ)*base89 + (101562157/10000000000000000000000 : ℝ)*base91 + (101562157/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39939/50000 : ℝ) ≤ (119121648166263597588596431431841/149125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (354559133/100000000000000 : ℝ)*(lower3) + (42605971/50000000000000 : ℝ)*(upper4) + (71370567/50000000000000 : ℝ)*(lower5) + (1643441889307703/50000000000000 : ℝ)*(major0) + (1643441889307703/50000000000000 : ℝ)*(major1) + (1643441889307703/50000000000000 : ℝ)*(major2) + (28827716641/100000000000000 : ℝ)*(sp0) + (526551086283/100000000000000 : ℝ)*(sp1) + (138805510999/50000000000000 : ℝ)*(sp2) + (86792480721/50000000000000 : ℝ)*(sp3) + (4415769573860157/100000000000000 : ℝ)*(sp8) + (2207635925245257/50000000000000 : ℝ)*(sp9) + (11038801976387/250000000000 : ℝ)*(sp10) + (1065584385160057/50000000000000 : ℝ)*(sp11) + (532835588820389/25000000000000 : ℝ)*(f.failure) + (2207899200788399/50000000000000 : ℝ)*(f.sum) + (29217378523403/17895000000000000000000000000 : ℝ)*base65 + (2574083704911593159/894750000000000000000000000000000 : ℝ)*base68 + (1511645915108843159/894750000000000000000000000000000 : ℝ)*base70 + (6370965299255406841/894750000000000000000000000000000 : ℝ)*base71 + (4754781895009/8947500000000000000000000000 : ℝ)*base73 + (5930119920804156841/894750000000000000000000000000000 : ℝ)*base75 + (463182637705343159/894750000000000000000000000000000 : ℝ)*base78 + (3697629879353843159/894750000000000000000000000000000 : ℝ)*base80 + (26289732050269/8947500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (18718567/2500000000000000000000 : ℝ)*base89 + (18718567/2500000000000000000000 : ℝ)*base91 + (18718567/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84301/100000 : ℝ) ≤ (-12571053445683728174142459192327/14912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27477819/50000000000000 : ℝ)*(lower0) + (15097127/100000000000000 : ℝ)*(lower1) + (12700631/50000000000000 : ℝ)*(upper3) + (10424923/10000000000000 : ℝ)*(lower4) + (166159049288853/5000000000000 : ℝ)*(major0) + (166159049288853/5000000000000 : ℝ)*(major1) + (166159049288853/5000000000000 : ℝ)*(major2) + (26419992143/25000000000000 : ℝ)*(sp6) + (25198747289/50000000000000 : ℝ)*(sp7) + (245895241/6250000000000 : ℝ)*(sp8) + (4519578759907053/100000000000000 : ℝ)*(sp12) + (4519582694230909/100000000000000 : ℝ)*(sp13) + (4519477014262337/100000000000000 : ℝ)*(sp14) + (107741423420957/5000000000000 : ℝ)*(sp15) + (1077439432956859/50000000000000 : ℝ)*(f.failure) + (4519582694230909/100000000000000 : ℝ)*(f.sum) + (601885537153/1193000000000000000000000000 : ℝ)*base66 + (266843032154979703/29825000000000000000000000000000 : ℝ)*base68 + (706310934689879703/29825000000000000000000000000000 : ℝ)*base70 + (175636897144854703/29825000000000000000000000000000 : ℝ)*base72 + (5561487411913/1193000000000000000000000000 : ℝ)*base73 + (1446504018895904703/29825000000000000000000000000000 : ℝ)*base76 + (160972720184329703/29825000000000000000000000000000 : ℝ)*base78 + (149803029731854703/29825000000000000000000000000000 : ℝ)*base80 + (18831326358907/1193000000000000000000000000 : ℝ)*base82 + (40529977/5000000000000000000000 : ℝ)*base89 + (40529977/5000000000000000000000 : ℝ)*base91 + (40529977/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1329_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11119/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1257/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(14729/25000 : ℝ) else (39939/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84301/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1329_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1329_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1257/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(14729/25000 : ℝ) else (39939/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84301/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1329_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1329_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1329_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (4289/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154216603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1257/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(14729/25000 : ℝ) else (39939/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84301/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1329_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
