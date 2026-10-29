-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1409_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:41.286437+00:00
-- url     : https://prove2.me/submissions/bb105cb0-4bf9-47a2-9f9d-9644aa2de211

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
theorem support_rectangle_w1409_s6_0 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-993736301/5000000000 : ℝ)*x 0 + (1352313971/2500000000 : ℝ)*x 1 + (1311609261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (993736301/5000000000 : ℝ)^4369 ≤ (12119678490693/100000000000000 : ℝ)^3345 := by
    have hnat : (993736301 : ℕ)^4369*100000000000000^3345 ≤ 12119678490693^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993736301 5000000000 12119678490693 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352313971/2500000000 : ℝ)^4369 ≤ (44817053866833/100000000000000 : ℝ)^3345 := by
    have hnat : (1352313971 : ℕ)^4369*100000000000000^3345 ≤ 44817053866833^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352313971 2500000000 44817053866833 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311609261/2500000000 : ℝ)^4369 ≤ (21531633814753/50000000000000 : ℝ)^3345 := by
    have hnat : (1311609261 : ℕ)^4369*50000000000000^3345 ≤ 21531633814753^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311609261 2500000000 21531633814753 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-993736301/5000000000 : ℝ), (1352313971/2500000000 : ℝ), (1311609261/2500000000 : ℝ)] ![(12119678490693/100000000000000 : ℝ), (44817053866833/100000000000000 : ℝ), (21531633814753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-993736301/5000000000 : ℝ)|^4369 ≤ (12119678490693/100000000000000 : ℝ)^3345
        have hw : |(-993736301/5000000000 : ℝ)|=(993736301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352313971/2500000000 : ℝ)|^4369 ≤ (44817053866833/100000000000000 : ℝ)^3345
        have hw : |(1352313971/2500000000 : ℝ)|=(1352313971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311609261/2500000000 : ℝ)|^4369 ≤ (21531633814753/50000000000000 : ℝ)^3345
        have hw : |(1311609261/2500000000 : ℝ)|=(1311609261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s6_1 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673870801/5000000000 : ℝ)*x 0 + (-1035190157/5000000000 : ℝ)*x 1 + (1311609267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673870801/5000000000 : ℝ)^4369 ≤ (2207626617831/5000000000000 : ℝ)^3345 := by
    have hnat : (2673870801 : ℕ)^4369*5000000000000^3345 ≤ 2207626617831^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673870801 5000000000 2207626617831 5000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035190157/5000000000 : ℝ)^4369 ≤ (799012483703/6250000000000 : ℝ)^3345 := by
    have hnat : (1035190157 : ℕ)^4369*6250000000000^3345 ≤ 799012483703^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035190157 5000000000 799012483703 6250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311609267/2500000000 : ℝ)^4369 ≤ (21531633943403/50000000000000 : ℝ)^3345 := by
    have hnat : (1311609267 : ℕ)^4369*50000000000000^3345 ≤ 21531633943403^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311609267 2500000000 21531633943403 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673870801/5000000000 : ℝ), (-1035190157/5000000000 : ℝ), (1311609267/2500000000 : ℝ)] ![(2207626617831/5000000000000 : ℝ), (799012483703/6250000000000 : ℝ), (21531633943403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673870801/5000000000 : ℝ)|^4369 ≤ (2207626617831/5000000000000 : ℝ)^3345
        have hw : |(2673870801/5000000000 : ℝ)|=(2673870801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035190157/5000000000 : ℝ)|^4369 ≤ (799012483703/6250000000000 : ℝ)^3345
        have hw : |(-1035190157/5000000000 : ℝ)|=(1035190157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311609267/2500000000 : ℝ)|^4369 ≤ (21531633943403/50000000000000 : ℝ)^3345
        have hw : |(1311609267/2500000000 : ℝ)|=(1311609267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s6_2 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334233847/625000000 : ℝ)*x 0 + (524643709/1000000000 : ℝ)*x 1 + (-32349693/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334233847/625000000 : ℝ)^4369 ≤ (44152531817431/100000000000000 : ℝ)^3345 := by
    have hnat : (334233847 : ℕ)^4369*100000000000000^3345 ≤ 44152531817431^3345*625000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334233847 625000000 44152531817431 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524643709/1000000000 : ℝ)^4369 ≤ (5382908515333/12500000000000 : ℝ)^3345 := by
    have hnat : (524643709 : ℕ)^4369*12500000000000^3345 ≤ 5382908515333^3345*1000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524643709 1000000000 5382908515333 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32349693/156250000 : ℝ)^4369 ≤ (6392100022861/50000000000000 : ℝ)^3345 := by
    have hnat : (32349693 : ℕ)^4369*50000000000000^3345 ≤ 6392100022861^3345*156250000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32349693 156250000 6392100022861 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334233847/625000000 : ℝ), (524643709/1000000000 : ℝ), (-32349693/156250000 : ℝ)] ![(44152531817431/100000000000000 : ℝ), (5382908515333/12500000000000 : ℝ), (6392100022861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334233847/625000000 : ℝ)|^4369 ≤ (44152531817431/100000000000000 : ℝ)^3345
        have hw : |(334233847/625000000 : ℝ)|=(334233847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524643709/1000000000 : ℝ)|^4369 ≤ (5382908515333/12500000000000 : ℝ)^3345
        have hw : |(524643709/1000000000 : ℝ)|=(524643709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32349693/156250000 : ℝ)|^4369 ≤ (6392100022861/50000000000000 : ℝ)^3345
        have hw : |(-32349693/156250000 : ℝ)|=(32349693/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s6_3 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4309399399/10000000000 : ℝ)*x 0 + (4137791157/10000000000 : ℝ)*x 1 + (4487443221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309399399/10000000000 : ℝ)^4369 ≤ (16652187022283/50000000000000 : ℝ)^3345 := by
    have hnat : (4309399399 : ℕ)^4369*50000000000000^3345 ≤ 16652187022283^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309399399 10000000000 16652187022283 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4137791157/10000000000 : ℝ)^4369 ≤ (3158278939099/10000000000000 : ℝ)^3345 := by
    have hnat : (4137791157 : ℕ)^4369*10000000000000^3345 ≤ 3158278939099^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137791157 10000000000 3158278939099 10000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487443221/10000000000 : ℝ)^4369 ≤ (17556418270877/50000000000000 : ℝ)^3345 := by
    have hnat : (4487443221 : ℕ)^4369*50000000000000^3345 ≤ 17556418270877^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487443221 10000000000 17556418270877 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309399399/10000000000 : ℝ), (4137791157/10000000000 : ℝ), (4487443221/10000000000 : ℝ)] ![(16652187022283/50000000000000 : ℝ), (3158278939099/10000000000000 : ℝ), (17556418270877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309399399/10000000000 : ℝ)|^4369 ≤ (16652187022283/50000000000000 : ℝ)^3345
        have hw : |(4309399399/10000000000 : ℝ)|=(4309399399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4137791157/10000000000 : ℝ)|^4369 ≤ (3158278939099/10000000000000 : ℝ)^3345
        have hw : |(4137791157/10000000000 : ℝ)|=(4137791157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487443221/10000000000 : ℝ)|^4369 ≤ (17556418270877/50000000000000 : ℝ)^3345
        have hw : |(4487443221/10000000000 : ℝ)|=(4487443221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s6_4 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-24843553/125000000 : ℝ)*x 0 + (1311755781/2500000000 : ℝ)*x 1 + (1352166669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24843553/125000000 : ℝ)^4369 ≤ (12119771185331/100000000000000 : ℝ)^3345 := by
    have hnat : (24843553 : ℕ)^4369*100000000000000^3345 ≤ 12119771185331^3345*125000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24843553 125000000 12119771185331 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311755781/2500000000 : ℝ)^4369 ≤ (21534775500697/50000000000000 : ℝ)^3345 := by
    have hnat : (1311755781 : ℕ)^4369*50000000000000^3345 ≤ 21534775500697^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311755781 2500000000 21534775500697 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352166669/2500000000 : ℝ)^4369 ≤ (44810677796571/100000000000000 : ℝ)^3345 := by
    have hnat : (1352166669 : ℕ)^4369*100000000000000^3345 ≤ 44810677796571^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352166669 2500000000 44810677796571 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24843553/125000000 : ℝ), (1311755781/2500000000 : ℝ), (1352166669/2500000000 : ℝ)] ![(12119771185331/100000000000000 : ℝ), (21534775500697/50000000000000 : ℝ), (44810677796571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24843553/125000000 : ℝ)|^4369 ≤ (12119771185331/100000000000000 : ℝ)^3345
        have hw : |(-24843553/125000000 : ℝ)|=(24843553/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311755781/2500000000 : ℝ)|^4369 ≤ (21534775500697/50000000000000 : ℝ)^3345
        have hw : |(1311755781/2500000000 : ℝ)|=(1311755781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352166669/2500000000 : ℝ)|^4369 ≤ (44810677796571/100000000000000 : ℝ)^3345
        have hw : |(1352166669/2500000000 : ℝ)|=(1352166669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s6_5 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305497559/10000000000 : ℝ)*x 0 + (-119259421/625000000 : ℝ)*x 1 + (338041659/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305497559/10000000000 : ℝ)^4369 ≤ (43697533603357/100000000000000 : ℝ)^3345 := by
    have hnat : (5305497559 : ℕ)^4369*100000000000000^3345 ≤ 43697533603357^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305497559 10000000000 43697533603357 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119259421/625000000 : ℝ)^4369 ≤ (718236875981/6250000000000 : ℝ)^3345 := by
    have hnat : (119259421 : ℕ)^4369*6250000000000^3345 ≤ 718236875981^3345*625000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119259421 625000000 718236875981 6250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338041659/625000000 : ℝ)^4369 ≤ (44810676368167/100000000000000 : ℝ)^3345 := by
    have hnat : (338041659 : ℕ)^4369*100000000000000^3345 ≤ 44810676368167^3345*625000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338041659 625000000 44810676368167 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305497559/10000000000 : ℝ), (-119259421/625000000 : ℝ), (338041659/625000000 : ℝ)] ![(43697533603357/100000000000000 : ℝ), (718236875981/6250000000000 : ℝ), (44810676368167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305497559/10000000000 : ℝ)|^4369 ≤ (43697533603357/100000000000000 : ℝ)^3345
        have hw : |(5305497559/10000000000 : ℝ)|=(5305497559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-119259421/625000000 : ℝ)|^4369 ≤ (718236875981/6250000000000 : ℝ)^3345
        have hw : |(-119259421/625000000 : ℝ)|=(119259421/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338041659/625000000 : ℝ)|^4369 ≤ (44810676368167/100000000000000 : ℝ)^3345
        have hw : |(338041659/625000000 : ℝ)|=(338041659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s6_6 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326374419/2500000000 : ℝ)*x 0 + (540866639/1000000000 : ℝ)*x 1 + (-477037697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326374419/2500000000 : ℝ)^4369 ≤ (21848767431/50000000000 : ℝ)^3345 := by
    have hnat : (1326374419 : ℕ)^4369*50000000000^3345 ≤ 21848767431^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326374419 2500000000 21848767431 50000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540866639/1000000000 : ℝ)^4369 ≤ (8962134940339/20000000000000 : ℝ)^3345 := by
    have hnat : (540866639 : ℕ)^4369*20000000000000^3345 ≤ 8962134940339^3345*1000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540866639 1000000000 8962134940339 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477037697/2500000000 : ℝ)^4369 ≤ (5745895212367/50000000000000 : ℝ)^3345 := by
    have hnat : (477037697 : ℕ)^4369*50000000000000^3345 ≤ 5745895212367^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477037697 2500000000 5745895212367 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326374419/2500000000 : ℝ), (540866639/1000000000 : ℝ), (-477037697/2500000000 : ℝ)] ![(21848767431/50000000000 : ℝ), (8962134940339/20000000000000 : ℝ), (5745895212367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326374419/2500000000 : ℝ)|^4369 ≤ (21848767431/50000000000 : ℝ)^3345
        have hw : |(1326374419/2500000000 : ℝ)|=(1326374419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540866639/1000000000 : ℝ)|^4369 ≤ (8962134940339/20000000000000 : ℝ)^3345
        have hw : |(540866639/1000000000 : ℝ)|=(540866639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-477037697/2500000000 : ℝ)|^4369 ≤ (5745895212367/50000000000000 : ℝ)^3345
        have hw : |(-477037697/2500000000 : ℝ)|=(477037697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s6_7 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4309424343/10000000000 : ℝ)*x 0 + (4486184129/10000000000 : ℝ)*x 1 + (4139056537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309424343/10000000000 : ℝ)^4369 ≤ (33304625833671/100000000000000 : ℝ)^3345 := by
    have hnat : (4309424343 : ℕ)^4369*100000000000000^3345 ≤ 33304625833671^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309424343 10000000000 33304625833671 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486184129/10000000000 : ℝ)^4369 ≤ (4387496139459/12500000000000 : ℝ)^3345 := by
    have hnat : (4486184129 : ℕ)^4369*12500000000000^3345 ≤ 4387496139459^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486184129 10000000000 4387496139459 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4139056537/10000000000 : ℝ)^4369 ≤ (31595405026487/100000000000000 : ℝ)^3345 := by
    have hnat : (4139056537 : ℕ)^4369*100000000000000^3345 ≤ 31595405026487^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139056537 10000000000 31595405026487 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309424343/10000000000 : ℝ), (4486184129/10000000000 : ℝ), (4139056537/10000000000 : ℝ)] ![(33304625833671/100000000000000 : ℝ), (4387496139459/12500000000000 : ℝ), (31595405026487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309424343/10000000000 : ℝ)|^4369 ≤ (33304625833671/100000000000000 : ℝ)^3345
        have hw : |(4309424343/10000000000 : ℝ)|=(4309424343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486184129/10000000000 : ℝ)|^4369 ≤ (4387496139459/12500000000000 : ℝ)^3345
        have hw : |(4486184129/10000000000 : ℝ)|=(4486184129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4139056537/10000000000 : ℝ)|^4369 ≤ (31595405026487/100000000000000 : ℝ)^3345
        have hw : |(4139056537/10000000000 : ℝ)|=(4139056537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1409_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5649/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14747/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5647/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5647/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5647/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5647/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5647/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5647/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5647/50000 : ℝ) ^ (273/64 : ℝ) ≤ (1823197941102189/20000000000000000000 : ℝ) := by
    have hpowers : (5647/50000 : ℝ)^273 ≤ (1823197941102189/20000000000000000000 : ℝ)^64 := by
      have hnat : (5647 : ℕ)^273*20000000000000000000^64 ≤ 1823197941102189^64*50000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5647 50000 1823197941102189 20000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5647/50000 : ℝ)) (X := (1823197941102189/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14751/100000 : ℝ) ^ (273/64 : ℝ) ≤ (14238821887267851/50000000000000000000 : ℝ) := by
    have hpowers : (14751/100000 : ℝ)^273 ≤ (14238821887267851/50000000000000000000 : ℝ)^64 := by
      have hnat : (14751 : ℕ)^273*50000000000000000000^64 ≤ 14238821887267851^64*100000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14751 100000 14238821887267851 50000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14751/100000 : ℝ)) (X := (14238821887267851/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001823197941102189/10000000000000000000 : ℝ) ≤ (10000427386541351/10000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (10001823197941102189/10000000000000000000 : ℝ)^64 ≤ (10000427386541351/10000000000000000 : ℝ)^273 := by
      have hnat : (10001823197941102189 : ℕ)^64*10000000000000000^273 ≤ 10000427386541351^273*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001823197941102189 10000000000000000000 10000427386541351 10000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000427386541351/10000000000000000 : ℝ)) (X := (10001823197941102189/10000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037593633480046647/100000000000000000000 : ℝ) ≤ (5000440594577157/5000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (100037593633480046647/100000000000000000000 : ℝ)^64 ≤ (5000440594577157/5000000000000000 : ℝ)^273 := by
      have hnat : (100037593633480046647 : ℕ)^64*5000000000000000^273 ≤ 5000440594577157^273*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037593633480046647 100000000000000000000 5000440594577157 5000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000440594577157/5000000000000000 : ℝ)) (X := (100037593633480046647/100000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014238821887267851/25000000000000000000 : ℝ) ≤ (10001334991767277/10000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (25014238821887267851/25000000000000000000 : ℝ)^64 ≤ (10001334991767277/10000000000000000 : ℝ)^273 := by
      have hnat : (25014238821887267851 : ℕ)^64*10000000000000000^273 ≤ 10001334991767277^273*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014238821887267851 25000000000000000000 10001334991767277 10000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001334991767277/10000000000000000 : ℝ)) (X := (25014238821887267851/25000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1823197941102189/20000000000000000000 : ℝ) ≤ ((34561226981851842163/34570000000000000000 : ℝ)+2*(453802612963/345700000000000 : ℝ)*(5647/50000 : ℝ))^(273/64 : ℝ) := by
    rw [show (34561226981851842163/34570000000000000000 : ℝ)+2*(453802612963/345700000000000 : ℝ)*(5647/50000 : ℝ)=(10000427386541351/10000000000000000 : ℝ) by norm_num, show 1+2*(1823197941102189/20000000000000000000 : ℝ)=(10001823197941102189/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14238821887267851/50000000000000000000 : ℝ)+(1823197941102189/20000000000000000000 : ℝ) ≤ ((34561226981851842163/34570000000000000000 : ℝ)+(453802612963/345700000000000 : ℝ)*((14751/100000 : ℝ)+(5647/50000 : ℝ)))^(273/64 : ℝ) := by
    rw [show (34561226981851842163/34570000000000000000 : ℝ)+(453802612963/345700000000000 : ℝ)*((14751/100000 : ℝ)+(5647/50000 : ℝ))=(5000440594577157/5000000000000000 : ℝ) by norm_num, show 1+(14238821887267851/50000000000000000000 : ℝ)+(1823197941102189/20000000000000000000 : ℝ)=(100037593633480046647/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14238821887267851/50000000000000000000 : ℝ) ≤ ((34561226981851842163/34570000000000000000 : ℝ)+2*(453802612963/345700000000000 : ℝ)*(14751/100000 : ℝ))^(273/64 : ℝ) := by
    rw [show (34561226981851842163/34570000000000000000 : ℝ)+2*(453802612963/345700000000000 : ℝ)*(14751/100000 : ℝ)=(10001334991767277/10000000000000000 : ℝ) by norm_num, show 1+2*(14238821887267851/50000000000000000000 : ℝ)=(25014238821887267851/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34561226981851842163/34570000000000000000 : ℝ)*(X 1 0+X 2 0)+(453802612963/345700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (34561226981851842163/34570000000000000000 : ℝ)) (alpha := (453802612963/345700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34561226981851842163/34570000000000000000 : ℝ)*(X 0 1+X 2 1)+(453802612963/345700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (34561226981851842163/34570000000000000000 : ℝ)) (alpha := (453802612963/345700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34561226981851842163/34570000000000000000 : ℝ)*(X 0 2+X 1 2)+(453802612963/345700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (34561226981851842163/34570000000000000000 : ℝ)) (alpha := (453802612963/345700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-993736301/5000000000 : ℝ)*X 0 0+(1352313971/2500000000 : ℝ)*X 0 1+(1311609261/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673870801/5000000000 : ℝ)*X 1 0+(-1035190157/5000000000 : ℝ)*X 1 1+(1311609267/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334233847/625000000 : ℝ)*X 2 0+(524643709/1000000000 : ℝ)*X 2 1+(-32349693/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4309399399/10000000000 : ℝ)*X 0 0+(4137791157/10000000000 : ℝ)*X 0 1+(4487443221/10000000000 : ℝ)*X 0 2+(4309399399/10000000000 : ℝ)*X 1 0+(4137791157/10000000000 : ℝ)*X 1 1+(4487443221/10000000000 : ℝ)*X 1 2+(4309399399/10000000000 : ℝ)*X 2 0+(4137791157/10000000000 : ℝ)*X 2 1+(4487443221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-24843553/125000000 : ℝ)*X 0 0+(1311755781/2500000000 : ℝ)*X 0 1+(1352166669/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305497559/10000000000 : ℝ)*X 1 0+(-119259421/625000000 : ℝ)*X 1 1+(338041659/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326374419/2500000000 : ℝ)*X 2 0+(540866639/1000000000 : ℝ)*X 2 1+(-477037697/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309424343/10000000000 : ℝ)*X 0 0+(4486184129/10000000000 : ℝ)*X 0 1+(4139056537/10000000000 : ℝ)*X 0 2+(4309424343/10000000000 : ℝ)*X 1 0+(4486184129/10000000000 : ℝ)*X 1 1+(4139056537/10000000000 : ℝ)*X 1 2+(4309424343/10000000000 : ℝ)*X 2 0+(4486184129/10000000000 : ℝ)*X 2 1+(4139056537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16337978592720929532815766291/1728500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (332640717/20000000000000 : ℝ)*(base19) + (75612351/5000000000000 : ℝ)*(base23) + (50018331/100000000000000 : ℝ)*(lower2) + (236044571/100000000000000 : ℝ)*(upper3) + (22061447/20000000000000 : ℝ)*(upper5) + (225047231028351/5000000000000 : ℝ)*(major0) + (225047231028351/5000000000000 : ℝ)*(major1) + (4500944620567021/100000000000000 : ℝ)*(major2) + (6141834369092449/100000000000000 : ℝ)*(sp0) + (3070933899375361/50000000000000 : ℝ)*(sp1) + (767733493713411/12500000000000 : ℝ)*(sp2) + (178750102439531/6250000000000 : ℝ)*(sp3) + (35092861859/100000000000000 : ℝ)*(sp4) + (17825076769/100000000000000 : ℝ)*(sp7) + (1430009732054633/50000000000000 : ℝ)*(f.failure) + (6141869461954307/100000000000000 : ℝ)*(f.sum) + (34137916200073/34570000000000000000000000000 : ℝ)*base65 + (765641514992971787/172850000000000000000000000000000 : ℝ)*base68 + (30304461493368106423/3457000000000000000000000000000000 : ℝ)*base69 + (1528119130651471787/172850000000000000000000000000000 : ℝ)*base72 + (15723267055433/34570000000000000000000000000 : ℝ)*base73 + (41873064278576106423/3457000000000000000000000000000000 : ℝ)*base75 + (1635462679002486787/172850000000000000000000000000000 : ℝ)*base78 + (1010361084808586787/172850000000000000000000000000000 : ℝ)*base80 + (20377819387851/3457000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (5468259/1000000000000000000000 : ℝ)*base89 + (5468259/1000000000000000000000 : ℝ)*base91 + (4531741/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4005186782313895177779895473/432125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2214331541/100000000000000 : ℝ)*(base19) + (296652181/12500000000000 : ℝ)*(base23) + (345466967/50000000000000 : ℝ)*(lower1) + (156459479/100000000000000 : ℝ)*(upper3) + (271341/781250000000 : ℝ)*(lower4) + (164532043/50000000000000 : ℝ)*(upper5) + (2266794611164543/50000000000000 : ℝ)*(major0) + (2266794611164543/50000000000000 : ℝ)*(major1) + (2266794611164543/50000000000000 : ℝ)*(major2) + (2700475711/50000000000000 : ℝ)*(sp1) + (3093207713360067/50000000000000 : ℝ)*(sp4) + (6186407811437171/100000000000000 : ℝ)*(sp5) + (1237282610700537/20000000000000 : ℝ)*(sp6) + (720190677246309/25000000000000 : ℝ)*(sp7) + (720190677246309/25000000000000 : ℝ)*(f.failure) + (3093207713360067/50000000000000 : ℝ)*(f.sum) + (16769231856881/8642500000000000000000000000 : ℝ)*base66 + (3902027038361073491/1728500000000000000000000000000000 : ℝ)*base68 + (6643647815142926509/1728500000000000000000000000000000 : ℝ)*base69 + (6125994448590426509/1728500000000000000000000000000000 : ℝ)*base71 + (49331521132991/8642500000000000000000000000 : ℝ)*base74 + (4137732234566926509/1728500000000000000000000000000000 : ℝ)*base75 + (30161761084520926509/1728500000000000000000000000000000 : ℝ)*base77 + (7229722915619926509/1728500000000000000000000000000000 : ℝ)*base79 + (64554566449251/8642500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2190793/500000000000000000000 : ℝ)*base90 + (2190793/500000000000000000000 : ℝ)*base92 + (2190793/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1409_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1409_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1409_s7_0 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-993737729/5000000000 : ℝ)*x 0 + (2704613069/5000000000 : ℝ)*x 1 + (1311616237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (993737729/5000000000 : ℝ)^4369 ≤ (12119701238219/100000000000000 : ℝ)^3345 := by
    have hnat : (993737729 : ℕ)^4369*100000000000000^3345 ≤ 12119701238219^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993737729 5000000000 12119701238219 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704613069/5000000000 : ℝ)^4369 ≤ (358533855741/800000000000 : ℝ)^3345 := by
    have hnat : (2704613069 : ℕ)^4369*800000000000^3345 ≤ 358533855741^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704613069 5000000000 358533855741 800000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311616237/2500000000 : ℝ)^4369 ≤ (43063566783809/100000000000000 : ℝ)^3345 := by
    have hnat : (1311616237 : ℕ)^4369*100000000000000^3345 ≤ 43063566783809^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311616237 2500000000 43063566783809 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-993737729/5000000000 : ℝ), (2704613069/5000000000 : ℝ), (1311616237/2500000000 : ℝ)] ![(12119701238219/100000000000000 : ℝ), (358533855741/800000000000 : ℝ), (43063566783809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-993737729/5000000000 : ℝ)|^4369 ≤ (12119701238219/100000000000000 : ℝ)^3345
        have hw : |(-993737729/5000000000 : ℝ)|=(993737729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704613069/5000000000 : ℝ)|^4369 ≤ (358533855741/800000000000 : ℝ)^3345
        have hw : |(2704613069/5000000000 : ℝ)|=(2704613069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311616237/2500000000 : ℝ)|^4369 ≤ (43063566783809/100000000000000 : ℝ)^3345
        have hw : |(1311616237/2500000000 : ℝ)|=(1311616237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s7_1 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069546813/2000000000 : ℝ)*x 0 + (-2070353321/10000000000 : ℝ)*x 1 + (1311616239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069546813/2000000000 : ℝ)^4369 ≤ (11038112769817/25000000000000 : ℝ)^3345 := by
    have hnat : (1069546813 : ℕ)^4369*25000000000000^3345 ≤ 11038112769817^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069546813 2000000000 11038112769817 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070353321/10000000000 : ℝ)^4369 ≤ (12783982038647/100000000000000 : ℝ)^3345 := by
    have hnat : (2070353321 : ℕ)^4369*100000000000000^3345 ≤ 12783982038647^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070353321 10000000000 12783982038647 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311616239/2500000000 : ℝ)^4369 ≤ (5382945858697/12500000000000 : ℝ)^3345 := by
    have hnat : (1311616239 : ℕ)^4369*12500000000000^3345 ≤ 5382945858697^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311616239 2500000000 5382945858697 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069546813/2000000000 : ℝ), (-2070353321/10000000000 : ℝ), (1311616239/2500000000 : ℝ)] ![(11038112769817/25000000000000 : ℝ), (12783982038647/100000000000000 : ℝ), (5382945858697/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069546813/2000000000 : ℝ)|^4369 ≤ (11038112769817/25000000000000 : ℝ)^3345
        have hw : |(1069546813/2000000000 : ℝ)|=(1069546813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2070353321/10000000000 : ℝ)|^4369 ≤ (12783982038647/100000000000000 : ℝ)^3345
        have hw : |(-2070353321/10000000000 : ℝ)|=(2070353321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311616239/2500000000 : ℝ)|^4369 ≤ (5382945858697/12500000000000 : ℝ)^3345
        have hw : |(1311616239/2500000000 : ℝ)|=(1311616239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s7_2 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347734071/10000000000 : ℝ)*x 0 + (5246464947/10000000000 : ℝ)*x 1 + (-82814133/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347734071/10000000000 : ℝ)^4369 ≤ (44152451143971/100000000000000 : ℝ)^3345 := by
    have hnat : (5347734071 : ℕ)^4369*100000000000000^3345 ≤ 44152451143971^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347734071 10000000000 44152451143971 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246464947/10000000000 : ℝ)^4369 ≤ (1345736461659/3125000000000 : ℝ)^3345 := by
    have hnat : (5246464947 : ℕ)^4369*3125000000000^3345 ≤ 1345736461659^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246464947 10000000000 1345736461659 3125000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82814133/400000000 : ℝ)^4369 ≤ (12783982070907/100000000000000 : ℝ)^3345 := by
    have hnat : (82814133 : ℕ)^4369*100000000000000^3345 ≤ 12783982070907^3345*400000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82814133 400000000 12783982070907 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347734071/10000000000 : ℝ), (5246464947/10000000000 : ℝ), (-82814133/400000000 : ℝ)] ![(44152451143971/100000000000000 : ℝ), (1345736461659/3125000000000 : ℝ), (12783982070907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347734071/10000000000 : ℝ)|^4369 ≤ (44152451143971/100000000000000 : ℝ)^3345
        have hw : |(5347734071/10000000000 : ℝ)|=(5347734071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246464947/10000000000 : ℝ)|^4369 ≤ (1345736461659/3125000000000 : ℝ)^3345
        have hw : |(5246464947/10000000000 : ℝ)|=(5246464947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82814133/400000000 : ℝ)|^4369 ≤ (12783982070907/100000000000000 : ℝ)^3345
        have hw : |(-82814133/400000000 : ℝ)|=(82814133/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s7_3 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2154700759/5000000000 : ℝ)*x 0 + (827570541/2000000000 : ℝ)*x 1 + (448738109/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154700759/5000000000 : ℝ)^4369 ≤ (16652197717053/50000000000000 : ℝ)^3345 := by
    have hnat : (2154700759 : ℕ)^4369*50000000000000^3345 ≤ 16652197717053^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154700759 5000000000 16652197717053 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (827570541/2000000000 : ℝ)^4369 ≤ (7895850746837/25000000000000 : ℝ)^3345 := by
    have hnat : (827570541 : ℕ)^4369*25000000000000^3345 ≤ 7895850746837^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827570541 2000000000 7895850746837 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448738109/1000000000 : ℝ)^4369 ≤ (2194512597587/6250000000000 : ℝ)^3345 := by
    have hnat : (448738109 : ℕ)^4369*6250000000000^3345 ≤ 2194512597587^3345*1000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448738109 1000000000 2194512597587 6250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154700759/5000000000 : ℝ), (827570541/2000000000 : ℝ), (448738109/1000000000 : ℝ)] ![(16652197717053/50000000000000 : ℝ), (7895850746837/25000000000000 : ℝ), (2194512597587/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154700759/5000000000 : ℝ)|^4369 ≤ (16652197717053/50000000000000 : ℝ)^3345
        have hw : |(2154700759/5000000000 : ℝ)|=(2154700759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(827570541/2000000000 : ℝ)|^4369 ≤ (7895850746837/25000000000000 : ℝ)^3345
        have hw : |(827570541/2000000000 : ℝ)|=(827570541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448738109/1000000000 : ℝ)|^4369 ≤ (2194512597587/6250000000000 : ℝ)^3345
        have hw : |(448738109/1000000000 : ℝ)|=(448738109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s7_4 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1987486957/10000000000 : ℝ)*x 0 + (5247050769/10000000000 : ℝ)*x 1 + (5408637287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1987486957/10000000000 : ℝ)^4369 ≤ (6059896412893/50000000000000 : ℝ)^3345 := by
    have hnat : (1987486957 : ℕ)^4369*50000000000000^3345 ≤ 6059896412893^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987486957 10000000000 6059896412893 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247050769/10000000000 : ℝ)^4369 ≤ (43069847389133/100000000000000 : ℝ)^3345 := by
    have hnat : (5247050769 : ℕ)^4369*100000000000000^3345 ≤ 43069847389133^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247050769 10000000000 43069847389133 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408637287/10000000000 : ℝ)^4369 ≤ (1792414390851/4000000000000 : ℝ)^3345 := by
    have hnat : (5408637287 : ℕ)^4369*4000000000000^3345 ≤ 1792414390851^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408637287 10000000000 1792414390851 4000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1987486957/10000000000 : ℝ), (5247050769/10000000000 : ℝ), (5408637287/10000000000 : ℝ)] ![(6059896412893/50000000000000 : ℝ), (43069847389133/100000000000000 : ℝ), (1792414390851/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1987486957/10000000000 : ℝ)|^4369 ≤ (6059896412893/50000000000000 : ℝ)^3345
        have hw : |(-1987486957/10000000000 : ℝ)|=(1987486957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247050769/10000000000 : ℝ)|^4369 ≤ (43069847389133/100000000000000 : ℝ)^3345
        have hw : |(5247050769/10000000000 : ℝ)|=(5247050769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408637287/10000000000 : ℝ)|^4369 ≤ (1792414390851/4000000000000 : ℝ)^3345
        have hw : |(5408637287/10000000000 : ℝ)|=(5408637287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s7_5 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165797027/312500000 : ℝ)*x 0 + (-1863458/9765625 : ℝ)*x 1 + (676079661/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165797027/312500000 : ℝ)^4369 ≤ (43697612187883/100000000000000 : ℝ)^3345 := by
    have hnat : (165797027 : ℕ)^4369*100000000000000^3345 ≤ 43697612187883^3345*312500000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165797027 312500000 43697612187883 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1863458/9765625 : ℝ)^4369 ≤ (2873007003449/25000000000000 : ℝ)^3345 := by
    have hnat : (1863458 : ℕ)^4369*25000000000000^3345 ≤ 2873007003449^3345*9765625^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863458 9765625 2873007003449 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676079661/1250000000 : ℝ)^4369 ≤ (2800647486381/6250000000000 : ℝ)^3345 := by
    have hnat : (676079661 : ℕ)^4369*6250000000000^3345 ≤ 2800647486381^3345*1250000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676079661 1250000000 2800647486381 6250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165797027/312500000 : ℝ), (-1863458/9765625 : ℝ), (676079661/1250000000 : ℝ)] ![(43697612187883/100000000000000 : ℝ), (2873007003449/25000000000000 : ℝ), (2800647486381/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165797027/312500000 : ℝ)|^4369 ≤ (43697612187883/100000000000000 : ℝ)^3345
        have hw : |(165797027/312500000 : ℝ)|=(165797027/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1863458/9765625 : ℝ)|^4369 ≤ (2873007003449/25000000000000 : ℝ)^3345
        have hw : |(-1863458/9765625 : ℝ)|=(1863458/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676079661/1250000000 : ℝ)|^4369 ≤ (2800647486381/6250000000000 : ℝ)^3345
        have hw : |(676079661/1250000000 : ℝ)|=(676079661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s7_6 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305504863/10000000000 : ℝ)*x 0 + (5408637293/10000000000 : ℝ)*x 1 + (-954090493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305504863/10000000000 : ℝ)^4369 ≤ (349580897417/800000000000 : ℝ)^3345 := by
    have hnat : (5305504863 : ℕ)^4369*800000000000^3345 ≤ 349580897417^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305504863 10000000000 349580897417 800000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408637293/10000000000 : ℝ)^4369 ≤ (44810359836203/100000000000000 : ℝ)^3345 := by
    have hnat : (5408637293 : ℕ)^4369*100000000000000^3345 ≤ 44810359836203^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408637293 10000000000 44810359836203 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (954090493/5000000000 : ℝ)^4369 ≤ (11492027966599/100000000000000 : ℝ)^3345 := by
    have hnat : (954090493 : ℕ)^4369*100000000000000^3345 ≤ 11492027966599^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954090493 5000000000 11492027966599 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305504863/10000000000 : ℝ), (5408637293/10000000000 : ℝ), (-954090493/5000000000 : ℝ)] ![(349580897417/800000000000 : ℝ), (44810359836203/100000000000000 : ℝ), (11492027966599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305504863/10000000000 : ℝ)|^4369 ≤ (349580897417/800000000000 : ℝ)^3345
        have hw : |(5305504863/10000000000 : ℝ)|=(5305504863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408637293/10000000000 : ℝ)|^4369 ≤ (44810359836203/100000000000000 : ℝ)^3345
        have hw : |(5408637293/10000000000 : ℝ)|=(5408637293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-954090493/5000000000 : ℝ)|^4369 ≤ (11492027966599/100000000000000 : ℝ)^3345
        have hw : |(-954090493/5000000000 : ℝ)|=(954090493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_s7_7 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (430942621/1000000000 : ℝ)*x 0 + (1121530763/2500000000 : ℝ)*x 1 + (64673707/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430942621/1000000000 : ℝ)^4369 ≤ (16652322339757/50000000000000 : ℝ)^3345 := by
    have hnat : (430942621 : ℕ)^4369*50000000000000^3345 ≤ 16652322339757^3345*1000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430942621 1000000000 16652322339757 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121530763/2500000000 : ℝ)^4369 ≤ (7019868992163/20000000000000 : ℝ)^3345 := by
    have hnat : (1121530763 : ℕ)^4369*20000000000000^3345 ≤ 7019868992163^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121530763 2500000000 7019868992163 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64673707/156250000 : ℝ)^4369 ≤ (31596010335099/100000000000000 : ℝ)^3345 := by
    have hnat : (64673707 : ℕ)^4369*100000000000000^3345 ≤ 31596010335099^3345*156250000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64673707 156250000 31596010335099 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430942621/1000000000 : ℝ), (1121530763/2500000000 : ℝ), (64673707/156250000 : ℝ)] ![(16652322339757/50000000000000 : ℝ), (7019868992163/20000000000000 : ℝ), (31596010335099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430942621/1000000000 : ℝ)|^4369 ≤ (16652322339757/50000000000000 : ℝ)^3345
        have hw : |(430942621/1000000000 : ℝ)|=(430942621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121530763/2500000000 : ℝ)|^4369 ≤ (7019868992163/20000000000000 : ℝ)^3345
        have hw : |(1121530763/2500000000 : ℝ)|=(1121530763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64673707/156250000 : ℝ)|^4369 ≤ (31596010335099/100000000000000 : ℝ)^3345
        have hw : |(64673707/156250000 : ℝ)|=(64673707/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1409_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11299/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7373/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5649/50000 : ℝ) ^ (273/64 : ℝ) ≤ (9129769725622281/100000000000000000000 : ℝ) := by
    have hpowers : (5649/50000 : ℝ)^273 ≤ (9129769725622281/100000000000000000000 : ℝ)^64 := by
      have hnat : (5649 : ℕ)^273*100000000000000000000^64 ≤ 9129769725622281^64*50000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5649 50000 9129769725622281 100000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5649/50000 : ℝ)) (X := (9129769725622281/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14747/100000 : ℝ) ^ (273/64 : ℝ) ≤ (28444718230453249/100000000000000000000 : ℝ) := by
    have hpowers : (14747/100000 : ℝ)^273 ≤ (28444718230453249/100000000000000000000 : ℝ)^64 := by
      have hnat : (14747 : ℕ)^273*100000000000000000000^64 ≤ 28444718230453249^64*100000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14747 100000 28444718230453249 100000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14747/100000 : ℝ)) (X := (28444718230453249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009129769725622281/50000000000000000000 : ℝ) ≤ (5000214016273649/5000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (50009129769725622281/50000000000000000000 : ℝ)^64 ≤ (5000214016273649/5000000000000000 : ℝ)^273 := by
      have hnat : (50009129769725622281 : ℕ)^64*5000000000000000^273 ≤ 5000214016273649^273*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009129769725622281 50000000000000000000 5000214016273649 5000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000214016273649/5000000000000000 : ℝ)) (X := (50009129769725622281/50000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003757448795607553/10000000000000000000 : ℝ) ≤ (5000440370225309/5000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (10003757448795607553/10000000000000000000 : ℝ)^64 ≤ (5000440370225309/5000000000000000 : ℝ)^273 := by
      have hnat : (10003757448795607553 : ℕ)^64*5000000000000000^273 ≤ 5000440370225309^273*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003757448795607553 10000000000000000000 5000440370225309 5000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000440370225309/5000000000000000 : ℝ)) (X := (10003757448795607553/10000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028444718230453249/50000000000000000000 : ℝ) ≤ (5000666724176969/5000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (50028444718230453249/50000000000000000000 : ℝ)^64 ≤ (5000666724176969/5000000000000000 : ℝ)^273 := by
      have hnat : (50028444718230453249 : ℕ)^64*5000000000000000^273 ≤ 5000666724176969^273*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028444718230453249 50000000000000000000 5000666724176969 5000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000666724176969/5000000000000000 : ℝ)) (X := (50028444718230453249/50000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9129769725622281/100000000000000000000 : ℝ) ≤ ((17240623448236106041/17245000000000000000 : ℝ)+2*(11317697583/8622500000000 : ℝ)*(5649/50000 : ℝ))^(273/64 : ℝ) := by
    rw [show (17240623448236106041/17245000000000000000 : ℝ)+2*(11317697583/8622500000000 : ℝ)*(5649/50000 : ℝ)=(5000214016273649/5000000000000000 : ℝ) by norm_num, show 1+2*(9129769725622281/100000000000000000000 : ℝ)=(50009129769725622281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28444718230453249/100000000000000000000 : ℝ)+(9129769725622281/100000000000000000000 : ℝ) ≤ ((17240623448236106041/17245000000000000000 : ℝ)+(11317697583/8622500000000 : ℝ)*((14747/100000 : ℝ)+(5649/50000 : ℝ)))^(273/64 : ℝ) := by
    rw [show (17240623448236106041/17245000000000000000 : ℝ)+(11317697583/8622500000000 : ℝ)*((14747/100000 : ℝ)+(5649/50000 : ℝ))=(5000440370225309/5000000000000000 : ℝ) by norm_num, show 1+(28444718230453249/100000000000000000000 : ℝ)+(9129769725622281/100000000000000000000 : ℝ)=(10003757448795607553/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28444718230453249/100000000000000000000 : ℝ) ≤ ((17240623448236106041/17245000000000000000 : ℝ)+2*(11317697583/8622500000000 : ℝ)*(14747/100000 : ℝ))^(273/64 : ℝ) := by
    rw [show (17240623448236106041/17245000000000000000 : ℝ)+2*(11317697583/8622500000000 : ℝ)*(14747/100000 : ℝ)=(5000666724176969/5000000000000000 : ℝ) by norm_num, show 1+2*(28444718230453249/100000000000000000000 : ℝ)=(50028444718230453249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17240623448236106041/17245000000000000000 : ℝ)*(X 1 0+X 2 0)+(11317697583/8622500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (17240623448236106041/17245000000000000000 : ℝ)) (alpha := (11317697583/8622500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17240623448236106041/17245000000000000000 : ℝ)*(X 0 1+X 2 1)+(11317697583/8622500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (17240623448236106041/17245000000000000000 : ℝ)) (alpha := (11317697583/8622500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17240623448236106041/17245000000000000000 : ℝ)*(X 0 2+X 1 2)+(11317697583/8622500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (17240623448236106041/17245000000000000000 : ℝ)) (alpha := (11317697583/8622500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-993737729/5000000000 : ℝ)*X 0 0+(2704613069/5000000000 : ℝ)*X 0 1+(1311616237/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069546813/2000000000 : ℝ)*X 1 0+(-2070353321/10000000000 : ℝ)*X 1 1+(1311616239/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347734071/10000000000 : ℝ)*X 2 0+(5246464947/10000000000 : ℝ)*X 2 1+(-82814133/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154700759/5000000000 : ℝ)*X 0 0+(827570541/2000000000 : ℝ)*X 0 1+(448738109/1000000000 : ℝ)*X 0 2+(2154700759/5000000000 : ℝ)*X 1 0+(827570541/2000000000 : ℝ)*X 1 1+(448738109/1000000000 : ℝ)*X 1 2+(2154700759/5000000000 : ℝ)*X 2 0+(827570541/2000000000 : ℝ)*X 2 1+(448738109/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1987486957/10000000000 : ℝ)*X 0 0+(5247050769/10000000000 : ℝ)*X 0 1+(5408637287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165797027/312500000 : ℝ)*X 1 0+(-1863458/9765625 : ℝ)*X 1 1+(676079661/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305504863/10000000000 : ℝ)*X 2 0+(5408637293/10000000000 : ℝ)*X 2 1+(-954090493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((430942621/1000000000 : ℝ)*X 0 0+(1121530763/2500000000 : ℝ)*X 0 1+(64673707/156250000 : ℝ)*X 0 2+(430942621/1000000000 : ℝ)*X 1 0+(1121530763/2500000000 : ℝ)*X 1 1+(64673707/156250000 : ℝ)*X 1 2+(430942621/1000000000 : ℝ)*X 2 0+(1121530763/2500000000 : ℝ)*X 2 1+(64673707/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (181361214224388601317563343/34490000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (480116877/50000000000000 : ℝ)*(base19) + (449188571/50000000000000 : ℝ)*(base23) + (36765679/100000000000000 : ℝ)*(lower2) + (33457289/25000000000000 : ℝ)*(upper3) + (15964173/20000000000000 : ℝ)*(upper5) + (2251257400225881/50000000000000 : ℝ)*(major0) + (2251257400225881/50000000000000 : ℝ)*(major1) + (4502514800451763/100000000000000 : ℝ)*(major2) + (47999937740593/781250000000 : ℝ)*(sp0) + (3072005633690447/50000000000000 : ℝ)*(sp1) + (6144011329237507/100000000000000 : ℝ)*(sp2) + (1430503496513517/50000000000000 : ℝ)*(sp3) + (4039363749/20000000000000 : ℝ)*(sp4) + (10204982799/100000000000000 : ℝ)*(sp7) + (1430508599004917/50000000000000 : ℝ)*(f.failure) + (768001528451831/12500000000000 : ℝ)*(f.sum) + (5338240497891/689800000000000000000000000 : ℝ)*base65 + (8867588848046102879/862250000000000000000000000000000 : ℝ)*base68 + (26014282294500099717/1724500000000000000000000000000000 : ℝ)*base70 + (3641440153624352879/862250000000000000000000000000000 : ℝ)*base72 + (5456429601011/862250000000000000000000000 : ℝ)*base73 + (19822349256396599717/1724500000000000000000000000000000 : ℝ)*base76 + (1123204470476897121/862250000000000000000000000000000 : ℝ)*base77 + (4177198249361102879/862250000000000000000000000000000 : ℝ)*base80 + (896823303151/689800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (19196391/1000000000000000000000 : ℝ)*base89 + (19196391/1000000000000000000000 : ℝ)*base91 + (9196391/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23754902568709096551117/3449000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288813481/25000000000000 : ℝ)*(base19) + (1259383917/100000000000000 : ℝ)*(base23) + (391228953/100000000000000 : ℝ)*(lower1) + (69904443/50000000000000 : ℝ)*(upper3) + (9398053/20000000000000 : ℝ)*(lower4) + (140998849/100000000000000 : ℝ)*(upper5) + (4535197368333983/100000000000000 : ℝ)*(major0) + (4535197368333983/100000000000000 : ℝ)*(major1) + (4535197368333983/100000000000000 : ℝ)*(major2) + (210158441/10000000000000 : ℝ)*(sp2) + (247544397580839/4000000000000 : ℝ)*(sp4) + (6188608784267051/100000000000000 : ℝ)*(sp5) + (6188606578552649/100000000000000 : ℝ)*(sp6) + (144089228378223/5000000000000 : ℝ)*(sp7) + (144089228378223/5000000000000 : ℝ)*(f.failure) + (247544397580839/4000000000000 : ℝ)*(f.sum) + (6866618683013/3449000000000000000000000000 : ℝ)*base66 + (31021069947642391303/1724500000000000000000000000000000 : ℝ)*base67 + (3701718945002608697/1724500000000000000000000000000000 : ℝ)*base70 + (186294668886601891303/1724500000000000000000000000000000 : ℝ)*base71 + (88409499011/86225000000000000000000000 : ℝ)*base73 + (20058261482246108697/1724500000000000000000000000000000 : ℝ)*base76 + (988471146743391303/1724500000000000000000000000000000 : ℝ)*base77 + (31417273234231608697/1724500000000000000000000000000000 : ℝ)*base80 + (4610656586143/862250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (801829/100000000000000000000 : ℝ)*base89 + (801829/100000000000000000000 : ℝ)*base91 + (801829/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1409_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1409_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1409_box_0 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-912676463/5000000000 : ℝ)*x 0 + (134677797/250000000 : ℝ)*x 1 + (5387111609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (912676463/5000000000 : ℝ)^4369 ≤ (5422430967023/50000000000000 : ℝ)^3345 := by
    have hnat : (912676463 : ℕ)^4369*50000000000000^3345 ≤ 5422430967023^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912676463 5000000000 5422430967023 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134677797/250000000 : ℝ)^4369 ≤ (22288785243739/50000000000000 : ℝ)^3345 := by
    have hnat : (134677797 : ℕ)^4369*50000000000000^3345 ≤ 22288785243739^3345*250000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134677797 250000000 22288785243739 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387111609/10000000000 : ℝ)^4369 ≤ (44577567558503/100000000000000 : ℝ)^3345 := by
    have hnat : (5387111609 : ℕ)^4369*100000000000000^3345 ≤ 44577567558503^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387111609 10000000000 44577567558503 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-912676463/5000000000 : ℝ), (134677797/250000000 : ℝ), (5387111609/10000000000 : ℝ)] ![(5422430967023/50000000000000 : ℝ), (22288785243739/50000000000000 : ℝ), (44577567558503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-912676463/5000000000 : ℝ)|^4369 ≤ (5422430967023/50000000000000 : ℝ)^3345
        have hw : |(-912676463/5000000000 : ℝ)|=(912676463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134677797/250000000 : ℝ)|^4369 ≤ (22288785243739/50000000000000 : ℝ)^3345
        have hw : |(134677797/250000000 : ℝ)|=(134677797/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387111609/10000000000 : ℝ)|^4369 ≤ (44577567558503/100000000000000 : ℝ)^3345
        have hw : |(5387111609/10000000000 : ℝ)|=(5387111609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_1 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330369249/625000000 : ℝ)*x 0 + (-1964309301/10000000000 : ℝ)*x 1 + (1077422323/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330369249/625000000 : ℝ)^4369 ≤ (5435864418167/12500000000000 : ℝ)^3345 := by
    have hnat : (330369249 : ℕ)^4369*12500000000000^3345 ≤ 5435864418167^3345*625000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330369249 625000000 5435864418167 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1964309301/10000000000 : ℝ)^4369 ≤ (11935517015589/100000000000000 : ℝ)^3345 := by
    have hnat : (1964309301 : ℕ)^4369*100000000000000^3345 ≤ 11935517015589^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964309301 10000000000 11935517015589 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077422323/2000000000 : ℝ)^4369 ≤ (44577567623351/100000000000000 : ℝ)^3345 := by
    have hnat : (1077422323 : ℕ)^4369*100000000000000^3345 ≤ 44577567623351^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077422323 2000000000 44577567623351 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330369249/625000000 : ℝ), (-1964309301/10000000000 : ℝ), (1077422323/2000000000 : ℝ)] ![(5435864418167/12500000000000 : ℝ), (11935517015589/100000000000000 : ℝ), (44577567623351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330369249/625000000 : ℝ)|^4369 ≤ (5435864418167/12500000000000 : ℝ)^3345
        have hw : |(330369249/625000000 : ℝ)|=(330369249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1964309301/10000000000 : ℝ)|^4369 ≤ (11935517015589/100000000000000 : ℝ)^3345
        have hw : |(-1964309301/10000000000 : ℝ)|=(1964309301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077422323/2000000000 : ℝ)|^4369 ≤ (44577567623351/100000000000000 : ℝ)^3345
        have hw : |(1077422323/2000000000 : ℝ)|=(1077422323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_2 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642953671/5000000000 : ℝ)*x 0 + (5387111921/10000000000 : ℝ)*x 1 + (-982154877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642953671/5000000000 : ℝ)^4369 ≤ (1358965888961/3125000000000 : ℝ)^3345 := by
    have hnat : (2642953671 : ℕ)^4369*3125000000000^3345 ≤ 1358965888961^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642953671 5000000000 1358965888961 3125000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387111921/10000000000 : ℝ)^4369 ≤ (44577570930607/100000000000000 : ℝ)^3345 := by
    have hnat : (5387111921 : ℕ)^4369*100000000000000^3345 ≤ 44577570930607^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387111921 10000000000 44577570930607 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982154877/5000000000 : ℝ)^4369 ≤ (5967760305363/50000000000000 : ℝ)^3345 := by
    have hnat : (982154877 : ℕ)^4369*50000000000000^3345 ≤ 5967760305363^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982154877 5000000000 5967760305363 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642953671/5000000000 : ℝ), (5387111921/10000000000 : ℝ), (-982154877/5000000000 : ℝ)] ![(1358965888961/3125000000000 : ℝ), (44577570930607/100000000000000 : ℝ), (5967760305363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642953671/5000000000 : ℝ)|^4369 ≤ (1358965888961/3125000000000 : ℝ)^3345
        have hw : |(2642953671/5000000000 : ℝ)|=(2642953671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387111921/10000000000 : ℝ)|^4369 ≤ (44577570930607/100000000000000 : ℝ)^3345
        have hw : |(5387111921/10000000000 : ℝ)|=(5387111921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-982154877/5000000000 : ℝ)|^4369 ≤ (5967760305363/50000000000000 : ℝ)^3345
        have hw : |(-982154877/5000000000 : ℝ)|=(982154877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_3 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4456108503/10000000000 : ℝ)*x 0 + (2119898069/5000000000 : ℝ)*x 1 + (4239796297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4456108503/10000000000 : ℝ)^4369 ≤ (17396468550077/50000000000000 : ℝ)^3345 := by
    have hnat : (4456108503 : ℕ)^4369*50000000000000^3345 ≤ 17396468550077^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4456108503 10000000000 17396468550077 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119898069/5000000000 : ℝ)^4369 ≤ (6520706128123/20000000000000 : ℝ)^3345 := by
    have hnat : (2119898069 : ℕ)^4369*20000000000000^3345 ≤ 6520706128123^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119898069 5000000000 6520706128123 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239796297/10000000000 : ℝ)^4369 ≤ (32603532237607/100000000000000 : ℝ)^3345 := by
    have hnat : (4239796297 : ℕ)^4369*100000000000000^3345 ≤ 32603532237607^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239796297 10000000000 32603532237607 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4456108503/10000000000 : ℝ), (2119898069/5000000000 : ℝ), (4239796297/10000000000 : ℝ)] ![(17396468550077/50000000000000 : ℝ), (6520706128123/20000000000000 : ℝ), (32603532237607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4456108503/10000000000 : ℝ)|^4369 ≤ (17396468550077/50000000000000 : ℝ)^3345
        have hw : |(4456108503/10000000000 : ℝ)|=(4456108503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119898069/5000000000 : ℝ)|^4369 ≤ (6520706128123/20000000000000 : ℝ)^3345
        have hw : |(2119898069/5000000000 : ℝ)|=(2119898069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239796297/10000000000 : ℝ)|^4369 ≤ (32603532237607/100000000000000 : ℝ)^3345
        have hw : |(4239796297/10000000000 : ℝ)|=(4239796297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_4 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076168549/5000000000 : ℝ)*x 0 + (164569211/312500000 : ℝ)*x 1 + (1053242869/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076168549/5000000000 : ℝ)^4369 ≤ (13449157700857/100000000000000 : ℝ)^3345 := by
    have hnat : (1076168549 : ℕ)^4369*100000000000000^3345 ≤ 13449157700857^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076168549 5000000000 13449157700857 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164569211/312500000 : ℝ)^4369 ≤ (43275423328029/100000000000000 : ℝ)^3345 := by
    have hnat : (164569211 : ℕ)^4369*100000000000000^3345 ≤ 43275423328029^3345*312500000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164569211 312500000 43275423328029 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053242869/2000000000 : ℝ)^4369 ≤ (21637709479811/50000000000000 : ℝ)^3345 := by
    have hnat : (1053242869 : ℕ)^4369*50000000000000^3345 ≤ 21637709479811^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053242869 2000000000 21637709479811 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076168549/5000000000 : ℝ), (164569211/312500000 : ℝ), (1053242869/2000000000 : ℝ)] ![(13449157700857/100000000000000 : ℝ), (43275423328029/100000000000000 : ℝ), (21637709479811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076168549/5000000000 : ℝ)|^4369 ≤ (13449157700857/100000000000000 : ℝ)^3345
        have hw : |(-1076168549/5000000000 : ℝ)|=(1076168549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164569211/312500000 : ℝ)|^4369 ≤ (43275423328029/100000000000000 : ℝ)^3345
        have hw : |(164569211/312500000 : ℝ)|=(164569211/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053242869/2000000000 : ℝ)|^4369 ≤ (21637709479811/50000000000000 : ℝ)^3345
        have hw : |(1053242869/2000000000 : ℝ)|=(1053242869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_5 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537058661/1000000000 : ℝ)*x 0 + (-100663299/500000000 : ℝ)*x 1 + (658276877/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537058661/1000000000 : ℝ)^4369 ≤ (11099762221069/25000000000000 : ℝ)^3345 := by
    have hnat : (537058661 : ℕ)^4369*25000000000000^3345 ≤ 11099762221069^3345*1000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537058661 1000000000 11099762221069 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100663299/500000000 : ℝ)^4369 ≤ (12325524939279/100000000000000 : ℝ)^3345 := by
    have hnat : (100663299 : ℕ)^4369*100000000000000^3345 ≤ 12325524939279^3345*500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100663299 500000000 12325524939279 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658276877/1250000000 : ℝ)^4369 ≤ (43275426161591/100000000000000 : ℝ)^3345 := by
    have hnat : (658276877 : ℕ)^4369*100000000000000^3345 ≤ 43275426161591^3345*1250000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658276877 1250000000 43275426161591 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537058661/1000000000 : ℝ), (-100663299/500000000 : ℝ), (658276877/1250000000 : ℝ)] ![(11099762221069/25000000000000 : ℝ), (12325524939279/100000000000000 : ℝ), (43275426161591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537058661/1000000000 : ℝ)|^4369 ≤ (11099762221069/25000000000000 : ℝ)^3345
        have hw : |(537058661/1000000000 : ℝ)|=(537058661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100663299/500000000 : ℝ)|^4369 ≤ (12325524939279/100000000000000 : ℝ)^3345
        have hw : |(-100663299/500000000 : ℝ)|=(100663299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658276877/1250000000 : ℝ)|^4369 ≤ (43275426161591/100000000000000 : ℝ)^3345
        have hw : |(658276877/1250000000 : ℝ)|=(658276877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_6 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67132333/125000000 : ℝ)*x 0 + (2633107343/5000000000 : ℝ)*x 1 + (-1006633191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67132333/125000000 : ℝ)^4369 ≤ (11099762302053/25000000000000 : ℝ)^3345 := by
    have hnat : (67132333 : ℕ)^4369*25000000000000^3345 ≤ 11099762302053^3345*125000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67132333 125000000 11099762302053 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633107343/5000000000 : ℝ)^4369 ≤ (43275422619639/100000000000000 : ℝ)^3345 := by
    have hnat : (2633107343 : ℕ)^4369*100000000000000^3345 ≤ 43275422619639^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633107343 5000000000 43275422619639 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006633191/5000000000 : ℝ)^4369 ≤ (61627640769/500000000000 : ℝ)^3345 := by
    have hnat : (1006633191 : ℕ)^4369*500000000000^3345 ≤ 61627640769^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006633191 5000000000 61627640769 500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67132333/125000000 : ℝ), (2633107343/5000000000 : ℝ), (-1006633191/5000000000 : ℝ)] ![(11099762302053/25000000000000 : ℝ), (43275422619639/100000000000000 : ℝ), (61627640769/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67132333/125000000 : ℝ)|^4369 ≤ (11099762302053/25000000000000 : ℝ)^3345
        have hw : |(67132333/125000000 : ℝ)|=(67132333/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633107343/5000000000 : ℝ)|^4369 ≤ (43275422619639/100000000000000 : ℝ)^3345
        have hw : |(2633107343/5000000000 : ℝ)|=(2633107343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1006633191/5000000000 : ℝ)|^4369 ≤ (61627640769/500000000000 : ℝ)^3345
        have hw : |(-1006633191/5000000000 : ℝ)|=(1006633191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_7 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2080836597/5000000000 : ℝ)*x 0 + (2193481111/5000000000 : ℝ)*x 1 + (4386962561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080836597/5000000000 : ℝ)^4369 ≤ (7955272094947/25000000000000 : ℝ)^3345 := by
    have hnat : (2080836597 : ℕ)^4369*25000000000000^3345 ≤ 7955272094947^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080836597 5000000000 7955272094947 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193481111/5000000000 : ℝ)^4369 ≤ (34089454083673/100000000000000 : ℝ)^3345 := by
    have hnat : (2193481111 : ℕ)^4369*100000000000000^3345 ≤ 34089454083673^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193481111 5000000000 34089454083673 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386962561/10000000000 : ℝ)^4369 ≤ (17044728762167/50000000000000 : ℝ)^3345 := by
    have hnat : (4386962561 : ℕ)^4369*50000000000000^3345 ≤ 17044728762167^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386962561 10000000000 17044728762167 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2080836597/5000000000 : ℝ), (2193481111/5000000000 : ℝ), (4386962561/10000000000 : ℝ)] ![(7955272094947/25000000000000 : ℝ), (34089454083673/100000000000000 : ℝ), (17044728762167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2080836597/5000000000 : ℝ)|^4369 ≤ (7955272094947/25000000000000 : ℝ)^3345
        have hw : |(2080836597/5000000000 : ℝ)|=(2080836597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2193481111/5000000000 : ℝ)|^4369 ≤ (34089454083673/100000000000000 : ℝ)^3345
        have hw : |(2193481111/5000000000 : ℝ)|=(2193481111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4386962561/10000000000 : ℝ)|^4369 ≤ (17044728762167/50000000000000 : ℝ)^3345
        have hw : |(4386962561/10000000000 : ℝ)|=(4386962561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_8 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083509239/10000000000 : ℝ)*x 0 + (80979389/156250000 : ℝ)*x 1 + (270054877/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083509239/10000000000 : ℝ)^4369 ≤ (402818386137/3125000000000 : ℝ)^3345 := by
    have hnat : (2083509239 : ℕ)^4369*3125000000000^3345 ≤ 402818386137^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083509239 10000000000 402818386137 3125000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80979389/156250000 : ℝ)^4369 ≤ (8476204750441/20000000000000 : ℝ)^3345 := by
    have hnat : (80979389 : ℕ)^4369*20000000000000^3345 ≤ 8476204750441^3345*156250000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80979389 156250000 8476204750441 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270054877/500000000 : ℝ)^4369 ≤ (4472878787441/10000000000000 : ℝ)^3345 := by
    have hnat : (270054877 : ℕ)^4369*10000000000000^3345 ≤ 4472878787441^3345*500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270054877 500000000 4472878787441 10000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083509239/10000000000 : ℝ), (80979389/156250000 : ℝ), (270054877/500000000 : ℝ)] ![(402818386137/3125000000000 : ℝ), (8476204750441/20000000000000 : ℝ), (4472878787441/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083509239/10000000000 : ℝ)|^4369 ≤ (402818386137/3125000000000 : ℝ)^3345
        have hw : |(-2083509239/10000000000 : ℝ)|=(2083509239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80979389/156250000 : ℝ)|^4369 ≤ (8476204750441/20000000000000 : ℝ)^3345
        have hw : |(80979389/156250000 : ℝ)|=(80979389/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270054877/500000000 : ℝ)|^4369 ≤ (4472878787441/10000000000000 : ℝ)^3345
        have hw : |(270054877/500000000 : ℝ)|=(270054877/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_9 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638053367/5000000000 : ℝ)*x 0 + (-979259393/5000000000 : ℝ)*x 1 + (1080219567/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638053367/5000000000 : ℝ)^4369 ≤ (4338162633007/10000000000000 : ℝ)^3345 := by
    have hnat : (2638053367 : ℕ)^4369*10000000000000^3345 ≤ 4338162633007^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638053367 5000000000 4338162633007 10000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (979259393/5000000000 : ℝ)^4369 ≤ (11889582584739/100000000000000 : ℝ)^3345 := by
    have hnat : (979259393 : ℕ)^4369*100000000000000^3345 ≤ 11889582584739^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979259393 5000000000 11889582584739 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080219567/2000000000 : ℝ)^4369 ≤ (44728791065309/100000000000000 : ℝ)^3345 := by
    have hnat : (1080219567 : ℕ)^4369*100000000000000^3345 ≤ 44728791065309^3345*2000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080219567 2000000000 44728791065309 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638053367/5000000000 : ℝ), (-979259393/5000000000 : ℝ), (1080219567/2000000000 : ℝ)] ![(4338162633007/10000000000000 : ℝ), (11889582584739/100000000000000 : ℝ), (44728791065309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638053367/5000000000 : ℝ)|^4369 ≤ (4338162633007/10000000000000 : ℝ)^3345
        have hw : |(2638053367/5000000000 : ℝ)|=(2638053367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-979259393/5000000000 : ℝ)|^4369 ≤ (11889582584739/100000000000000 : ℝ)^3345
        have hw : |(-979259393/5000000000 : ℝ)|=(979259393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080219567/2000000000 : ℝ)|^4369 ≤ (44728791065309/100000000000000 : ℝ)^3345
        have hw : |(1080219567/2000000000 : ℝ)|=(1080219567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_10 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276107307/10000000000 : ℝ)*x 0 + (21098039/39062500 : ℝ)*x 1 + (-1958517807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276107307/10000000000 : ℝ)^4369 ≤ (43381632483721/100000000000000 : ℝ)^3345 := by
    have hnat : (5276107307 : ℕ)^4369*100000000000000^3345 ≤ 43381632483721^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276107307 10000000000 43381632483721 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21098039/39062500 : ℝ)^4369 ≤ (5591099084623/12500000000000 : ℝ)^3345 := by
    have hnat : (21098039 : ℕ)^4369*12500000000000^3345 ≤ 5591099084623^3345*39062500^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21098039 39062500 5591099084623 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1958517807/10000000000 : ℝ)^4369 ≤ (2377914964427/20000000000000 : ℝ)^3345 := by
    have hnat : (1958517807 : ℕ)^4369*20000000000000^3345 ≤ 2377914964427^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958517807 10000000000 2377914964427 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276107307/10000000000 : ℝ), (21098039/39062500 : ℝ), (-1958517807/10000000000 : ℝ)] ![(43381632483721/100000000000000 : ℝ), (5591099084623/12500000000000 : ℝ), (2377914964427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276107307/10000000000 : ℝ)|^4369 ≤ (43381632483721/100000000000000 : ℝ)^3345
        have hw : |(5276107307/10000000000 : ℝ)|=(5276107307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21098039/39062500 : ℝ)|^4369 ≤ (5591099084623/12500000000000 : ℝ)^3345
        have hw : |(21098039/39062500 : ℝ)|=(21098039/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1958517807/10000000000 : ℝ)|^4369 ≤ (2377914964427/20000000000000 : ℝ)^3345
        have hw : |(-1958517807/10000000000 : ℝ)|=(1958517807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_11 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2244806447/5000000000 : ℝ)*x 0 + (4222756123/10000000000 : ℝ)*x 1 + (4222757571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2244806447/5000000000 : ℝ)^4369 ≤ (35135012341499/100000000000000 : ℝ)^3345 := by
    have hnat : (2244806447 : ℕ)^4369*100000000000000^3345 ≤ 35135012341499^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244806447 5000000000 35135012341499 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222756123/10000000000 : ℝ)^4369 ≤ (8108121639459/25000000000000 : ℝ)^3345 := by
    have hnat : (4222756123 : ℕ)^4369*25000000000000^3345 ≤ 8108121639459^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222756123 10000000000 8108121639459 25000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222757571/10000000000 : ℝ)^4369 ≤ (4054062635449/12500000000000 : ℝ)^3345 := by
    have hnat : (4222757571 : ℕ)^4369*12500000000000^3345 ≤ 4054062635449^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222757571 10000000000 4054062635449 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2244806447/5000000000 : ℝ), (4222756123/10000000000 : ℝ), (4222757571/10000000000 : ℝ)] ![(35135012341499/100000000000000 : ℝ), (8108121639459/25000000000000 : ℝ), (4054062635449/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2244806447/5000000000 : ℝ)|^4369 ≤ (35135012341499/100000000000000 : ℝ)^3345
        have hw : |(2244806447/5000000000 : ℝ)|=(2244806447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222756123/10000000000 : ℝ)|^4369 ≤ (8108121639459/25000000000000 : ℝ)^3345
        have hw : |(4222756123/10000000000 : ℝ)|=(4222756123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222757571/10000000000 : ℝ)|^4369 ≤ (4054062635449/12500000000000 : ℝ)^3345
        have hw : |(4222757571/10000000000 : ℝ)|=(4222757571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_12 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-236799403/1250000000 : ℝ)*x 0 + (68357279/125000000 : ℝ)*x 1 + (5255099217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236799403/1250000000 : ℝ)^4369 ≤ (1422963376287/12500000000000 : ℝ)^3345 := by
    have hnat : (236799403 : ℕ)^4369*12500000000000^3345 ≤ 1422963376287^3345*1250000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236799403 1250000000 1422963376287 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68357279/125000000 : ℝ)^4369 ≤ (5682517025211/12500000000000 : ℝ)^3345 := by
    have hnat : (68357279 : ℕ)^4369*12500000000000^3345 ≤ 5682517025211^3345*125000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68357279 125000000 5682517025211 12500000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255099217/10000000000 : ℝ)^4369 ≤ (674314949681/1562500000000 : ℝ)^3345 := by
    have hnat : (5255099217 : ℕ)^4369*1562500000000^3345 ≤ 674314949681^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255099217 10000000000 674314949681 1562500000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-236799403/1250000000 : ℝ), (68357279/125000000 : ℝ), (5255099217/10000000000 : ℝ)] ![(1422963376287/12500000000000 : ℝ), (5682517025211/12500000000000 : ℝ), (674314949681/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-236799403/1250000000 : ℝ)|^4369 ≤ (1422963376287/12500000000000 : ℝ)^3345
        have hw : |(-236799403/1250000000 : ℝ)|=(236799403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68357279/125000000 : ℝ)|^4369 ≤ (5682517025211/12500000000000 : ℝ)^3345
        have hw : |(68357279/125000000 : ℝ)|=(68357279/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255099217/10000000000 : ℝ)|^4369 ≤ (674314949681/1562500000000 : ℝ)^3345
        have hw : |(5255099217/10000000000 : ℝ)|=(5255099217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_13 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84037047/156250000 : ℝ)*x 0 + (-201766697/1000000000 : ℝ)*x 1 + (2627549253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84037047/156250000 : ℝ)^4369 ≤ (8896624479901/20000000000000 : ℝ)^3345 := by
    have hnat : (84037047 : ℕ)^4369*20000000000000^3345 ≤ 8896624479901^3345*156250000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84037047 156250000 8896624479901 20000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201766697/1000000000 : ℝ)^4369 ≤ (618036421747/5000000000000 : ℝ)^3345 := by
    have hnat : (201766697 : ℕ)^4369*5000000000000^3345 ≤ 618036421747^3345*1000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201766697 1000000000 618036421747 5000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627549253/5000000000 : ℝ)^4369 ≤ (43156149153223/100000000000000 : ℝ)^3345 := by
    have hnat : (2627549253 : ℕ)^4369*100000000000000^3345 ≤ 43156149153223^3345*5000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627549253 5000000000 43156149153223 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84037047/156250000 : ℝ), (-201766697/1000000000 : ℝ), (2627549253/5000000000 : ℝ)] ![(8896624479901/20000000000000 : ℝ), (618036421747/5000000000000 : ℝ), (43156149153223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84037047/156250000 : ℝ)|^4369 ≤ (8896624479901/20000000000000 : ℝ)^3345
        have hw : |(84037047/156250000 : ℝ)|=(84037047/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201766697/1000000000 : ℝ)|^4369 ≤ (618036421747/5000000000000 : ℝ)^3345
        have hw : |(-201766697/1000000000 : ℝ)|=(201766697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627549253/5000000000 : ℝ)|^4369 ≤ (43156149153223/100000000000000 : ℝ)^3345
        have hw : |(2627549253/5000000000 : ℝ)|=(2627549253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_14 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378370553/10000000000 : ℝ)*x 0 + (1313774711/2500000000 : ℝ)*x 1 + (-201766713/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378370553/10000000000 : ℝ)^4369 ≤ (22241558742149/50000000000000 : ℝ)^3345 := by
    have hnat : (5378370553 : ℕ)^4369*50000000000000^3345 ≤ 22241558742149^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378370553 10000000000 22241558742149 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313774711/2500000000 : ℝ)^4369 ≤ (21578076389347/50000000000000 : ℝ)^3345 := by
    have hnat : (1313774711 : ℕ)^4369*50000000000000^3345 ≤ 21578076389347^3345*2500000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313774711 2500000000 21578076389347 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201766713/1000000000 : ℝ)^4369 ≤ (12360729715207/100000000000000 : ℝ)^3345 := by
    have hnat : (201766713 : ℕ)^4369*100000000000000^3345 ≤ 12360729715207^3345*1000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201766713 1000000000 12360729715207 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378370553/10000000000 : ℝ), (1313774711/2500000000 : ℝ), (-201766713/1000000000 : ℝ)] ![(22241558742149/50000000000000 : ℝ), (21578076389347/50000000000000 : ℝ), (12360729715207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378370553/10000000000 : ℝ)|^4369 ≤ (22241558742149/50000000000000 : ℝ)^3345
        have hw : |(5378370553/10000000000 : ℝ)|=(5378370553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313774711/2500000000 : ℝ)|^4369 ≤ (21578076389347/50000000000000 : ℝ)^3345
        have hw : |(1313774711/2500000000 : ℝ)|=(1313774711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201766713/1000000000 : ℝ)|^4369 ≤ (12360729715207/100000000000000 : ℝ)^3345
        have hw : |(-201766713/1000000000 : ℝ)|=(201766713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1409_box_15 (p : ℝ) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4134153639/10000000000 : ℝ)*x 0 + (4400482239/10000000000 : ℝ)*x 1 + (275030083/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4134153639/10000000000 : ℝ)^4369 ≤ (31546530498299/100000000000000 : ℝ)^3345 := by
    have hnat : (4134153639 : ℕ)^4369*100000000000000^3345 ≤ 31546530498299^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134153639 10000000000 31546530498299 100000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4400482239/10000000000 : ℝ)^4369 ≤ (17113369683579/50000000000000 : ℝ)^3345 := by
    have hnat : (4400482239 : ℕ)^4369*50000000000000^3345 ≤ 17113369683579^3345*10000000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4400482239 10000000000 17113369683579 50000000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275030083/625000000 : ℝ)^4369 ≤ (2139170632019/6250000000000 : ℝ)^3345 := by
    have hnat : (275030083 : ℕ)^4369*6250000000000^3345 ≤ 2139170632019^3345*625000000^4369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275030083 625000000 2139170632019 6250000000000 4369 3345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4369/1024 : ℝ)) 4369 3345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4134153639/10000000000 : ℝ), (4400482239/10000000000 : ℝ), (275030083/625000000 : ℝ)] ![(31546530498299/100000000000000 : ℝ), (17113369683579/50000000000000 : ℝ), (2139170632019/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4134153639/10000000000 : ℝ)|^4369 ≤ (31546530498299/100000000000000 : ℝ)^3345
        have hw : |(4134153639/10000000000 : ℝ)|=(4134153639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4400482239/10000000000 : ℝ)|^4369 ≤ (17113369683579/50000000000000 : ℝ)^3345
        have hw : |(4400482239/10000000000 : ℝ)|=(4400482239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275030083/625000000 : ℝ)|^4369 ≤ (2139170632019/6250000000000 : ℝ)^3345
        have hw : |(275030083/625000000 : ℝ)|=(275030083/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1409_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7861/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59073/100000 : ℝ) ∧ (40169/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84609/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7373/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7373/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7373/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7373/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7373/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7373/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11299/100000 : ℝ) ^ (273/64 : ℝ) ≤ (285413038155931/3125000000000000000 : ℝ) := by
    have hpowers : (11299/100000 : ℝ)^273 ≤ (285413038155931/3125000000000000000 : ℝ)^64 := by
      have hnat : (11299 : ℕ)^273*3125000000000000000^64 ≤ 285413038155931^64*100000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11299 100000 285413038155931 3125000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11299/100000 : ℝ)) (X := (285413038155931/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hpowhi : (7373/50000 : ℝ) ^ (273/64 : ℝ) ≤ (7109122850019719/25000000000000000000 : ℝ) := by
    have hpowers : (7373/50000 : ℝ)^273 ≤ (7109122850019719/25000000000000000000 : ℝ)^64 := by
      have hnat : (7373 : ℕ)^273*25000000000000000000^64 ≤ 7109122850019719^64*50000^273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7373 50000 7109122850019719 25000000000000000000 273 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7373/50000 : ℝ)) (X := (7109122850019719/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562785413038155931/1562500000000000000 : ℝ) ≤ (1000042819416551/1000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (1562785413038155931/1562500000000000000 : ℝ)^64 ≤ (1000042819416551/1000000000000000 : ℝ)^273 := by
      have hnat : (1562785413038155931 : ℕ)^64*1000000000000000^273 ≤ 1000042819416551^273*1562500000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562785413038155931 1562500000000000000 1000042819416551 1000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000042819416551/1000000000000000 : ℝ)) (X := (1562785413038155931/1562500000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009392427155267167/25000000000000000000 : ℝ) ≤ (10000880628439817/10000000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (25009392427155267167/25000000000000000000 : ℝ)^64 ≤ (10000880628439817/10000000000000000 : ℝ)^273 := by
      have hnat : (25009392427155267167 : ℕ)^64*10000000000000000^273 ≤ 10000880628439817^273*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009392427155267167 25000000000000000000 10000880628439817 10000000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000880628439817/10000000000000000 : ℝ)) (X := (25009392427155267167/25000000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507109122850019719/12500000000000000000 : ℝ) ≤ (2500333265678531/2500000000000000 : ℝ) ^ (273/64 : ℝ) := by
    have hpowers : (12507109122850019719/12500000000000000000 : ℝ)^64 ≤ (2500333265678531/2500000000000000 : ℝ)^273 := by
      have hnat : (12507109122850019719 : ℕ)^64*2500000000000000^273 ≤ 2500333265678531^273*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507109122850019719 12500000000000000000 2500333265678531 2500000000000000 64 273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500333265678531/2500000000000000 : ℝ)) (X := (12507109122850019719/12500000000000000000 : ℝ)) (by norm_num) 273 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(285413038155931/3125000000000000000 : ℝ) ≤ ((478628498271635047/478750000000000000 : ℝ)+2*(50270474923/38300000000000 : ℝ)*(11299/100000 : ℝ))^(273/64 : ℝ) := by
    rw [show (478628498271635047/478750000000000000 : ℝ)+2*(50270474923/38300000000000 : ℝ)*(11299/100000 : ℝ)=(1000042819416551/1000000000000000 : ℝ) by norm_num, show 1+2*(285413038155931/3125000000000000000 : ℝ)=(1562785413038155931/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7109122850019719/25000000000000000000 : ℝ)+(285413038155931/3125000000000000000 : ℝ) ≤ ((478628498271635047/478750000000000000 : ℝ)+(50270474923/38300000000000 : ℝ)*((7373/50000 : ℝ)+(11299/100000 : ℝ)))^(273/64 : ℝ) := by
    rw [show (478628498271635047/478750000000000000 : ℝ)+(50270474923/38300000000000 : ℝ)*((7373/50000 : ℝ)+(11299/100000 : ℝ))=(10000880628439817/10000000000000000 : ℝ) by norm_num, show 1+(7109122850019719/25000000000000000000 : ℝ)+(285413038155931/3125000000000000000 : ℝ)=(25009392427155267167/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7109122850019719/25000000000000000000 : ℝ) ≤ ((478628498271635047/478750000000000000 : ℝ)+2*(50270474923/38300000000000 : ℝ)*(7373/50000 : ℝ))^(273/64 : ℝ) := by
    rw [show (478628498271635047/478750000000000000 : ℝ)+2*(50270474923/38300000000000 : ℝ)*(7373/50000 : ℝ)=(2500333265678531/2500000000000000 : ℝ) by norm_num, show 1+2*(7109122850019719/25000000000000000000 : ℝ)=(12507109122850019719/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (478628498271635047/478750000000000000 : ℝ)*(X 1 0+X 2 0)+(50270474923/38300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (478628498271635047/478750000000000000 : ℝ)) (alpha := (50270474923/38300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (478628498271635047/478750000000000000 : ℝ)*(X 0 1+X 2 1)+(50270474923/38300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (478628498271635047/478750000000000000 : ℝ)) (alpha := (50270474923/38300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (478628498271635047/478750000000000000 : ℝ)*(X 0 2+X 1 2)+(50270474923/38300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (273/64 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (478628498271635047/478750000000000000 : ℝ)) (alpha := (50270474923/38300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-912676463/5000000000 : ℝ)*X 0 0+(134677797/250000000 : ℝ)*X 0 1+(5387111609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((330369249/625000000 : ℝ)*X 1 0+(-1964309301/10000000000 : ℝ)*X 1 1+(1077422323/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642953671/5000000000 : ℝ)*X 2 0+(5387111921/10000000000 : ℝ)*X 2 1+(-982154877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4456108503/10000000000 : ℝ)*X 0 0+(2119898069/5000000000 : ℝ)*X 0 1+(4239796297/10000000000 : ℝ)*X 0 2+(4456108503/10000000000 : ℝ)*X 1 0+(2119898069/5000000000 : ℝ)*X 1 1+(4239796297/10000000000 : ℝ)*X 1 2+(4456108503/10000000000 : ℝ)*X 2 0+(2119898069/5000000000 : ℝ)*X 2 1+(4239796297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1076168549/5000000000 : ℝ)*X 0 0+(164569211/312500000 : ℝ)*X 0 1+(1053242869/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((537058661/1000000000 : ℝ)*X 1 0+(-100663299/500000000 : ℝ)*X 1 1+(658276877/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((67132333/125000000 : ℝ)*X 2 0+(2633107343/5000000000 : ℝ)*X 2 1+(-1006633191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2080836597/5000000000 : ℝ)*X 0 0+(2193481111/5000000000 : ℝ)*X 0 1+(4386962561/10000000000 : ℝ)*X 0 2+(2080836597/5000000000 : ℝ)*X 1 0+(2193481111/5000000000 : ℝ)*X 1 1+(4386962561/10000000000 : ℝ)*X 1 2+(2080836597/5000000000 : ℝ)*X 2 0+(2193481111/5000000000 : ℝ)*X 2 1+(4386962561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2083509239/10000000000 : ℝ)*X 0 0+(80979389/156250000 : ℝ)*X 0 1+(270054877/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638053367/5000000000 : ℝ)*X 1 0+(-979259393/5000000000 : ℝ)*X 1 1+(1080219567/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276107307/10000000000 : ℝ)*X 2 0+(21098039/39062500 : ℝ)*X 2 1+(-1958517807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2244806447/5000000000 : ℝ)*X 0 0+(4222756123/10000000000 : ℝ)*X 0 1+(4222757571/10000000000 : ℝ)*X 0 2+(2244806447/5000000000 : ℝ)*X 1 0+(4222756123/10000000000 : ℝ)*X 1 1+(4222757571/10000000000 : ℝ)*X 1 2+(2244806447/5000000000 : ℝ)*X 2 0+(4222756123/10000000000 : ℝ)*X 2 1+(4222757571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-236799403/1250000000 : ℝ)*X 0 0+(68357279/125000000 : ℝ)*X 0 1+(5255099217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((84037047/156250000 : ℝ)*X 1 0+(-201766697/1000000000 : ℝ)*X 1 1+(2627549253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5378370553/10000000000 : ℝ)*X 2 0+(1313774711/2500000000 : ℝ)*X 2 1+(-201766713/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4134153639/10000000000 : ℝ)*X 0 0+(4400482239/10000000000 : ℝ)*X 0 1+(275030083/625000000 : ℝ)*X 0 2+(4134153639/10000000000 : ℝ)*X 1 0+(4400482239/10000000000 : ℝ)*X 1 1+(275030083/625000000 : ℝ)*X 1 2+(4134153639/10000000000 : ℝ)*X 2 0+(4400482239/10000000000 : ℝ)*X 2 1+(275030083/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1409_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7861/12500 : ℝ) ≤ (-4912898403919615273681829067/7812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (841689/20000000000000 : ℝ)*(lower1) + (68646537/50000000000000 : ℝ)*(lower4) + (20239223/100000000000000 : ℝ)*(lower5) + (374363614607423/12500000000000 : ℝ)*(major0) + (374363614607423/12500000000000 : ℝ)*(major1) + (374363614607423/12500000000000 : ℝ)*(major2) + (5429000743/100000000000000 : ℝ)*(sp3) + (2053866049378691/50000000000000 : ℝ)*(sp4) + (4107526803159791/100000000000000 : ℝ)*(sp5) + (2053859501175729/50000000000000 : ℝ)*(sp6) + (1903039046666049/100000000000000 : ℝ)*(sp7) + (2959151309/100000000000000 : ℝ)*(sp8) + (208254748899/100000000000000 : ℝ)*(sp13) + (1003472327/6250000000000 : ℝ)*(sp14) + (1903044475666793/100000000000000 : ℝ)*(f.failure) + (410773505790869/10000000000000 : ℝ)*(f.sum) + (4685045641/1250000000000000000000000 : ℝ)*base65 + (81715927131407/15625000000000000000000000000 : ℝ)*base67 + (15423780212343/15625000000000000000000000000 : ℝ)*base70 + (88183718276641/7812500000000000000000000000 : ℝ)*base71 + (3083220647/2500000000000000000000000 : ℝ)*base73 + (189874002600157/15625000000000000000000000000 : ℝ)*base75 + (9482152563877/976562500000000000000000000 : ℝ)*base77 + (193791554193907/15625000000000000000000000000 : ℝ)*base79 + (10627840521/1250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (3331939/2000000000000000000000 : ℝ)*base89 + (3331939/2000000000000000000000 : ℝ)*base91 + (3331939/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59073/100000 : ℝ) ≤ (7070609795762303110747182196809/11968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19655527/25000000000000 : ℝ)*(lower0) + (290006537/100000000000000 : ℝ)*(upper2) + (8228931/12500000000000 : ℝ)*(lower5) + (1532920322054517/50000000000000 : ℝ)*(major0) + (1532920322054517/50000000000000 : ℝ)*(major1) + (1532920322054517/50000000000000 : ℝ)*(major2) + (2081935724773553/50000000000000 : ℝ)*(sp0) + (166554843829539/4000000000000 : ℝ)*(sp1) + (1040966696981027/25000000000000 : ℝ)*(sp2) + (1948110271627173/100000000000000 : ℝ)*(sp3) + (488581611/25000000000000 : ℝ)*(sp5) + (6102865011/100000000000000 : ℝ)*(sp7) + (6262140811/100000000000000 : ℝ)*(sp10) + (1600517813/100000000000000 : ℝ)*(sp12) + (389623274898437/20000000000000 : ℝ)*(f.failure) + (4163873050064919/100000000000000 : ℝ)*(f.sum) + (6978021324607/1915000000000000000000000000 : ℝ)*base65 + (144885953292494799/23937500000000000000000000000000 : ℝ)*base67 + (81162418774182299/23937500000000000000000000000000 : ℝ)*base69 + (291847634044307299/23937500000000000000000000000000 : ℝ)*base71 + (13922157183833/1915000000000000000000000000 : ℝ)*base74 + (13712186944057299/23937500000000000000000000000000 : ℝ)*base75 + (418663537871869799/23937500000000000000000000000000 : ℝ)*base77 + (132983484985244799/23937500000000000000000000000000 : ℝ)*base79 + (4376588123037/1915000000000000000000000000 : ℝ)*base81 + (1395351/400000000000000000000 : ℝ)*base89 + (1395351/400000000000000000000 : ℝ)*base91 + (1395351/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (40169/50000 : ℝ) ≤ (2403922646053120564863309730437/2992187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (25128821/10000000000000 : ℝ)*(upper0) + (227774103/100000000000000 : ℝ)*(lower1) + (144876463/100000000000000 : ℝ)*(lower3) + (245195029/50000000000000 : ℝ)*(upper4) + (210925891650903/6250000000000 : ℝ)*(major0) + (210925891650903/6250000000000 : ℝ)*(major1) + (210925891650903/6250000000000 : ℝ)*(major2) + (18648792479/50000000000000 : ℝ)*(sp1) + (27000302589/10000000000000 : ℝ)*(sp2) + (120514019827/100000000000000 : ℝ)*(sp3) + (4578402141306963/100000000000000 : ℝ)*(sp8) + (915672968744401/20000000000000 : ℝ)*(sp9) + (4578132138281073/100000000000000 : ℝ)*(sp10) + (214432588631891/10000000000000 : ℝ)*(sp11) + (1072223200169369/50000000000000 : ℝ)*(f.failure) + (4578402141306963/100000000000000 : ℝ)*(f.sum) + (861010936361/478750000000000000000000000 : ℝ)*base65 + (30535282119922441/2992187500000000000000000000000 : ℝ)*base67 + (56996842518985507/5984375000000000000000000000000 : ℝ)*base69 + (44271179110204257/5984375000000000000000000000000 : ℝ)*base71 + (353845527723/239375000000000000000000000 : ℝ)*base73 + (4884747015117329/748046875000000000000000000000 : ℝ)*base75 + (33424519195984941/2992187500000000000000000000000 : ℝ)*base77 + (13645258035969033/1496093750000000000000000000000 : ℝ)*base79 + (10198513821717/957500000000000000000000000 : ℝ)*base81 + (3766413/1000000000000000000000 : ℝ)*base90 + (3766413/1000000000000000000000 : ℝ)*base92 + (3766413/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-84609/100000 : ℝ) ≤ (-5063198022274337341595277720597/5984375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12555879/12500000000000 : ℝ)*(lower0) + (84768943/50000000000000 : ℝ)*(upper1) + (853061/3125000000000 : ℝ)*(upper3) + (169220709/100000000000000 : ℝ)*(lower4) + (3412056766165289/100000000000000 : ℝ)*(major0) + (3412056766165289/100000000000000 : ℝ)*(major1) + (341205676616529/10000000000000 : ℝ)*(major2) + (171642908999/100000000000000 : ℝ)*(sp5) + (7202601099/6250000000000 : ℝ)*(sp6) + (267502431/781250000000 : ℝ)*(sp7) + (234210229117989/5000000000000 : ℝ)*(sp12) + (4684032939450781/100000000000000 : ℝ)*(sp13) + (1171022335185549/25000000000000 : ℝ)*(sp14) + (1084038515553291/50000000000000 : ℝ)*(sp15) + (8672445085671/400000000000 : ℝ)*(f.failure) + (234210229117989/5000000000000 : ℝ)*(f.sum) + (1425530091317/3830000000000000000000000000 : ℝ)*base65 + (352089135607908583/47875000000000000000000000000000 : ℝ)*base67 + (52613602881425613/4787500000000000000000000000000 : ℝ)*base69 + (86217183817658583/47875000000000000000000000000000 : ℝ)*base71 + (4926751271097/3830000000000000000000000000 : ℝ)*base73 + (70525220687300613/4787500000000000000000000000000 : ℝ)*base75 + (214890966839871083/47875000000000000000000000000000 : ℝ)*base77 + (410290969473371083/47875000000000000000000000000000 : ℝ)*base79 + (19723281699707/1915000000000000000000000000 : ℝ)*base81 + (8333/8000000000000000000 : ℝ)*base89 + (8333/8000000000000000000 : ℝ)*base91 + (71667/8000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1409_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7861/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(59073/100000 : ℝ) else (40169/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84609/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1409_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1409_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7861/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(59073/100000 : ℝ) else (40169/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84609/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1409_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1409_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1409_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (273/64 : ℝ) ≤ p) (hpb : p ≤ (4369/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31474923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7861/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(59073/100000 : ℝ) else (40169/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84609/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1409_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
