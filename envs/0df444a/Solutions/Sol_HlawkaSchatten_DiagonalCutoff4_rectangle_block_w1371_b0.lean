-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1371_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:20:38.125921+00:00
-- url     : https://prove2.me/submissions/f202fe9e-2898-45fb-989e-96a6d64f52bc

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
theorem support_rectangle_w1371_s0_0 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-224015717/1250000000 : ℝ)*x 0 + (2992242791/5000000000 : ℝ)*x 1 + (4817780899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224015717/1250000000 : ℝ)^4331 ≤ (5261951770787/50000000000000 : ℝ)^3307 := by
    have hnat : (224015717 : ℕ)^4331*50000000000000^3307 ≤ 5261951770787^3307*1250000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224015717 1250000000 5261951770787 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2992242791/5000000000 : ℝ)^4331 ≤ (5104862249963/10000000000000 : ℝ)^3307 := by
    have hnat : (2992242791 : ℕ)^4331*10000000000000^3307 ≤ 5104862249963^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2992242791 5000000000 5104862249963 10000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4817780899/10000000000 : ℝ)^4331 ≤ (2401717120963/6250000000000 : ℝ)^3307 := by
    have hnat : (4817780899 : ℕ)^4331*6250000000000^3307 ≤ 2401717120963^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817780899 10000000000 2401717120963 6250000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-224015717/1250000000 : ℝ), (2992242791/5000000000 : ℝ), (4817780899/10000000000 : ℝ)] ![(5261951770787/50000000000000 : ℝ), (5104862249963/10000000000000 : ℝ), (2401717120963/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-224015717/1250000000 : ℝ)|^4331 ≤ (5261951770787/50000000000000 : ℝ)^3307
        have hw : |(-224015717/1250000000 : ℝ)|=(224015717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2992242791/5000000000 : ℝ)|^4331 ≤ (5104862249963/10000000000000 : ℝ)^3307
        have hw : |(2992242791/5000000000 : ℝ)|=(2992242791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4817780899/10000000000 : ℝ)|^4331 ≤ (2401717120963/6250000000000 : ℝ)^3307
        have hw : |(4817780899/10000000000 : ℝ)|=(4817780899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s0_1 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1099713583/2000000000 : ℝ)*x 0 + (-2453889863/10000000000 : ℝ)*x 1 + (2408890741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099713583/2000000000 : ℝ)^4331 ≤ (45689758860777/100000000000000 : ℝ)^3307 := by
    have hnat : (1099713583 : ℕ)^4331*100000000000000^3307 ≤ 45689758860777^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099713583 2000000000 45689758860777 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2453889863/10000000000 : ℝ)^4331 ≤ (3176552219117/20000000000000 : ℝ)^3307 := by
    have hnat : (2453889863 : ℕ)^4331*20000000000000^3307 ≤ 3176552219117^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453889863 10000000000 3176552219117 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2408890741/5000000000 : ℝ)^4331 ≤ (38427480025409/100000000000000 : ℝ)^3307 := by
    have hnat : (2408890741 : ℕ)^4331*100000000000000^3307 ≤ 38427480025409^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2408890741 5000000000 38427480025409 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099713583/2000000000 : ℝ), (-2453889863/10000000000 : ℝ), (2408890741/5000000000 : ℝ)] ![(45689758860777/100000000000000 : ℝ), (3176552219117/20000000000000 : ℝ), (38427480025409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099713583/2000000000 : ℝ)|^4331 ≤ (45689758860777/100000000000000 : ℝ)^3307
        have hw : |(1099713583/2000000000 : ℝ)|=(1099713583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2453889863/10000000000 : ℝ)|^4331 ≤ (3176552219117/20000000000000 : ℝ)^3307
        have hw : |(-2453889863/10000000000 : ℝ)|=(2453889863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2408890741/5000000000 : ℝ)|^4331 ≤ (38427480025409/100000000000000 : ℝ)^3307
        have hw : |(2408890741/5000000000 : ℝ)|=(2408890741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s0_2 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1099713561/2000000000 : ℝ)*x 0 + (4817780827/10000000000 : ℝ)*x 1 + (-613472703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099713561/2000000000 : ℝ)^4331 ≤ (45689757663717/100000000000000 : ℝ)^3307 := by
    have hnat : (1099713561 : ℕ)^4331*100000000000000^3307 ≤ 45689757663717^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099713561 2000000000 45689757663717 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4817780827/10000000000 : ℝ)^4331 ≤ (19213736591649/50000000000000 : ℝ)^3307 := by
    have hnat : (4817780827 : ℕ)^4331*50000000000000^3307 ≤ 19213736591649^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817780827 10000000000 19213736591649 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (613472703/2500000000 : ℝ)^4331 ≤ (7941384569969/50000000000000 : ℝ)^3307 := by
    have hnat : (613472703 : ℕ)^4331*50000000000000^3307 ≤ 7941384569969^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613472703 2500000000 7941384569969 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099713561/2000000000 : ℝ), (4817780827/10000000000 : ℝ), (-613472703/2500000000 : ℝ)] ![(45689757663717/100000000000000 : ℝ), (19213736591649/50000000000000 : ℝ), (7941384569969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099713561/2000000000 : ℝ)|^4331 ≤ (45689757663717/100000000000000 : ℝ)^3307
        have hw : |(1099713561/2000000000 : ℝ)|=(1099713561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4817780827/10000000000 : ℝ)|^4331 ≤ (19213736591649/50000000000000 : ℝ)^3307
        have hw : |(4817780827/10000000000 : ℝ)|=(4817780827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-613472703/2500000000 : ℝ)|^4331 ≤ (7941384569969/50000000000000 : ℝ)^3307
        have hw : |(-613472703/2500000000 : ℝ)|=(613472703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s0_3 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2087218877/5000000000 : ℝ)*x 0 + (1940783/6250000 : ℝ)*x 1 + (5575689799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087218877/5000000000 : ℝ)^4331 ≤ (15925299226341/50000000000000 : ℝ)^3307 := by
    have hnat : (2087218877 : ℕ)^4331*50000000000000^3307 ≤ 15925299226341^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087218877 5000000000 15925299226341 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1940783/6250000 : ℝ)^4331 ≤ (21618557579181/100000000000000 : ℝ)^3307 := by
    have hnat : (1940783 : ℕ)^4331*100000000000000^3307 ≤ 21618557579181^3307*6250000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940783 6250000 21618557579181 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5575689799/10000000000 : ℝ)^4331 ≤ (46530843940093/100000000000000 : ℝ)^3307 := by
    have hnat : (5575689799 : ℕ)^4331*100000000000000^3307 ≤ 46530843940093^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5575689799 10000000000 46530843940093 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2087218877/5000000000 : ℝ), (1940783/6250000 : ℝ), (5575689799/10000000000 : ℝ)] ![(15925299226341/50000000000000 : ℝ), (21618557579181/100000000000000 : ℝ), (46530843940093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2087218877/5000000000 : ℝ)|^4331 ≤ (15925299226341/50000000000000 : ℝ)^3307
        have hw : |(2087218877/5000000000 : ℝ)|=(2087218877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1940783/6250000 : ℝ)|^4331 ≤ (21618557579181/100000000000000 : ℝ)^3307
        have hw : |(1940783/6250000 : ℝ)|=(1940783/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5575689799/10000000000 : ℝ)|^4331 ≤ (46530843940093/100000000000000 : ℝ)^3307
        have hw : |(5575689799/10000000000 : ℝ)|=(5575689799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s0_4 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-224554061/1250000000 : ℝ)*x 0 + (1211938701/2500000000 : ℝ)*x 1 + (2976720221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224554061/1250000000 : ℝ)^4331 ≤ (10557037528839/100000000000000 : ℝ)^3307 := by
    have hnat : (224554061 : ℕ)^4331*100000000000000^3307 ≤ 10557037528839^3307*1250000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224554061 1250000000 10557037528839 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1211938701/2500000000 : ℝ)^4331 ≤ (38740881616347/100000000000000 : ℝ)^3307 := by
    have hnat : (1211938701 : ℕ)^4331*100000000000000^3307 ≤ 38740881616347^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211938701 2500000000 38740881616347 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2976720221/5000000000 : ℝ)^4331 ≤ (6337760105307/12500000000000 : ℝ)^3307 := by
    have hnat : (2976720221 : ℕ)^4331*12500000000000^3307 ≤ 6337760105307^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2976720221 5000000000 6337760105307 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-224554061/1250000000 : ℝ), (1211938701/2500000000 : ℝ), (2976720221/5000000000 : ℝ)] ![(10557037528839/100000000000000 : ℝ), (38740881616347/100000000000000 : ℝ), (6337760105307/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-224554061/1250000000 : ℝ)|^4331 ≤ (10557037528839/100000000000000 : ℝ)^3307
        have hw : |(-224554061/1250000000 : ℝ)|=(224554061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1211938701/2500000000 : ℝ)|^4331 ≤ (38740881616347/100000000000000 : ℝ)^3307
        have hw : |(1211938701/2500000000 : ℝ)|=(1211938701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2976720221/5000000000 : ℝ)|^4331 ≤ (6337760105307/12500000000000 : ℝ)^3307
        have hw : |(2976720221/5000000000 : ℝ)|=(2976720221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s0_5 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1295107193/2500000000 : ℝ)*x 0 + (-1318233489/10000000000 : ℝ)*x 1 + (1190687847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295107193/2500000000 : ℝ)^4331 ≤ (42259089129953/100000000000000 : ℝ)^3307 := by
    have hnat : (1295107193 : ℕ)^4331*100000000000000^3307 ≤ 42259089129953^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295107193 2500000000 42259089129953 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318233489/10000000000 : ℝ)^4331 ≤ (7038843483529/100000000000000 : ℝ)^3307 := by
    have hnat : (1318233489 : ℕ)^4331*100000000000000^3307 ≤ 7038843483529^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318233489 10000000000 7038843483529 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1190687847/2000000000 : ℝ)^4331 ≤ (12675516845041/25000000000000 : ℝ)^3307 := by
    have hnat : (1190687847 : ℕ)^4331*25000000000000^3307 ≤ 12675516845041^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190687847 2000000000 12675516845041 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295107193/2500000000 : ℝ), (-1318233489/10000000000 : ℝ), (1190687847/2000000000 : ℝ)] ![(42259089129953/100000000000000 : ℝ), (7038843483529/100000000000000 : ℝ), (12675516845041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295107193/2500000000 : ℝ)|^4331 ≤ (42259089129953/100000000000000 : ℝ)^3307
        have hw : |(1295107193/2500000000 : ℝ)|=(1295107193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1318233489/10000000000 : ℝ)|^4331 ≤ (7038843483529/100000000000000 : ℝ)^3307
        have hw : |(-1318233489/10000000000 : ℝ)|=(1318233489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1190687847/2000000000 : ℝ)|^4331 ≤ (12675516845041/25000000000000 : ℝ)^3307
        have hw : |(1190687847/2000000000 : ℝ)|=(1190687847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s0_6 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2590213939/5000000000 : ℝ)*x 0 + (5953441403/10000000000 : ℝ)*x 1 + (-1318231397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2590213939/5000000000 : ℝ)^4331 ≤ (21129539789509/50000000000000 : ℝ)^3307 := by
    have hnat : (2590213939 : ℕ)^4331*50000000000000^3307 ≤ 21129539789509^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590213939 5000000000 21129539789509 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5953441403/10000000000 : ℝ)^4331 ≤ (10140418312197/20000000000000 : ℝ)^3307 := by
    have hnat : (5953441403 : ℕ)^4331*20000000000000^3307 ≤ 10140418312197^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5953441403 10000000000 10140418312197 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318231397/10000000000 : ℝ)^4331 ≤ (1407765770839/20000000000000 : ℝ)^3307 := by
    have hnat : (1318231397 : ℕ)^4331*20000000000000^3307 ≤ 1407765770839^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318231397 10000000000 1407765770839 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2590213939/5000000000 : ℝ), (5953441403/10000000000 : ℝ), (-1318231397/10000000000 : ℝ)] ![(21129539789509/50000000000000 : ℝ), (10140418312197/20000000000000 : ℝ), (1407765770839/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2590213939/5000000000 : ℝ)|^4331 ≤ (21129539789509/50000000000000 : ℝ)^3307
        have hw : |(2590213939/5000000000 : ℝ)|=(2590213939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5953441403/10000000000 : ℝ)|^4331 ≤ (10140418312197/20000000000000 : ℝ)^3307
        have hw : |(5953441403/10000000000 : ℝ)|=(5953441403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1318231397/10000000000 : ℝ)|^4331 ≤ (1407765770839/20000000000000 : ℝ)^3307
        have hw : |(-1318231397/10000000000 : ℝ)|=(1318231397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s0_7 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2091774919/5000000000 : ℝ)*x 0 + (5512224347/10000000000 : ℝ)*x 1 + (1585495309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091774919/5000000000 : ℝ)^4331 ≤ (15970840795199/50000000000000 : ℝ)^3307 := by
    have hnat : (2091774919 : ℕ)^4331*50000000000000^3307 ≤ 15970840795199^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091774919 5000000000 15970840795199 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5512224347/10000000000 : ℝ)^4331 ≤ (22919215121131/50000000000000 : ℝ)^3307 := by
    have hnat : (5512224347 : ℕ)^4331*50000000000000^3307 ≤ 22919215121131^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512224347 10000000000 22919215121131 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1585495309/5000000000 : ℝ)^4331 ≤ (22219888151607/100000000000000 : ℝ)^3307 := by
    have hnat : (1585495309 : ℕ)^4331*100000000000000^3307 ≤ 22219888151607^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585495309 5000000000 22219888151607 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2091774919/5000000000 : ℝ), (5512224347/10000000000 : ℝ), (1585495309/5000000000 : ℝ)] ![(15970840795199/50000000000000 : ℝ), (22919215121131/50000000000000 : ℝ), (22219888151607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2091774919/5000000000 : ℝ)|^4331 ≤ (15970840795199/50000000000000 : ℝ)^3307
        have hw : |(2091774919/5000000000 : ℝ)|=(2091774919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5512224347/10000000000 : ℝ)|^4331 ≤ (22919215121131/50000000000000 : ℝ)^3307
        have hw : |(5512224347/10000000000 : ℝ)|=(5512224347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1585495309/5000000000 : ℝ)|^4331 ≤ (22219888151607/100000000000000 : ℝ)^3307
        have hw : |(1585495309/5000000000 : ℝ)|=(1585495309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1371_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (163/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3333/12500 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (2165/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2165 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2165*1^512 ≤ 0^512*1^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2165/512 : ℝ) ≤ (519092153470677317/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2165 ≤ (519092153470677317/25000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2165*25000000000000000000^512 ≤ 519092153470677317^512*5^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 519092153470677317 25000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (519092153470677317/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2165 := by
      have hnat : (1 : ℕ)^512*1^2165 ≤ 1^2165*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25519092153470677317/25000000000000000000 : ℝ) ≤ (10048719413869191/10000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (25519092153470677317/25000000000000000000 : ℝ)^512 ≤ (10048719413869191/10000000000000000 : ℝ)^2165 := by
      have hnat : (25519092153470677317 : ℕ)^512*10000000000000000^2165 ≤ 10048719413869191^2165*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25519092153470677317 25000000000000000000 10048719413869191 10000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10048719413869191/10000000000000000 : ℝ)) (X := (25519092153470677317/25000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (13019092153470677317/12500000000000000000 : ℝ) ≤ (5048719413869191/5000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (13019092153470677317/12500000000000000000 : ℝ)^512 ≤ (5048719413869191/5000000000000000 : ℝ)^2165 := by
      have hnat : (13019092153470677317 : ℕ)^512*5000000000000000^2165 ≤ 5048719413869191^2165*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13019092153470677317 12500000000000000000 5048719413869191 5000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048719413869191/5000000000000000 : ℝ)) (X := (13019092153470677317/12500000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(48719413869191/4000000000000000 : ℝ)*(0 : ℝ))^(2165/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(48719413869191/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(519092153470677317/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(48719413869191/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2165/512 : ℝ) := by
    rw [show (1 : ℝ)+(48719413869191/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10048719413869191/10000000000000000 : ℝ) by norm_num, show 1+(519092153470677317/25000000000000000000 : ℝ)+(0 : ℝ)=(25519092153470677317/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(519092153470677317/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(48719413869191/4000000000000000 : ℝ)*(2/5 : ℝ))^(2165/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(48719413869191/4000000000000000 : ℝ)*(2/5 : ℝ)=(5048719413869191/5000000000000000 : ℝ) by norm_num, show 1+2*(519092153470677317/25000000000000000000 : ℝ)=(13019092153470677317/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(48719413869191/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48719413869191/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(48719413869191/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48719413869191/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(48719413869191/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48719413869191/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-224015717/1250000000 : ℝ)*X 0 0+(2992242791/5000000000 : ℝ)*X 0 1+(4817780899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1099713583/2000000000 : ℝ)*X 1 0+(-2453889863/10000000000 : ℝ)*X 1 1+(2408890741/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1099713561/2000000000 : ℝ)*X 2 0+(4817780827/10000000000 : ℝ)*X 2 1+(-613472703/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2087218877/5000000000 : ℝ)*X 0 0+(1940783/6250000 : ℝ)*X 0 1+(5575689799/10000000000 : ℝ)*X 0 2+(2087218877/5000000000 : ℝ)*X 1 0+(1940783/6250000 : ℝ)*X 1 1+(5575689799/10000000000 : ℝ)*X 1 2+(2087218877/5000000000 : ℝ)*X 2 0+(1940783/6250000 : ℝ)*X 2 1+(5575689799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-224554061/1250000000 : ℝ)*X 0 0+(1211938701/2500000000 : ℝ)*X 0 1+(2976720221/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1295107193/2500000000 : ℝ)*X 1 0+(-1318233489/10000000000 : ℝ)*X 1 1+(1190687847/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2590213939/5000000000 : ℝ)*X 2 0+(5953441403/10000000000 : ℝ)*X 2 1+(-1318231397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2091774919/5000000000 : ℝ)*X 0 0+(5512224347/10000000000 : ℝ)*X 0 1+(1585495309/5000000000 : ℝ)*X 0 2+(2091774919/5000000000 : ℝ)*X 1 0+(5512224347/10000000000 : ℝ)*X 1 1+(1585495309/5000000000 : ℝ)*X 1 2+(2091774919/5000000000 : ℝ)*X 2 0+(5512224347/10000000000 : ℝ)*X 2 1+(1585495309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136569424794930427826103/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173201049/100000000000000 : ℝ)*(base1) + (9912177/20000000000000 : ℝ)*(base16) + (289794009/50000000000000 : ℝ)*(base19) + (61200209/10000000000000 : ℝ)*(base23) + (214389/250000000000 : ℝ)*(upper3) + (630953117513611/100000000000000 : ℝ)*(major0) + (630953117513611/100000000000000 : ℝ)*(major1) + (630953117513611/100000000000000 : ℝ)*(major2) + (428558421183927/50000000000000 : ℝ)*(sp0) + (85711742465591/10000000000000 : ℝ)*(sp1) + (214279360450681/25000000000000 : ℝ)*(sp2) + (404787180322969/100000000000000 : ℝ)*(sp3) + (173079751/12500000000000 : ℝ)*(sp4) + (92081513/12500000000000 : ℝ)*(sp7) + (202394045088061/50000000000000 : ℝ)*(f.failure) + (857118053804813/100000000000000 : ℝ)*(f.sum) + (88452149941299/200000000000000000000000000000 : ℝ)*base66 + (1352430816858701/400000000000000000000000000000 : ℝ)*base67 + (1114602397941299/400000000000000000000000000000 : ℝ)*base70 + (38731744858701/400000000000000000000000000000 : ℝ)*base71 + (784824675541299/200000000000000000000000000000 : ℝ)*base74 + (366409733141299/400000000000000000000000000000 : ℝ)*base76 + (1043897523141299/400000000000000000000000000000 : ℝ)*base78 + (1814489698341299/400000000000000000000000000000 : ℝ)*base80 + (711901206941299/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (28907511/5000000000000000000000 : ℝ)*base89 + (28907511/5000000000000000000000 : ℝ)*base91 + (28907511/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (155131004545681884302037/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70492283/10000000000000 : ℝ)*(base19) + (1212730203/100000000000000 : ℝ)*(base23) + (453433073/100000000000000 : ℝ)*(base39) + (42113301/50000000000000 : ℝ)*(upper2) + (264632281/100000000000000 : ℝ)*(upper5) + (133153871278431/20000000000000 : ℝ)*(major0) + (133153871278431/20000000000000 : ℝ)*(major1) + (332884451479541/50000000000000 : ℝ)*(major2) + (1550542767/100000000000000 : ℝ)*(sp1) + (2503543111/100000000000000 : ℝ)*(sp2) + (180882709215949/20000000000000 : ℝ)*(sp4) + (226102822653537/25000000000000 : ℝ)*(sp5) + (180882056647901/20000000000000 : ℝ)*(sp6) + (427124454719811/100000000000000 : ℝ)*(sp7) + (427124454719811/100000000000000 : ℝ)*(f.failure) + (452206999756409/50000000000000 : ℝ)*(f.sum) + (1223573618839267/400000000000000000000000000000 : ℝ)*base65 + (101361292678669/200000000000000000000000000000 : ℝ)*base68 + (709228934679321/80000000000000000000000000000 : ℝ)*base69 + (597209850921331/200000000000000000000000000000 : ℝ)*base71 + (1660298407560733/400000000000000000000000000000 : ℝ)*base74 + (596357719959321/80000000000000000000000000000 : ℝ)*base75 + (458691184679321/80000000000000000000000000000 : ℝ)*base77 + (258260364600679/80000000000000000000000000000 : ℝ)*base80 + (40043430479321/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (41173239/10000000000000000000000 : ℝ)*base90 + (41173239/10000000000000000000000 : ℝ)*base92 + (41173239/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1371_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (163/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3333/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1371_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1371_s1_0 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-246595473/1250000000 : ℝ)*x 0 + (5629364531/10000000000 : ℝ)*x 1 + (2528593557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246595473/1250000000 : ℝ)^4331 ≤ (11934322299633/100000000000000 : ℝ)^3307 := by
    have hnat : (246595473 : ℕ)^4331*100000000000000^3307 ≤ 11934322299633^3307*1250000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246595473 1250000000 11934322299633 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5629364531/10000000000 : ℝ)^4331 ≤ (23559174471991/50000000000000 : ℝ)^3307 := by
    have hnat : (5629364531 : ℕ)^4331*50000000000000^3307 ≤ 23559174471991^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5629364531 10000000000 23559174471991 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2528593557/5000000000 : ℝ)^4331 ≤ (5118416092663/12500000000000 : ℝ)^3307 := by
    have hnat : (2528593557 : ℕ)^4331*12500000000000^3307 ≤ 5118416092663^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528593557 5000000000 5118416092663 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-246595473/1250000000 : ℝ), (5629364531/10000000000 : ℝ), (2528593557/5000000000 : ℝ)] ![(11934322299633/100000000000000 : ℝ), (23559174471991/50000000000000 : ℝ), (5118416092663/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-246595473/1250000000 : ℝ)|^4331 ≤ (11934322299633/100000000000000 : ℝ)^3307
        have hw : |(-246595473/1250000000 : ℝ)|=(246595473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5629364531/10000000000 : ℝ)|^4331 ≤ (23559174471991/50000000000000 : ℝ)^3307
        have hw : |(5629364531/10000000000 : ℝ)|=(5629364531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2528593557/5000000000 : ℝ)|^4331 ≤ (5118416092663/12500000000000 : ℝ)^3307
        have hw : |(2528593557/5000000000 : ℝ)|=(2528593557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s1_1 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2701355169/5000000000 : ℝ)*x 0 + (-1138674027/5000000000 : ℝ)*x 1 + (5057188391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701355169/5000000000 : ℝ)^4331 ≤ (44649428707989/100000000000000 : ℝ)^3307 := by
    have hnat : (2701355169 : ℕ)^4331*100000000000000^3307 ≤ 44649428707989^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701355169 5000000000 44649428707989 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138674027/5000000000 : ℝ)^4331 ≤ (14403228998831/100000000000000 : ℝ)^3307 := by
    have hnat : (1138674027 : ℕ)^4331*100000000000000^3307 ≤ 14403228998831^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138674027 5000000000 14403228998831 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5057188391/10000000000 : ℝ)^4331 ≤ (20473671141319/50000000000000 : ℝ)^3307 := by
    have hnat : (5057188391 : ℕ)^4331*50000000000000^3307 ≤ 20473671141319^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5057188391 10000000000 20473671141319 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701355169/5000000000 : ℝ), (-1138674027/5000000000 : ℝ), (5057188391/10000000000 : ℝ)] ![(44649428707989/100000000000000 : ℝ), (14403228998831/100000000000000 : ℝ), (20473671141319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701355169/5000000000 : ℝ)|^4331 ≤ (44649428707989/100000000000000 : ℝ)^3307
        have hw : |(2701355169/5000000000 : ℝ)|=(2701355169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1138674027/5000000000 : ℝ)|^4331 ≤ (14403228998831/100000000000000 : ℝ)^3307
        have hw : |(-1138674027/5000000000 : ℝ)|=(1138674027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5057188391/10000000000 : ℝ)|^4331 ≤ (20473671141319/50000000000000 : ℝ)^3307
        have hw : |(5057188391/10000000000 : ℝ)|=(5057188391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s1_2 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5402710789/10000000000 : ℝ)*x 0 + (5057187311/10000000000 : ℝ)*x 1 + (-142334303/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402710789/10000000000 : ℝ)^4331 ≤ (279058959933/625000000000 : ℝ)^3307 := by
    have hnat : (5402710789 : ℕ)^4331*625000000000^3307 ≤ 279058959933^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402710789 10000000000 279058959933 625000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5057187311/10000000000 : ℝ)^4331 ≤ (5118416353787/12500000000000 : ℝ)^3307 := by
    have hnat : (5057187311 : ℕ)^4331*12500000000000^3307 ≤ 5118416353787^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5057187311 10000000000 5118416353787 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142334303/625000000 : ℝ)^4331 ≤ (2880647115097/20000000000000 : ℝ)^3307 := by
    have hnat : (142334303 : ℕ)^4331*20000000000000^3307 ≤ 2880647115097^3307*625000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142334303 625000000 2880647115097 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402710789/10000000000 : ℝ), (5057187311/10000000000 : ℝ), (-142334303/625000000 : ℝ)] ![(279058959933/625000000000 : ℝ), (5118416353787/12500000000000 : ℝ), (2880647115097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402710789/10000000000 : ℝ)|^4331 ≤ (279058959933/625000000000 : ℝ)^3307
        have hw : |(5402710789/10000000000 : ℝ)|=(5402710789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5057187311/10000000000 : ℝ)|^4331 ≤ (5118416353787/12500000000000 : ℝ)^3307
        have hw : |(5057187311/10000000000 : ℝ)|=(5057187311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-142334303/625000000 : ℝ)|^4331 ≤ (2880647115097/20000000000000 : ℝ)^3307
        have hw : |(-142334303/625000000 : ℝ)|=(142334303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s1_3 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071780091/2500000000 : ℝ)*x 0 + (3720511981/10000000000 : ℝ)*x 1 + (2466031761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071780091/2500000000 : ℝ)^4331 ≤ (16490627393733/50000000000000 : ℝ)^3307 := by
    have hnat : (1071780091 : ℕ)^4331*50000000000000^3307 ≤ 16490627393733^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071780091 2500000000 16490627393733 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3720511981/10000000000 : ℝ)^4331 ≤ (27393117812473/100000000000000 : ℝ)^3307 := by
    have hnat : (3720511981 : ℕ)^4331*100000000000000^3307 ≤ 27393117812473^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3720511981 10000000000 27393117812473 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2466031761/5000000000 : ℝ)^4331 ≤ (4953203422947/12500000000000 : ℝ)^3307 := by
    have hnat : (2466031761 : ℕ)^4331*12500000000000^3307 ≤ 4953203422947^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2466031761 5000000000 4953203422947 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071780091/2500000000 : ℝ), (3720511981/10000000000 : ℝ), (2466031761/5000000000 : ℝ)] ![(16490627393733/50000000000000 : ℝ), (27393117812473/100000000000000 : ℝ), (4953203422947/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071780091/2500000000 : ℝ)|^4331 ≤ (16490627393733/50000000000000 : ℝ)^3307
        have hw : |(1071780091/2500000000 : ℝ)|=(1071780091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3720511981/10000000000 : ℝ)|^4331 ≤ (27393117812473/100000000000000 : ℝ)^3307
        have hw : |(3720511981/10000000000 : ℝ)|=(3720511981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2466031761/5000000000 : ℝ)|^4331 ≤ (4953203422947/12500000000000 : ℝ)^3307
        have hw : |(2466031761/5000000000 : ℝ)|=(2466031761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s1_4 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1973249657/10000000000 : ℝ)*x 0 + (5064208073/10000000000 : ℝ)*x 1 + (2811109363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1973249657/10000000000 : ℝ)^4331 ≤ (2387634380607/20000000000000 : ℝ)^3307 := by
    have hnat : (1973249657 : ℕ)^4331*20000000000000^3307 ≤ 2387634380607^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973249657 10000000000 2387634380607 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5064208073/10000000000 : ℝ)^4331 ≤ (20510897564489/50000000000000 : ℝ)^3307 := by
    have hnat : (5064208073 : ℕ)^4331*50000000000000^3307 ≤ 20510897564489^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5064208073 10000000000 20510897564489 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2811109363/5000000000 : ℝ)^4331 ≤ (4704003295147/10000000000000 : ℝ)^3307 := by
    have hnat : (2811109363 : ℕ)^4331*10000000000000^3307 ≤ 4704003295147^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2811109363 5000000000 4704003295147 10000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1973249657/10000000000 : ℝ), (5064208073/10000000000 : ℝ), (2811109363/5000000000 : ℝ)] ![(2387634380607/20000000000000 : ℝ), (20510897564489/50000000000000 : ℝ), (4704003295147/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1973249657/10000000000 : ℝ)|^4331 ≤ (2387634380607/20000000000000 : ℝ)^3307
        have hw : |(-1973249657/10000000000 : ℝ)|=(1973249657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5064208073/10000000000 : ℝ)|^4331 ≤ (20510897564489/50000000000000 : ℝ)^3307
        have hw : |(5064208073/10000000000 : ℝ)|=(5064208073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2811109363/5000000000 : ℝ)|^4331 ≤ (4704003295147/10000000000000 : ℝ)^3307
        have hw : |(2811109363/5000000000 : ℝ)|=(2811109363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s1_5 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253884623/10000000000 : ℝ)*x 0 + (-856158759/5000000000 : ℝ)*x 1 + (1124443763/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253884623/10000000000 : ℝ)^4331 ≤ (8609112524639/20000000000000 : ℝ)^3307 := by
    have hnat : (5253884623 : ℕ)^4331*20000000000000^3307 ≤ 8609112524639^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253884623 10000000000 8609112524639 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (856158759/5000000000 : ℝ)^4331 ≤ (9914403425657/100000000000000 : ℝ)^3307 := by
    have hnat : (856158759 : ℕ)^4331*100000000000000^3307 ≤ 9914403425657^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856158759 5000000000 9914403425657 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124443763/2000000000 : ℝ)^4331 ≤ (47040033926693/100000000000000 : ℝ)^3307 := by
    have hnat : (1124443763 : ℕ)^4331*100000000000000^3307 ≤ 47040033926693^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124443763 2000000000 47040033926693 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253884623/10000000000 : ℝ), (-856158759/5000000000 : ℝ), (1124443763/2000000000 : ℝ)] ![(8609112524639/20000000000000 : ℝ), (9914403425657/100000000000000 : ℝ), (47040033926693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253884623/10000000000 : ℝ)|^4331 ≤ (8609112524639/20000000000000 : ℝ)^3307
        have hw : |(5253884623/10000000000 : ℝ)|=(5253884623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-856158759/5000000000 : ℝ)|^4331 ≤ (9914403425657/100000000000000 : ℝ)^3307
        have hw : |(-856158759/5000000000 : ℝ)|=(856158759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124443763/2000000000 : ℝ)|^4331 ≤ (47040033926693/100000000000000 : ℝ)^3307
        have hw : |(1124443763/2000000000 : ℝ)|=(1124443763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s1_6 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253884517/10000000000 : ℝ)*x 0 + (5622218917/10000000000 : ℝ)*x 1 + (-856158761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253884517/10000000000 : ℝ)^4331 ≤ (4304556148581/10000000000000 : ℝ)^3307 := by
    have hnat : (5253884517 : ℕ)^4331*10000000000000^3307 ≤ 4304556148581^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253884517 10000000000 4304556148581 10000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5622218917/10000000000 : ℝ)^4331 ≤ (11760008761091/25000000000000 : ℝ)^3307 := by
    have hnat : (5622218917 : ℕ)^4331*25000000000000^3307 ≤ 11760008761091^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5622218917 10000000000 11760008761091 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (856158761/5000000000 : ℝ)^4331 ≤ (9914403455989/100000000000000 : ℝ)^3307 := by
    have hnat : (856158761 : ℕ)^4331*100000000000000^3307 ≤ 9914403455989^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856158761 5000000000 9914403455989 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253884517/10000000000 : ℝ), (5622218917/10000000000 : ℝ), (-856158761/5000000000 : ℝ)] ![(4304556148581/10000000000000 : ℝ), (11760008761091/25000000000000 : ℝ), (9914403455989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253884517/10000000000 : ℝ)|^4331 ≤ (4304556148581/10000000000000 : ℝ)^3307
        have hw : |(5253884517/10000000000 : ℝ)|=(5253884517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5622218917/10000000000 : ℝ)|^4331 ≤ (11760008761091/25000000000000 : ℝ)^3307
        have hw : |(5622218917/10000000000 : ℝ)|=(5622218917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-856158761/5000000000 : ℝ)|^4331 ≤ (9914403455989/100000000000000 : ℝ)^3307
        have hw : |(-856158761/5000000000 : ℝ)|=(856158761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s1_7 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536018739/1250000000 : ℝ)*x 0 + (4917198869/10000000000 : ℝ)*x 1 + (3735639581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536018739/1250000000 : ℝ)^4331 ≤ (8247907029593/25000000000000 : ℝ)^3307 := by
    have hnat : (536018739 : ℕ)^4331*25000000000000^3307 ≤ 8247907029593^3307*1250000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536018739 1250000000 8247907029593 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4917198869/10000000000 : ℝ)^4331 ≤ (9867323348019/25000000000000 : ℝ)^3307 := by
    have hnat : (4917198869 : ℕ)^4331*25000000000000^3307 ≤ 9867323348019^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4917198869 10000000000 9867323348019 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3735639581/10000000000 : ℝ)^4331 ≤ (13769539238341/50000000000000 : ℝ)^3307 := by
    have hnat : (3735639581 : ℕ)^4331*50000000000000^3307 ≤ 13769539238341^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3735639581 10000000000 13769539238341 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536018739/1250000000 : ℝ), (4917198869/10000000000 : ℝ), (3735639581/10000000000 : ℝ)] ![(8247907029593/25000000000000 : ℝ), (9867323348019/25000000000000 : ℝ), (13769539238341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536018739/1250000000 : ℝ)|^4331 ≤ (8247907029593/25000000000000 : ℝ)^3307
        have hw : |(536018739/1250000000 : ℝ)|=(536018739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4917198869/10000000000 : ℝ)|^4331 ≤ (9867323348019/25000000000000 : ℝ)^3307
        have hw : |(4917198869/10000000000 : ℝ)|=(4917198869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3735639581/10000000000 : ℝ)|^4331 ≤ (13769539238341/50000000000000 : ℝ)^3307
        have hw : |(3735639581/10000000000 : ℝ)|=(3735639581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1371_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3333/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (163/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (3577/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1203/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3333/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (163/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3333/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (163/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3333/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (163/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3333/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (163/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3333/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (163/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3333/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (163/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (163/10000 : ℝ) ^ (2165/512 : ℝ) ≤ (2755544003207/100000000000000000000 : ℝ) := by
    have hpowers : (163/10000 : ℝ)^2165 ≤ (2755544003207/100000000000000000000 : ℝ)^512 := by
      have hnat : (163 : ℕ)^2165*100000000000000000000^512 ≤ 2755544003207^512*10000^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        163 10000 2755544003207 100000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (163/10000 : ℝ)) (X := (2755544003207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3333/12500 : ℝ) ^ (2165/512 : ℝ) ≤ (74738806708598223/20000000000000000000 : ℝ) := by
    have hpowers : (3333/12500 : ℝ)^2165 ≤ (74738806708598223/20000000000000000000 : ℝ)^512 := by
      have hnat : (3333 : ℕ)^2165*20000000000000000000^512 ≤ 74738806708598223^512*12500^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3333 12500 74738806708598223 20000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3333/12500 : ℝ)) (X := (74738806708598223/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000002755544003207/50000000000000000000 : ℝ) ≤ (5000000065165751/5000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (50000002755544003207/50000000000000000000 : ℝ)^512 ≤ (5000000065165751/5000000000000000 : ℝ)^2165 := by
      have hnat : (50000002755544003207 : ℕ)^512*5000000000000000^2165 ≤ 5000000065165751^2165*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000002755544003207 50000000000000000000 5000000065165751 5000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000065165751/5000000000000000 : ℝ)) (X := (50000002755544003207/50000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50186848394543497161/50000000000000000000 : ℝ) ≤ (250220624015529/250000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (50186848394543497161/50000000000000000000 : ℝ)^512 ≤ (250220624015529/250000000000000 : ℝ)^2165 := by
      have hnat : (50186848394543497161 : ℕ)^512*250000000000000^2165 ≤ 250220624015529^2165*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50186848394543497161 50000000000000000000 250220624015529 250000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250220624015529/250000000000000 : ℝ)) (X := (50186848394543497161/50000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10074738806708598223/10000000000000000000 : ℝ) ≤ (5008824895455409/5000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (10074738806708598223/10000000000000000000 : ℝ)^512 ≤ (5008824895455409/5000000000000000 : ℝ)^2165 := by
      have hnat : (10074738806708598223 : ℕ)^512*5000000000000000^2165 ≤ 5008824895455409^2165*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10074738806708598223 10000000000000000000 5008824895455409 5000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008824895455409/5000000000000000 : ℝ)) (X := (10074738806708598223/10000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2755544003207/100000000000000000000 : ℝ) ≤ ((62577808578993633997/62585000000000000000 : ℝ)+2*(4412415144829/1251700000000000 : ℝ)*(163/10000 : ℝ))^(2165/512 : ℝ) := by
    rw [show (62577808578993633997/62585000000000000000 : ℝ)+2*(4412415144829/1251700000000000 : ℝ)*(163/10000 : ℝ)=(5000000065165751/5000000000000000 : ℝ) by norm_num, show 1+2*(2755544003207/100000000000000000000 : ℝ)=(50000002755544003207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(74738806708598223/20000000000000000000 : ℝ)+(2755544003207/100000000000000000000 : ℝ) ≤ ((62577808578993633997/62585000000000000000 : ℝ)+(4412415144829/1251700000000000 : ℝ)*((3333/12500 : ℝ)+(163/10000 : ℝ)))^(2165/512 : ℝ) := by
    rw [show (62577808578993633997/62585000000000000000 : ℝ)+(4412415144829/1251700000000000 : ℝ)*((3333/12500 : ℝ)+(163/10000 : ℝ))=(250220624015529/250000000000000 : ℝ) by norm_num, show 1+(74738806708598223/20000000000000000000 : ℝ)+(2755544003207/100000000000000000000 : ℝ)=(50186848394543497161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(74738806708598223/20000000000000000000 : ℝ) ≤ ((62577808578993633997/62585000000000000000 : ℝ)+2*(4412415144829/1251700000000000 : ℝ)*(3333/12500 : ℝ))^(2165/512 : ℝ) := by
    rw [show (62577808578993633997/62585000000000000000 : ℝ)+2*(4412415144829/1251700000000000 : ℝ)*(3333/12500 : ℝ)=(5008824895455409/5000000000000000 : ℝ) by norm_num, show 1+2*(74738806708598223/20000000000000000000 : ℝ)=(10074738806708598223/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (62577808578993633997/62585000000000000000 : ℝ)*(X 1 0+X 2 0)+(4412415144829/1251700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (163/10000 : ℝ)) (hi := (3333/12500 : ℝ)) (c := (62577808578993633997/62585000000000000000 : ℝ)) (alpha := (4412415144829/1251700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (62577808578993633997/62585000000000000000 : ℝ)*(X 0 1+X 2 1)+(4412415144829/1251700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (163/10000 : ℝ)) (hi := (3333/12500 : ℝ)) (c := (62577808578993633997/62585000000000000000 : ℝ)) (alpha := (4412415144829/1251700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (62577808578993633997/62585000000000000000 : ℝ)*(X 0 2+X 1 2)+(4412415144829/1251700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (163/10000 : ℝ)) (hi := (3333/12500 : ℝ)) (c := (62577808578993633997/62585000000000000000 : ℝ)) (alpha := (4412415144829/1251700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-246595473/1250000000 : ℝ)*X 0 0+(5629364531/10000000000 : ℝ)*X 0 1+(2528593557/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2701355169/5000000000 : ℝ)*X 1 0+(-1138674027/5000000000 : ℝ)*X 1 1+(5057188391/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5402710789/10000000000 : ℝ)*X 2 0+(5057187311/10000000000 : ℝ)*X 2 1+(-142334303/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1071780091/2500000000 : ℝ)*X 0 0+(3720511981/10000000000 : ℝ)*X 0 1+(2466031761/5000000000 : ℝ)*X 0 2+(1071780091/2500000000 : ℝ)*X 1 0+(3720511981/10000000000 : ℝ)*X 1 1+(2466031761/5000000000 : ℝ)*X 1 2+(1071780091/2500000000 : ℝ)*X 2 0+(3720511981/10000000000 : ℝ)*X 2 1+(2466031761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1973249657/10000000000 : ℝ)*X 0 0+(5064208073/10000000000 : ℝ)*X 0 1+(2811109363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5253884623/10000000000 : ℝ)*X 1 0+(-856158759/5000000000 : ℝ)*X 1 1+(1124443763/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253884517/10000000000 : ℝ)*X 2 0+(5622218917/10000000000 : ℝ)*X 2 1+(-856158761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((536018739/1250000000 : ℝ)*X 0 0+(4917198869/10000000000 : ℝ)*X 0 1+(3735639581/10000000000 : ℝ)*X 0 2+(536018739/1250000000 : ℝ)*X 1 0+(4917198869/10000000000 : ℝ)*X 1 1+(3735639581/10000000000 : ℝ)*X 1 2+(536018739/1250000000 : ℝ)*X 2 0+(4917198869/10000000000 : ℝ)*X 2 1+(3735639581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23461646131894971506719004001/3129250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5183623/20000000000000 : ℝ)*(base16) + (1130517887/100000000000000 : ℝ)*(base19) + (1326504101/100000000000000 : ℝ)*(base23) + (163253/1250000000000 : ℝ)*(upper2) + (53309047/25000000000000 : ℝ)*(upper3) + (1286563307878963/100000000000000 : ℝ)*(major0) + (1286563307878963/100000000000000 : ℝ)*(major1) + (1286563307878963/100000000000000 : ℝ)*(major2) + (436930400523979/25000000000000 : ℝ)*(sp0) + (349546055873377/20000000000000 : ℝ)*(sp1) + (873865054649393/50000000000000 : ℝ)*(sp2) + (103173849637877/12500000000000 : ℝ)*(sp3) + (2458426743/25000000000000 : ℝ)*(sp4) + (206646717/5000000000000 : ℝ)*(sp7) + (206348732509339/25000000000000 : ℝ)*(f.failure) + (218466429475361/12500000000000 : ℝ)*(f.sum) + (116893400684067/62585000000000000000000000000 : ℝ)*base65 + (40673018410896255111/6258500000000000000000000000000000 : ℝ)*base67 + (23638373508316255111/6258500000000000000000000000000000 : ℝ)*base69 + (50385481132925255111/6258500000000000000000000000000000 : ℝ)*base71 + (143217570413783/62585000000000000000000000000 : ℝ)*base74 + (11813263582084755111/6258500000000000000000000000000000 : ℝ)*base75 + (33722568950221255111/6258500000000000000000000000000000 : ℝ)*base77 + (79740051828597255111/6258500000000000000000000000000000 : ℝ)*base79 + (66318817523613/62585000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (24680111/2500000000000000000000 : ℝ)*base90 + (24680111/2500000000000000000000 : ℝ)*base92 + (24680111/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4767277150506860801851077207/782312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61550721/100000000000000 : ℝ)*(base1) + (615473737/50000000000000 : ℝ)*(base19) + (598077991/50000000000000 : ℝ)*(base23) + (18382817/12500000000000 : ℝ)*(upper3) + (134696553/100000000000000 : ℝ)*(upper5) + (659604932859523/50000000000000 : ℝ)*(major0) + (659604932859523/50000000000000 : ℝ)*(major1) + (659604932859523/50000000000000 : ℝ)*(major2) + (6604311381/100000000000000 : ℝ)*(sp1) + (166311573/2500000000000 : ℝ)*(sp2) + (112005015909683/6250000000000 : ℝ)*(sp4) + (224009044718169/12500000000000 : ℝ)*(sp5) + (224009043048163/12500000000000 : ℝ)*(sp6) + (13224051152431/1562500000000 : ℝ)*(sp7) + (169267867061261/20000000000000 : ℝ)*(f.failure) + (112005012062763/6250000000000 : ℝ)*(f.sum) + (3209328222193/31292500000000000000000000000 : ℝ)*base66 + (4946718946286353431/3129250000000000000000000000000000 : ℝ)*base67 + (6793550484829646569/3129250000000000000000000000000000 : ℝ)*base70 + (3929651857407853431/3129250000000000000000000000000000 : ℝ)*base71 + (20516390909169/15646250000000000000000000000 : ℝ)*base74 + (16555679705772603431/3129250000000000000000000000000000 : ℝ)*base75 + (8460483626018353431/3129250000000000000000000000000000 : ℝ)*base77 + (38091515448174353431/3129250000000000000000000000000000 : ℝ)*base79 + (173800659335313/31292500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (779289/2000000000000000000000 : ℝ)*base90 + (779289/2000000000000000000000 : ℝ)*base92 + (779289/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1371_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3333/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (163/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3577/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1203/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1371_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1371_s2_0 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2010457251/10000000000 : ℝ)*x 0 + (218882837/400000000 : ℝ)*x 1 + (5190296177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010457251/10000000000 : ℝ)^4331 ≤ (3058459569153/25000000000000 : ℝ)^3307 := by
    have hnat : (2010457251 : ℕ)^4331*25000000000000^3307 ≤ 3058459569153^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010457251 10000000000 3058459569153 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218882837/400000000 : ℝ)^4331 ≤ (11350406082993/25000000000000 : ℝ)^3307 := by
    have hnat : (218882837 : ℕ)^4331*25000000000000^3307 ≤ 11350406082993^3307*400000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218882837 400000000 11350406082993 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5190296177/10000000000 : ℝ)^4331 ≤ (8472907475459/20000000000000 : ℝ)^3307 := by
    have hnat : (5190296177 : ℕ)^4331*20000000000000^3307 ≤ 8472907475459^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190296177 10000000000 8472907475459 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2010457251/10000000000 : ℝ), (218882837/400000000 : ℝ), (5190296177/10000000000 : ℝ)] ![(3058459569153/25000000000000 : ℝ), (11350406082993/25000000000000 : ℝ), (8472907475459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2010457251/10000000000 : ℝ)|^4331 ≤ (3058459569153/25000000000000 : ℝ)^3307
        have hw : |(-2010457251/10000000000 : ℝ)|=(2010457251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218882837/400000000 : ℝ)|^4331 ≤ (11350406082993/25000000000000 : ℝ)^3307
        have hw : |(218882837/400000000 : ℝ)|=(218882837/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5190296177/10000000000 : ℝ)|^4331 ≤ (8472907475459/20000000000000 : ℝ)^3307
        have hw : |(5190296177/10000000000 : ℝ)|=(5190296177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s2_1 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363946901/10000000000 : ℝ)*x 0 + (-1724663/8000000 : ℝ)*x 1 + (5190296369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363946901/10000000000 : ℝ)^4331 ≤ (11057587162637/25000000000000 : ℝ)^3307 := by
    have hnat : (5363946901 : ℕ)^4331*25000000000000^3307 ≤ 11057587162637^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363946901 10000000000 11057587162637 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1724663/8000000 : ℝ)^4331 ≤ (13405111901433/100000000000000 : ℝ)^3307 := by
    have hnat : (1724663 : ℕ)^4331*100000000000000^3307 ≤ 13405111901433^3307*8000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724663 8000000 13405111901433 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5190296369/10000000000 : ℝ)^4331 ≤ (42364539429711/100000000000000 : ℝ)^3307 := by
    have hnat : (5190296369 : ℕ)^4331*100000000000000^3307 ≤ 42364539429711^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190296369 10000000000 42364539429711 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363946901/10000000000 : ℝ), (-1724663/8000000 : ℝ), (5190296369/10000000000 : ℝ)] ![(11057587162637/25000000000000 : ℝ), (13405111901433/100000000000000 : ℝ), (42364539429711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363946901/10000000000 : ℝ)|^4331 ≤ (11057587162637/25000000000000 : ℝ)^3307
        have hw : |(5363946901/10000000000 : ℝ)|=(5363946901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1724663/8000000 : ℝ)|^4331 ≤ (13405111901433/100000000000000 : ℝ)^3307
        have hw : |(-1724663/8000000 : ℝ)|=(1724663/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5190296369/10000000000 : ℝ)|^4331 ≤ (42364539429711/100000000000000 : ℝ)^3307
        have hw : |(5190296369/10000000000 : ℝ)|=(5190296369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s2_2 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681973443/5000000000 : ℝ)*x 0 + (519029637/1000000000 : ℝ)*x 1 + (-2155828769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681973443/5000000000 : ℝ)^4331 ≤ (44230348488561/100000000000000 : ℝ)^3307 := by
    have hnat : (2681973443 : ℕ)^4331*100000000000000^3307 ≤ 44230348488561^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681973443 5000000000 44230348488561 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519029637/1000000000 : ℝ)^4331 ≤ (42364539440401/100000000000000 : ℝ)^3307 := by
    have hnat : (519029637 : ℕ)^4331*100000000000000^3307 ≤ 42364539440401^3307*1000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519029637 1000000000 42364539440401 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2155828769/10000000000 : ℝ)^4331 ≤ (13405112056159/100000000000000 : ℝ)^3307 := by
    have hnat : (2155828769 : ℕ)^4331*100000000000000^3307 ≤ 13405112056159^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155828769 10000000000 13405112056159 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681973443/5000000000 : ℝ), (519029637/1000000000 : ℝ), (-2155828769/10000000000 : ℝ)] ![(44230348488561/100000000000000 : ℝ), (42364539440401/100000000000000 : ℝ), (13405112056159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681973443/5000000000 : ℝ)|^4331 ≤ (44230348488561/100000000000000 : ℝ)^3307
        have hw : |(2681973443/5000000000 : ℝ)|=(2681973443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519029637/1000000000 : ℝ)|^4331 ≤ (42364539440401/100000000000000 : ℝ)^3307
        have hw : |(519029637/1000000000 : ℝ)|=(519029637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2155828769/10000000000 : ℝ)|^4331 ≤ (13405112056159/100000000000000 : ℝ)^3307
        have hw : |(-2155828769/10000000000 : ℝ)|=(2155828769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s2_3 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4313564363/10000000000 : ℝ)*x 0 + (2012369027/5000000000 : ℝ)*x 1 + (231069059/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313564363/10000000000 : ℝ)^4331 ≤ (33247938553489/100000000000000 : ℝ)^3307 := by
    have hnat : (4313564363 : ℕ)^4331*100000000000000^3307 ≤ 33247938553489^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313564363 10000000000 33247938553489 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012369027/5000000000 : ℝ)^4331 ≤ (7590775247123/25000000000000 : ℝ)^3307 := by
    have hnat : (2012369027 : ℕ)^4331*25000000000000^3307 ≤ 7590775247123^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012369027 5000000000 7590775247123 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231069059/500000000 : ℝ)^4331 ≤ (3638896043643/10000000000000 : ℝ)^3307 := by
    have hnat : (231069059 : ℕ)^4331*10000000000000^3307 ≤ 3638896043643^3307*500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231069059 500000000 3638896043643 10000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313564363/10000000000 : ℝ), (2012369027/5000000000 : ℝ), (231069059/500000000 : ℝ)] ![(33247938553489/100000000000000 : ℝ), (7590775247123/25000000000000 : ℝ), (3638896043643/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313564363/10000000000 : ℝ)|^4331 ≤ (33247938553489/100000000000000 : ℝ)^3307
        have hw : |(4313564363/10000000000 : ℝ)|=(4313564363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012369027/5000000000 : ℝ)|^4331 ≤ (7590775247123/25000000000000 : ℝ)^3307
        have hw : |(2012369027/5000000000 : ℝ)|=(2012369027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(231069059/500000000 : ℝ)|^4331 ≤ (3638896043643/10000000000000 : ℝ)^3307
        have hw : |(231069059/500000000 : ℝ)|=(231069059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s2_4 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-251314419/1250000000 : ℝ)*x 0 + (2596004253/5000000000 : ℝ)*x 1 + (1094068723/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251314419/1250000000 : ℝ)^4331 ≤ (12234301304801/100000000000000 : ℝ)^3307 := by
    have hnat : (251314419 : ℕ)^4331*100000000000000^3307 ≤ 12234301304801^3307*1250000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251314419 1250000000 12234301304801 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596004253/5000000000 : ℝ)^4331 ≤ (42382842544851/100000000000000 : ℝ)^3307 := by
    have hnat : (2596004253 : ℕ)^4331*100000000000000^3307 ≤ 42382842544851^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596004253 5000000000 42382842544851 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094068723/2000000000 : ℝ)^4331 ≤ (22691428063829/50000000000000 : ℝ)^3307 := by
    have hnat : (1094068723 : ℕ)^4331*50000000000000^3307 ≤ 22691428063829^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094068723 2000000000 22691428063829 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-251314419/1250000000 : ℝ), (2596004253/5000000000 : ℝ), (1094068723/2000000000 : ℝ)] ![(12234301304801/100000000000000 : ℝ), (42382842544851/100000000000000 : ℝ), (22691428063829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-251314419/1250000000 : ℝ)|^4331 ≤ (12234301304801/100000000000000 : ℝ)^3307
        have hw : |(-251314419/1250000000 : ℝ)|=(251314419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596004253/5000000000 : ℝ)|^4331 ≤ (42382842544851/100000000000000 : ℝ)^3307
        have hw : |(2596004253/5000000000 : ℝ)|=(2596004253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1094068723/2000000000 : ℝ)|^4331 ≤ (22691428063829/50000000000000 : ℝ)^3307
        have hw : |(1094068723/2000000000 : ℝ)|=(1094068723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s2_5 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645547829/5000000000 : ℝ)*x 0 + (-1875781253/10000000000 : ℝ)*x 1 + (1367585887/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645547829/5000000000 : ℝ)^4331 ≤ (43445276095179/100000000000000 : ℝ)^3307 := by
    have hnat : (2645547829 : ℕ)^4331*100000000000000^3307 ≤ 43445276095179^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645547829 5000000000 43445276095179 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1875781253/10000000000 : ℝ)^4331 ≤ (446874739693/4000000000000 : ℝ)^3307 := by
    have hnat : (1875781253 : ℕ)^4331*4000000000000^3307 ≤ 446874739693^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875781253 10000000000 446874739693 4000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367585887/2500000000 : ℝ)^4331 ≤ (453828553997/1000000000000 : ℝ)^3307 := by
    have hnat : (1367585887 : ℕ)^4331*1000000000000^3307 ≤ 453828553997^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367585887 2500000000 453828553997 1000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645547829/5000000000 : ℝ), (-1875781253/10000000000 : ℝ), (1367585887/2500000000 : ℝ)] ![(43445276095179/100000000000000 : ℝ), (446874739693/4000000000000 : ℝ), (453828553997/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645547829/5000000000 : ℝ)|^4331 ≤ (43445276095179/100000000000000 : ℝ)^3307
        have hw : |(2645547829/5000000000 : ℝ)|=(2645547829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1875781253/10000000000 : ℝ)|^4331 ≤ (446874739693/4000000000000 : ℝ)^3307
        have hw : |(-1875781253/10000000000 : ℝ)|=(1875781253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367585887/2500000000 : ℝ)|^4331 ≤ (453828553997/1000000000000 : ℝ)^3307
        have hw : |(1367585887/2500000000 : ℝ)|=(1367585887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s2_6 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645547803/5000000000 : ℝ)*x 0 + (85474119/156250000 : ℝ)*x 1 + (-1875781229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645547803/5000000000 : ℝ)^4331 ≤ (10861318883999/25000000000000 : ℝ)^3307 := by
    have hnat : (2645547803 : ℕ)^4331*25000000000000^3307 ≤ 10861318883999^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645547803 5000000000 10861318883999 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85474119/156250000 : ℝ)^4331 ≤ (45382856138523/100000000000000 : ℝ)^3307 := by
    have hnat : (85474119 : ℕ)^4331*100000000000000^3307 ≤ 45382856138523^3307*156250000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85474119 156250000 45382856138523 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1875781229/10000000000 : ℝ)^4331 ≤ (2792967076281/25000000000000 : ℝ)^3307 := by
    have hnat : (1875781229 : ℕ)^4331*25000000000000^3307 ≤ 2792967076281^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875781229 10000000000 2792967076281 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645547803/5000000000 : ℝ), (85474119/156250000 : ℝ), (-1875781229/10000000000 : ℝ)] ![(10861318883999/25000000000000 : ℝ), (45382856138523/100000000000000 : ℝ), (2792967076281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645547803/5000000000 : ℝ)|^4331 ≤ (10861318883999/25000000000000 : ℝ)^3307
        have hw : |(2645547803/5000000000 : ℝ)|=(2645547803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85474119/156250000 : ℝ)|^4331 ≤ (45382856138523/100000000000000 : ℝ)^3307
        have hw : |(85474119/156250000 : ℝ)|=(85474119/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1875781229/10000000000 : ℝ)|^4331 ≤ (2792967076281/25000000000000 : ℝ)^3307
        have hw : |(-1875781229/10000000000 : ℝ)|=(1875781229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s2_7 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4313687563/10000000000 : ℝ)*x 0 + (4617755811/10000000000 : ℝ)*x 1 + (1007098781/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313687563/10000000000 : ℝ)^4331 ≤ (6649836438913/20000000000000 : ℝ)^3307 := by
    have hnat : (4313687563 : ℕ)^4331*20000000000000^3307 ≤ 6649836438913^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313687563 10000000000 6649836438913 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4617755811/10000000000 : ℝ)^4331 ≤ (36351579403057/100000000000000 : ℝ)^3307 := by
    have hnat : (4617755811 : ℕ)^4331*100000000000000^3307 ≤ 36351579403057^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4617755811 10000000000 36351579403057 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007098781/2500000000 : ℝ)^4331 ≤ (15199619191857/50000000000000 : ℝ)^3307 := by
    have hnat : (1007098781 : ℕ)^4331*50000000000000^3307 ≤ 15199619191857^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007098781 2500000000 15199619191857 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313687563/10000000000 : ℝ), (4617755811/10000000000 : ℝ), (1007098781/2500000000 : ℝ)] ![(6649836438913/20000000000000 : ℝ), (36351579403057/100000000000000 : ℝ), (15199619191857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313687563/10000000000 : ℝ)|^4331 ≤ (6649836438913/20000000000000 : ℝ)^3307
        have hw : |(4313687563/10000000000 : ℝ)|=(4313687563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4617755811/10000000000 : ℝ)|^4331 ≤ (36351579403057/100000000000000 : ℝ)^3307
        have hw : |(4617755811/10000000000 : ℝ)|=(4617755811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007098781/2500000000 : ℝ)|^4331 ≤ (15199619191857/50000000000000 : ℝ)^3307
        have hw : |(1007098781/2500000000 : ℝ)|=(1007098781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1371_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1203/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2007/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7997/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1203/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1203/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1203/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1203/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1203/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1203/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3577/50000 : ℝ) ^ (2165/512 : ℝ) ≤ (1433647155671127/100000000000000000000 : ℝ) := by
    have hpowers : (3577/50000 : ℝ)^2165 ≤ (1433647155671127/100000000000000000000 : ℝ)^512 := by
      have hnat : (3577 : ℕ)^2165*100000000000000000000^512 ≤ 1433647155671127^512*50000^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3577 50000 1433647155671127 100000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3577/50000 : ℝ)) (X := (1433647155671127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1203/6250 : ℝ) ^ (2165/512 : ℝ) ≤ (94191859442117697/100000000000000000000 : ℝ) := by
    have hpowers : (1203/6250 : ℝ)^2165 ≤ (94191859442117697/100000000000000000000 : ℝ)^512 := by
      have hnat : (1203 : ℕ)^2165*100000000000000000000^512 ≤ 94191859442117697^512*6250^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1203 6250 94191859442117697 100000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1203/6250 : ℝ)) (X := (94191859442117697/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001433647155671127/50000000000000000000 : ℝ) ≤ (5000033903894187/5000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (50001433647155671127/50000000000000000000 : ℝ)^512 ≤ (5000033903894187/5000000000000000 : ℝ)^2165 := by
      have hnat : (50001433647155671127 : ℕ)^512*5000000000000000^2165 ≤ 5000033903894187^2165*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001433647155671127 50000000000000000000 5000033903894187 5000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000033903894187/5000000000000000 : ℝ)) (X := (50001433647155671127/50000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12511953188324723603/12500000000000000000 : ℝ) ≤ (10002260618762781/10000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (12511953188324723603/12500000000000000000 : ℝ)^512 ≤ (10002260618762781/10000000000000000 : ℝ)^2165 := by
      have hnat : (12511953188324723603 : ℕ)^512*10000000000000000^2165 ≤ 10002260618762781^2165*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511953188324723603 12500000000000000000 10002260618762781 10000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002260618762781/10000000000000000 : ℝ)) (X := (12511953188324723603/12500000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50094191859442117697/50000000000000000000 : ℝ) ≤ (2501113357434297/2500000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (50094191859442117697/50000000000000000000 : ℝ)^512 ≤ (2501113357434297/2500000000000000 : ℝ)^2165 := by
      have hnat : (50094191859442117697 : ℕ)^512*2500000000000000^2165 ≤ 2501113357434297^2165*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50094191859442117697 50000000000000000000 2501113357434297 2500000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501113357434297/2500000000000000 : ℝ)) (X := (50094191859442117697/50000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1433647155671127/100000000000000000000 : ℝ) ≤ ((604547226639853899/604700000000000000 : ℝ)+2*(2192810974407/1209400000000000 : ℝ)*(3577/50000 : ℝ))^(2165/512 : ℝ) := by
    rw [show (604547226639853899/604700000000000000 : ℝ)+2*(2192810974407/1209400000000000 : ℝ)*(3577/50000 : ℝ)=(5000033903894187/5000000000000000 : ℝ) by norm_num, show 1+2*(1433647155671127/100000000000000000000 : ℝ)=(50001433647155671127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(94191859442117697/100000000000000000000 : ℝ)+(1433647155671127/100000000000000000000 : ℝ) ≤ ((604547226639853899/604700000000000000 : ℝ)+(2192810974407/1209400000000000 : ℝ)*((1203/6250 : ℝ)+(3577/50000 : ℝ)))^(2165/512 : ℝ) := by
    rw [show (604547226639853899/604700000000000000 : ℝ)+(2192810974407/1209400000000000 : ℝ)*((1203/6250 : ℝ)+(3577/50000 : ℝ))=(10002260618762781/10000000000000000 : ℝ) by norm_num, show 1+(94191859442117697/100000000000000000000 : ℝ)+(1433647155671127/100000000000000000000 : ℝ)=(12511953188324723603/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(94191859442117697/100000000000000000000 : ℝ) ≤ ((604547226639853899/604700000000000000 : ℝ)+2*(2192810974407/1209400000000000 : ℝ)*(1203/6250 : ℝ))^(2165/512 : ℝ) := by
    rw [show (604547226639853899/604700000000000000 : ℝ)+2*(2192810974407/1209400000000000 : ℝ)*(1203/6250 : ℝ)=(2501113357434297/2500000000000000 : ℝ) by norm_num, show 1+2*(94191859442117697/100000000000000000000 : ℝ)=(50094191859442117697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (604547226639853899/604700000000000000 : ℝ)*(X 1 0+X 2 0)+(2192810974407/1209400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (3577/50000 : ℝ)) (hi := (1203/6250 : ℝ)) (c := (604547226639853899/604700000000000000 : ℝ)) (alpha := (2192810974407/1209400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (604547226639853899/604700000000000000 : ℝ)*(X 0 1+X 2 1)+(2192810974407/1209400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (3577/50000 : ℝ)) (hi := (1203/6250 : ℝ)) (c := (604547226639853899/604700000000000000 : ℝ)) (alpha := (2192810974407/1209400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (604547226639853899/604700000000000000 : ℝ)*(X 0 2+X 1 2)+(2192810974407/1209400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (3577/50000 : ℝ)) (hi := (1203/6250 : ℝ)) (c := (604547226639853899/604700000000000000 : ℝ)) (alpha := (2192810974407/1209400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2010457251/10000000000 : ℝ)*X 0 0+(218882837/400000000 : ℝ)*X 0 1+(5190296177/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363946901/10000000000 : ℝ)*X 1 0+(-1724663/8000000 : ℝ)*X 1 1+(5190296369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681973443/5000000000 : ℝ)*X 2 0+(519029637/1000000000 : ℝ)*X 2 1+(-2155828769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4313564363/10000000000 : ℝ)*X 0 0+(2012369027/5000000000 : ℝ)*X 0 1+(231069059/500000000 : ℝ)*X 0 2+(4313564363/10000000000 : ℝ)*X 1 0+(2012369027/5000000000 : ℝ)*X 1 1+(231069059/500000000 : ℝ)*X 1 2+(4313564363/10000000000 : ℝ)*X 2 0+(2012369027/5000000000 : ℝ)*X 2 1+(231069059/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-251314419/1250000000 : ℝ)*X 0 0+(2596004253/5000000000 : ℝ)*X 0 1+(1094068723/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645547829/5000000000 : ℝ)*X 1 0+(-1875781253/10000000000 : ℝ)*X 1 1+(1367585887/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645547803/5000000000 : ℝ)*X 2 0+(85474119/156250000 : ℝ)*X 2 1+(-1875781229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313687563/10000000000 : ℝ)*X 0 0+(4617755811/10000000000 : ℝ)*X 0 1+(1007098781/2500000000 : ℝ)*X 0 2+(4313687563/10000000000 : ℝ)*X 1 0+(4617755811/10000000000 : ℝ)*X 1 1+(1007098781/2500000000 : ℝ)*X 1 2+(4313687563/10000000000 : ℝ)*X 2 0+(4617755811/10000000000 : ℝ)*X 2 1+(1007098781/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (162560018164964813948645997/15117500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94954709/5000000000000 : ℝ)*(base19) + (1777963903/100000000000000 : ℝ)*(base23) + (59650161/100000000000000 : ℝ)*(lower2) + (274302029/100000000000000 : ℝ)*(upper3) + (10449423/6250000000000 : ℝ)*(upper5) + (2612526667207849/100000000000000 : ℝ)*(major0) + (2612526667207849/100000000000000 : ℝ)*(major1) + (2612526667207849/100000000000000 : ℝ)*(major2) + (221810046939073/6250000000000 : ℝ)*(sp0) + (17744920532283/500000000000 : ℝ)*(sp1) + (887246056896719/25000000000000 : ℝ)*(sp2) + (33521093554929/2000000000000 : ℝ)*(sp3) + (25254525611/100000000000000 : ℝ)*(sp4) + (12292681729/100000000000000 : ℝ)*(sp7) + (83803348521409/5000000000000 : ℝ)*(f.failure) + (177449300277539/5000000000000 : ℝ)*(f.sum) + (12131317231847/60470000000000000000000000000 : ℝ)*base66 + (80528692563625249/60470000000000000000000000000000 : ℝ)*base68 + (711196925824734751/60470000000000000000000000000000 : ℝ)*base69 + (169174837909134751/60470000000000000000000000000000 : ℝ)*base71 + (39763372686613/60470000000000000000000000000 : ℝ)*base73 + (339483064802204751/60470000000000000000000000000000 : ℝ)*base75 + (462232320127214751/60470000000000000000000000000000 : ℝ)*base77 + (324647364495994751/60470000000000000000000000000000 : ℝ)*base79 + (410612020967103/60470000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1803459/500000000000000000000 : ℝ)*base89 + (1803459/500000000000000000000 : ℝ)*base91 + (1803459/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27584237592801648779464923/3023500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (466658983/25000000000000 : ℝ)*(base19) + (1009011207/50000000000000 : ℝ)*(base23) + (103704157/50000000000000 : ℝ)*(upper3) + (78111219/100000000000000 : ℝ)*(lower4) + (164697997/100000000000000 : ℝ)*(upper5) + (264477178161153/10000000000000 : ℝ)*(major0) + (264477178161153/10000000000000 : ℝ)*(major1) + (264477178161153/10000000000000 : ℝ)*(major2) + (4385274999/20000000000000 : ℝ)*(sp1) + (24763830963/100000000000000 : ℝ)*(sp2) + (718557885905611/20000000000000 : ℝ)*(sp4) + (3592765636517129/100000000000000 : ℝ)*(sp5) + (3592762647674679/100000000000000 : ℝ)*(sp6) + (1696753829585659/100000000000000 : ℝ)*(sp7) + (1696753829585659/100000000000000 : ℝ)*(f.failure) + (718557885905611/20000000000000 : ℝ)*(f.sum) + (873521560951/755875000000000000000000000 : ℝ)*base66 + (682663634091953/6047000000000000000000000000000 : ℝ)*base68 + (51039632183405953/6047000000000000000000000000000 : ℝ)*base70 + (23976766554496953/6047000000000000000000000000000 : ℝ)*base72 + (3312487437857/6047000000000000000000000000 : ℝ)*base73 + (72596630992439953/6047000000000000000000000000000 : ℝ)*base76 + (8858814934301953/6047000000000000000000000000000 : ℝ)*base78 + (78927020382059953/6047000000000000000000000000000 : ℝ)*base80 + (939868157119/1209400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (17219791/10000000000000000000000 : ℝ)*base90 + (17219791/10000000000000000000000 : ℝ)*base92 + (17219791/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1371_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1203/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2007/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7997/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1371_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1371_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2007/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7997/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1371_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1371_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1371_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2007/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7997/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1371_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
