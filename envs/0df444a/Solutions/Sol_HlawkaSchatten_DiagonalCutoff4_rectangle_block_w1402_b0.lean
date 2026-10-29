-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1402_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:45:33.455934+00:00
-- url     : https://prove2.me/submissions/cdb2f374-11e8-4a29-b326-0ecafc1c2518

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
theorem support_rectangle_w1402_s0_0 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1774202311/10000000000 : ℝ)*x 0 + (5971402913/10000000000 : ℝ)*x 1 + (965004239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1774202311/10000000000 : ℝ)^2181 ≤ (1304756459421/12500000000000 : ℝ)^1669 := by
    have hnat : (1774202311 : ℕ)^2181*12500000000000^1669 ≤ 1304756459421^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774202311 10000000000 1304756459421 12500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5971402913/10000000000 : ℝ)^2181 ≤ (50978048798211/100000000000000 : ℝ)^1669 := by
    have hnat : (5971402913 : ℕ)^2181*100000000000000^1669 ≤ 50978048798211^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5971402913 10000000000 50978048798211 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965004239/2000000000 : ℝ)^2181 ≤ (7716779902103/20000000000000 : ℝ)^1669 := by
    have hnat : (965004239 : ℕ)^2181*20000000000000^1669 ≤ 7716779902103^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965004239 2000000000 7716779902103 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1774202311/10000000000 : ℝ), (5971402913/10000000000 : ℝ), (965004239/2000000000 : ℝ)] ![(1304756459421/12500000000000 : ℝ), (50978048798211/100000000000000 : ℝ), (7716779902103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1774202311/10000000000 : ℝ)|^2181 ≤ (1304756459421/12500000000000 : ℝ)^1669
        have hw : |(-1774202311/10000000000 : ℝ)|=(1774202311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5971402913/10000000000 : ℝ)|^2181 ≤ (50978048798211/100000000000000 : ℝ)^1669
        have hw : |(5971402913/10000000000 : ℝ)|=(5971402913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(965004239/2000000000 : ℝ)|^2181 ≤ (7716779902103/20000000000000 : ℝ)^1669
        have hw : |(965004239/2000000000 : ℝ)|=(965004239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s0_1 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1099021257/2000000000 : ℝ)*x 0 + (-605752839/2500000000 : ℝ)*x 1 + (965004289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099021257/2000000000 : ℝ)^2181 ≤ (45730761007011/100000000000000 : ℝ)^1669 := by
    have hnat : (1099021257 : ℕ)^2181*100000000000000^1669 ≤ 45730761007011^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099021257 2000000000 45730761007011 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605752839/2500000000 : ℝ)^2181 ≤ (15685336853469/100000000000000 : ℝ)^1669 := by
    have hnat : (605752839 : ℕ)^2181*100000000000000^1669 ≤ 15685336853469^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605752839 2500000000 15685336853469 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965004289/2000000000 : ℝ)^2181 ≤ (7716780424591/20000000000000 : ℝ)^1669 := by
    have hnat : (965004289 : ℕ)^2181*20000000000000^1669 ≤ 7716780424591^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965004289 2000000000 7716780424591 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099021257/2000000000 : ℝ), (-605752839/2500000000 : ℝ), (965004289/2000000000 : ℝ)] ![(45730761007011/100000000000000 : ℝ), (15685336853469/100000000000000 : ℝ), (7716780424591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099021257/2000000000 : ℝ)|^2181 ≤ (45730761007011/100000000000000 : ℝ)^1669
        have hw : |(1099021257/2000000000 : ℝ)|=(1099021257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-605752839/2500000000 : ℝ)|^2181 ≤ (15685336853469/100000000000000 : ℝ)^1669
        have hw : |(-605752839/2500000000 : ℝ)|=(605752839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(965004289/2000000000 : ℝ)|^2181 ≤ (7716780424591/20000000000000 : ℝ)^1669
        have hw : |(965004289/2000000000 : ℝ)|=(965004289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s0_2 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5495106461/10000000000 : ℝ)*x 0 + (4825021347/10000000000 : ℝ)*x 1 + (-2423011251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5495106461/10000000000 : ℝ)^2181 ≤ (22865381460511/50000000000000 : ℝ)^1669 := by
    have hnat : (5495106461 : ℕ)^2181*50000000000000^1669 ≤ 22865381460511^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495106461 10000000000 22865381460511 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4825021347/10000000000 : ℝ)^2181 ≤ (19291950549439/50000000000000 : ℝ)^1669 := by
    have hnat : (4825021347 : ℕ)^2181*50000000000000^1669 ≤ 19291950549439^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4825021347 10000000000 19291950549439 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2423011251/10000000000 : ℝ)^2181 ≤ (3921333991309/25000000000000 : ℝ)^1669 := by
    have hnat : (2423011251 : ℕ)^2181*25000000000000^1669 ≤ 3921333991309^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423011251 10000000000 3921333991309 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5495106461/10000000000 : ℝ), (4825021347/10000000000 : ℝ), (-2423011251/10000000000 : ℝ)] ![(22865381460511/50000000000000 : ℝ), (19291950549439/50000000000000 : ℝ), (3921333991309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5495106461/10000000000 : ℝ)|^2181 ≤ (22865381460511/50000000000000 : ℝ)^1669
        have hw : |(5495106461/10000000000 : ℝ)|=(5495106461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4825021347/10000000000 : ℝ)|^2181 ≤ (19291950549439/50000000000000 : ℝ)^1669
        have hw : |(4825021347/10000000000 : ℝ)|=(4825021347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2423011251/10000000000 : ℝ)|^2181 ≤ (3921333991309/25000000000000 : ℝ)^1669
        have hw : |(-2423011251/10000000000 : ℝ)|=(2423011251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s0_3 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4169898511/10000000000 : ℝ)*x 0 + (3104122273/10000000000 : ℝ)*x 1 + (5559617541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169898511/10000000000 : ℝ)^2181 ≤ (3188534952537/10000000000000 : ℝ)^1669 := by
    have hnat : (4169898511 : ℕ)^2181*10000000000000^1669 ≤ 3188534952537^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169898511 10000000000 3188534952537 10000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104122273/10000000000 : ℝ)^2181 ≤ (677533305477/3125000000000 : ℝ)^1669 := by
    have hnat : (3104122273 : ℕ)^2181*3125000000000^1669 ≤ 677533305477^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104122273 10000000000 677533305477 3125000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5559617541/10000000000 : ℝ)^2181 ≤ (46433584685421/100000000000000 : ℝ)^1669 := by
    have hnat : (5559617541 : ℕ)^2181*100000000000000^1669 ≤ 46433584685421^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5559617541 10000000000 46433584685421 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169898511/10000000000 : ℝ), (3104122273/10000000000 : ℝ), (5559617541/10000000000 : ℝ)] ![(3188534952537/10000000000000 : ℝ), (677533305477/3125000000000 : ℝ), (46433584685421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169898511/10000000000 : ℝ)|^2181 ≤ (3188534952537/10000000000000 : ℝ)^1669
        have hw : |(4169898511/10000000000 : ℝ)|=(4169898511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104122273/10000000000 : ℝ)|^2181 ≤ (677533305477/3125000000000 : ℝ)^1669
        have hw : |(3104122273/10000000000 : ℝ)|=(3104122273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5559617541/10000000000 : ℝ)|^2181 ≤ (46433584685421/100000000000000 : ℝ)^1669
        have hw : |(5559617541/10000000000 : ℝ)|=(5559617541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s0_4 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-355670463/2000000000 : ℝ)*x 0 + (75850173/156250000 : ℝ)*x 1 + (2970481479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (355670463/2000000000 : ℝ)^2181 ≤ (10469968512729/100000000000000 : ℝ)^1669 := by
    have hnat : (355670463 : ℕ)^2181*100000000000000^1669 ≤ 10469968512729^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355670463 2000000000 10469968512729 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75850173/156250000 : ℝ)^2181 ≤ (19445651569231/50000000000000 : ℝ)^1669 := by
    have hnat : (75850173 : ℕ)^2181*50000000000000^1669 ≤ 19445651569231^1669*156250000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75850173 156250000 19445651569231 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2970481479/5000000000 : ℝ)^2181 ≤ (12659682082203/25000000000000 : ℝ)^1669 := by
    have hnat : (2970481479 : ℕ)^2181*25000000000000^1669 ≤ 12659682082203^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2970481479 5000000000 12659682082203 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-355670463/2000000000 : ℝ), (75850173/156250000 : ℝ), (2970481479/5000000000 : ℝ)] ![(10469968512729/100000000000000 : ℝ), (19445651569231/50000000000000 : ℝ), (12659682082203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-355670463/2000000000 : ℝ)|^2181 ≤ (10469968512729/100000000000000 : ℝ)^1669
        have hw : |(-355670463/2000000000 : ℝ)|=(355670463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(75850173/156250000 : ℝ)|^2181 ≤ (19445651569231/50000000000000 : ℝ)^1669
        have hw : |(75850173/156250000 : ℝ)|=(75850173/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2970481479/5000000000 : ℝ)|^2181 ≤ (12659682082203/25000000000000 : ℝ)^1669
        have hw : |(2970481479/5000000000 : ℝ)|=(2970481479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s0_5 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5182345071/10000000000 : ℝ)*x 0 + (-40845893/312500000 : ℝ)*x 1 + (1485240587/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5182345071/10000000000 : ℝ)^2181 ≤ (42359558033803/100000000000000 : ℝ)^1669 := by
    have hnat : (5182345071 : ℕ)^2181*100000000000000^1669 ≤ 42359558033803^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182345071 10000000000 42359558033803 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40845893/312500000 : ℝ)^2181 ≤ (7001720416387/100000000000000 : ℝ)^1669 := by
    have hnat : (40845893 : ℕ)^2181*100000000000000^1669 ≤ 7001720416387^1669*312500000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40845893 312500000 7001720416387 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1485240587/2500000000 : ℝ)^2181 ≤ (1012774430687/2000000000000 : ℝ)^1669 := by
    have hnat : (1485240587 : ℕ)^2181*2000000000000^1669 ≤ 1012774430687^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1485240587 2500000000 1012774430687 2000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5182345071/10000000000 : ℝ), (-40845893/312500000 : ℝ), (1485240587/2500000000 : ℝ)] ![(42359558033803/100000000000000 : ℝ), (7001720416387/100000000000000 : ℝ), (1012774430687/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5182345071/10000000000 : ℝ)|^2181 ≤ (42359558033803/100000000000000 : ℝ)^1669
        have hw : |(5182345071/10000000000 : ℝ)|=(5182345071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40845893/312500000 : ℝ)|^2181 ≤ (7001720416387/100000000000000 : ℝ)^1669
        have hw : |(-40845893/312500000 : ℝ)|=(40845893/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1485240587/2500000000 : ℝ)|^2181 ≤ (1012774430687/2000000000000 : ℝ)^1669
        have hw : |(1485240587/2500000000 : ℝ)|=(1485240587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s0_6 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2591171293/5000000000 : ℝ)*x 0 + (2970482353/5000000000 : ℝ)*x 1 + (-163383577/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591171293/5000000000 : ℝ)^2181 ≤ (8471906298151/20000000000000 : ℝ)^1669 := by
    have hnat : (2591171293 : ℕ)^2181*20000000000000^1669 ≤ 8471906298151^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591171293 5000000000 8471906298151 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2970482353/5000000000 : ℝ)^2181 ≤ (50638747798847/100000000000000 : ℝ)^1669 := by
    have hnat : (2970482353 : ℕ)^2181*100000000000000^1669 ≤ 50638747798847^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2970482353 5000000000 50638747798847 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163383577/1250000000 : ℝ)^2181 ≤ (875215087049/12500000000000 : ℝ)^1669 := by
    have hnat : (163383577 : ℕ)^2181*12500000000000^1669 ≤ 875215087049^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163383577 1250000000 875215087049 12500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591171293/5000000000 : ℝ), (2970482353/5000000000 : ℝ), (-163383577/1250000000 : ℝ)] ![(8471906298151/20000000000000 : ℝ), (50638747798847/100000000000000 : ℝ), (875215087049/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591171293/5000000000 : ℝ)|^2181 ≤ (8471906298151/20000000000000 : ℝ)^1669
        have hw : |(2591171293/5000000000 : ℝ)|=(2591171293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2970482353/5000000000 : ℝ)|^2181 ≤ (50638747798847/100000000000000 : ℝ)^1669
        have hw : |(2970482353/5000000000 : ℝ)|=(2970482353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-163383577/1250000000 : ℝ)|^2181 ≤ (875215087049/12500000000000 : ℝ)^1669
        have hw : |(-163383577/1250000000 : ℝ)|=(163383577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s0_7 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (522348169/1250000000 : ℝ)*x 0 + (687083281/1250000000 : ℝ)*x 1 + (1584662387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522348169/1250000000 : ℝ)^2181 ≤ (31974178430809/100000000000000 : ℝ)^1669 := by
    have hnat : (522348169 : ℕ)^2181*100000000000000^1669 ≤ 31974178430809^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522348169 1250000000 31974178430809 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687083281/1250000000 : ℝ)^2181 ≤ (45747726436841/100000000000000 : ℝ)^1669 := by
    have hnat : (687083281 : ℕ)^2181*100000000000000^1669 ≤ 45747726436841^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687083281 1250000000 45747726436841 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584662387/5000000000 : ℝ)^2181 ≤ (2784761889433/12500000000000 : ℝ)^1669 := by
    have hnat : (1584662387 : ℕ)^2181*12500000000000^1669 ≤ 2784761889433^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584662387 5000000000 2784761889433 12500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522348169/1250000000 : ℝ), (687083281/1250000000 : ℝ), (1584662387/5000000000 : ℝ)] ![(31974178430809/100000000000000 : ℝ), (45747726436841/100000000000000 : ℝ), (2784761889433/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522348169/1250000000 : ℝ)|^2181 ≤ (31974178430809/100000000000000 : ℝ)^1669
        have hw : |(522348169/1250000000 : ℝ)|=(522348169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(687083281/1250000000 : ℝ)|^2181 ≤ (45747726436841/100000000000000 : ℝ)^1669
        have hw : |(687083281/1250000000 : ℝ)|=(687083281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1584662387/5000000000 : ℝ)|^2181 ≤ (2784761889433/12500000000000 : ℝ)^1669
        have hw : |(1584662387/5000000000 : ℝ)|=(1584662387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1402_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (371/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13223/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4361/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4361 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4361*1^1024 ≤ 0^1024*1^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4361/1024 : ℝ) ≤ (2019563176988480007/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4361 ≤ (2019563176988480007/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4361*100000000000000000000^1024 ≤ 2019563176988480007^1024*5^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2019563176988480007 100000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2019563176988480007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4361 := by
      have hnat : (1 : ℕ)^1024*1^4361 ≤ 1^4361*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102019563176988480007/100000000000000000000 : ℝ) ≤ (10047058949001511/10000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (102019563176988480007/100000000000000000000 : ℝ)^1024 ≤ (10047058949001511/10000000000000000 : ℝ)^4361 := by
      have hnat : (102019563176988480007 : ℕ)^1024*10000000000000000^4361 ≤ 10047058949001511^4361*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102019563176988480007 100000000000000000000 10047058949001511 10000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10047058949001511/10000000000000000 : ℝ)) (X := (102019563176988480007/100000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52019563176988480007/50000000000000000000 : ℝ) ≤ (5047058949001511/5000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (52019563176988480007/50000000000000000000 : ℝ)^1024 ≤ (5047058949001511/5000000000000000 : ℝ)^4361 := by
      have hnat : (52019563176988480007 : ℕ)^1024*5000000000000000^4361 ≤ 5047058949001511^4361*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52019563176988480007 50000000000000000000 5047058949001511 5000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5047058949001511/5000000000000000 : ℝ)) (X := (52019563176988480007/50000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(47058949001511/4000000000000000 : ℝ)*(0 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(47058949001511/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2019563176988480007/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(47058949001511/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4361/1024 : ℝ) := by
    rw [show (1 : ℝ)+(47058949001511/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10047058949001511/10000000000000000 : ℝ) by norm_num, show 1+(2019563176988480007/100000000000000000000 : ℝ)+(0 : ℝ)=(102019563176988480007/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2019563176988480007/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(47058949001511/4000000000000000 : ℝ)*(2/5 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(47058949001511/4000000000000000 : ℝ)*(2/5 : ℝ)=(5047058949001511/5000000000000000 : ℝ) by norm_num, show 1+2*(2019563176988480007/100000000000000000000 : ℝ)=(52019563176988480007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(47058949001511/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47058949001511/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(47058949001511/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47058949001511/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(47058949001511/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47058949001511/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1774202311/10000000000 : ℝ)*X 0 0+(5971402913/10000000000 : ℝ)*X 0 1+(965004239/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1099021257/2000000000 : ℝ)*X 1 0+(-605752839/2500000000 : ℝ)*X 1 1+(965004289/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5495106461/10000000000 : ℝ)*X 2 0+(4825021347/10000000000 : ℝ)*X 2 1+(-2423011251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4169898511/10000000000 : ℝ)*X 0 0+(3104122273/10000000000 : ℝ)*X 0 1+(5559617541/10000000000 : ℝ)*X 0 2+(4169898511/10000000000 : ℝ)*X 1 0+(3104122273/10000000000 : ℝ)*X 1 1+(5559617541/10000000000 : ℝ)*X 1 2+(4169898511/10000000000 : ℝ)*X 2 0+(3104122273/10000000000 : ℝ)*X 2 1+(5559617541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-355670463/2000000000 : ℝ)*X 0 0+(75850173/156250000 : ℝ)*X 0 1+(2970481479/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5182345071/10000000000 : ℝ)*X 1 0+(-40845893/312500000 : ℝ)*X 1 1+(1485240587/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2591171293/5000000000 : ℝ)*X 2 0+(2970482353/5000000000 : ℝ)*X 2 1+(-163383577/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((522348169/1250000000 : ℝ)*X 0 0+(687083281/1250000000 : ℝ)*X 0 1+(1584662387/5000000000 : ℝ)*X 0 2+(522348169/1250000000 : ℝ)*X 1 0+(687083281/1250000000 : ℝ)*X 1 1+(1584662387/5000000000 : ℝ)*X 1 2+(522348169/1250000000 : ℝ)*X 2 0+(687083281/1250000000 : ℝ)*X 2 1+(1584662387/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (124026495003572199771939/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7254053/100000000000000 : ℝ)*(base1) + (182304617/12500000000000 : ℝ)*(base19) + (1486375989/100000000000000 : ℝ)*(base23) + (85190487/50000000000000 : ℝ)*(upper3) + (103389393/50000000000000 : ℝ)*(upper5) + (319893745067017/50000000000000 : ℝ)*(major0) + (319893745067017/50000000000000 : ℝ)*(major1) + (319893745067017/50000000000000 : ℝ)*(major2) + (218078661615497/25000000000000 : ℝ)*(sp0) + (218079645319023/25000000000000 : ℝ)*(sp1) + (10903981916713/1250000000000 : ℝ)*(sp2) + (81450449824441/20000000000000 : ℝ)*(sp3) + (5400505093/100000000000000 : ℝ)*(sp4) + (2477467947/100000000000000 : ℝ)*(sp7) + (81450946768841/20000000000000 : ℝ)*(f.failure) + (218080009928257/25000000000000 : ℝ)*(f.sum) + (186978475662687/100000000000000000000000000000 : ℝ)*base65 + (1483096817062687/200000000000000000000000000000 : ℝ)*base67 + (1943274401862687/200000000000000000000000000000 : ℝ)*base69 + (1688216465462687/200000000000000000000000000000 : ℝ)*base71 + (501151522362687/100000000000000000000000000000 : ℝ)*base73 + (1243151964662687/200000000000000000000000000000 : ℝ)*base75 + (659181021462687/200000000000000000000000000000 : ℝ)*base77 + (106349610937313/200000000000000000000000000000 : ℝ)*base80 + (866675944962687/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (15510421/2000000000000000000000 : ℝ)*base90 + (15510421/2000000000000000000000 : ℝ)*base92 + (15510421/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23283672937700370011823/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40651227/2000000000000 : ℝ)*(base19) + (192584431/10000000000000 : ℝ)*(base23) + (50387323/12500000000000 : ℝ)*(base39) + (2121933/2000000000000 : ℝ)*(upper3) + (363622741/100000000000000 : ℝ)*(upper5) + (5273495218507/781250000000 : ℝ)*(major0) + (5273495218507/781250000000 : ℝ)*(major1) + (84375873108789/12500000000000 : ℝ)*(major2) + (2969632623/50000000000000 : ℝ)*(sp1) + (1238950989/25000000000000 : ℝ)*(sp2) + (92034021229267/10000000000000 : ℝ)*(sp4) + (920332240466073/100000000000000 : ℝ)*(sp5) + (920333733742989/100000000000000 : ℝ)*(sp6) + (10741846252439/2500000000000 : ℝ)*(sp7) + (10741846252439/2500000000000 : ℝ)*(f.failure) + (460170307695627/50000000000000 : ℝ)*(f.sum) + (75928215505411/50000000000000000000000000000 : ℝ)*base65 + (99367172380179/50000000000000000000000000000 : ℝ)*base67 + (16822923398423/3125000000000000000000000000 : ℝ)*base70 + (3452607730179/50000000000000000000000000000 : ℝ)*base71 + (263643756205411/50000000000000000000000000000 : ℝ)*base73 + (6824882807827/3125000000000000000000000000 : ℝ)*base75 + (12721864304673/3125000000000000000000000000 : ℝ)*base78 + (28636300104673/3125000000000000000000000000 : ℝ)*base80 + (3403684945327/1562500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (157259/250000000000000000000 : ℝ)*base90 + (157259/250000000000000000000 : ℝ)*base92 + (157259/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1402_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (371/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13223/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1402_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1402_s1_0 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1950397251/10000000000 : ℝ)*x 0 + (2808122679/5000000000 : ℝ)*x 1 + (2026907/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1950397251/10000000000 : ℝ)^2181 ≤ (2362564956449/20000000000000 : ℝ)^1669 := by
    have hnat : (1950397251 : ℕ)^2181*20000000000000^1669 ≤ 2362564956449^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950397251 10000000000 2362564956449 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2808122679/5000000000 : ℝ)^2181 ≤ (47052587797567/100000000000000 : ℝ)^1669 := by
    have hnat : (2808122679 : ℕ)^2181*100000000000000^1669 ≤ 47052587797567^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808122679 5000000000 47052587797567 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2026907/4000000 : ℝ)^2181 ≤ (8226917480781/20000000000000 : ℝ)^1669 := by
    have hnat : (2026907 : ℕ)^2181*20000000000000^1669 ≤ 8226917480781^1669*4000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026907 4000000 8226917480781 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1950397251/10000000000 : ℝ), (2808122679/5000000000 : ℝ), (2026907/4000000 : ℝ)] ![(2362564956449/20000000000000 : ℝ), (47052587797567/100000000000000 : ℝ), (8226917480781/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1950397251/10000000000 : ℝ)|^2181 ≤ (2362564956449/20000000000000 : ℝ)^1669
        have hw : |(-1950397251/10000000000 : ℝ)|=(1950397251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2808122679/5000000000 : ℝ)|^2181 ≤ (47052587797567/100000000000000 : ℝ)^1669
        have hw : |(2808122679/5000000000 : ℝ)|=(2808122679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2026907/4000000 : ℝ)|^2181 ≤ (8226917480781/20000000000000 : ℝ)^1669
        have hw : |(2026907/4000000 : ℝ)|=(2026907/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s1_1 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2699769441/5000000000 : ℝ)*x 0 + (-448380737/2000000000 : ℝ)*x 1 + (5067268449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699769441/5000000000 : ℝ)^2181 ≤ (44694243410809/100000000000000 : ℝ)^1669 := by
    have hnat : (2699769441 : ℕ)^2181*100000000000000^1669 ≤ 44694243410809^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699769441 5000000000 44694243410809 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448380737/2000000000 : ℝ)^2181 ≤ (14171159113821/100000000000000 : ℝ)^1669 := by
    have hnat : (448380737 : ℕ)^2181*100000000000000^1669 ≤ 14171159113821^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448380737 2000000000 14171159113821 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5067268449/10000000000 : ℝ)^2181 ≤ (20567298735439/50000000000000 : ℝ)^1669 := by
    have hnat : (5067268449 : ℕ)^2181*50000000000000^1669 ≤ 20567298735439^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5067268449 10000000000 20567298735439 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699769441/5000000000 : ℝ), (-448380737/2000000000 : ℝ), (5067268449/10000000000 : ℝ)] ![(44694243410809/100000000000000 : ℝ), (14171159113821/100000000000000 : ℝ), (20567298735439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699769441/5000000000 : ℝ)|^2181 ≤ (44694243410809/100000000000000 : ℝ)^1669
        have hw : |(2699769441/5000000000 : ℝ)|=(2699769441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-448380737/2000000000 : ℝ)|^2181 ≤ (14171159113821/100000000000000 : ℝ)^1669
        have hw : |(-448380737/2000000000 : ℝ)|=(448380737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5067268449/10000000000 : ℝ)|^2181 ≤ (20567298735439/50000000000000 : ℝ)^1669
        have hw : |(5067268449/10000000000 : ℝ)|=(5067268449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s1_2 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5399539597/10000000000 : ℝ)*x 0 + (5067267841/10000000000 : ℝ)*x 1 + (-280237941/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399539597/10000000000 : ℝ)^2181 ≤ (2234712557237/5000000000000 : ℝ)^1669 := by
    have hnat : (5399539597 : ℕ)^2181*5000000000000^1669 ≤ 2234712557237^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399539597 10000000000 2234712557237 5000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5067267841/10000000000 : ℝ)^2181 ≤ (20567295510613/50000000000000 : ℝ)^1669 := by
    have hnat : (5067267841 : ℕ)^2181*50000000000000^1669 ≤ 20567295510613^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5067267841 10000000000 20567295510613 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280237941/1250000000 : ℝ)^2181 ≤ (7085578908489/50000000000000 : ℝ)^1669 := by
    have hnat : (280237941 : ℕ)^2181*50000000000000^1669 ≤ 7085578908489^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280237941 1250000000 7085578908489 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399539597/10000000000 : ℝ), (5067267841/10000000000 : ℝ), (-280237941/1250000000 : ℝ)] ![(2234712557237/5000000000000 : ℝ), (20567295510613/50000000000000 : ℝ), (7085578908489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399539597/10000000000 : ℝ)|^2181 ≤ (2234712557237/5000000000000 : ℝ)^1669
        have hw : |(5399539597/10000000000 : ℝ)|=(5399539597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5067267841/10000000000 : ℝ)|^2181 ≤ (20567295510613/50000000000000 : ℝ)^1669
        have hw : |(5067267841/10000000000 : ℝ)|=(5067267841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-280237941/1250000000 : ℝ)|^2181 ≤ (7085578908489/50000000000000 : ℝ)^1669
        have hw : |(-280237941/1250000000 : ℝ)|=(280237941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s1_3 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267595763/625000000 : ℝ)*x 0 + (746008693/2000000000 : ℝ)*x 1 + (4905926269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267595763/625000000 : ℝ)^2181 ≤ (33005378279571/100000000000000 : ℝ)^1669 := by
    have hnat : (267595763 : ℕ)^2181*100000000000000^1669 ≤ 33005378279571^1669*625000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267595763 625000000 33005378279571 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (746008693/2000000000 : ℝ)^2181 ≤ (551262354591/2000000000000 : ℝ)^1669 := by
    have hnat : (746008693 : ℕ)^2181*2000000000000^1669 ≤ 551262354591^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746008693 2000000000 551262354591 2000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4905926269/10000000000 : ℝ)^2181 ≤ (9857875994939/25000000000000 : ℝ)^1669 := by
    have hnat : (4905926269 : ℕ)^2181*25000000000000^1669 ≤ 9857875994939^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4905926269 10000000000 9857875994939 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267595763/625000000 : ℝ), (746008693/2000000000 : ℝ), (4905926269/10000000000 : ℝ)] ![(33005378279571/100000000000000 : ℝ), (551262354591/2000000000000 : ℝ), (9857875994939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267595763/625000000 : ℝ)|^2181 ≤ (33005378279571/100000000000000 : ℝ)^1669
        have hw : |(267595763/625000000 : ℝ)|=(267595763/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(746008693/2000000000 : ℝ)|^2181 ≤ (551262354591/2000000000000 : ℝ)^1669
        have hw : |(746008693/2000000000 : ℝ)|=(746008693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4905926269/10000000000 : ℝ)|^2181 ≤ (9857875994939/25000000000000 : ℝ)^1669
        have hw : |(4905926269/10000000000 : ℝ)|=(4905926269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s1_4 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-975416953/5000000000 : ℝ)*x 0 + (1014768551/2000000000 : ℝ)*x 1 + (350597261/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975416953/5000000000 : ℝ)^2181 ≤ (1477035107361/12500000000000 : ℝ)^1669 := by
    have hnat : (975416953 : ℕ)^2181*12500000000000^1669 ≤ 1477035107361^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975416953 5000000000 1477035107361 12500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014768551/2000000000 : ℝ)^2181 ≤ (20602175723951/50000000000000 : ℝ)^1669 := by
    have hnat : (1014768551 : ℕ)^2181*50000000000000^1669 ≤ 20602175723951^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014768551 2000000000 20602175723951 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (350597261/625000000 : ℝ)^2181 ≤ (23489683840761/50000000000000 : ℝ)^1669 := by
    have hnat : (350597261 : ℕ)^2181*50000000000000^1669 ≤ 23489683840761^1669*625000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350597261 625000000 23489683840761 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975416953/5000000000 : ℝ), (1014768551/2000000000 : ℝ), (350597261/625000000 : ℝ)] ![(1477035107361/12500000000000 : ℝ), (20602175723951/50000000000000 : ℝ), (23489683840761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975416953/5000000000 : ℝ)|^2181 ≤ (1477035107361/12500000000000 : ℝ)^1669
        have hw : |(-975416953/5000000000 : ℝ)|=(975416953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1014768551/2000000000 : ℝ)|^2181 ≤ (20602175723951/50000000000000 : ℝ)^1669
        have hw : |(1014768551/2000000000 : ℝ)|=(1014768551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(350597261/625000000 : ℝ)|^2181 ≤ (23489683840761/50000000000000 : ℝ)^1669
        have hw : |(350597261/625000000 : ℝ)|=(350597261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s1_5 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2628199123/5000000000 : ℝ)*x 0 + (-339923177/2000000000 : ℝ)*x 1 + (2804778049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628199123/5000000000 : ℝ)^2181 ≤ (21576135382139/50000000000000 : ℝ)^1669 := by
    have hnat : (2628199123 : ℕ)^2181*50000000000000^1669 ≤ 21576135382139^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628199123 5000000000 21576135382139 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339923177/2000000000 : ℝ)^2181 ≤ (1233545298849/12500000000000 : ℝ)^1669 := by
    have hnat : (339923177 : ℕ)^2181*12500000000000^1669 ≤ 1233545298849^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339923177 2000000000 1233545298849 12500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2804778049/5000000000 : ℝ)^2181 ≤ (23489683413943/50000000000000 : ℝ)^1669 := by
    have hnat : (2804778049 : ℕ)^2181*50000000000000^1669 ≤ 23489683413943^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2804778049 5000000000 23489683413943 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628199123/5000000000 : ℝ), (-339923177/2000000000 : ℝ), (2804778049/5000000000 : ℝ)] ![(21576135382139/50000000000000 : ℝ), (1233545298849/12500000000000 : ℝ), (23489683413943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628199123/5000000000 : ℝ)|^2181 ≤ (21576135382139/50000000000000 : ℝ)^1669
        have hw : |(2628199123/5000000000 : ℝ)|=(2628199123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-339923177/2000000000 : ℝ)|^2181 ≤ (1233545298849/12500000000000 : ℝ)^1669
        have hw : |(-339923177/2000000000 : ℝ)|=(339923177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2804778049/5000000000 : ℝ)|^2181 ≤ (23489683413943/50000000000000 : ℝ)^1669
        have hw : |(2804778049/5000000000 : ℝ)|=(2804778049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s1_6 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2628199397/5000000000 : ℝ)*x 0 + (1121911309/2000000000 : ℝ)*x 1 + (-339922893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628199397/5000000000 : ℝ)^2181 ≤ (43152276643167/100000000000000 : ℝ)^1669 := by
    have hnat : (2628199397 : ℕ)^2181*100000000000000^1669 ≤ 43152276643167^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628199397 5000000000 43152276643167 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121911309/2000000000 : ℝ)^2181 ≤ (11744842929969/25000000000000 : ℝ)^1669 := by
    have hnat : (1121911309 : ℕ)^2181*25000000000000^1669 ≤ 11744842929969^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121911309 2000000000 11744842929969 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339922893/2000000000 : ℝ)^2181 ≤ (9868351616669/100000000000000 : ℝ)^1669 := by
    have hnat : (339922893 : ℕ)^2181*100000000000000^1669 ≤ 9868351616669^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339922893 2000000000 9868351616669 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628199397/5000000000 : ℝ), (1121911309/2000000000 : ℝ), (-339922893/2000000000 : ℝ)] ![(43152276643167/100000000000000 : ℝ), (11744842929969/25000000000000 : ℝ), (9868351616669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628199397/5000000000 : ℝ)|^2181 ≤ (43152276643167/100000000000000 : ℝ)^1669
        have hw : |(2628199397/5000000000 : ℝ)|=(2628199397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121911309/2000000000 : ℝ)|^2181 ≤ (11744842929969/25000000000000 : ℝ)^1669
        have hw : |(1121911309/2000000000 : ℝ)|=(1121911309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-339922893/2000000000 : ℝ)|^2181 ≤ (9868351616669/100000000000000 : ℝ)^1669
        have hw : |(-339922893/2000000000 : ℝ)|=(339922893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s1_7 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4282469181/10000000000 : ℝ)*x 0 + (4891841651/10000000000 : ℝ)*x 1 + (468046323/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282469181/10000000000 : ℝ)^2181 ≤ (33014817290337/100000000000000 : ℝ)^1669 := by
    have hnat : (4282469181 : ℕ)^2181*100000000000000^1669 ≤ 33014817290337^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282469181 10000000000 33014817290337 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4891841651/10000000000 : ℝ)^2181 ≤ (39283635600869/100000000000000 : ℝ)^1669 := by
    have hnat : (4891841651 : ℕ)^2181*100000000000000^1669 ≤ 39283635600869^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4891841651 10000000000 39283635600869 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468046323/1250000000 : ℝ)^2181 ≤ (6925386772213/25000000000000 : ℝ)^1669 := by
    have hnat : (468046323 : ℕ)^2181*25000000000000^1669 ≤ 6925386772213^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468046323 1250000000 6925386772213 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282469181/10000000000 : ℝ), (4891841651/10000000000 : ℝ), (468046323/1250000000 : ℝ)] ![(33014817290337/100000000000000 : ℝ), (39283635600869/100000000000000 : ℝ), (6925386772213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282469181/10000000000 : ℝ)|^2181 ≤ (33014817290337/100000000000000 : ℝ)^1669
        have hw : |(4282469181/10000000000 : ℝ)|=(4282469181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4891841651/10000000000 : ℝ)|^2181 ≤ (39283635600869/100000000000000 : ℝ)^1669
        have hw : |(4891841651/10000000000 : ℝ)|=(4891841651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(468046323/1250000000 : ℝ)|^2181 ≤ (6925386772213/25000000000000 : ℝ)^1669
        have hw : |(468046323/1250000000 : ℝ)|=(468046323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1402_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13223/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (371/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (297/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19029/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13223/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (371/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13223/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (371/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13223/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (371/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13223/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (371/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13223/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (371/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13223/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (371/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (371/20000 : ℝ) ^ (4361/1024 : ℝ) ≤ (4219315496959/100000000000000000000 : ℝ) := by
    have hpowers : (371/20000 : ℝ)^4361 ≤ (4219315496959/100000000000000000000 : ℝ)^1024 := by
      have hnat : (371 : ℕ)^4361*100000000000000000000^1024 ≤ 4219315496959^1024*20000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        371 20000 4219315496959 100000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (371/20000 : ℝ)) (X := (4219315496959/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13223/50000 : ℝ) ^ (4361/1024 : ℝ) ≤ (677147216693071/195312500000000000 : ℝ) := by
    have hpowers : (13223/50000 : ℝ)^4361 ≤ (677147216693071/195312500000000000 : ℝ)^1024 := by
      have hnat : (13223 : ℕ)^4361*195312500000000000^1024 ≤ 677147216693071^1024*50000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13223 50000 677147216693071 195312500000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13223/50000 : ℝ)) (X := (677147216693071/195312500000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000004219315496959/50000000000000000000 : ℝ) ≤ (1250000024768281/1250000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (50000004219315496959/50000000000000000000 : ℝ)^1024 ≤ (1250000024768281/1250000000000000 : ℝ)^4361 := by
      have hnat : (50000004219315496959 : ℕ)^1024*1250000000000000^4361 ≤ 1250000024768281^4361*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000004219315496959 50000000000000000000 1250000024768281 1250000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000024768281/1250000000000000 : ℝ)) (X := (50000004219315496959/50000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100346703594262349311/100000000000000000000 : ℝ) ≤ (2001626023886619/2000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (100346703594262349311/100000000000000000000 : ℝ)^1024 ≤ (2001626023886619/2000000000000000 : ℝ)^4361 := by
      have hnat : (100346703594262349311 : ℕ)^1024*2000000000000000^4361 ≤ 2001626023886619^4361*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100346703594262349311 100000000000000000000 2001626023886619 2000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001626023886619/2000000000000000 : ℝ)) (X := (100346703594262349311/100000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (98333397216693071/97656250000000000 : ℝ) ≤ (5008130020359971/5000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (98333397216693071/97656250000000000 : ℝ)^1024 ≤ (5008130020359971/5000000000000000 : ℝ)^4361 := by
      have hnat : (98333397216693071 : ℕ)^1024*5000000000000000^4361 ≤ 5008130020359971^4361*97656250000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        98333397216693071 97656250000000000 5008130020359971 5000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008130020359971/5000000000000000 : ℝ)) (X := (98333397216693071/97656250000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4219315496959/100000000000000000000 : ℝ) ≤ ((17562845918902870157/17565000000000000000 : ℝ)+2*(8129921286847/2459100000000000 : ℝ)*(371/20000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (17562845918902870157/17565000000000000000 : ℝ)+2*(8129921286847/2459100000000000 : ℝ)*(371/20000 : ℝ)=(1250000024768281/1250000000000000 : ℝ) by norm_num, show 1+2*(4219315496959/100000000000000000000 : ℝ)=(50000004219315496959/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(677147216693071/195312500000000000 : ℝ)+(4219315496959/100000000000000000000 : ℝ) ≤ ((17562845918902870157/17565000000000000000 : ℝ)+(8129921286847/2459100000000000 : ℝ)*((13223/50000 : ℝ)+(371/20000 : ℝ)))^(4361/1024 : ℝ) := by
    rw [show (17562845918902870157/17565000000000000000 : ℝ)+(8129921286847/2459100000000000 : ℝ)*((13223/50000 : ℝ)+(371/20000 : ℝ))=(2001626023886619/2000000000000000 : ℝ) by norm_num, show 1+(677147216693071/195312500000000000 : ℝ)+(4219315496959/100000000000000000000 : ℝ)=(100346703594262349311/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(677147216693071/195312500000000000 : ℝ) ≤ ((17562845918902870157/17565000000000000000 : ℝ)+2*(8129921286847/2459100000000000 : ℝ)*(13223/50000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (17562845918902870157/17565000000000000000 : ℝ)+2*(8129921286847/2459100000000000 : ℝ)*(13223/50000 : ℝ)=(5008130020359971/5000000000000000 : ℝ) by norm_num, show 1+2*(677147216693071/195312500000000000 : ℝ)=(98333397216693071/97656250000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17562845918902870157/17565000000000000000 : ℝ)*(X 1 0+X 2 0)+(8129921286847/2459100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (371/20000 : ℝ)) (hi := (13223/50000 : ℝ)) (c := (17562845918902870157/17565000000000000000 : ℝ)) (alpha := (8129921286847/2459100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17562845918902870157/17565000000000000000 : ℝ)*(X 0 1+X 2 1)+(8129921286847/2459100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (371/20000 : ℝ)) (hi := (13223/50000 : ℝ)) (c := (17562845918902870157/17565000000000000000 : ℝ)) (alpha := (8129921286847/2459100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17562845918902870157/17565000000000000000 : ℝ)*(X 0 2+X 1 2)+(8129921286847/2459100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (371/20000 : ℝ)) (hi := (13223/50000 : ℝ)) (c := (17562845918902870157/17565000000000000000 : ℝ)) (alpha := (8129921286847/2459100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1950397251/10000000000 : ℝ)*X 0 0+(2808122679/5000000000 : ℝ)*X 0 1+(2026907/4000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2699769441/5000000000 : ℝ)*X 1 0+(-448380737/2000000000 : ℝ)*X 1 1+(5067268449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5399539597/10000000000 : ℝ)*X 2 0+(5067267841/10000000000 : ℝ)*X 2 1+(-280237941/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((267595763/625000000 : ℝ)*X 0 0+(746008693/2000000000 : ℝ)*X 0 1+(4905926269/10000000000 : ℝ)*X 0 2+(267595763/625000000 : ℝ)*X 1 0+(746008693/2000000000 : ℝ)*X 1 1+(4905926269/10000000000 : ℝ)*X 1 2+(267595763/625000000 : ℝ)*X 2 0+(746008693/2000000000 : ℝ)*X 2 1+(4905926269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-975416953/5000000000 : ℝ)*X 0 0+(1014768551/2000000000 : ℝ)*X 0 1+(350597261/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628199123/5000000000 : ℝ)*X 1 0+(-339923177/2000000000 : ℝ)*X 1 1+(2804778049/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2628199397/5000000000 : ℝ)*X 2 0+(1121911309/2000000000 : ℝ)*X 2 1+(-339922893/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4282469181/10000000000 : ℝ)*X 0 0+(4891841651/10000000000 : ℝ)*X 0 1+(468046323/1250000000 : ℝ)*X 0 2+(4282469181/10000000000 : ℝ)*X 1 0+(4891841651/10000000000 : ℝ)*X 1 1+(468046323/1250000000 : ℝ)*X 1 2+(4282469181/10000000000 : ℝ)*X 2 0+(4891841651/10000000000 : ℝ)*X 2 1+(468046323/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46221736086393931376409/10246250000000000000000000000 : ℝ) := by norm_num
    linear_combination (841040951/100000000000000 : ℝ)*(base19) + (263703571/25000000000000 : ℝ)*(base23) + (25682573/50000000000000 : ℝ)*(upper3) + (14815487/100000000000000 : ℝ)*(upper4) + (76760183/50000000000000 : ℝ)*(upper5) + (1336008408857103/100000000000000 : ℝ)*(major0) + (1336008408857103/100000000000000 : ℝ)*(major1) + (1336008408857103/100000000000000 : ℝ)*(major2) + (113848424106047/6250000000000 : ℝ)*(sp0) + (1821583835442537/100000000000000 : ℝ)*(sp1) + (455395905417301/25000000000000 : ℝ)*(sp2) + (212607126375701/25000000000000 : ℝ)*(sp3) + (9890786737/100000000000000 : ℝ)*(sp4) + (3485358307/100000000000000 : ℝ)*(sp7) + (850431990861111/100000000000000 : ℝ)*(f.failure) + (56924521140109/3125000000000 : ℝ)*(f.sum) + (97261501682311/20492500000000000000000000000 : ℝ)*base65 + (14628443441699574601/4098500000000000000000000000000000 : ℝ)*base68 + (42349709326137574601/4098500000000000000000000000000000 : ℝ)*base70 + (6086895108602074601/4098500000000000000000000000000000 : ℝ)*base72 + (46458859699173/40985000000000000000000000000 : ℝ)*base74 + (25725484655863925399/4098500000000000000000000000000000 : ℝ)*base75 + (10203629430728925399/4098500000000000000000000000000000 : ℝ)*base77 + (13339511891369925399/4098500000000000000000000000000000 : ℝ)*base79 + (161064230739473/40985000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2205291/10000000000000000000000 : ℝ)*base90 + (2205291/10000000000000000000000 : ℝ)*base92 + (2205291/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (182359520679810157998041893/292750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42202889/25000000000000 : ℝ)*(base1) + (118142687/25000000000000 : ℝ)*(base19) + (155461377/20000000000000 : ℝ)*(base23) + (7361879/100000000000000 : ℝ)*(upper3) + (137167361/100000000000000 : ℝ)*(upper5) + (1369076774830649/100000000000000 : ℝ)*(major0) + (1369076774830649/100000000000000 : ℝ)*(major1) + (1369076774830649/100000000000000 : ℝ)*(major2) + (1675528197/100000000000000 : ℝ)*(sp1) + (5719646957/100000000000000 : ℝ)*(sp2) + (933336070749253/50000000000000 : ℝ)*(sp4) + (466667456147001/25000000000000 : ℝ)*(sp5) + (466666368933277/25000000000000 : ℝ)*(sp6) + (435740693699411/50000000000000 : ℝ)*(sp7) + (871481556210377/100000000000000 : ℝ)*(f.failure) + (37333439453739/2000000000000 : ℝ)*(f.sum) + (38399556168727/122955000000000000000000000000 : ℝ)*base66 + (81489906658753556749/12295500000000000000000000000000000 : ℝ)*base68 + (37024041821569556749/12295500000000000000000000000000000 : ℝ)*base70 + (58642929494497556749/12295500000000000000000000000000000 : ℝ)*base72 + (14231034073523/7684687500000000000000000000 : ℝ)*base73 + (11952232466780943251/12295500000000000000000000000000000 : ℝ)*base75 + (192074080872354056749/12295500000000000000000000000000000 : ℝ)*base78 + (14134930536647943251/12295500000000000000000000000000000 : ℝ)*base79 + (341959254361643/122955000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10207637/10000000000000000000000 : ℝ)*base90 + (10207637/10000000000000000000000 : ℝ)*base92 + (10207637/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1402_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13223/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (371/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (297/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19029/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1402_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1402_s2_0 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1985596001/10000000000 : ℝ)*x 0 + (5464409539/10000000000 : ℝ)*x 1 + (2598240159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1985596001/10000000000 : ℝ)^2181 ≤ (12092177448217/100000000000000 : ℝ)^1669 := by
    have hnat : (1985596001 : ℕ)^2181*100000000000000^1669 ≤ 12092177448217^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985596001 10000000000 12092177448217 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464409539/10000000000 : ℝ)^2181 ≤ (45397218461529/100000000000000 : ℝ)^1669 := by
    have hnat : (5464409539 : ℕ)^2181*100000000000000^1669 ≤ 45397218461529^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464409539 10000000000 45397218461529 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598240159/5000000000 : ℝ)^2181 ≤ (4251060408183/10000000000000 : ℝ)^1669 := by
    have hnat : (2598240159 : ℕ)^2181*10000000000000^1669 ≤ 4251060408183^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598240159 5000000000 4251060408183 10000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1985596001/10000000000 : ℝ), (5464409539/10000000000 : ℝ), (2598240159/5000000000 : ℝ)] ![(12092177448217/100000000000000 : ℝ), (45397218461529/100000000000000 : ℝ), (4251060408183/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1985596001/10000000000 : ℝ)|^2181 ≤ (12092177448217/100000000000000 : ℝ)^1669
        have hw : |(-1985596001/10000000000 : ℝ)|=(1985596001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464409539/10000000000 : ℝ)|^2181 ≤ (45397218461529/100000000000000 : ℝ)^1669
        have hw : |(5464409539/10000000000 : ℝ)|=(5464409539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598240159/5000000000 : ℝ)|^2181 ≤ (4251060408183/10000000000000 : ℝ)^1669
        have hw : |(2598240159/5000000000 : ℝ)|=(2598240159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s2_1 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5361878533/10000000000 : ℝ)*x 0 + (-212361413/1000000000 : ℝ)*x 1 + (324780019/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361878533/10000000000 : ℝ)^2181 ≤ (172997342681/390625000000 : ℝ)^1669 := by
    have hnat : (5361878533 : ℕ)^2181*390625000000^1669 ≤ 172997342681^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361878533 10000000000 172997342681 390625000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212361413/1000000000 : ℝ)^2181 ≤ (13202076329607/100000000000000 : ℝ)^1669 := by
    have hnat : (212361413 : ℕ)^2181*100000000000000^1669 ≤ 13202076329607^1669*1000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212361413 1000000000 13202076329607 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324780019/625000000 : ℝ)^2181 ≤ (42510603932167/100000000000000 : ℝ)^1669 := by
    have hnat : (324780019 : ℕ)^2181*100000000000000^1669 ≤ 42510603932167^1669*625000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324780019 625000000 42510603932167 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361878533/10000000000 : ℝ), (-212361413/1000000000 : ℝ), (324780019/625000000 : ℝ)] ![(172997342681/390625000000 : ℝ), (13202076329607/100000000000000 : ℝ), (42510603932167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361878533/10000000000 : ℝ)|^2181 ≤ (172997342681/390625000000 : ℝ)^1669
        have hw : |(5361878533/10000000000 : ℝ)|=(5361878533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212361413/1000000000 : ℝ)|^2181 ≤ (13202076329607/100000000000000 : ℝ)^1669
        have hw : |(-212361413/1000000000 : ℝ)|=(212361413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324780019/625000000 : ℝ)|^2181 ≤ (42510603932167/100000000000000 : ℝ)^1669
        have hw : |(324780019/625000000 : ℝ)|=(324780019/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s2_2 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2680939167/5000000000 : ℝ)*x 0 + (5196480529/10000000000 : ℝ)*x 1 + (-1061807049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680939167/5000000000 : ℝ)^2181 ≤ (691989337163/1562500000000 : ℝ)^1669 := by
    have hnat : (2680939167 : ℕ)^2181*1562500000000^1669 ≤ 691989337163^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680939167 5000000000 691989337163 1562500000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196480529/10000000000 : ℝ)^2181 ≤ (4251060633747/10000000000000 : ℝ)^1669 := by
    have hnat : (5196480529 : ℕ)^2181*10000000000000^1669 ≤ 4251060633747^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196480529 10000000000 4251060633747 10000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061807049/5000000000 : ℝ)^2181 ≤ (13202076069641/100000000000000 : ℝ)^1669 := by
    have hnat : (1061807049 : ℕ)^2181*100000000000000^1669 ≤ 13202076069641^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061807049 5000000000 13202076069641 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680939167/5000000000 : ℝ), (5196480529/10000000000 : ℝ), (-1061807049/5000000000 : ℝ)] ![(691989337163/1562500000000 : ℝ), (4251060633747/10000000000000 : ℝ), (13202076069641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680939167/5000000000 : ℝ)|^2181 ≤ (691989337163/1562500000000 : ℝ)^1669
        have hw : |(2680939167/5000000000 : ℝ)|=(2680939167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196480529/10000000000 : ℝ)|^2181 ≤ (4251060633747/10000000000000 : ℝ)^1669
        have hw : |(5196480529/10000000000 : ℝ)|=(5196480529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1061807049/5000000000 : ℝ)|^2181 ≤ (13202076069641/100000000000000 : ℝ)^1669
        have hw : |(-1061807049/5000000000 : ℝ)|=(1061807049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s2_3 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4306309357/10000000000 : ℝ)*x 0 + (1007011357/2500000000 : ℝ)*x 1 + (2300968589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306309357/10000000000 : ℝ)^2181 ≤ (4156899336847/12500000000000 : ℝ)^1669 := by
    have hnat : (4306309357 : ℕ)^2181*12500000000000^1669 ≤ 4156899336847^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306309357 10000000000 4156899336847 12500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007011357/2500000000 : ℝ)^2181 ≤ (30475367452637/100000000000000 : ℝ)^1669 := by
    have hnat : (1007011357 : ℕ)^2181*100000000000000^1669 ≤ 30475367452637^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007011357 2500000000 30475367452637 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2300968589/5000000000 : ℝ)^2181 ≤ (36269437833977/100000000000000 : ℝ)^1669 := by
    have hnat : (2300968589 : ℕ)^2181*100000000000000^1669 ≤ 36269437833977^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2300968589 5000000000 36269437833977 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306309357/10000000000 : ℝ), (1007011357/2500000000 : ℝ), (2300968589/5000000000 : ℝ)] ![(4156899336847/12500000000000 : ℝ), (30475367452637/100000000000000 : ℝ), (36269437833977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306309357/10000000000 : ℝ)|^2181 ≤ (4156899336847/12500000000000 : ℝ)^1669
        have hw : |(4306309357/10000000000 : ℝ)|=(4306309357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007011357/2500000000 : ℝ)|^2181 ≤ (30475367452637/100000000000000 : ℝ)^1669
        have hw : |(1007011357/2500000000 : ℝ)|=(1007011357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2300968589/5000000000 : ℝ)|^2181 ≤ (36269437833977/100000000000000 : ℝ)^1669
        have hw : |(2300968589/5000000000 : ℝ)|=(2300968589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s2_4 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-397129313/2000000000 : ℝ)*x 0 + (5198056051/10000000000 : ℝ)*x 1 + (5462820713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397129313/2000000000 : ℝ)^2181 ≤ (6046289923227/50000000000000 : ℝ)^1669 := by
    have hnat : (397129313 : ℕ)^2181*50000000000000^1669 ≤ 6046289923227^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397129313 2000000000 6046289923227 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5198056051/10000000000 : ℝ)^2181 ≤ (42527449823893/100000000000000 : ℝ)^1669 := by
    have hnat : (5198056051 : ℕ)^2181*100000000000000^1669 ≤ 42527449823893^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198056051 10000000000 42527449823893 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462820713/10000000000 : ℝ)^2181 ≤ (11344992580073/25000000000000 : ℝ)^1669 := by
    have hnat : (5462820713 : ℕ)^2181*25000000000000^1669 ≤ 11344992580073^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462820713 10000000000 11344992580073 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397129313/2000000000 : ℝ), (5198056051/10000000000 : ℝ), (5462820713/10000000000 : ℝ)] ![(6046289923227/50000000000000 : ℝ), (42527449823893/100000000000000 : ℝ), (11344992580073/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397129313/2000000000 : ℝ)|^2181 ≤ (6046289923227/50000000000000 : ℝ)^1669
        have hw : |(-397129313/2000000000 : ℝ)|=(397129313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5198056051/10000000000 : ℝ)|^2181 ≤ (42527449823893/100000000000000 : ℝ)^1669
        have hw : |(5198056051/10000000000 : ℝ)|=(5198056051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462820713/10000000000 : ℝ)|^2181 ≤ (11344992580073/25000000000000 : ℝ)^1669
        have hw : |(5462820713/10000000000 : ℝ)|=(5462820713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s2_5 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2646194559/5000000000 : ℝ)*x 0 + (-232159291/1250000000 : ℝ)*x 1 + (273141021/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646194559/5000000000 : ℝ)^2181 ≤ (21769391054103/50000000000000 : ℝ)^1669 := by
    have hnat : (2646194559 : ℕ)^2181*50000000000000^1669 ≤ 21769391054103^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646194559 5000000000 21769391054103 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232159291/1250000000 : ℝ)^2181 ≤ (11081250748949/100000000000000 : ℝ)^1669 := by
    have hnat : (232159291 : ℕ)^2181*100000000000000^1669 ≤ 11081250748949^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232159291 1250000000 11081250748949 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273141021/500000000 : ℝ)^2181 ≤ (9075993427931/20000000000000 : ℝ)^1669 := by
    have hnat : (273141021 : ℕ)^2181*20000000000000^1669 ≤ 9075993427931^1669*500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273141021 500000000 9075993427931 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646194559/5000000000 : ℝ), (-232159291/1250000000 : ℝ), (273141021/500000000 : ℝ)] ![(21769391054103/50000000000000 : ℝ), (11081250748949/100000000000000 : ℝ), (9075993427931/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646194559/5000000000 : ℝ)|^2181 ≤ (21769391054103/50000000000000 : ℝ)^1669
        have hw : |(2646194559/5000000000 : ℝ)|=(2646194559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-232159291/1250000000 : ℝ)|^2181 ≤ (11081250748949/100000000000000 : ℝ)^1669
        have hw : |(-232159291/1250000000 : ℝ)|=(232159291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(273141021/500000000 : ℝ)|^2181 ≤ (9075993427931/20000000000000 : ℝ)^1669
        have hw : |(273141021/500000000 : ℝ)|=(273141021/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s2_6 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5292390531/10000000000 : ℝ)*x 0 + (2731410199/5000000000 : ℝ)*x 1 + (-1857272409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292390531/10000000000 : ℝ)^2181 ≤ (21769398649247/50000000000000 : ℝ)^1669 := by
    have hnat : (5292390531 : ℕ)^2181*50000000000000^1669 ≤ 21769398649247^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292390531 10000000000 21769398649247 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731410199/5000000000 : ℝ)^2181 ≤ (9075993380167/20000000000000 : ℝ)^1669 := by
    have hnat : (2731410199 : ℕ)^2181*20000000000000^1669 ≤ 9075993380167^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731410199 5000000000 9075993380167 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1857272409/10000000000 : ℝ)^2181 ≤ (5540617893521/50000000000000 : ℝ)^1669 := by
    have hnat : (1857272409 : ℕ)^2181*50000000000000^1669 ≤ 5540617893521^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857272409 10000000000 5540617893521 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292390531/10000000000 : ℝ), (2731410199/5000000000 : ℝ), (-1857272409/10000000000 : ℝ)] ![(21769398649247/50000000000000 : ℝ), (9075993380167/20000000000000 : ℝ), (5540617893521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292390531/10000000000 : ℝ)|^2181 ≤ (21769398649247/50000000000000 : ℝ)^1669
        have hw : |(5292390531/10000000000 : ℝ)|=(5292390531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731410199/5000000000 : ℝ)|^2181 ≤ (9075993380167/20000000000000 : ℝ)^1669
        have hw : |(2731410199/5000000000 : ℝ)|=(2731410199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1857272409/10000000000 : ℝ)|^2181 ≤ (5540617893521/50000000000000 : ℝ)^1669
        have hw : |(-1857272409/10000000000 : ℝ)|=(1857272409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s2_7 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2153209467/5000000000 : ℝ)*x 0 + (4598562533/10000000000 : ℝ)*x 1 + (2015724069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153209467/5000000000 : ℝ)^2181 ≤ (16628150244987/50000000000000 : ℝ)^1669 := by
    have hnat : (2153209467 : ℕ)^2181*50000000000000^1669 ≤ 16628150244987^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153209467 5000000000 16628150244987 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4598562533/10000000000 : ℝ)^2181 ≤ (36234685922221/100000000000000 : ℝ)^1669 := by
    have hnat : (4598562533 : ℕ)^2181*100000000000000^1669 ≤ 36234685922221^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4598562533 10000000000 36234685922221 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015724069/5000000000 : ℝ)^2181 ≤ (30509013582389/100000000000000 : ℝ)^1669 := by
    have hnat : (2015724069 : ℕ)^2181*100000000000000^1669 ≤ 30509013582389^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015724069 5000000000 30509013582389 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153209467/5000000000 : ℝ), (4598562533/10000000000 : ℝ), (2015724069/5000000000 : ℝ)] ![(16628150244987/50000000000000 : ℝ), (36234685922221/100000000000000 : ℝ), (30509013582389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153209467/5000000000 : ℝ)|^2181 ≤ (16628150244987/50000000000000 : ℝ)^1669
        have hw : |(2153209467/5000000000 : ℝ)|=(2153209467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4598562533/10000000000 : ℝ)|^2181 ≤ (36234685922221/100000000000000 : ℝ)^1669
        have hw : |(4598562533/10000000000 : ℝ)|=(4598562533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015724069/5000000000 : ℝ)|^2181 ≤ (30509013582389/100000000000000 : ℝ)^1669
        have hw : |(2015724069/5000000000 : ℝ)|=(2015724069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1402_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (297/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (10219/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7943/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (297/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (297/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (297/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (297/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (297/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (297/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (297/4000 : ℝ) ^ (4361/1024 : ℝ) ≤ (1550723709642019/100000000000000000000 : ℝ) := by
    have hpowers : (297/4000 : ℝ)^4361 ≤ (1550723709642019/100000000000000000000 : ℝ)^1024 := by
      have hnat : (297 : ℕ)^4361*100000000000000000000^1024 ≤ 1550723709642019^1024*4000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        297 4000 1550723709642019 100000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (297/4000 : ℝ)) (X := (1550723709642019/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19029/100000 : ℝ) ^ (4361/1024 : ℝ) ≤ (42673140164808021/50000000000000000000 : ℝ) := by
    have hpowers : (19029/100000 : ℝ)^4361 ≤ (42673140164808021/50000000000000000000 : ℝ)^1024 := by
      have hnat : (19029 : ℕ)^4361*50000000000000000000^1024 ≤ 42673140164808021^1024*100000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19029 100000 42673140164808021 50000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19029/100000 : ℝ)) (X := (42673140164808021/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001550723709642019/50000000000000000000 : ℝ) ≤ (5000036411883433/5000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (50001550723709642019/50000000000000000000 : ℝ)^1024 ≤ (5000036411883433/5000000000000000 : ℝ)^4361 := by
      have hnat : (50001550723709642019 : ℕ)^1024*5000000000000000^4361 ≤ 5000036411883433^4361*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001550723709642019 50000000000000000000 5000036411883433 5000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000036411883433/5000000000000000 : ℝ)) (X := (50001550723709642019/50000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100086897004039258061/100000000000000000000 : ℝ) ≤ (5001019868880349/5000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (100086897004039258061/100000000000000000000 : ℝ)^1024 ≤ (5001019868880349/5000000000000000 : ℝ)^4361 := by
      have hnat : (100086897004039258061 : ℕ)^1024*5000000000000000^4361 ≤ 5001019868880349^4361*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100086897004039258061 100000000000000000000 5001019868880349 5000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001019868880349/5000000000000000 : ℝ)) (X := (100086897004039258061/100000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25042673140164808021/25000000000000000000 : ℝ) ≤ (1000400665175453/1000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (25042673140164808021/25000000000000000000 : ℝ)^1024 ≤ (1000400665175453/1000000000000000 : ℝ)^4361 := by
      have hnat : (25042673140164808021 : ℕ)^1024*1000000000000000^4361 ≤ 1000400665175453^4361*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25042673140164808021 25000000000000000000 1000400665175453 1000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000400665175453/1000000000000000 : ℝ)) (X := (25042673140164808021/25000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1550723709642019/100000000000000000000 : ℝ) ≤ ((4833818182257596161/4835000000000000000 : ℝ)+2*(81954749743/48350000000000 : ℝ)*(297/4000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (4833818182257596161/4835000000000000000 : ℝ)+2*(81954749743/48350000000000 : ℝ)*(297/4000 : ℝ)=(5000036411883433/5000000000000000 : ℝ) by norm_num, show 1+2*(1550723709642019/100000000000000000000 : ℝ)=(50001550723709642019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42673140164808021/50000000000000000000 : ℝ)+(1550723709642019/100000000000000000000 : ℝ) ≤ ((4833818182257596161/4835000000000000000 : ℝ)+(81954749743/48350000000000 : ℝ)*((19029/100000 : ℝ)+(297/4000 : ℝ)))^(4361/1024 : ℝ) := by
    rw [show (4833818182257596161/4835000000000000000 : ℝ)+(81954749743/48350000000000 : ℝ)*((19029/100000 : ℝ)+(297/4000 : ℝ))=(5001019868880349/5000000000000000 : ℝ) by norm_num, show 1+(42673140164808021/50000000000000000000 : ℝ)+(1550723709642019/100000000000000000000 : ℝ)=(100086897004039258061/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42673140164808021/50000000000000000000 : ℝ) ≤ ((4833818182257596161/4835000000000000000 : ℝ)+2*(81954749743/48350000000000 : ℝ)*(19029/100000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (4833818182257596161/4835000000000000000 : ℝ)+2*(81954749743/48350000000000 : ℝ)*(19029/100000 : ℝ)=(1000400665175453/1000000000000000 : ℝ) by norm_num, show 1+2*(42673140164808021/50000000000000000000 : ℝ)=(25042673140164808021/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4833818182257596161/4835000000000000000 : ℝ)*(X 1 0+X 2 0)+(81954749743/48350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (297/4000 : ℝ)) (hi := (19029/100000 : ℝ)) (c := (4833818182257596161/4835000000000000000 : ℝ)) (alpha := (81954749743/48350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4833818182257596161/4835000000000000000 : ℝ)*(X 0 1+X 2 1)+(81954749743/48350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (297/4000 : ℝ)) (hi := (19029/100000 : ℝ)) (c := (4833818182257596161/4835000000000000000 : ℝ)) (alpha := (81954749743/48350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4833818182257596161/4835000000000000000 : ℝ)*(X 0 2+X 1 2)+(81954749743/48350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (297/4000 : ℝ)) (hi := (19029/100000 : ℝ)) (c := (4833818182257596161/4835000000000000000 : ℝ)) (alpha := (81954749743/48350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1985596001/10000000000 : ℝ)*X 0 0+(5464409539/10000000000 : ℝ)*X 0 1+(2598240159/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361878533/10000000000 : ℝ)*X 1 0+(-212361413/1000000000 : ℝ)*X 1 1+(324780019/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2680939167/5000000000 : ℝ)*X 2 0+(5196480529/10000000000 : ℝ)*X 2 1+(-1061807049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4306309357/10000000000 : ℝ)*X 0 0+(1007011357/2500000000 : ℝ)*X 0 1+(2300968589/5000000000 : ℝ)*X 0 2+(4306309357/10000000000 : ℝ)*X 1 0+(1007011357/2500000000 : ℝ)*X 1 1+(2300968589/5000000000 : ℝ)*X 1 2+(4306309357/10000000000 : ℝ)*X 2 0+(1007011357/2500000000 : ℝ)*X 2 1+(2300968589/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-397129313/2000000000 : ℝ)*X 0 0+(5198056051/10000000000 : ℝ)*X 0 1+(5462820713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646194559/5000000000 : ℝ)*X 1 0+(-232159291/1250000000 : ℝ)*X 1 1+(273141021/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5292390531/10000000000 : ℝ)*X 2 0+(2731410199/5000000000 : ℝ)*X 2 1+(-1857272409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2153209467/5000000000 : ℝ)*X 0 0+(4598562533/10000000000 : ℝ)*X 0 1+(2015724069/5000000000 : ℝ)*X 0 2+(2153209467/5000000000 : ℝ)*X 1 0+(4598562533/10000000000 : ℝ)*X 1 1+(2015724069/5000000000 : ℝ)*X 1 2+(2153209467/5000000000 : ℝ)*X 2 0+(4598562533/10000000000 : ℝ)*X 2 1+(2015724069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (185598774764660560993593819/60437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (374368921/100000000000000 : ℝ)*(base19) + (129831331/100000000000000 : ℝ)*(base23) + (56844601/100000000000000 : ℝ)*(lower2) + (106855177/100000000000000 : ℝ)*(upper3) + (1332961/6250000000000 : ℝ)*(upper5) + (1368707165340393/50000000000000 : ℝ)*(major0) + (1368707165340393/50000000000000 : ℝ)*(major1) + (1368707165340393/50000000000000 : ℝ)*(major2) + (1866166725219413/50000000000000 : ℝ)*(sp0) + (3732335619747167/100000000000000 : ℝ)*(sp1) + (933083966071189/25000000000000 : ℝ)*(sp2) + (871245159383197/50000000000000 : ℝ)*(sp3) + (1271838631/50000000000000 : ℝ)*(sp4) + (449223011/20000000000000 : ℝ)*(sp7) + (1742492564881449/100000000000000 : ℝ)*(f.failure) + (466541999264511/12500000000000 : ℝ)*(f.sum) + (4130945919453/604375000000000000000000000 : ℝ)*base66 + (1400473825540318727/241750000000000000000000000000000 : ℝ)*base68 + (2176422105988068727/241750000000000000000000000000000 : ℝ)*base70 + (1624554684533318727/241750000000000000000000000000000 : ℝ)*base72 + (24340462754899/4835000000000000000000000000 : ℝ)*base74 + (3376117189062568727/241750000000000000000000000000000 : ℝ)*base76 + (2102738721216068727/241750000000000000000000000000000 : ℝ)*base78 + (2708081361830681273/241750000000000000000000000000000 : ℝ)*base79 + (15839301097197/2417500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (55169931/10000000000000000000000 : ℝ)*base89 + (55169931/10000000000000000000000 : ℝ)*base91 + (55169931/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11946815565238261060526091/1510937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1054506073/100000000000000 : ℝ)*(base19) + (319275259/10000000000000 : ℝ)*(base23) + (230632971/100000000000000 : ℝ)*(upper3) + (313451903/100000000000000 : ℝ)*(lower4) + (16359749/20000000000000 : ℝ)*(upper5) + (69253180464629/2500000000000 : ℝ)*(major0) + (69253180464629/2500000000000 : ℝ)*(major1) + (69253180464629/2500000000000 : ℝ)*(major2) + (2574735653/50000000000000 : ℝ)*(sp1) + (46093527927/100000000000000 : ℝ)*(sp2) + (944234580458551/25000000000000 : ℝ)*(sp4) + (1888466058928413/50000000000000 : ℝ)*(sp5) + (3776889035553687/100000000000000 : ℝ)*(sp6) + (440828962943283/25000000000000 : ℝ)*(sp7) + (440828962943283/25000000000000 : ℝ)*(f.failure) + (944234580458551/25000000000000 : ℝ)*(f.sum) + (502236976381/241750000000000000000000000 : ℝ)*base66 + (107836619487610731/12087500000000000000000000000000 : ℝ)*base68 + (76935698225560731/12087500000000000000000000000000 : ℝ)*base70 + (24808667113664269/12087500000000000000000000000000 : ℝ)*base71 + (761884820383/120875000000000000000000000 : ℝ)*base74 + (120308990322610731/12087500000000000000000000000000 : ℝ)*base76 + (17266443886123231/12087500000000000000000000000000 : ℝ)*base78 + (42805535933048231/12087500000000000000000000000000 : ℝ)*base80 + (2315892425677/967000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8656823/2500000000000000000000 : ℝ)*base90 + (8656823/2500000000000000000000 : ℝ)*base92 + (8656823/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1402_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (297/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7943/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1402_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1402_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7943/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1402_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1402_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1402_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7943/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1402_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
