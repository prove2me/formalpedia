-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1287_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:32.535621+00:00
-- url     : https://prove2.me/submissions/218af3b5-e488-413d-a963-2025d17fbece

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
theorem support_rectangle_w1287_box_0 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1920699623/10000000000 : ℝ)*x 0 + (5392216007/10000000000 : ℝ)*x 1 + (5392215699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1920699623/10000000000 : ℝ)^4247 ≤ (1137110730883/10000000000000 : ℝ)^3223 := by
    have hnat : (1920699623 : ℕ)^4247*10000000000000^3223 ≤ 1137110730883^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920699623 10000000000 1137110730883 10000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392216007/10000000000 : ℝ)^4247 ≤ (22157224003659/50000000000000 : ℝ)^3223 := by
    have hnat : (5392216007 : ℕ)^4247*50000000000000^3223 ≤ 22157224003659^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392216007 10000000000 22157224003659 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392215699/10000000000 : ℝ)^4247 ≤ (44314444671897/100000000000000 : ℝ)^3223 := by
    have hnat : (5392215699 : ℕ)^4247*100000000000000^3223 ≤ 44314444671897^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392215699 10000000000 44314444671897 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1920699623/10000000000 : ℝ), (5392216007/10000000000 : ℝ), (5392215699/10000000000 : ℝ)] ![(1137110730883/10000000000000 : ℝ), (22157224003659/50000000000000 : ℝ), (44314444671897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1920699623/10000000000 : ℝ)|^4247 ≤ (1137110730883/10000000000000 : ℝ)^3223
        have hw : |(-1920699623/10000000000 : ℝ)|=(1920699623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392216007/10000000000 : ℝ)|^4247 ≤ (22157224003659/50000000000000 : ℝ)^3223
        have hw : |(5392216007/10000000000 : ℝ)|=(5392216007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392215699/10000000000 : ℝ)|^4247 ≤ (44314444671897/100000000000000 : ℝ)^3223
        have hw : |(5392215699/10000000000 : ℝ)|=(5392215699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_1 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321069229/2500000000 : ℝ)*x 0 + (-258535587/1250000000 : ℝ)*x 1 + (2696107977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321069229/2500000000 : ℝ)^4247 ≤ (43149278325417/100000000000000 : ℝ)^3223 := by
    have hnat : (1321069229 : ℕ)^4247*100000000000000^3223 ≤ 43149278325417^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321069229 2500000000 43149278325417 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258535587/1250000000 : ℝ)^4247 ≤ (12536274225227/100000000000000 : ℝ)^3223 := by
    have hnat : (258535587 : ℕ)^4247*100000000000000^3223 ≤ 12536274225227^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258535587 1250000000 12536274225227 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696107977/5000000000 : ℝ)^4247 ≤ (22157223716683/50000000000000 : ℝ)^3223 := by
    have hnat : (2696107977 : ℕ)^4247*50000000000000^3223 ≤ 22157223716683^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696107977 5000000000 22157223716683 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321069229/2500000000 : ℝ), (-258535587/1250000000 : ℝ), (2696107977/5000000000 : ℝ)] ![(43149278325417/100000000000000 : ℝ), (12536274225227/100000000000000 : ℝ), (22157223716683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321069229/2500000000 : ℝ)|^4247 ≤ (43149278325417/100000000000000 : ℝ)^3223
        have hw : |(1321069229/2500000000 : ℝ)|=(1321069229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-258535587/1250000000 : ℝ)|^4247 ≤ (12536274225227/100000000000000 : ℝ)^3223
        have hw : |(-258535587/1250000000 : ℝ)|=(258535587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696107977/5000000000 : ℝ)|^4247 ≤ (22157223716683/50000000000000 : ℝ)^3223
        have hw : |(2696107977/5000000000 : ℝ)|=(2696107977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_2 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1056855433/2000000000 : ℝ)*x 0 + (1348053989/2500000000 : ℝ)*x 1 + (-1034142179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056855433/2000000000 : ℝ)^4247 ≤ (43149281004643/100000000000000 : ℝ)^3223 := by
    have hnat : (1056855433 : ℕ)^4247*100000000000000^3223 ≤ 43149281004643^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056855433 2000000000 43149281004643 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348053989/2500000000 : ℝ)^4247 ≤ (1772577898201/4000000000000 : ℝ)^3223 := by
    have hnat : (1348053989 : ℕ)^4247*4000000000000^3223 ≤ 1772577898201^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348053989 2500000000 1772577898201 4000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034142179/5000000000 : ℝ)^4247 ≤ (12536271525643/100000000000000 : ℝ)^3223 := by
    have hnat : (1034142179 : ℕ)^4247*100000000000000^3223 ≤ 12536271525643^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034142179 5000000000 12536271525643 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056855433/2000000000 : ℝ), (1348053989/2500000000 : ℝ), (-1034142179/5000000000 : ℝ)] ![(43149281004643/100000000000000 : ℝ), (1772577898201/4000000000000 : ℝ), (12536271525643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056855433/2000000000 : ℝ)|^4247 ≤ (43149281004643/100000000000000 : ℝ)^3223
        have hw : |(1056855433/2000000000 : ℝ)|=(1056855433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348053989/2500000000 : ℝ)|^4247 ≤ (1772577898201/4000000000000 : ℝ)^3223
        have hw : |(1348053989/2500000000 : ℝ)|=(1348053989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1034142179/5000000000 : ℝ)|^4247 ≤ (12536271525643/100000000000000 : ℝ)^3223
        have hw : |(-1034142179/5000000000 : ℝ)|=(1034142179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_3 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4490764367/10000000000 : ℝ)*x 0 + (170818113/400000000 : ℝ)*x 1 + (106761321/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4490764367/10000000000 : ℝ)^4247 ≤ (34822240492063/100000000000000 : ℝ)^3223 := by
    have hnat : (4490764367 : ℕ)^4247*100000000000000^3223 ≤ 34822240492063^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490764367 10000000000 34822240492063 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170818113/400000000 : ℝ)^4247 ≤ (32588879666941/100000000000000 : ℝ)^3223 := by
    have hnat : (170818113 : ℕ)^4247*100000000000000^3223 ≤ 32588879666941^3223*400000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170818113 400000000 32588879666941 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106761321/250000000 : ℝ)^4247 ≤ (16294439908889/50000000000000 : ℝ)^3223 := by
    have hnat : (106761321 : ℕ)^4247*50000000000000^3223 ≤ 16294439908889^3223*250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106761321 250000000 16294439908889 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4490764367/10000000000 : ℝ), (170818113/400000000 : ℝ), (106761321/250000000 : ℝ)] ![(34822240492063/100000000000000 : ℝ), (32588879666941/100000000000000 : ℝ), (16294439908889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4490764367/10000000000 : ℝ)|^4247 ≤ (34822240492063/100000000000000 : ℝ)^3223
        have hw : |(4490764367/10000000000 : ℝ)|=(4490764367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170818113/400000000 : ℝ)|^4247 ≤ (32588879666941/100000000000000 : ℝ)^3223
        have hw : |(170818113/400000000 : ℝ)|=(170818113/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(106761321/250000000 : ℝ)|^4247 ≤ (16294439908889/50000000000000 : ℝ)^3223
        have hw : |(106761321/250000000 : ℝ)|=(106761321/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_4 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1133495501/5000000000 : ℝ)*x 0 + (5263557897/10000000000 : ℝ)*x 1 + (5263557439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1133495501/5000000000 : ℝ)^4247 ≤ (2829408234531/20000000000000 : ℝ)^3223 := by
    have hnat : (1133495501 : ℕ)^4247*20000000000000^3223 ≤ 2829408234531^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133495501 5000000000 2829408234531 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263557897/10000000000 : ℝ)^4247 ≤ (167681569799/390625000000 : ℝ)^3223 := by
    have hnat : (5263557897 : ℕ)^4247*390625000000^3223 ≤ 167681569799^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263557897 10000000000 167681569799 390625000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263557439/10000000000 : ℝ)^4247 ≤ (21463238473319/50000000000000 : ℝ)^3223 := by
    have hnat : (5263557439 : ℕ)^4247*50000000000000^3223 ≤ 21463238473319^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263557439 10000000000 21463238473319 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1133495501/5000000000 : ℝ), (5263557897/10000000000 : ℝ), (5263557439/10000000000 : ℝ)] ![(2829408234531/20000000000000 : ℝ), (167681569799/390625000000 : ℝ), (21463238473319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1133495501/5000000000 : ℝ)|^4247 ≤ (2829408234531/20000000000000 : ℝ)^3223
        have hw : |(-1133495501/5000000000 : ℝ)|=(1133495501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263557897/10000000000 : ℝ)|^4247 ≤ (167681569799/390625000000 : ℝ)^3223
        have hw : |(5263557897/10000000000 : ℝ)|=(5263557897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263557439/10000000000 : ℝ)|^4247 ≤ (21463238473319/50000000000000 : ℝ)^3223
        have hw : |(5263557439/10000000000 : ℝ)|=(5263557439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_5 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374857021/10000000000 : ℝ)*x 0 + (-2069828/9765625 : ℝ)*x 1 + (1052711591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374857021/10000000000 : ℝ)^4247 ≤ (44126558706603/100000000000000 : ℝ)^3223 := by
    have hnat : (5374857021 : ℕ)^4247*100000000000000^3223 ≤ 44126558706603^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374857021 10000000000 44126558706603 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069828/9765625 : ℝ)^4247 ≤ (2589391756909/20000000000000 : ℝ)^3223 := by
    have hnat : (2069828 : ℕ)^4247*20000000000000^3223 ≤ 2589391756909^3223*9765625^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069828 9765625 2589391756909 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052711591/2000000000 : ℝ)^4247 ≤ (21463241245921/50000000000000 : ℝ)^3223 := by
    have hnat : (1052711591 : ℕ)^4247*50000000000000^3223 ≤ 21463241245921^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052711591 2000000000 21463241245921 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374857021/10000000000 : ℝ), (-2069828/9765625 : ℝ), (1052711591/2000000000 : ℝ)] ![(44126558706603/100000000000000 : ℝ), (2589391756909/20000000000000 : ℝ), (21463241245921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374857021/10000000000 : ℝ)|^4247 ≤ (44126558706603/100000000000000 : ℝ)^3223
        have hw : |(5374857021/10000000000 : ℝ)|=(5374857021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069828/9765625 : ℝ)|^4247 ≤ (2589391756909/20000000000000 : ℝ)^3223
        have hw : |(-2069828/9765625 : ℝ)|=(2069828/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052711591/2000000000 : ℝ)|^4247 ≤ (21463241245921/50000000000000 : ℝ)^3223
        have hw : |(1052711591/2000000000 : ℝ)|=(1052711591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_6 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335928541/625000000 : ℝ)*x 0 + (1052711633/2000000000 : ℝ)*x 1 + (-1059752041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335928541/625000000 : ℝ)^4247 ≤ (44126554757959/100000000000000 : ℝ)^3223 := by
    have hnat : (335928541 : ℕ)^4247*100000000000000^3223 ≤ 44126554757959^3223*625000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335928541 625000000 44126554757959 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052711633/2000000000 : ℝ)^4247 ≤ (42926484748611/100000000000000 : ℝ)^3223 := by
    have hnat : (1052711633 : ℕ)^4247*100000000000000^3223 ≤ 42926484748611^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052711633 2000000000 42926484748611 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059752041/5000000000 : ℝ)^4247 ≤ (12946960474887/100000000000000 : ℝ)^3223 := by
    have hnat : (1059752041 : ℕ)^4247*100000000000000^3223 ≤ 12946960474887^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059752041 5000000000 12946960474887 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335928541/625000000 : ℝ), (1052711633/2000000000 : ℝ), (-1059752041/5000000000 : ℝ)] ![(44126554757959/100000000000000 : ℝ), (42926484748611/100000000000000 : ℝ), (12946960474887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335928541/625000000 : ℝ)|^4247 ≤ (44126554757959/100000000000000 : ℝ)^3223
        have hw : |(335928541/625000000 : ℝ)|=(335928541/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052711633/2000000000 : ℝ)|^4247 ≤ (42926484748611/100000000000000 : ℝ)^3223
        have hw : |(1052711633/2000000000 : ℝ)|=(1052711633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1059752041/5000000000 : ℝ)|^4247 ≤ (12946960474887/100000000000000 : ℝ)^3223
        have hw : |(-1059752041/5000000000 : ℝ)|=(1059752041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_7 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4190816721/10000000000 : ℝ)*x 0 + (4420370749/10000000000 : ℝ)*x 1 + (4420371463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4190816721/10000000000 : ℝ)^4247 ≤ (15895227930853/50000000000000 : ℝ)^3223 := by
    have hnat : (4190816721 : ℕ)^4247*50000000000000^3223 ≤ 15895227930853^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190816721 10000000000 15895227930853 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4420370749/10000000000 : ℝ)^4247 ≤ (17052384215153/50000000000000 : ℝ)^3223 := by
    have hnat : (4420370749 : ℕ)^4247*50000000000000^3223 ≤ 17052384215153^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420370749 10000000000 17052384215153 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4420371463/10000000000 : ℝ)^4247 ≤ (34104775689303/100000000000000 : ℝ)^3223 := by
    have hnat : (4420371463 : ℕ)^4247*100000000000000^3223 ≤ 34104775689303^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420371463 10000000000 34104775689303 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4190816721/10000000000 : ℝ), (4420370749/10000000000 : ℝ), (4420371463/10000000000 : ℝ)] ![(15895227930853/50000000000000 : ℝ), (17052384215153/50000000000000 : ℝ), (34104775689303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4190816721/10000000000 : ℝ)|^4247 ≤ (15895227930853/50000000000000 : ℝ)^3223
        have hw : |(4190816721/10000000000 : ℝ)|=(4190816721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4420370749/10000000000 : ℝ)|^4247 ≤ (17052384215153/50000000000000 : ℝ)^3223
        have hw : |(4420370749/10000000000 : ℝ)|=(4420370749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4420371463/10000000000 : ℝ)|^4247 ≤ (34104775689303/100000000000000 : ℝ)^3223
        have hw : |(4420371463/10000000000 : ℝ)|=(4420371463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_8 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097213159/5000000000 : ℝ)*x 0 + (103505087/200000000 : ℝ)*x 1 + (5406255359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097213159/5000000000 : ℝ)^4247 ≤ (2710677621917/20000000000000 : ℝ)^3223 := by
    have hnat : (1097213159 : ℕ)^4247*20000000000000^3223 ≤ 2710677621917^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097213159 5000000000 2710677621917 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103505087/200000000 : ℝ)^4247 ≤ (20990032396639/50000000000000 : ℝ)^3223 := by
    have hnat : (103505087 : ℕ)^4247*50000000000000^3223 ≤ 20990032396639^3223*200000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103505087 200000000 20990032396639 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406255359/10000000000 : ℝ)^4247 ≤ (44466547079799/100000000000000 : ℝ)^3223 := by
    have hnat : (5406255359 : ℕ)^4247*100000000000000^3223 ≤ 44466547079799^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406255359 10000000000 44466547079799 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097213159/5000000000 : ℝ), (103505087/200000000 : ℝ), (5406255359/10000000000 : ℝ)] ![(2710677621917/20000000000000 : ℝ), (20990032396639/50000000000000 : ℝ), (44466547079799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097213159/5000000000 : ℝ)|^4247 ≤ (2710677621917/20000000000000 : ℝ)^3223
        have hw : |(-1097213159/5000000000 : ℝ)|=(1097213159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103505087/200000000 : ℝ)|^4247 ≤ (20990032396639/50000000000000 : ℝ)^3223
        have hw : |(103505087/200000000 : ℝ)|=(103505087/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406255359/10000000000 : ℝ)|^4247 ≤ (44466547079799/100000000000000 : ℝ)^3223
        have hw : |(5406255359/10000000000 : ℝ)|=(5406255359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_9 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527438677/1000000000 : ℝ)*x 0 + (-128909937/625000000 : ℝ)*x 1 + (5406255063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527438677/1000000000 : ℝ)^4247 ≤ (5380361572923/12500000000000 : ℝ)^3223 := by
    have hnat : (527438677 : ℕ)^4247*12500000000000^3223 ≤ 5380361572923^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527438677 1000000000 5380361572923 12500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128909937/625000000 : ℝ)^4247 ≤ (6245281763247/50000000000000 : ℝ)^3223 := by
    have hnat : (128909937 : ℕ)^4247*50000000000000^3223 ≤ 6245281763247^3223*625000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128909937 625000000 6245281763247 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406255063/10000000000 : ℝ)^4247 ≤ (138957949599/312500000000 : ℝ)^3223 := by
    have hnat : (5406255063 : ℕ)^4247*312500000000^3223 ≤ 138957949599^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406255063 10000000000 138957949599 312500000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527438677/1000000000 : ℝ), (-128909937/625000000 : ℝ), (5406255063/10000000000 : ℝ)] ![(5380361572923/12500000000000 : ℝ), (6245281763247/50000000000000 : ℝ), (138957949599/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527438677/1000000000 : ℝ)|^4247 ≤ (5380361572923/12500000000000 : ℝ)^3223
        have hw : |(527438677/1000000000 : ℝ)|=(527438677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128909937/625000000 : ℝ)|^4247 ≤ (6245281763247/50000000000000 : ℝ)^3223
        have hw : |(-128909937/625000000 : ℝ)|=(128909937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406255063/10000000000 : ℝ)|^4247 ≤ (138957949599/312500000000 : ℝ)^3223
        have hw : |(5406255063/10000000000 : ℝ)|=(5406255063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_10 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318596671/2500000000 : ℝ)*x 0 + (2703127479/5000000000 : ℝ)*x 1 + (-8250237/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318596671/2500000000 : ℝ)^4247 ≤ (43042891658579/100000000000000 : ℝ)^3223 := by
    have hnat : (1318596671 : ℕ)^4247*100000000000000^3223 ≤ 43042891658579^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318596671 2500000000 43042891658579 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703127479/5000000000 : ℝ)^4247 ≤ (1389579460427/3125000000000 : ℝ)^3223 := by
    have hnat : (2703127479 : ℕ)^4247*3125000000000^3223 ≤ 1389579460427^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703127479 5000000000 1389579460427 3125000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8250237/40000000 : ℝ)^4247 ≤ (12490565585309/100000000000000 : ℝ)^3223 := by
    have hnat : (8250237 : ℕ)^4247*100000000000000^3223 ≤ 12490565585309^3223*40000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8250237 40000000 12490565585309 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318596671/2500000000 : ℝ), (2703127479/5000000000 : ℝ), (-8250237/40000000 : ℝ)] ![(43042891658579/100000000000000 : ℝ), (1389579460427/3125000000000 : ℝ), (12490565585309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318596671/2500000000 : ℝ)|^4247 ≤ (43042891658579/100000000000000 : ℝ)^3223
        have hw : |(1318596671/2500000000 : ℝ)|=(1318596671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703127479/5000000000 : ℝ)|^4247 ≤ (1389579460427/3125000000000 : ℝ)^3223
        have hw : |(2703127479/5000000000 : ℝ)|=(2703127479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8250237/40000000 : ℝ)|^4247 ≤ (12490565585309/100000000000000 : ℝ)^3223
        have hw : |(-8250237/40000000 : ℝ)|=(8250237/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_11 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (904586947/2000000000 : ℝ)*x 0 + (1063519971/2500000000 : ℝ)*x 1 + (132940001/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904586947/2000000000 : ℝ)^4247 ≤ (35151325103749/100000000000000 : ℝ)^3223 := by
    have hnat : (904586947 : ℕ)^4247*100000000000000^3223 ≤ 35151325103749^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904586947 2000000000 35151325103749 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063519971/2500000000 : ℝ)^4247 ≤ (16212168348907/50000000000000 : ℝ)^3223 := by
    have hnat : (1063519971 : ℕ)^4247*50000000000000^3223 ≤ 16212168348907^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063519971 2500000000 16212168348907 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132940001/312500000 : ℝ)^4247 ≤ (1621216909213/5000000000000 : ℝ)^3223 := by
    have hnat : (132940001 : ℕ)^4247*5000000000000^3223 ≤ 1621216909213^3223*312500000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132940001 312500000 1621216909213 5000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(904586947/2000000000 : ℝ), (1063519971/2500000000 : ℝ), (132940001/312500000 : ℝ)] ![(35151325103749/100000000000000 : ℝ), (16212168348907/50000000000000 : ℝ), (1621216909213/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(904586947/2000000000 : ℝ)|^4247 ≤ (35151325103749/100000000000000 : ℝ)^3223
        have hw : |(904586947/2000000000 : ℝ)|=(904586947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1063519971/2500000000 : ℝ)|^4247 ≤ (16212168348907/50000000000000 : ℝ)^3223
        have hw : |(1063519971/2500000000 : ℝ)|=(1063519971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132940001/312500000 : ℝ)|^4247 ≤ (1621216909213/5000000000000 : ℝ)^3223
        have hw : |(132940001/312500000 : ℝ)|=(132940001/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_12 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-498428291/2500000000 : ℝ)*x 0 + (5478183459/10000000000 : ℝ)*x 1 + (5252540267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498428291/2500000000 : ℝ)^4247 ≤ (11944116036361/100000000000000 : ℝ)^3223 := by
    have hnat : (498428291 : ℕ)^4247*100000000000000^3223 ≤ 11944116036361^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498428291 2500000000 11944116036361 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5478183459/10000000000 : ℝ)^4247 ≤ (22623881937949/50000000000000 : ℝ)^3223 := by
    have hnat : (5478183459 : ℕ)^4247*50000000000000^3223 ≤ 22623881937949^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478183459 10000000000 22623881937949 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252540267/10000000000 : ℝ)^4247 ≤ (42808120077999/100000000000000 : ℝ)^3223 := by
    have hnat : (5252540267 : ℕ)^4247*100000000000000^3223 ≤ 42808120077999^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252540267 10000000000 42808120077999 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-498428291/2500000000 : ℝ), (5478183459/10000000000 : ℝ), (5252540267/10000000000 : ℝ)] ![(11944116036361/100000000000000 : ℝ), (22623881937949/50000000000000 : ℝ), (42808120077999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-498428291/2500000000 : ℝ)|^4247 ≤ (11944116036361/100000000000000 : ℝ)^3223
        have hw : |(-498428291/2500000000 : ℝ)|=(498428291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5478183459/10000000000 : ℝ)|^4247 ≤ (22623881937949/50000000000000 : ℝ)^3223
        have hw : |(5478183459/10000000000 : ℝ)|=(5478183459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252540267/10000000000 : ℝ)|^4247 ≤ (42808120077999/100000000000000 : ℝ)^3223
        have hw : |(5252540267/10000000000 : ℝ)|=(5252540267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_13 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672826357/1250000000 : ℝ)*x 0 + (-2123783817/10000000000 : ℝ)*x 1 + (1313135049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672826357/1250000000 : ℝ)^4247 ≤ (44210460479483/100000000000000 : ℝ)^3223 := by
    have hnat : (672826357 : ℕ)^4247*100000000000000^3223 ≤ 44210460479483^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672826357 1250000000 44210460479483 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123783817/10000000000 : ℝ)^4247 ≤ (12981420185081/100000000000000 : ℝ)^3223 := by
    have hnat : (2123783817 : ℕ)^4247*100000000000000^3223 ≤ 12981420185081^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123783817 10000000000 12981420185081 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313135049/2500000000 : ℝ)^4247 ≤ (2675507457219/6250000000000 : ℝ)^3223 := by
    have hnat : (1313135049 : ℕ)^4247*6250000000000^3223 ≤ 2675507457219^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313135049 2500000000 2675507457219 6250000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672826357/1250000000 : ℝ), (-2123783817/10000000000 : ℝ), (1313135049/2500000000 : ℝ)] ![(44210460479483/100000000000000 : ℝ), (12981420185081/100000000000000 : ℝ), (2675507457219/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672826357/1250000000 : ℝ)|^4247 ≤ (44210460479483/100000000000000 : ℝ)^3223
        have hw : |(672826357/1250000000 : ℝ)|=(672826357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2123783817/10000000000 : ℝ)|^4247 ≤ (12981420185081/100000000000000 : ℝ)^3223
        have hw : |(-2123783817/10000000000 : ℝ)|=(2123783817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313135049/2500000000 : ℝ)|^4247 ≤ (2675507457219/6250000000000 : ℝ)^3223
        have hw : |(1313135049/2500000000 : ℝ)|=(1313135049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_14 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382610833/10000000000 : ℝ)*x 0 + (2626270101/5000000000 : ℝ)*x 1 + (-2123783841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382610833/10000000000 : ℝ)^4247 ≤ (884209204611/2000000000000 : ℝ)^3223 := by
    have hnat : (5382610833 : ℕ)^4247*2000000000000^3223 ≤ 884209204611^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382610833 10000000000 884209204611 2000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626270101/5000000000 : ℝ)^4247 ≤ (2140405968997/5000000000000 : ℝ)^3223 := by
    have hnat : (2626270101 : ℕ)^4247*5000000000000^3223 ≤ 2140405968997^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626270101 5000000000 2140405968997 5000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123783841/10000000000 : ℝ)^4247 ≤ (12981420378387/100000000000000 : ℝ)^3223 := by
    have hnat : (2123783841 : ℕ)^4247*100000000000000^3223 ≤ 12981420378387^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123783841 10000000000 12981420378387 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382610833/10000000000 : ℝ), (2626270101/5000000000 : ℝ), (-2123783841/10000000000 : ℝ)] ![(884209204611/2000000000000 : ℝ), (2140405968997/5000000000000 : ℝ), (12981420378387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382610833/10000000000 : ℝ)|^4247 ≤ (884209204611/2000000000000 : ℝ)^3223
        have hw : |(5382610833/10000000000 : ℝ)|=(5382610833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626270101/5000000000 : ℝ)|^4247 ≤ (2140405968997/5000000000000 : ℝ)^3223
        have hw : |(2626270101/5000000000 : ℝ)|=(2626270101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2123783841/10000000000 : ℝ)|^4247 ≤ (12981420378387/100000000000000 : ℝ)^3223
        have hw : |(-2123783841/10000000000 : ℝ)|=(2123783841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_box_15 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (520585577/1250000000 : ℝ)*x 0 + (4433199091/10000000000 : ℝ)*x 1 + (4433198889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520585577/1250000000 : ℝ)^4247 ≤ (31529502189503/100000000000000 : ℝ)^3223 := by
    have hnat : (520585577 : ℕ)^4247*100000000000000^3223 ≤ 31529502189503^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520585577 1250000000 31529502189503 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4433199091/10000000000 : ℝ)^4247 ≤ (34235249928571/100000000000000 : ℝ)^3223 := by
    have hnat : (4433199091 : ℕ)^4247*100000000000000^3223 ≤ 34235249928571^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433199091 10000000000 34235249928571 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4433198889/10000000000 : ℝ)^4247 ≤ (17117623936507/50000000000000 : ℝ)^3223 := by
    have hnat : (4433198889 : ℕ)^4247*50000000000000^3223 ≤ 17117623936507^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433198889 10000000000 17117623936507 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520585577/1250000000 : ℝ), (4433199091/10000000000 : ℝ), (4433198889/10000000000 : ℝ)] ![(31529502189503/100000000000000 : ℝ), (34235249928571/100000000000000 : ℝ), (17117623936507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520585577/1250000000 : ℝ)|^4247 ≤ (31529502189503/100000000000000 : ℝ)^3223
        have hw : |(520585577/1250000000 : ℝ)|=(520585577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4433199091/10000000000 : ℝ)|^4247 ≤ (34235249928571/100000000000000 : ℝ)^3223
        have hw : |(4433199091/10000000000 : ℝ)|=(4433199091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4433198889/10000000000 : ℝ)|^4247 ≤ (17117623936507/50000000000000 : ℝ)^3223
        have hw : |(4433198889/10000000000 : ℝ)|=(4433198889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1287_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31419/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14709/25000 : ℝ) ∧ (39813/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16827/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3667/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2203/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3667/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2203/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3667/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2203/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3667/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2203/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3667/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2203/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3667/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2203/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2203/20000 : ℝ) ^ (2123/512 : ℝ) ≤ (10656232915801949/100000000000000000000 : ℝ) := by
    have hpowers : (2203/20000 : ℝ)^2123 ≤ (10656232915801949/100000000000000000000 : ℝ)^512 := by
      have hnat : (2203 : ℕ)^2123*100000000000000000000^512 ≤ 10656232915801949^512*20000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2203 20000 10656232915801949 100000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2203/20000 : ℝ)) (X := (10656232915801949/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3667/25000 : ℝ) ^ (2123/512 : ℝ) ≤ (34943786854755211/100000000000000000000 : ℝ) := by
    have hpowers : (3667/25000 : ℝ)^2123 ≤ (34943786854755211/100000000000000000000 : ℝ)^512 := by
      have hnat : (3667 : ℕ)^2123*100000000000000000000^512 ≤ 34943786854755211^512*25000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3667 25000 34943786854755211 100000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3667/25000 : ℝ)) (X := (34943786854755211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010656232915801949/50000000000000000000 : ℝ) ≤ (5000256973627923/5000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (50010656232915801949/50000000000000000000 : ℝ)^512 ≤ (5000256973627923/5000000000000000 : ℝ)^2123 := by
      have hnat : (50010656232915801949 : ℕ)^512*5000000000000000^2123 ≤ 5000256973627923^2123*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010656232915801949 50000000000000000000 5000256973627923 5000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000256973627923/5000000000000000 : ℝ)) (X := (50010656232915801949/50000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501140000494263929/2500000000000000000 : ℝ) ≤ (5000549768530713/5000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (2501140000494263929/2500000000000000000 : ℝ)^512 ≤ (5000549768530713/5000000000000000 : ℝ)^2123 := by
      have hnat : (2501140000494263929 : ℕ)^512*5000000000000000^2123 ≤ 5000549768530713^2123*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501140000494263929 2500000000000000000 5000549768530713 5000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000549768530713/5000000000000000 : ℝ)) (X := (2501140000494263929/2500000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034943786854755211/50000000000000000000 : ℝ) ≤ (5000842563433503/5000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (50034943786854755211/50000000000000000000 : ℝ)^512 ≤ (5000842563433503/5000000000000000 : ℝ)^2123 := by
      have hnat : (50034943786854755211 : ℕ)^512*5000000000000000^2123 ≤ 5000842563433503^2123*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034943786854755211 50000000000000000000 5000842563433503 5000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000842563433503/5000000000000000 : ℝ)) (X := (50034943786854755211/50000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10656232915801949/100000000000000000000 : ℝ) ≤ ((1404576034842641463/1405000000000000000 : ℝ)+2*(2252268483/1405000000000 : ℝ)*(2203/20000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (1404576034842641463/1405000000000000000 : ℝ)+2*(2252268483/1405000000000 : ℝ)*(2203/20000 : ℝ)=(5000256973627923/5000000000000000 : ℝ) by norm_num, show 1+2*(10656232915801949/100000000000000000000 : ℝ)=(50010656232915801949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34943786854755211/100000000000000000000 : ℝ)+(10656232915801949/100000000000000000000 : ℝ) ≤ ((1404576034842641463/1405000000000000000 : ℝ)+(2252268483/1405000000000 : ℝ)*((3667/25000 : ℝ)+(2203/20000 : ℝ)))^(2123/512 : ℝ) := by
    rw [show (1404576034842641463/1405000000000000000 : ℝ)+(2252268483/1405000000000 : ℝ)*((3667/25000 : ℝ)+(2203/20000 : ℝ))=(5000549768530713/5000000000000000 : ℝ) by norm_num, show 1+(34943786854755211/100000000000000000000 : ℝ)+(10656232915801949/100000000000000000000 : ℝ)=(2501140000494263929/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34943786854755211/100000000000000000000 : ℝ) ≤ ((1404576034842641463/1405000000000000000 : ℝ)+2*(2252268483/1405000000000 : ℝ)*(3667/25000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (1404576034842641463/1405000000000000000 : ℝ)+2*(2252268483/1405000000000 : ℝ)*(3667/25000 : ℝ)=(5000842563433503/5000000000000000 : ℝ) by norm_num, show 1+2*(34943786854755211/100000000000000000000 : ℝ)=(50034943786854755211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1404576034842641463/1405000000000000000 : ℝ)*(X 1 0+X 2 0)+(2252268483/1405000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (2203/20000 : ℝ)) (hi := (3667/25000 : ℝ)) (c := (1404576034842641463/1405000000000000000 : ℝ)) (alpha := (2252268483/1405000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1404576034842641463/1405000000000000000 : ℝ)*(X 0 1+X 2 1)+(2252268483/1405000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (2203/20000 : ℝ)) (hi := (3667/25000 : ℝ)) (c := (1404576034842641463/1405000000000000000 : ℝ)) (alpha := (2252268483/1405000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1404576034842641463/1405000000000000000 : ℝ)*(X 0 2+X 1 2)+(2252268483/1405000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (2203/20000 : ℝ)) (hi := (3667/25000 : ℝ)) (c := (1404576034842641463/1405000000000000000 : ℝ)) (alpha := (2252268483/1405000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1920699623/10000000000 : ℝ)*X 0 0+(5392216007/10000000000 : ℝ)*X 0 1+(5392215699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321069229/2500000000 : ℝ)*X 1 0+(-258535587/1250000000 : ℝ)*X 1 1+(2696107977/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1056855433/2000000000 : ℝ)*X 2 0+(1348053989/2500000000 : ℝ)*X 2 1+(-1034142179/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4490764367/10000000000 : ℝ)*X 0 0+(170818113/400000000 : ℝ)*X 0 1+(106761321/250000000 : ℝ)*X 0 2+(4490764367/10000000000 : ℝ)*X 1 0+(170818113/400000000 : ℝ)*X 1 1+(106761321/250000000 : ℝ)*X 1 2+(4490764367/10000000000 : ℝ)*X 2 0+(170818113/400000000 : ℝ)*X 2 1+(106761321/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1133495501/5000000000 : ℝ)*X 0 0+(5263557897/10000000000 : ℝ)*X 0 1+(5263557439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374857021/10000000000 : ℝ)*X 1 0+(-2069828/9765625 : ℝ)*X 1 1+(1052711591/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((335928541/625000000 : ℝ)*X 2 0+(1052711633/2000000000 : ℝ)*X 2 1+(-1059752041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4190816721/10000000000 : ℝ)*X 0 0+(4420370749/10000000000 : ℝ)*X 0 1+(4420371463/10000000000 : ℝ)*X 0 2+(4190816721/10000000000 : ℝ)*X 1 0+(4420370749/10000000000 : ℝ)*X 1 1+(4420371463/10000000000 : ℝ)*X 1 2+(4190816721/10000000000 : ℝ)*X 2 0+(4420370749/10000000000 : ℝ)*X 2 1+(4420371463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1097213159/5000000000 : ℝ)*X 0 0+(103505087/200000000 : ℝ)*X 0 1+(5406255359/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((527438677/1000000000 : ℝ)*X 1 0+(-128909937/625000000 : ℝ)*X 1 1+(5406255063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1318596671/2500000000 : ℝ)*X 2 0+(2703127479/5000000000 : ℝ)*X 2 1+(-8250237/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((904586947/2000000000 : ℝ)*X 0 0+(1063519971/2500000000 : ℝ)*X 0 1+(132940001/312500000 : ℝ)*X 0 2+(904586947/2000000000 : ℝ)*X 1 0+(1063519971/2500000000 : ℝ)*X 1 1+(132940001/312500000 : ℝ)*X 1 2+(904586947/2000000000 : ℝ)*X 2 0+(1063519971/2500000000 : ℝ)*X 2 1+(132940001/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-498428291/2500000000 : ℝ)*X 0 0+(5478183459/10000000000 : ℝ)*X 0 1+(5252540267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((672826357/1250000000 : ℝ)*X 1 0+(-2123783817/10000000000 : ℝ)*X 1 1+(1313135049/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5382610833/10000000000 : ℝ)*X 2 0+(2626270101/5000000000 : ℝ)*X 2 1+(-2123783841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((520585577/1250000000 : ℝ)*X 0 0+(4433199091/10000000000 : ℝ)*X 0 1+(4433198889/10000000000 : ℝ)*X 0 2+(520585577/1250000000 : ℝ)*X 1 0+(4433199091/10000000000 : ℝ)*X 1 1+(4433198889/10000000000 : ℝ)*X 1 2+(520585577/1250000000 : ℝ)*X 2 0+(4433199091/10000000000 : ℝ)*X 2 1+(4433198889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31419/50000 : ℝ) ≤ (-44141951596932333787954640159259/70250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74876037/100000000000000 : ℝ)*(upper0) + (37883149/100000000000000 : ℝ)*(upper2) + (2306887/10000000000000 : ℝ)*(upper3) + (50834751/50000000000000 : ℝ)*(lower4) + (2858399531428831/100000000000000 : ℝ)*(major0) + (2858399531428831/100000000000000 : ℝ)*(major1) + (2858399531428831/100000000000000 : ℝ)*(major2) + (26865013/1250000000000 : ℝ)*(sp3) + (1932094690294109/50000000000000 : ℝ)*(sp4) + (3864029345046693/100000000000000 : ℝ)*(sp5) + (1932013715111637/50000000000000 : ℝ)*(sp6) + (1873552705830879/100000000000000 : ℝ)*(sp7) + (6401421661/4000000000000 : ℝ)*(sp13) + (161950364943/100000000000000 : ℝ)*(sp14) + (23419435687899/1250000000000 : ℝ)*(f.failure) + (1932094690294109/50000000000000 : ℝ)*(f.sum) + (2646838477649/281000000000000000000000000 : ℝ)*base65 + (85025566668719753/140500000000000000000000000000000 : ℝ)*base67 + (731849773692280247/140500000000000000000000000000000 : ℝ)*base70 + (282437076068780247/140500000000000000000000000000000 : ℝ)*base72 + (1269573295671/140500000000000000000000000 : ℝ)*base73 + (332216015481219753/140500000000000000000000000000000 : ℝ)*base75 + (761117919376219753/140500000000000000000000000000000 : ℝ)*base77 + (1496261919093719753/140500000000000000000000000000000 : ℝ)*base79 + (170744034217/140500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (40009/31250000000000000000 : ℝ)*base89 + (40009/31250000000000000000 : ℝ)*base91 + (40009/31250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (14709/25000 : ℝ) ≤ (516672115693964181332026267833/878125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2970859/10000000000000 : ℝ)*(upper0) + (30070079/50000000000000 : ℝ)*(lower1) + (44391629/25000000000000 : ℝ)*(upper4) + (36565837537253/1250000000000 : ℝ)*(major0) + (36565837537253/1250000000000 : ℝ)*(major1) + (36565837537253/1250000000000 : ℝ)*(major2) + (489191443607581/12500000000000 : ℝ)*(sp0) + (1956767683261837/50000000000000 : ℝ)*(sp1) + (1956763260650693/50000000000000 : ℝ)*(sp2) + (191738046816819/10000000000000 : ℝ)*(sp3) + (300418263/12500000000000 : ℝ)*(sp5) + (1406071049/12500000000000 : ℝ)*(sp6) + (1533010949/50000000000000 : ℝ)*(sp7) + (622100913/10000000000000 : ℝ)*(sp8) + (239672941773761/12500000000000 : ℝ)*(f.failure) + (3913537769869779/100000000000000 : ℝ)*(f.sum) + (217761674973/35125000000000000000000000 : ℝ)*base66 + (2600389789996139/1756250000000000000000000000000 : ℝ)*base67 + (3526828159696139/1756250000000000000000000000000 : ℝ)*base69 + (4319307862553861/1756250000000000000000000000000 : ℝ)*base72 + (8688656963/439062500000000000000000 : ℝ)*base73 + (7689822622108639/1756250000000000000000000000000 : ℝ)*base75 + (7255691606266361/1756250000000000000000000000000 : ℝ)*base78 + (70099351212121139/1756250000000000000000000000000 : ℝ)*base79 + (174972734061/140500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1841551/312500000000000000000 : ℝ)*base89 + (1841551/312500000000000000000 : ℝ)*base91 + (1841551/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39813/50000 : ℝ) ≤ (27969559181325991821111620493561/35125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (159021081/100000000000000 : ℝ)*(upper0) + (7537723/4000000000000 : ℝ)*(upper1) + (125026569/100000000000000 : ℝ)*(upper2) + (1619712055286549/50000000000000 : ℝ)*(major0) + (1619712055286549/50000000000000 : ℝ)*(major1) + (1619712055286549/50000000000000 : ℝ)*(major2) + (135368116007/50000000000000 : ℝ)*(sp1) + (90978874681/50000000000000 : ℝ)*(sp2) + (47345382171/50000000000000 : ℝ)*(sp3) + (22409930047/100000000000000 : ℝ)*(sp4) + (2164491632990089/50000000000000 : ℝ)*(sp8) + (432873493967821/10000000000000 : ℝ)*(sp9) + (2164411859080431/50000000000000 : ℝ)*(sp10) + (1061602487529369/50000000000000 : ℝ)*(sp11) + (53082491645577/2500000000000 : ℝ)*(f.failure) + (270562854744389/6250000000000 : ℝ)*(f.sum) + (19494178821/28100000000000000000000000 : ℝ)*base65 + (305506988869668813/70250000000000000000000000000000 : ℝ)*base68 + (363350588077168813/70250000000000000000000000000000 : ℝ)*base70 + (367260508823581187/70250000000000000000000000000000 : ℝ)*base71 + (1408501711491/140500000000000000000000000 : ℝ)*base74 + (228673262909918813/70250000000000000000000000000000 : ℝ)*base76 + (182432069390081187/70250000000000000000000000000000 : ℝ)*base77 + (245202169601918813/70250000000000000000000000000000 : ℝ)*base80 + (41506343779/17562500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (472393/62500000000000000000 : ℝ)*base90 + (472393/62500000000000000000 : ℝ)*base92 + (472393/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-16827/20000 : ℝ) ≤ (-7387874916641480988715763983563/8781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2606603/10000000000000 : ℝ)*(lower0) + (21824917/100000000000000 : ℝ)*(upper1) + (114243/2500000000000 : ℝ)*(upper3) + (6492759/50000000000000 : ℝ)*(lower4) + (409407428898183/12500000000000 : ℝ)*(major0) + (409407428898183/12500000000000 : ℝ)*(major1) + (409407428898183/12500000000000 : ℝ)*(major2) + (845288901/100000000000000 : ℝ)*(sp4) + (3435741671/25000000000000 : ℝ)*(sp5) + (17343563129/100000000000000 : ℝ)*(sp6) + (221588700325599/5000000000000 : ℝ)*(sp12) + (1107940277208549/25000000000000 : ℝ)*(sp13) + (4431757508237751/100000000000000 : ℝ)*(sp14) + (536697034591873/25000000000000 : ℝ)*(sp15) + (536697034591873/25000000000000 : ℝ)*(f.failure) + (55397185647511/1250000000000 : ℝ)*(f.sum) + (9562139551/140500000000000000000000000 : ℝ)*base66 + (749692629150771/17562500000000000000000000000000 : ℝ)*base68 + (533367802206525771/17562500000000000000000000000000 : ℝ)*base70 + (161406760870588271/17562500000000000000000000000000 : ℝ)*base72 + (96266089063/35125000000000000000000000 : ℝ)*base74 + (310915481993661729/17562500000000000000000000000000 : ℝ)*base75 + (94210406609775771/17562500000000000000000000000000 : ℝ)*base78 + (106098380147724229/17562500000000000000000000000000 : ℝ)*base79 + (336152039091/281000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3515343/625000000000000000000 : ℝ)*base89 + (3515343/625000000000000000000 : ℝ)*base91 + (3515343/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1287_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14709/25000 : ℝ) else (39813/50000 : ℝ) ≤ X j i ∧ X j i ≤ (16827/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1287_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1287_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14709/25000 : ℝ) else (39813/50000 : ℝ) ≤ X j i ∧ X j i ≤ (16827/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1287_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14709/25000 : ℝ) else (39813/50000 : ℝ) ≤ X j i ∧ X j i ≤ (16827/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1287_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
