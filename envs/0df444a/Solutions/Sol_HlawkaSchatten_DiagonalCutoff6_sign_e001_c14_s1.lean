-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff6.sign_e001_c14_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T19:15:49.833984+00:00
-- url     : https://prove2.me/submissions/46cf91a3-90af-4019-b0f2-077fa474e93c

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
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
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff6
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
theorem support_e001_c14_s1_0 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-437038267/5000000000 : ℝ)*x 0 + (5949502483/10000000000 : ℝ)*x 1 + (4691173673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-437038267/5000000000 : ℝ), (5949502483/10000000000 : ℝ), (4691173673/10000000000 : ℝ)] ![(549464747947/10000000000000 : ℝ), (53892035037787/100000000000000 : ℝ), (5076664682909/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_1 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5411838891/10000000000 : ℝ)*x 0 + (-1594741801/10000000000 : ℝ)*x 1 + (4691173573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5411838891/10000000000 : ℝ), (-1594741801/10000000000 : ℝ), (4691173573/10000000000 : ℝ)] ![(24072622657521/50000000000000 : ℝ), (2810359558377/25000000000000 : ℝ), (4061331643263/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_2 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2705919443/5000000000 : ℝ)*x 0 + (938234711/2000000000 : ℝ)*x 1 + (-1594741829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2705919443/5000000000 : ℝ), (938234711/2000000000 : ℝ), (-1594741829/10000000000 : ℝ)] ![(6018155657761/12500000000000 : ℝ), (8122663249423/20000000000000 : ℝ), (11241438468477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_6 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3654761123/10000000000 : ℝ)*x 0 + (330882709/2000000000 : ℝ)*x 1 + (6335955879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3654761123/10000000000 : ℝ), (330882709/2000000000 : ℝ), (6335955879/10000000000 : ℝ)] ![(15085650705759/50000000000000 : ℝ), (11743954973311/100000000000000 : ℝ), (11616948719511/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_8 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2707690211/5000000000 : ℝ)*x 0 + (-1641336017/10000000000 : ℝ)*x 1 + (2324727871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2707690211/5000000000 : ℝ), (-1641336017/10000000000 : ℝ), (2324727871/5000000000 : ℝ)] ![(6022844417657/12500000000000 : ℝ), (5816762253897/50000000000000 : ℝ), (627870627193/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_9 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2707690219/5000000000 : ℝ)*x 0 + (464945573/1000000000 : ℝ)*x 1 + (-164133601/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2707690219/5000000000 : ℝ), (464945573/1000000000 : ℝ), (-164133601/1000000000 : ℝ)] ![(4818275551073/10000000000000 : ℝ), (8036744003377/20000000000000 : ℝ), (1454190556091/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_13 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3605784637/10000000000 : ℝ)*x 0 + (149141599/1000000000 : ℝ)*x 1 + (1626143379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3605784637/10000000000 : ℝ), (149141599/1000000000 : ℝ), (1626143379/2500000000 : ℝ)] ![(29690587448817/100000000000000 : ℝ), (10379801341999/100000000000000 : ℝ), (14982402799667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_14 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-825278/9765625 : ℝ)*x 0 + (6082081877/10000000000 : ℝ)*x 1 + (35725477/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-825278/9765625 : ℝ), (6082081877/10000000000 : ℝ), (35725477/78125000 : ℝ)] ![(2639187658903/50000000000000 : ℝ), (55324737233011/100000000000000 : ℝ), (39396887438493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_15 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (533185847/1000000000 : ℝ)*x 0 + (-615414343/5000000000 : ℝ)*x 1 + (5059964267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(533185847/1000000000 : ℝ), (-615414343/5000000000 : ℝ), (5059964267/10000000000 : ℝ)] ![(47299384736359/100000000000000 : ℝ), (8258514127161/100000000000000 : ℝ), (44442101122329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_16 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (666482331/1250000000 : ℝ)*x 0 + (505996501/1000000000 : ℝ)*x 1 + (-1230827479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(666482331/1250000000 : ℝ), (505996501/1000000000 : ℝ), (-1230827479/10000000000 : ℝ)] ![(5912423327023/12500000000000 : ℝ), (44442108891177/100000000000000 : ℝ), (1651700897187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_20 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3544465107/10000000000 : ℝ)*x 0 + (1178699443/10000000000 : ℝ)*x 1 + (6789320939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3544465107/10000000000 : ℝ), (1178699443/10000000000 : ℝ), (6789320939/10000000000 : ℝ)] ![(7272619203561/25000000000000 : ℝ), (1960954346423/25000000000000 : ℝ), (31532852894519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_21 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-584807291/10000000000 : ℝ)*x 0 + (5967675451/10000000000 : ℝ)*x 1 + (4874201631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-584807291/10000000000 : ℝ), (5967675451/10000000000 : ℝ), (4874201631/10000000000 : ℝ)] ![(681064220401/20000000000000 : ℝ), (13522015603457/25000000000000 : ℝ), (42506616474437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_22 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2577545103/5000000000 : ℝ)*x 0 + (-338225093/2000000000 : ℝ)*x 1 + (2437101851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2577545103/5000000000 : ℝ), (-338225093/2000000000 : ℝ), (2437101851/5000000000 : ℝ)] ![(45438515044201/100000000000000 : ℝ), (1506855870649/12500000000000 : ℝ), (53133297469/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_23 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5705984141/10000000000 : ℝ)*x 0 + (113257581/250000000 : ℝ)*x 1 + (-17707363/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5705984141/10000000000 : ℝ), (113257581/250000000 : ℝ), (-17707363/125000000 : ℝ)] ![(51276377200489/100000000000000 : ℝ), (38960785641767/100000000000000 : ℝ), (9762837137133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_27 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2312425751/5000000000 : ℝ)*x 0 + (1346155809/10000000000 : ℝ)*x 1 + (708632029/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2312425751/5000000000 : ℝ), (1346155809/10000000000 : ℝ), (708632029/1250000000 : ℝ)] ![(19965348732321/50000000000000 : ℝ), (9187740612887/100000000000000 : ℝ), (25440780951901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_28 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-79046327/1250000000 : ℝ)*x 0 + (728363491/1250000000 : ℝ)*x 1 + (4987920573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-79046327/1250000000 : ℝ), (728363491/1250000000 : ℝ), (4987920573/10000000000 : ℝ)] ![(58398993381/1562500000000 : ℝ), (52572630686581/100000000000000 : ℝ), (10922458432439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_29 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (565842301/1000000000 : ℝ)*x 0 + (-189361581/1250000000 : ℝ)*x 1 + (2250327319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(565842301/1000000000 : ℝ), (-189361581/1250000000 : ℝ), (2250327319/5000000000 : ℝ)] ![(25383983658197/50000000000000 : ℝ), (2114920818243/20000000000000 : ℝ), (38657428577307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_30 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2829210691/5000000000 : ℝ)*x 0 + (4669973117/10000000000 : ℝ)*x 1 + (-162859043/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2829210691/5000000000 : ℝ), (4669973117/10000000000 : ℝ), (-162859043/1250000000 : ℝ)] ![(126919874819/250000000000 : ℝ), (20197454936219/50000000000000 : ℝ), (8837140189729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_34 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2753680659/10000000000 : ℝ)*x 0 + (866771323/5000000000 : ℝ)*x 1 + (1411549469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2753680659/10000000000 : ℝ), (866771323/5000000000 : ℝ), (1411549469/2000000000 : ℝ)] ![(21539243477961/100000000000000 : ℝ), (2483131242569/20000000000000 : ℝ), (66045100283483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_35 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-326169439/5000000000 : ℝ)*x 0 + (6082539471/10000000000 : ℝ)*x 1 + (470849039/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-326169439/5000000000 : ℝ), (6082539471/10000000000 : ℝ), (470849039/1000000000 : ℝ)] ![(3878454006311/100000000000000 : ℝ), (13832423136939/25000000000000 : ℝ), (326334827469/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_36 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1127690541/2000000000 : ℝ)*x 0 + (-640040547/5000000000 : ℝ)*x 1 + (941698037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1127690541/2000000000 : ℝ), (-640040547/5000000000 : ℝ), (941698037/2000000000 : ℝ)] ![(50554734700421/100000000000000 : ℝ), (4326706983081/50000000000000 : ℝ), (20395925659663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_37 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1037446683/2000000000 : ℝ)*x 0 + (2505355147/5000000000 : ℝ)*x 1 + (-740673007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1037446683/2000000000 : ℝ), (2505355147/5000000000 : ℝ), (-740673007/5000000000 : ℝ)] ![(45776000604583/100000000000000 : ℝ), (8785515515909/20000000000000 : ℝ), (10296421796143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_41 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4505354767/10000000000 : ℝ)*x 0 + (7356231/62500000 : ℝ)*x 1 + (5909800303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(4505354767/10000000000 : ℝ), (7356231/62500000 : ℝ), (5909800303/10000000000 : ℝ)] ![(38705493798573/100000000000000 : ℝ), (3915165926207/50000000000000 : ℝ), (13366043583243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_42 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-636313081/10000000000 : ℝ)*x 0 + (6253926083/10000000000 : ℝ)*x 1 + (907687951/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-636313081/10000000000 : ℝ), (6253926083/10000000000 : ℝ), (907687951/2000000000 : ℝ)] ![(1882645874173/50000000000000 : ℝ), (57190605562731/100000000000000 : ℝ), (9761025669839/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_43 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5654481091/10000000000 : ℝ)*x 0 + (-1473322599/10000000000 : ℝ)*x 1 + (141826139/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5654481091/10000000000 : ℝ), (-1473322599/10000000000 : ℝ), (141826139/312500000 : ℝ)] ![(25362933083463/50000000000000 : ℝ), (204601300119/2000000000000 : ℝ), (39044068810249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_44 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1130895187/2000000000 : ℝ)*x 0 + (4365721957/10000000000 : ℝ)*x 1 + (-1683778001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1130895187/2000000000 : ℝ), (4365721957/10000000000 : ℝ), (-1683778001/10000000000 : ℝ)] ![(12681452775651/25000000000000 : ℝ), (37281667172117/100000000000000 : ℝ), (11992521704877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e001_c14_s1_48 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1384171117/5000000000 : ℝ)*x 0 + (1109629837/5000000000 : ℝ)*x 1 + (3331173647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (25/4 : ℝ)) 25 21 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1384171117/5000000000 : ℝ), (1109629837/5000000000 : ℝ), (3331173647/5000000000 : ℝ)] ![(10837919751723/50000000000000 : ℝ), (16660051337921/100000000000000 : ℝ), (61664109142827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem sign_e001_c14_s1 (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (117939/50000 : ℝ) (6069/4000 : ℝ) (83579/100000 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : 0 ≤ (X 1 2+X 2 2))
    (sign2 : 0 ≤ (X 0 0+X 2 0))
    (sign3 : 0 ≤ (X 0 2+X 2 2))
    (sign4 : 0 ≤ (X 0 0+X 1 0))
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (56363/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (23373/100000 : ℝ)*pair X i i := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f (by norm_num)
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have ratio0 : (0 : ℝ) ≤ ((56363/100000 : ℝ)*X 1 0+(1 : ℝ)*X 1 1+(56363/100000 : ℝ)*X 2 0+(1 : ℝ)*X 2 1) := by
    have hh := hratio 0 1 (by decide)
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh
    rw [abs_of_nonpos sign0] at hh
    linarith only [hh]
  have ratio1 : (0 : ℝ) ≤ ((56363/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 2+(56363/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) := by
    have hh := hratio 0 2 (by decide)
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh
    rw [abs_of_nonneg sign1] at hh
    linarith only [hh]
  have ratio2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56363/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56363/100000 : ℝ)*X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh
    rw [abs_of_nonneg sign2] at hh
    linarith only [hh]
  have ratio3 : (0 : ℝ) ≤ ((56363/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(56363/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hh := hratio 1 2 (by decide)
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh
    rw [abs_of_nonneg sign3] at hh
    linarith only [hh]
  have ratio4 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56363/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(56363/100000 : ℝ)*X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh
    rw [abs_of_nonneg sign4] at hh
    linarith only [hh]
  have ratio5 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 1+(56363/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 1+(56363/100000 : ℝ)*X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh
    rw [abs_of_nonneg sign5] at hh
    linarith only [hh]
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base43 : ((1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
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
  have hpow : (56363/100000 : ℝ) ^ (49/8 : ℝ) ≤ (2984275191060403233/100000000000000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (56363/100000 : ℝ)) (X := (2984275191060403233/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 49 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner1 : (102984275191060403233/100000000000000000000 : ℝ) ≤ (10048125491187/10000000000000 : ℝ) ^ (49/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10048125491187/10000000000000 : ℝ)) (X := (102984275191060403233/100000000000000000000 : ℝ)) (by norm_num) 49 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner2 : (52984275191060403233/50000000000000000000 : ℝ) ≤ (5048125491187/5000000000000 : ℝ) ^ (49/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5048125491187/5000000000000 : ℝ)) (X := (52984275191060403233/50000000000000000000 : ℝ)) (by norm_num) 49 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have major0 : P 0 ≤ (X 1 0+X 2 0)+(853849/100000000 : ℝ)*(-(X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign0 sign1
    have hh := signed_majorant (p := p) (a := (49/8 : ℝ)) (rho := (56363/100000 : ℝ)) (alpha := (853849/100000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 0) (hratio 0 1 (by decide)) (hratio 0 2 (by decide))
    change lpNorm p (pair X 0) ≤ _
    rw [lpNorm_eq3 p _ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonpos sign0, abs_of_nonneg sign1] using hh
  have major1 : P 1 ≤ (X 0 1+X 2 1)+(853849/100000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign2 sign3
    have hh := signed_majorant (p := p) (a := (49/8 : ℝ)) (rho := (56363/100000 : ℝ)) (alpha := (853849/100000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 1) (hratio 1 0 (by decide)) (hratio 1 2 (by decide))
    change lpNorm p (pair X 1) ≤ _
    rw [lpNorm_eq3 p _ (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonneg sign2, abs_of_nonneg sign3] using hh
  have major2 : P 2 ≤ (X 0 2+X 1 2)+(853849/100000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign4 sign5
    have hh := signed_majorant (p := p) (a := (49/8 : ℝ)) (rho := (56363/100000 : ℝ)) (alpha := (853849/100000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 2) (hratio 2 0 (by decide)) (hratio 2 1 (by decide))
    change lpNorm p (pair X 2) ≤ _
    rw [lpNorm_eq3 p _ (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonneg sign4, abs_of_nonneg sign5] using hh
  have sp0 : ((-437038267/5000000000 : ℝ)*X 0 0+(5949502483/10000000000 : ℝ)*X 0 1+(4691173673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5411838891/10000000000 : ℝ)*X 1 0+(-1594741801/10000000000 : ℝ)*X 1 1+(4691173573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2705919443/5000000000 : ℝ)*X 2 0+(938234711/2000000000 : ℝ)*X 2 1+(-1594741829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((3654761123/10000000000 : ℝ)*X 0 0+(330882709/2000000000 : ℝ)*X 0 1+(6335955879/10000000000 : ℝ)*X 0 2+(3654761123/10000000000 : ℝ)*X 1 0+(330882709/2000000000 : ℝ)*X 1 1+(6335955879/10000000000 : ℝ)*X 1 2+(3654761123/10000000000 : ℝ)*X 2 0+(330882709/2000000000 : ℝ)*X 2 1+(6335955879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((2707690211/5000000000 : ℝ)*X 1 0+(-1641336017/10000000000 : ℝ)*X 1 1+(2324727871/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2707690219/5000000000 : ℝ)*X 2 0+(464945573/1000000000 : ℝ)*X 2 1+(-164133601/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((3605784637/10000000000 : ℝ)*X 0 0+(149141599/1000000000 : ℝ)*X 0 1+(1626143379/2500000000 : ℝ)*X 0 2+(3605784637/10000000000 : ℝ)*X 1 0+(149141599/1000000000 : ℝ)*X 1 1+(1626143379/2500000000 : ℝ)*X 1 2+(3605784637/10000000000 : ℝ)*X 2 0+(149141599/1000000000 : ℝ)*X 2 1+(1626143379/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((-825278/9765625 : ℝ)*X 0 0+(6082081877/10000000000 : ℝ)*X 0 1+(35725477/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((533185847/1000000000 : ℝ)*X 1 0+(-615414343/5000000000 : ℝ)*X 1 1+(5059964267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp16 : ((666482331/1250000000 : ℝ)*X 2 0+(505996501/1000000000 : ℝ)*X 2 1+(-1230827479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp20 : ((3544465107/10000000000 : ℝ)*X 0 0+(1178699443/10000000000 : ℝ)*X 0 1+(6789320939/10000000000 : ℝ)*X 0 2+(3544465107/10000000000 : ℝ)*X 1 0+(1178699443/10000000000 : ℝ)*X 1 1+(6789320939/10000000000 : ℝ)*X 1 2+(3544465107/10000000000 : ℝ)*X 2 0+(1178699443/10000000000 : ℝ)*X 2 1+(6789320939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp21 : ((-584807291/10000000000 : ℝ)*X 0 0+(5967675451/10000000000 : ℝ)*X 0 1+(4874201631/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp22 : ((2577545103/5000000000 : ℝ)*X 1 0+(-338225093/2000000000 : ℝ)*X 1 1+(2437101851/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp23 : ((5705984141/10000000000 : ℝ)*X 2 0+(113257581/250000000 : ℝ)*X 2 1+(-17707363/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp27 : ((2312425751/5000000000 : ℝ)*X 0 0+(1346155809/10000000000 : ℝ)*X 0 1+(708632029/1250000000 : ℝ)*X 0 2+(2312425751/5000000000 : ℝ)*X 1 0+(1346155809/10000000000 : ℝ)*X 1 1+(708632029/1250000000 : ℝ)*X 1 2+(2312425751/5000000000 : ℝ)*X 2 0+(1346155809/10000000000 : ℝ)*X 2 1+(708632029/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp28 : ((-79046327/1250000000 : ℝ)*X 0 0+(728363491/1250000000 : ℝ)*X 0 1+(4987920573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_28 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp29 : ((565842301/1000000000 : ℝ)*X 1 0+(-189361581/1250000000 : ℝ)*X 1 1+(2250327319/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_29 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp30 : ((2829210691/5000000000 : ℝ)*X 2 0+(4669973117/10000000000 : ℝ)*X 2 1+(-162859043/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_30 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp34 : ((2753680659/10000000000 : ℝ)*X 0 0+(866771323/5000000000 : ℝ)*X 0 1+(1411549469/2000000000 : ℝ)*X 0 2+(2753680659/10000000000 : ℝ)*X 1 0+(866771323/5000000000 : ℝ)*X 1 1+(1411549469/2000000000 : ℝ)*X 1 2+(2753680659/10000000000 : ℝ)*X 2 0+(866771323/5000000000 : ℝ)*X 2 1+(1411549469/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_34 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp35 : ((-326169439/5000000000 : ℝ)*X 0 0+(6082539471/10000000000 : ℝ)*X 0 1+(470849039/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_35 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp36 : ((1127690541/2000000000 : ℝ)*X 1 0+(-640040547/5000000000 : ℝ)*X 1 1+(941698037/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_36 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp37 : ((1037446683/2000000000 : ℝ)*X 2 0+(2505355147/5000000000 : ℝ)*X 2 1+(-740673007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_37 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp41 : ((4505354767/10000000000 : ℝ)*X 0 0+(7356231/62500000 : ℝ)*X 0 1+(5909800303/10000000000 : ℝ)*X 0 2+(4505354767/10000000000 : ℝ)*X 1 0+(7356231/62500000 : ℝ)*X 1 1+(5909800303/10000000000 : ℝ)*X 1 2+(4505354767/10000000000 : ℝ)*X 2 0+(7356231/62500000 : ℝ)*X 2 1+(5909800303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_41 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp42 : ((-636313081/10000000000 : ℝ)*X 0 0+(6253926083/10000000000 : ℝ)*X 0 1+(907687951/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_42 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp43 : ((5654481091/10000000000 : ℝ)*X 1 0+(-1473322599/10000000000 : ℝ)*X 1 1+(141826139/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_43 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp44 : ((1130895187/2000000000 : ℝ)*X 2 0+(4365721957/10000000000 : ℝ)*X 2 1+(-1683778001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_44 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp48 : ((1384171117/5000000000 : ℝ)*X 0 0+(1109629837/5000000000 : ℝ)*X 0 1+(3331173647/5000000000 : ℝ)*X 0 2+(1384171117/5000000000 : ℝ)*X 1 0+(1109629837/5000000000 : ℝ)*X 1 1+(3331173647/5000000000 : ℝ)*X 1 2+(1384171117/5000000000 : ℝ)*X 2 0+(1109629837/5000000000 : ℝ)*X 2 1+(3331173647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e001_c14_s1_48 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have r0 : (0 : ℝ) ≤ ((23373/100000 : ℝ)*X 1 0+(1 : ℝ)*X 1 1+(23373/100000 : ℝ)*X 2 0+(1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3653141364750626539449/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (52079176103/1000000000000 : ℝ)*(base24) + (2821167420433/500000000000 : ℝ)*(major0) + (2821167420433/500000000000 : ℝ)*(major1) + (2821167420433/500000000000 : ℝ)*(major2) + (1381584901111/250000000000 : ℝ)*(sp0) + (1078206307797/1000000000000 : ℝ)*(sp6) + (56216261221/10000000000 : ℝ)*(sp8) + (6362029612501/1000000000000 : ℝ)*(sp9) + (787303940359/250000000000 : ℝ)*(sp22) + (168224307369/1000000000000 : ℝ)*(sp27) + (204483503273/200000000000 : ℝ)*(sp28) + (1111042381363/500000000000 : ℝ)*(sp35) + (589183273733/250000000000 : ℝ)*(sp37) + (572812902099/500000000000 : ℝ)*(sp48) + (598014104841/250000000000 : ℝ)*(f.failure) + (1754168376707/200000000000 : ℝ)*(f.sum) + (2253236437/10000000000000000000000 : ℝ)*base66 + (22088977/78125000000000000000 : ℝ)*base68 + (30837263/62500000000000000000 : ℝ)*base70 + (9632891217/10000000000000000000000 : ℝ)*base72 + (268082551/5000000000000000000000 : ℝ)*base73 + (1959322651/2000000000000000000000 : ℝ)*base76 + (8228477419/10000000000000000000000 : ℝ)*base78 + (1645778119/2500000000000000000000 : ℝ)*base80 + (33604259/400000000000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (1/1000000000000 : ℝ)*base87 + (17699/12500000000000000 : ℝ)*base89 + (17699/12500000000000000 : ℝ)*base91 + (17699/12500000000000000 : ℝ)*base93 + hcertificate_margin
  have out0 : |(X 1 1+X 2 1)| ≤ (23373/100000 : ℝ)*(X 1 0+X 2 0) := by
    rw [abs_of_nonpos sign0]
    linarith only [r0]
  have r1 : (0 : ℝ) ≤ ((23373/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 2+(23373/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34810045199495643/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (187591738329/100000000000 : ℝ)*(base43) + (2605185384791/200000000000 : ℝ)*(major0) + (2605185384791/200000000000 : ℝ)*(major1) + (2605185384791/200000000000 : ℝ)*(major2) + (358767/500000000000 : ℝ)*(sp13) + (20529492454793/1000000000000 : ℝ)*(sp14) + (5132379025667/250000000000 : ℝ)*(sp15) + (4105875960731/200000000000 : ℝ)*(sp16) + (2761136246513/500000000000 : ℝ)*(sp20) + (1111667/62500000000 : ℝ)*(sp22) + (16433253/500000000000 : ℝ)*(sp30) + (21053331/500000000000 : ℝ)*(sp34) + (6060959/50000000000 : ℝ)*(sp37) + (10358637/250000000000 : ℝ)*(sp42) + (5522315317221/1000000000000 : ℝ)*(f.failure) + (20529533889341/1000000000000 : ℝ)*(f.sum) + (935252457/5000000000000000000000 : ℝ)*base66 + (236903331/400000000000000000000 : ℝ)*base68 + (2290607749/2500000000000000000000 : ℝ)*base70 + (158067209/1000000000000000000000 : ℝ)*base72 + (1626962051/5000000000000000000000 : ℝ)*base74 + (1057639487/2500000000000000000000 : ℝ)*base76 + (698142913/1000000000000000000000 : ℝ)*base78 + (3303805001/5000000000000000000000 : ℝ)*base80 + (4309960019/10000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base86 + (22481/50000000000000000 : ℝ)*base90 + (22481/50000000000000000 : ℝ)*base92 + (22481/50000000000000000 : ℝ)*base94 + (1/1000000000000 : ℝ)*base95 + hcertificate_margin
  have out1 : |(X 1 2+X 2 2)| ≤ (23373/100000 : ℝ)*(X 1 0+X 2 0) := by
    rw [abs_of_nonneg sign1]
    linarith only [r1]
  have r2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23373/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23373/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (359790456144908856351/2000000000000000000000 : ℝ) := by norm_num
    linear_combination (2453716078659/1000000000000 : ℝ)*(base43) + (12127536406401/1000000000000 : ℝ)*(major0) + (12127536406401/1000000000000 : ℝ)*(major1) + (12127536406401/1000000000000 : ℝ)*(major2) + (897889319/12500000000 : ℝ)*(sp1) + (302392543999/500000000000 : ℝ)*(sp2) + (822149628167/500000000000 : ℝ)*(sp15) + (8538807544627/1000000000000 : ℝ)*(sp21) + (17337532856673/1000000000000 : ℝ)*(sp22) + (9124041339917/500000000000 : ℝ)*(sp23) + (642680559781/125000000000 : ℝ)*(sp27) + (3640923687327/500000000000 : ℝ)*(sp28) + (100397745347/500000000000 : ℝ)*(sp30) + (646601667849/200000000000 : ℝ)*(sp35) + (642680559781/125000000000 : ℝ)*(f.failure) + (9526831629263/500000000000 : ℝ)*(f.sum) + (342945853/2000000000000000000000 : ℝ)*base66 + (125606773/1250000000000000000000 : ℝ)*base67 + (120099113/2000000000000000000000 : ℝ)*base70 + (2749947767/5000000000000000000000 : ℝ)*base72 + (1801586043/10000000000000000000000 : ℝ)*base74 + (276543011/500000000000000000000 : ℝ)*base76 + (82402763/5000000000000000000000 : ℝ)*base78 + (82505789/500000000000000000000 : ℝ)*base80 + (1171748649/5000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base85 + (5109/6250000000000000 : ℝ)*base89 + (5109/6250000000000000 : ℝ)*base91 + (5109/6250000000000000 : ℝ)*base93 + hcertificate_margin
  have out2 : |(X 0 0+X 2 0)| ≤ (23373/100000 : ℝ)*(X 0 1+X 2 1) := by
    rw [abs_of_nonneg sign2]
    linarith only [r2]
  have r3 : (0 : ℝ) ≤ ((23373/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(23373/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (26014678639908890217/1000000000000000000000 : ℝ) := by norm_num
    linear_combination (280867294341/125000000000 : ℝ)*(base43) + (13486387527753/1000000000000 : ℝ)*(major0) + (13486387527753/1000000000000 : ℝ)*(major1) + (13486387527753/1000000000000 : ℝ)*(major2) + (208255199367/250000000000 : ℝ)*(sp0) + (79081718449/200000000000 : ℝ)*(sp1) + (370257904031/500000000000 : ℝ)*(sp2) + (101491067781/500000000000 : ℝ)*(sp8) + (49541204077/200000000000 : ℝ)*(sp20) + (376324287641/500000000000 : ℝ)*(sp23) + (20413556041589/1000000000000 : ℝ)*(sp28) + (16518548889/800000000 : ℝ)*(sp29) + (19753412455713/1000000000000 : ℝ)*(sp30) + (170931894891/31250000000 : ℝ)*(sp34) + (44668177007/7812500000 : ℝ)*(f.failure) + (21246576839057/1000000000000 : ℝ)*(f.sum) + (2849603467/10000000000000000000000 : ℝ)*base66 + (5273637243/10000000000000000000000 : ℝ)*base68 + (2536410729/2500000000000000000000 : ℝ)*base70 + (3433163931/5000000000000000000000 : ℝ)*base72 + (381330873/2500000000000000000000 : ℝ)*base73 + (1264848543/1250000000000000000000 : ℝ)*base76 + (6737454963/10000000000000000000000 : ℝ)*base78 + (1200873759/5000000000000000000000 : ℝ)*base80 + (1249941361/2000000000000000000000 : ℝ)*base82 + (459/3125000000000000 : ℝ)*base89 + (459/3125000000000000 : ℝ)*base91 + (459/3125000000000000 : ℝ)*base93 + (1/1000000000000 : ℝ)*base95 + hcertificate_margin
  have out3 : |(X 0 2+X 2 2)| ≤ (23373/100000 : ℝ)*(X 0 1+X 2 1) := by
    rw [abs_of_nonneg sign3]
    linarith only [r3]
  have r4 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23373/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23373/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (91178612501336571429/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (2144206828171/1000000000000 : ℝ)*(base43) + (3523313274317/250000000000 : ℝ)*(major0) + (3523313274317/250000000000 : ℝ)*(major1) + (3523313274317/250000000000 : ℝ)*(major2) + (10570487053/500000000000 : ℝ)*(sp2) + (93035255371/500000000000 : ℝ)*(sp14) + (1829342739/31250000000 : ℝ)*(sp27) + (8393796309/200000000000 : ℝ)*(sp30) + (21861039961713/1000000000000 : ℝ)*(sp35) + (4379747268121/200000000000 : ℝ)*(sp36) + (5535627894919/250000000000 : ℝ)*(sp37) + (5916267117391/1000000000000 : ℝ)*(sp41) + (19813882859/125000000000 : ℝ)*(sp42) + (306885194723/1000000000000 : ℝ)*(sp43) + (5974806085039/1000000000000 : ℝ)*(f.failure) + (22205621535327/1000000000000 : ℝ)*(f.sum) + (471800523/10000000000000000000000 : ℝ)*base66 + (22922707/400000000000000000000 : ℝ)*base67 + (429876591/10000000000000000000000 : ℝ)*base70 + (5474276311/10000000000000000000000 : ℝ)*base72 + (745613671/2000000000000000000000 : ℝ)*base73 + (2495312219/5000000000000000000000 : ℝ)*base76 + (102438361/10000000000000000000000 : ℝ)*base77 + (2932670869/10000000000000000000000 : ℝ)*base79 + (815262591/10000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base85 + (14621/50000000000000000 : ℝ)*base89 + (14621/50000000000000000 : ℝ)*base91 + (14621/50000000000000000 : ℝ)*base93 + hcertificate_margin
  have out4 : |(X 0 0+X 1 0)| ≤ (23373/100000 : ℝ)*(X 0 2+X 1 2) := by
    rw [abs_of_nonneg sign4]
    linarith only [r4]
  have r5 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 1+(23373/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 1+(23373/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8740963627143670359/62500000000000000000 : ℝ) := by norm_num
    linear_combination (3563714828301/1000000000000 : ℝ)*(base43) + (2151759386029/125000000000 : ℝ)*(major0) + (2151759386029/125000000000 : ℝ)*(major1) + (2151759386029/125000000000 : ℝ)*(major2) + (2297264889393/500000000000 : ℝ)*(sp1) + (93670985137/62500000000 : ℝ)*(sp6) + (1156619075297/250000000000 : ℝ)*(sp9) + (650560104229/100000000000 : ℝ)*(sp14) + (802324992233/1000000000000 : ℝ)*(sp23) + (3161140584677/250000000000 : ℝ)*(sp29) + (10289029209481/500000000000 : ℝ)*(sp42) + (9844567343757/1000000000000 : ℝ)*(sp43) + (21654858167831/1000000000000 : ℝ)*(sp44) + (5799136480337/1000000000000 : ℝ)*(sp48) + (7297872242529/1000000000000 : ℝ)*(f.failure) + (27083659461251/1000000000000 : ℝ)*(f.sum) + (55037491/1250000000000000000000 : ℝ)*base65 + (3937194077/5000000000000000000000 : ℝ)*base68 + (1800170149/2500000000000000000000 : ℝ)*base70 + (1457853967/10000000000000000000000 : ℝ)*base72 + (39960793/2000000000000000000000 : ℝ)*base74 + (167774579/625000000000000000000 : ℝ)*base76 + (55157827/78125000000000000000 : ℝ)*base78 + (1239425001/2000000000000000000000 : ℝ)*base80 + (68660157/2000000000000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base87 + (27731/50000000000000000 : ℝ)*base89 + (27731/50000000000000000 : ℝ)*base91 + (27731/50000000000000000 : ℝ)*base93 + hcertificate_margin
  have out5 : |(X 0 1+X 1 1)| ≤ (23373/100000 : ℝ)*(X 0 2+X 1 2) := by
    rw [abs_of_nonneg sign5]
    linarith only [r5]
  intro i h hij
  fin_cases i <;> fin_cases h <;> try contradiction
  · change |pair X 0 1| ≤ (23373/100000 : ℝ)*pair X 0 0
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out0
  · change |pair X 0 2| ≤ (23373/100000 : ℝ)*pair X 0 0
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out1
  · change |pair X 1 0| ≤ (23373/100000 : ℝ)*pair X 1 1
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out2
  · change |pair X 1 2| ≤ (23373/100000 : ℝ)*pair X 1 1
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out3
  · change |pair X 2 0| ≤ (23373/100000 : ℝ)*pair X 2 2
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out4
  · change |pair X 2 1| ≤ (23373/100000 : ℝ)*pair X 2 2
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out5

end HlawkaSchatten.DiagonalCutoff6


open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem solution (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (117939/50000 : ℝ) (6069/4000 : ℝ) (83579/100000 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : 0 ≤ (X 1 2+X 2 2))
    (sign2 : 0 ≤ (X 0 0+X 2 0))
    (sign3 : 0 ≤ (X 0 2+X 2 2))
    (sign4 : 0 ≤ (X 0 0+X 1 0))
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (56363/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (23373/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff6.sign_e001_c14_s1 p hpa hpb X hX sign0 sign1 sign2 sign3 sign4 sign5 hratio

#print axioms solution
