-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff6.sign_e005_c12_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T19:29:44.950164+00:00
-- url     : https://prove2.me/submissions/891b731a-6f08-497f-b6a4-6f784cc9af43

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
theorem support_e005_c12_s0_0 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-355187033/5000000000 : ℝ)*x 0 + (112469109/156250000 : ℝ)*x 1 + (3333252849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-355187033/5000000000 : ℝ), (112469109/156250000 : ℝ), (3333252849/10000000000 : ℝ)] ![(1121206824307/25000000000000 : ℝ), (6797993525133/10000000000000 : ℝ), (27535237436867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_2 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4795681311/10000000000 : ℝ)*x 0 + (4692081303/10000000000 : ℝ)*x 1 + (-434560807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(4795681311/10000000000 : ℝ), (4692081303/10000000000 : ℝ), (-434560807/2000000000 : ℝ)] ![(21101631098589/50000000000000 : ℝ), (41135019523131/100000000000000 : ℝ), (3332343653913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_6 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7709043181/10000000000 : ℝ)*x 0 + (219088821/10000000000 : ℝ)*x 1 + (3090139533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(7709043181/10000000000 : ℝ), (219088821/10000000000 : ℝ), (3090139533/10000000000 : ℝ)] ![(36839895695999/50000000000000 : ℝ), (1127281630701/100000000000000 : ℝ), (25192926958817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_7 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-60903093/2000000000 : ℝ)*x 0 + (900207509/1000000000 : ℝ)*x 1 + (700328423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-60903093/2000000000 : ℝ), (900207509/1000000000 : ℝ), (700328423/5000000000 : ℝ)] ![(103697732097/6250000000000 : ℝ), (88389813853673/100000000000000 : ℝ), (9951022416001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_8 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (240621291/500000000 : ℝ)*x 0 + (-628350469/10000000000 : ℝ)*x 1 + (46030619/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(240621291/500000000 : ℝ), (-628350469/10000000000 : ℝ), (46030619/78125000 : ℝ)] ![(5297037239649/12500000000000 : ℝ), (1941617109203/50000000000000 : ℝ), (671755848197/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_9 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (240621301/500000000 : ℝ)*x 0 + (2780611879/10000000000 : ℝ)*x 1 + (-2062709559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(240621301/500000000 : ℝ), (2780611879/10000000000 : ℝ), (-2062709559/5000000000 : ℝ)] ![(21188149992297/50000000000000 : ℝ), (5564282141023/25000000000000 : ℝ), (35366571437733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_13 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6878795943/10000000000 : ℝ)*x 0 + (46137251/10000000000 : ℝ)*x 1 + (4125201269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(6878795943/10000000000 : ℝ), (46137251/10000000000 : ℝ), (4125201269/10000000000 : ℝ)] ![(16113642596333/25000000000000 : ℝ), (4526263647/2500000000000 : ℝ), (17682189532511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_14 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-189102933/1250000000 : ℝ)*x 0 + (259071343/312500000 : ℝ)*x 1 + (1269225463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-189102933/1250000000 : ℝ), (259071343/312500000 : ℝ), (1269225463/10000000000 : ℝ)] ![(2723220069579/25000000000000 : ℝ), (80243064001401/100000000000000 : ℝ), (8864055701379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_15 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1702990357/5000000000 : ℝ)*x 0 + (-161449167/10000000000 : ℝ)*x 1 + (933361601/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1702990357/5000000000 : ℝ), (-161449167/10000000000 : ℝ), (933361601/1250000000 : ℝ)] ![(7060460177459/25000000000000 : ℝ), (78775263089/10000000000000 : ℝ), (70970406642533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_16 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3405978799/10000000000 : ℝ)*x 0 + (1321217177/2000000000 : ℝ)*x 1 + (-720770247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3405978799/10000000000 : ℝ), (1321217177/2000000000 : ℝ), (-720770247/5000000000 : ℝ)] ![(1765113879339/6250000000000 : ℝ), (61465322712471/100000000000000 : ℝ), (2058571040959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_20 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4241150639/10000000000 : ℝ)*x 0 + (206266951/10000000000 : ℝ)*x 1 + (418312233/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(4241150639/10000000000 : ℝ), (206266951/10000000000 : ℝ), (418312233/625000000 : ℝ)] ![(36534086643017/100000000000000 : ℝ), (525118094639/50000000000000 : ℝ), (3900979821871/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_21 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-45232107/10000000000 : ℝ)*x 0 + (1325409177/2000000000 : ℝ)*x 1 + (439834831/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-45232107/10000000000 : ℝ), (1325409177/2000000000 : ℝ), (439834831/1000000000 : ℝ)] ![(17688802751/10000000000000 : ℝ), (61694321328221/100000000000000 : ℝ), (38128790634359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_22 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1223593391/5000000000 : ℝ)*x 0 + (-218077663/1250000000 : ℝ)*x 1 + (3598330261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1223593391/5000000000 : ℝ), (-218077663/1250000000 : ℝ), (3598330261/5000000000 : ℝ)] ![(9578960017357/50000000000000 : ℝ), (12877249617631/100000000000000 : ℝ), (33982415170597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_23 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6403237811/10000000000 : ℝ)*x 0 + (1544471369/5000000000 : ℝ)*x 1 + (-102506051/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(6403237811/10000000000 : ℝ), (1544471369/5000000000 : ℝ), (-102506051/500000000 : ℝ)] ![(29627841080341/50000000000000 : ℝ), (12590736684791/50000000000000 : ℝ), (15562844442317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_27 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4505003641/5000000000 : ℝ)*x 0 + (165884857/5000000000 : ℝ)*x 1 + (684284321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(4505003641/5000000000 : ℝ), (165884857/5000000000 : ℝ), (684284321/5000000000 : ℝ)] ![(88481250860511/100000000000000 : ℝ), (91740469441/5000000000000 : ℝ), (2420984932161/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_28 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1256507019/10000000000 : ℝ)*x 0 + (1027466297/1250000000 : ℝ)*x 1 + (1619280241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-1256507019/10000000000 : ℝ), (1027466297/1250000000 : ℝ), (1619280241/10000000000 : ℝ)] ![(8759875793527/100000000000000 : ℝ), (19860501097413/25000000000000 : ℝ), (11798119806281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_29 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4413992553/10000000000 : ℝ)*x 0 + (-202129873/10000000000 : ℝ)*x 1 + (6534705409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(4413992553/10000000000 : ℝ), (-202129873/10000000000 : ℝ), (6534705409/10000000000 : ℝ)] ![(9572010949127/25000000000000 : ℝ), (512775836169/50000000000000 : ℝ), (30343202259911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_30 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2206996341/5000000000 : ℝ)*x 0 + (3287381853/10000000000 : ℝ)*x 1 + (-1012804791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2206996341/5000000000 : ℝ), (3287381853/10000000000 : ℝ), (-1012804791/2500000000 : ℝ)] ![(3828804511009/10000000000000 : ℝ), (13545470584471/50000000000000 : ℝ), (17310506851583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_34 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4398556199/5000000000 : ℝ)*x 0 + (145506911/10000000000 : ℝ)*x 1 + (1789930731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(4398556199/5000000000 : ℝ), (145506911/10000000000 : ℝ), (1789930731/10000000000 : ℝ)] ![(86032028964901/100000000000000 : ℝ), (697244537309/100000000000000 : ℝ), (13270726483793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_35 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-59616143/2000000000 : ℝ)*x 0 + (4288249143/5000000000 : ℝ)*x 1 + (493227353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-59616143/2000000000 : ℝ), (4288249143/5000000000 : ℝ), (493227353/2500000000 : ℝ)] ![(323616485099/20000000000000 : ℝ), (83504858642223/100000000000000 : ℝ), (464908091091/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_36 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3393209227/5000000000 : ℝ)*x 0 + (-10580557/400000000 : ℝ)*x 1 + (4104288261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3393209227/5000000000 : ℝ), (-10580557/400000000 : ℝ), (4104288261/10000000000 : ℝ)] ![(31719822596271/50000000000000 : ℝ), (1406344646089/100000000000000 : ℝ), (35154010151097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_37 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1833986973/10000000000 : ℝ)*x 0 + (136399767/200000000 : ℝ)*x 1 + (-1405175079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1833986973/10000000000 : ℝ), (136399767/200000000 : ℝ), (-1405175079/5000000000 : ℝ)] ![(6827492790757/50000000000000 : ℝ), (31904095955497/50000000000000 : ℝ), (11268411246333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_41 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (397108713/500000000 : ℝ)*x 0 + (299817531/10000000000 : ℝ)*x 1 + (345066331/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(397108713/500000000 : ℝ), (299817531/10000000000 : ℝ), (345066331/1250000000 : ℝ)] ![(76302289649453/100000000000000 : ℝ), (101822231361/6250000000000 : ℝ), (5517138657843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_42 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-314214361/10000000000 : ℝ)*x 0 + (9054143483/10000000000 : ℝ)*x 1 + (132079871/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-314214361/10000000000 : ℝ), (9054143483/10000000000 : ℝ), (132079871/1000000000 : ℝ)] ![(860684615163/50000000000000 : ℝ), (88990278885797/100000000000000 : ℝ), (1857670375559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_43 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1041052511/2000000000 : ℝ)*x 0 + (-284078467/10000000000 : ℝ)*x 1 + (229179727/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1041052511/2000000000 : ℝ), (-284078467/10000000000 : ℝ), (229179727/400000000 : ℝ)] ![(2904078384243/6250000000000 : ℝ), (1529223862347/100000000000000 : ℝ), (3250345123513/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_44 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2602631299/5000000000 : ℝ)*x 0 + (1365475313/5000000000 : ℝ)*x 1 + (-3762565459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2602631299/5000000000 : ℝ), (1365475313/5000000000 : ℝ), (-3762565459/10000000000 : ℝ)] ![(46465254598487/100000000000000 : ℝ), (174329731483/800000000000 : ℝ), (3174352894803/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e005_c12_s0_48 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1747394853/2500000000 : ℝ)*x 0 + (351267709/2500000000 : ℝ)*x 1 + (750127637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (27/4 : ℝ)) 27 23 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1747394853/2500000000 : ℝ), (351267709/2500000000 : ℝ), (750127637/2500000000 : ℝ)] ![(32837422089063/50000000000000 : ℝ), (4993922833177/50000000000000 : ℝ), (24337310142761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem sign_e005_c12_s0 (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25769/10000 : ℝ) (148389/100000 : ℝ) (42359/50000 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : 0 ≤ (X 1 2+X 2 2))
    (sign2 : 0 ≤ (X 0 0+X 2 0))
    (sign3 : (X 0 2+X 2 2) ≤ 0)
    (sign4 : 0 ≤ (X 0 0+X 1 0))
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (11617/25000 : ℝ)*pair X i i := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f (by norm_num)
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
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
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (148389/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base43 : ((1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
  have base53 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign3]
  have base61 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [sign5]
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
  have hpow : (1 : ℝ) ^ (53/8 : ℝ) ≤ (1 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 53 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner1 : (2 : ℝ) ≤ (13878691/12500000 : ℝ) ^ (53/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (13878691/12500000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 53 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner2 : (3 : ℝ) ≤ (7628691/6250000 : ℝ) ^ (53/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (7628691/6250000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 53 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have major0 : P 0 ≤ (X 1 0+X 2 0)+(1378691/12500000 : ℝ)*(-(X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign0 sign1
    have hh := signed_majorant (p := p) (a := (53/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1378691/12500000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 0) (hratio 0 1 (by decide)) (hratio 0 2 (by decide))
    change lpNorm p (pair X 0) ≤ _
    rw [lpNorm_eq3 p _ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonpos sign0, abs_of_nonneg sign1] using hh
  have major1 : P 1 ≤ (X 0 1+X 2 1)+(1378691/12500000 : ℝ)*((X 0 0+X 2 0)+-(X 0 2+X 2 2)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign2 sign3
    have hh := signed_majorant (p := p) (a := (53/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1378691/12500000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 1) (hratio 1 0 (by decide)) (hratio 1 2 (by decide))
    change lpNorm p (pair X 1) ≤ _
    rw [lpNorm_eq3 p _ (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonneg sign2, abs_of_nonpos sign3] using hh
  have major2 : P 2 ≤ (X 0 2+X 1 2)+(1378691/12500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign4 sign5
    have hh := signed_majorant (p := p) (a := (53/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1378691/12500000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 2) (hratio 2 0 (by decide)) (hratio 2 1 (by decide))
    change lpNorm p (pair X 2) ≤ _
    rw [lpNorm_eq3 p _ (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonneg sign4, abs_of_nonneg sign5] using hh
  have sp0 : ((-355187033/5000000000 : ℝ)*X 0 0+(112469109/156250000 : ℝ)*X 0 1+(3333252849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((4795681311/10000000000 : ℝ)*X 2 0+(4692081303/10000000000 : ℝ)*X 2 1+(-434560807/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((7709043181/10000000000 : ℝ)*X 0 0+(219088821/10000000000 : ℝ)*X 0 1+(3090139533/10000000000 : ℝ)*X 0 2+(7709043181/10000000000 : ℝ)*X 1 0+(219088821/10000000000 : ℝ)*X 1 1+(3090139533/10000000000 : ℝ)*X 1 2+(7709043181/10000000000 : ℝ)*X 2 0+(219088821/10000000000 : ℝ)*X 2 1+(3090139533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((-60903093/2000000000 : ℝ)*X 0 0+(900207509/1000000000 : ℝ)*X 0 1+(700328423/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((240621291/500000000 : ℝ)*X 1 0+(-628350469/10000000000 : ℝ)*X 1 1+(46030619/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((240621301/500000000 : ℝ)*X 2 0+(2780611879/10000000000 : ℝ)*X 2 1+(-2062709559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((6878795943/10000000000 : ℝ)*X 0 0+(46137251/10000000000 : ℝ)*X 0 1+(4125201269/10000000000 : ℝ)*X 0 2+(6878795943/10000000000 : ℝ)*X 1 0+(46137251/10000000000 : ℝ)*X 1 1+(4125201269/10000000000 : ℝ)*X 1 2+(6878795943/10000000000 : ℝ)*X 2 0+(46137251/10000000000 : ℝ)*X 2 1+(4125201269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((-189102933/1250000000 : ℝ)*X 0 0+(259071343/312500000 : ℝ)*X 0 1+(1269225463/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1702990357/5000000000 : ℝ)*X 1 0+(-161449167/10000000000 : ℝ)*X 1 1+(933361601/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp16 : ((3405978799/10000000000 : ℝ)*X 2 0+(1321217177/2000000000 : ℝ)*X 2 1+(-720770247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp20 : ((4241150639/10000000000 : ℝ)*X 0 0+(206266951/10000000000 : ℝ)*X 0 1+(418312233/625000000 : ℝ)*X 0 2+(4241150639/10000000000 : ℝ)*X 1 0+(206266951/10000000000 : ℝ)*X 1 1+(418312233/625000000 : ℝ)*X 1 2+(4241150639/10000000000 : ℝ)*X 2 0+(206266951/10000000000 : ℝ)*X 2 1+(418312233/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp21 : ((-45232107/10000000000 : ℝ)*X 0 0+(1325409177/2000000000 : ℝ)*X 0 1+(439834831/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp22 : ((1223593391/5000000000 : ℝ)*X 1 0+(-218077663/1250000000 : ℝ)*X 1 1+(3598330261/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp23 : ((6403237811/10000000000 : ℝ)*X 2 0+(1544471369/5000000000 : ℝ)*X 2 1+(-102506051/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp27 : ((4505003641/5000000000 : ℝ)*X 0 0+(165884857/5000000000 : ℝ)*X 0 1+(684284321/5000000000 : ℝ)*X 0 2+(4505003641/5000000000 : ℝ)*X 1 0+(165884857/5000000000 : ℝ)*X 1 1+(684284321/5000000000 : ℝ)*X 1 2+(4505003641/5000000000 : ℝ)*X 2 0+(165884857/5000000000 : ℝ)*X 2 1+(684284321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp28 : ((-1256507019/10000000000 : ℝ)*X 0 0+(1027466297/1250000000 : ℝ)*X 0 1+(1619280241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_28 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp29 : ((4413992553/10000000000 : ℝ)*X 1 0+(-202129873/10000000000 : ℝ)*X 1 1+(6534705409/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_29 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp30 : ((2206996341/5000000000 : ℝ)*X 2 0+(3287381853/10000000000 : ℝ)*X 2 1+(-1012804791/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_30 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp34 : ((4398556199/5000000000 : ℝ)*X 0 0+(145506911/10000000000 : ℝ)*X 0 1+(1789930731/10000000000 : ℝ)*X 0 2+(4398556199/5000000000 : ℝ)*X 1 0+(145506911/10000000000 : ℝ)*X 1 1+(1789930731/10000000000 : ℝ)*X 1 2+(4398556199/5000000000 : ℝ)*X 2 0+(145506911/10000000000 : ℝ)*X 2 1+(1789930731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_34 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp35 : ((-59616143/2000000000 : ℝ)*X 0 0+(4288249143/5000000000 : ℝ)*X 0 1+(493227353/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_35 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp36 : ((3393209227/5000000000 : ℝ)*X 1 0+(-10580557/400000000 : ℝ)*X 1 1+(4104288261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_36 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp37 : ((1833986973/10000000000 : ℝ)*X 2 0+(136399767/200000000 : ℝ)*X 2 1+(-1405175079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_37 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp41 : ((397108713/500000000 : ℝ)*X 0 0+(299817531/10000000000 : ℝ)*X 0 1+(345066331/1250000000 : ℝ)*X 0 2+(397108713/500000000 : ℝ)*X 1 0+(299817531/10000000000 : ℝ)*X 1 1+(345066331/1250000000 : ℝ)*X 1 2+(397108713/500000000 : ℝ)*X 2 0+(299817531/10000000000 : ℝ)*X 2 1+(345066331/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_41 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp42 : ((-314214361/10000000000 : ℝ)*X 0 0+(9054143483/10000000000 : ℝ)*X 0 1+(132079871/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_42 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp43 : ((1041052511/2000000000 : ℝ)*X 1 0+(-284078467/10000000000 : ℝ)*X 1 1+(229179727/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_43 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp44 : ((2602631299/5000000000 : ℝ)*X 2 0+(1365475313/5000000000 : ℝ)*X 2 1+(-3762565459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_44 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp48 : ((1747394853/2500000000 : ℝ)*X 0 0+(351267709/2500000000 : ℝ)*X 0 1+(750127637/2500000000 : ℝ)*X 0 2+(1747394853/2500000000 : ℝ)*X 1 0+(351267709/2500000000 : ℝ)*X 1 1+(750127637/2500000000 : ℝ)*X 1 2+(1747394853/2500000000 : ℝ)*X 2 0+(351267709/2500000000 : ℝ)*X 2 1+(750127637/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e005_c12_s0_48 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have r0 : (0 : ℝ) ≤ ((11617/25000 : ℝ)*X 1 0+(1 : ℝ)*X 1 1+(11617/25000 : ℝ)*X 2 0+(1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5565761594796074347167/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (255242367/1000000000000 : ℝ)*(base7) + (1252205367417/1000000000000 : ℝ)*(base53) + (41097895961/62500000000 : ℝ)*(base61) + (2717100035349/1000000000000 : ℝ)*(major0) + (2717100035349/1000000000000 : ℝ)*(major1) + (2717100035349/1000000000000 : ℝ)*(major2) + (850359144131/500000000000 : ℝ)*(sp7) + (3359135359001/1000000000000 : ℝ)*(sp8) + (65916357091/62500000000 : ℝ)*(sp13) + (59683181131/1000000000000 : ℝ)*(sp15) + (48457713903/62500000000 : ℝ)*(sp22) + (2049264652871/500000000000 : ℝ)*(sp30) + (2493423674317/1000000000000 : ℝ)*(sp35) + (47806328419/500000000000 : ℝ)*(sp37) + (1054406471089/1000000000000 : ℝ)*(f.failure) + (209707098129/50000000000 : ℝ)*(f.sum) + (441213877/10000000000000000000000 : ℝ)*base65 + (1053331751/5000000000000000000000 : ℝ)*base67 + (52804597/250000000000000000000 : ℝ)*base69 + (1883488749/5000000000000000000000 : ℝ)*base72 + (282563959/5000000000000000000000 : ℝ)*base74 + (22093297/50000000000000000000 : ℝ)*base76 + (1411366613/5000000000000000000000 : ℝ)*base78 + (2367706941/5000000000000000000000 : ℝ)*base80 + (1168286107/2500000000000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base84 + (2441/10000000000000000 : ℝ)*base89 + (2441/10000000000000000 : ℝ)*base91 + (2441/10000000000000000 : ℝ)*base93 + hcertificate_margin
  have out0 : |(X 1 1+X 2 1)| ≤ (11617/25000 : ℝ)*(X 1 0+X 2 0) := by
    rw [abs_of_nonpos sign0]
    linarith only [r0]
  have r1 : (0 : ℝ) ≤ ((11617/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 2+(11617/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8116516066249007757/500000000000000000000 : ℝ) := by norm_num
    linear_combination (280631427933/250000000000 : ℝ)*(base7) + (46382381/25000000000 : ℝ)*(base43) + (58549998039/500000000000 : ℝ)*(base53) + (94507869431/50000000000 : ℝ)*(major0) + (94507869431/50000000000 : ℝ)*(major1) + (94507869431/50000000000 : ℝ)*(major2) + (4876551807/1000000000000 : ℝ)*(sp2) + (2285329608499/1000000000000 : ℝ)*(sp14) + (1243084196533/500000000000 : ℝ)*(sp15) + (247698380659/100000000000 : ℝ)*(sp16) + (371205238479/200000000000 : ℝ)*(sp20) + (96451573101/500000000000 : ℝ)*(sp28) + (1077008667/250000000000 : ℝ)*(sp37) + (1983909591/250000000000 : ℝ)*(sp42) + (733500480663/1000000000000 : ℝ)*(f.failure) + (1243084196533/500000000000 : ℝ)*(f.sum) + (331639373/10000000000000000000000 : ℝ)*base65 + (10252671567/10000000000000000000000 : ℝ)*base67 + (4459260281/10000000000000000000000 : ℝ)*base69 + (3158616471/10000000000000000000000 : ℝ)*base71 + (778238377/10000000000000000000000 : ℝ)*base73 + (7201477/39062500000000000000 : ℝ)*base75 + (1792975311/2500000000000000000000 : ℝ)*base77 + (1941540471/2500000000000000000000 : ℝ)*base79 + (1072614311/10000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (1/1000000000000 : ℝ)*base88 + (4847/10000000000000000 : ℝ)*base89 + (4847/10000000000000000 : ℝ)*base91 + (4847/10000000000000000 : ℝ)*base93 + hcertificate_margin
  have out1 : |(X 1 2+X 2 2)| ≤ (11617/25000 : ℝ)*(X 1 0+X 2 0) := by
    rw [abs_of_nonneg sign1]
    linarith only [r1]
  have r2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11617/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11617/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (397528503835815693417/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (83603518599/100000000000 : ℝ)*(base7) + (330337187/800000000 : ℝ)*(base43) + (69429220473/200000000000 : ℝ)*(base53) + (124616815633/1000000000000 : ℝ)*(base61) + (1004494108203/500000000000 : ℝ)*(major0) + (1004494108203/500000000000 : ℝ)*(major1) + (1004494108203/500000000000 : ℝ)*(major2) + (63645729459/1000000000000 : ℝ)*(sp8) + (849988354367/1000000000000 : ℝ)*(sp15) + (554366039813/200000000000 : ℝ)*(sp21) + (1858196115239/1000000000000 : ℝ)*(sp22) + (346478704883/125000000000 : ℝ)*(sp23) + (1615649535171/1000000000000 : ℝ)*(sp27) + (7/12500000 : ℝ)*(sp44) + (389807174591/500000000000 : ℝ)*(f.failure) + (554366039813/200000000000 : ℝ)*(f.sum) + (3321538333/10000000000000000000000 : ℝ)*base65 + (1648928181/10000000000000000000000 : ℝ)*base67 + (854168683/2500000000000000000000 : ℝ)*base70 + (2461520631/5000000000000000000000 : ℝ)*base71 + (2872784561/5000000000000000000000 : ℝ)*base73 + (8928441/2500000000000000000000 : ℝ)*base76 + (4618096337/5000000000000000000000 : ℝ)*base77 + (3913137437/5000000000000000000000 : ℝ)*base79 + (3065071251/5000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base88 + (5479/5000000000000000 : ℝ)*base89 + (5479/5000000000000000 : ℝ)*base91 + (5479/5000000000000000 : ℝ)*base93 + (1/1000000000000 : ℝ)*base96 + hcertificate_margin
  have out2 : |(X 0 0+X 2 0)| ≤ (11617/25000 : ℝ)*(X 0 1+X 2 1) := by
    rw [abs_of_nonneg sign2]
    linarith only [r2]
  have r3 : (0 : ℝ) ≤ ((11617/25000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(11617/25000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (833943774060116595993/2000000000000000000000 : ℝ) := by norm_num
    linear_combination (72918378739/500000000000 : ℝ)*(base3) + (109884079127/250000000000 : ℝ)*(base7) + (634563706991/1000000000000 : ℝ)*(base43) + (579383486427/1000000000000 : ℝ)*(base61) + (2316818352711/1000000000000 : ℝ)*(major0) + (2316818352711/1000000000000 : ℝ)*(major1) + (2316818352711/1000000000000 : ℝ)*(major2) + (79921338287/62500000000 : ℝ)*(sp0) + (238554289757/200000000000 : ℝ)*(sp6) + (1343872665811/500000000000 : ℝ)*(sp9) + (83976997033/40000000000 : ℝ)*(sp14) + (458746860517/200000000000 : ℝ)*(sp29) + (1230268793311/1000000000000 : ℝ)*(sp43) + (138084201359/200000000000 : ℝ)*(sp44) + (224767972439/250000000000 : ℝ)*(f.failure) + (3378166338417/1000000000000 : ℝ)*(f.sum) + (557293387/10000000000000000000000 : ℝ)*base65 + (245539323/10000000000000000000000 : ℝ)*base67 + (314221303/2500000000000000000000 : ℝ)*base69 + (226272679/2000000000000000000000 : ℝ)*base72 + (2210823457/10000000000000000000000 : ℝ)*base73 + (426122259/2000000000000000000000 : ℝ)*base76 + (346219573/2000000000000000000000 : ℝ)*base77 + (3964385307/10000000000000000000000 : ℝ)*base79 + (86659263/1250000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base85 + (3091/2500000000000000 : ℝ)*base89 + (3091/2500000000000000 : ℝ)*base91 + (3091/2500000000000000 : ℝ)*base93 + (1/1000000000000 : ℝ)*base96 + hcertificate_margin
  have out3 : |(X 0 2+X 2 2)| ≤ (11617/25000 : ℝ)*(X 0 1+X 2 1) := by
    rw [abs_of_nonpos sign3]
    linarith only [r3]
  have r4 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11617/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11617/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23157477610438677/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (578752182867/500000000000 : ℝ)*(base7) + (1489/976562500 : ℝ)*(base43) + (18923902837/250000000000 : ℝ)*(base53) + (461487/1000000000000 : ℝ)*(base61) + (803930005039/500000000000 : ℝ)*(major0) + (803930005039/500000000000 : ℝ)*(major1) + (803930005039/500000000000 : ℝ)*(major2) + (13115923/1000000000000 : ℝ)*(sp7) + (50500513/1000000000000 : ℝ)*(sp16) + (28558793/500000000000 : ℝ)*(sp34) + (2019213081301/1000000000000 : ℝ)*(sp35) + (252403274653/125000000000 : ℝ)*(sp36) + (2019175696711/1000000000000 : ℝ)*(sp37) + (1781398511323/1000000000000 : ℝ)*(sp41) + (77993907897/125000000000 : ℝ)*(f.failure) + (252403274653/125000000000 : ℝ)*(f.sum) + (2134759501/5000000000000000000000 : ℝ)*base65 + (1518493977/2000000000000000000000 : ℝ)*base67 + (282877753/500000000000000000000 : ℝ)*base69 + (820946187/1250000000000000000000 : ℝ)*base71 + (5104303841/10000000000000000000000 : ℝ)*base73 + (1122934133/5000000000000000000000 : ℝ)*base75 + (2487585751/5000000000000000000000 : ℝ)*base77 + (1366882693/5000000000000000000000 : ℝ)*base79 + (479774109/1000000000000000000000 : ℝ)*base81 + (293/1250000000000000 : ℝ)*base89 + (293/1250000000000000 : ℝ)*base91 + (293/1250000000000000 : ℝ)*base93 + (1/1000000000000 : ℝ)*base96 + hcertificate_margin
  have out4 : |(X 0 0+X 1 0)| ≤ (11617/25000 : ℝ)*(X 0 2+X 1 2) := by
    rw [abs_of_nonneg sign4]
    linarith only [r4]
  have r5 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 1+(11617/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 1+(11617/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4857343501658858665857/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (1077858942767/1000000000000 : ℝ)*(base43) + (165357211/62500000000 : ℝ)*(base45) + (1153454758693/1000000000000 : ℝ)*(base53) + (2918116462159/1000000000000 : ℝ)*(major0) + (2918116462159/1000000000000 : ℝ)*(major1) + (2918116462159/1000000000000 : ℝ)*(major2) + (449877082967/1000000000000 : ℝ)*(sp2) + (2221098615093/500000000000 : ℝ)*(sp7) + (3211092449851/1000000000000 : ℝ)*(sp8) + (857323842221/1000000000000 : ℝ)*(sp23) + (12463837479/125000000000 : ℝ)*(sp28) + (1330815480167/1000000000000 : ℝ)*(sp36) + (323470700483/100000000000 : ℝ)*(sp44) + (1132413544243/1000000000000 : ℝ)*(sp48) + (1132413544243/1000000000000 : ℝ)*(f.failure) + (2270953965009/500000000000 : ℝ)*(f.sum) + (992893709/5000000000000000000000 : ℝ)*base66 + (17911681/125000000000000000000 : ℝ)*base67 + (1488851/312500000000000000000 : ℝ)*base70 + (334092277/5000000000000000000000 : ℝ)*base72 + (633670777/5000000000000000000000 : ℝ)*base74 + (1578066017/10000000000000000000000 : ℝ)*base75 + (557889/625000000000000000000 : ℝ)*base78 + (872176973/10000000000000000000000 : ℝ)*base79 + (1319050929/10000000000000000000000 : ℝ)*base82 + (7867/10000000000000000 : ℝ)*base89 + (7867/10000000000000000 : ℝ)*base91 + (7867/10000000000000000 : ℝ)*base93 + hcertificate_margin
  have out5 : |(X 0 1+X 1 1)| ≤ (11617/25000 : ℝ)*(X 0 2+X 1 2) := by
    rw [abs_of_nonneg sign5]
    linarith only [r5]
  intro i h hij
  fin_cases i <;> fin_cases h <;> try contradiction
  · change |pair X 0 1| ≤ (11617/25000 : ℝ)*pair X 0 0
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out0
  · change |pair X 0 2| ≤ (11617/25000 : ℝ)*pair X 0 0
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out1
  · change |pair X 1 0| ≤ (11617/25000 : ℝ)*pair X 1 1
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out2
  · change |pair X 1 2| ≤ (11617/25000 : ℝ)*pair X 1 1
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out3
  · change |pair X 2 0| ≤ (11617/25000 : ℝ)*pair X 2 2
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out4
  · change |pair X 2 1| ≤ (11617/25000 : ℝ)*pair X 2 2
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out5

end HlawkaSchatten.DiagonalCutoff6


open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem solution (p : ℝ) (hpa : (53/8 : ℝ) ≤ p) (hpb : p ≤ (27/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25769/10000 : ℝ) (148389/100000 : ℝ) (42359/50000 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : 0 ≤ (X 1 2+X 2 2))
    (sign2 : 0 ≤ (X 0 0+X 2 0))
    (sign3 : (X 0 2+X 2 2) ≤ 0)
    (sign4 : 0 ≤ (X 0 0+X 1 0))
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (11617/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff6.sign_e005_c12_s0 p hpa hpb X hX sign0 sign1 sign2 sign3 sign4 sign5 hratio

#print axioms solution
