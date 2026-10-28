-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff6.sign_e007_c10_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T19:32:36.27049+00:00
-- url     : https://prove2.me/submissions/83565033-cb4f-47cf-9928-d6b8c7e1f199

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
theorem support_e007_c10_s0_0 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (-220117967/5000000000 : ℝ)*x 0 + (807364357/1250000000 : ℝ)*x 1 + (4297578343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-220117967/5000000000 : ℝ), (807364357/1250000000 : ℝ), (4297578343/10000000000 : ℝ)] ![(2615971873089/100000000000000 : ℝ), (15012723805451/25000000000000 : ℝ), (37333132886707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_1 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (6458913407/10000000000 : ℝ)*x 0 + (-55029479/1250000000 : ℝ)*x 1 + (4297579963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(6458913407/10000000000 : ℝ), (-55029479/1250000000 : ℝ), (4297579963/10000000000 : ℝ)] ![(1876589984519/3125000000000 : ℝ), (2615971165967/100000000000000 : ℝ), (2333321831573/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_6 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (1304721521/10000000000 : ℝ)*x 0 + (1304721839/10000000000 : ℝ)*x 1 + (8384293829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1304721521/10000000000 : ℝ), (1304721839/10000000000 : ℝ), (8384293829/10000000000 : ℝ)] ![(1858378301589/20000000000000 : ℝ), (9291894150111/100000000000000 : ℝ), (40708107165103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_7 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (-120381553/2000000000 : ℝ)*x 0 + (1986273551/2500000000 : ℝ)*x 1 + (2492098487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-120381553/2000000000 : ℝ), (1986273551/2500000000 : ℝ), (2492098487/10000000000 : ℝ)] ![(58875999969/1562500000000 : ℝ), (38231285147953/50000000000000 : ℝ), (1976936569553/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_8 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (1223331337/2000000000 : ℝ)*x 0 + (-585931903/2000000000 : ℝ)*x 1 + (31151231/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1223331337/2000000000 : ℝ), (-585931903/2000000000 : ℝ), (31151231/125000000 : ℝ)] ![(14088771688387/25000000000000 : ℝ), (746110862517/3125000000000 : ℝ), (3953873126149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_9 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (577336199/1250000000 : ℝ)*x 0 + (810167419/2500000000 : ℝ)*x 1 + (-238720769/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(577336199/1250000000 : ℝ), (810167419/2500000000 : ℝ), (-238720769/625000000 : ℝ)] ![(40607405118389/100000000000000 : ℝ), (6714503453501/25000000000000 : ℝ), (32534581052723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_13 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (132556667/1250000000 : ℝ)*x 0 + (2556951/2500000000 : ℝ)*x 1 + (187369573/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(132556667/1250000000 : ℝ), (2556951/2500000000 : ℝ), (187369573/200000000 : ℝ)] ![(1823952392251/25000000000000 : ℝ), (32464804829/100000000000000 : ℝ), (2316793140357/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_14 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (-60418441/400000000 : ℝ)*x 0 + (345631559/400000000 : ℝ)*x 1 + (90062967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-60418441/400000000 : ℝ), (345631559/400000000 : ℝ), (90062967/1250000000 : ℝ)] ![(11022863871687/100000000000000 : ℝ), (16865878255567/20000000000000 : ℝ), (4647744831647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_15 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (4910618459/10000000000 : ℝ)*x 0 + (-46482767/2000000000 : ℝ)*x 1 + (3001771411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(4910618459/10000000000 : ℝ), (-46482767/2000000000 : ℝ), (3001771411/5000000000 : ℝ)] ![(5452163909981/12500000000000 : ℝ), (77598320867/6250000000000 : ℝ), (55141115571719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_16 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (3208640851/10000000000 : ℝ)*x 0 + (6938810447/10000000000 : ℝ)*x 1 + (-1167682381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3208640851/10000000000 : ℝ), (6938810447/10000000000 : ℝ), (-1167682381/10000000000 : ℝ)] ![(2654857976727/10000000000000 : ℝ), (65287874140513/100000000000000 : ℝ), (8163546078891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_20 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (163666337/1000000000 : ℝ)*x 0 + (251832527/10000000000 : ℝ)*x 1 + (4416936369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(163666337/1000000000 : ℝ), (251832527/10000000000 : ℝ), (4416936369/5000000000 : ℝ)] ![(3026164960941/25000000000000 : ℝ), (1363422512357/100000000000000 : ℝ), (86531917630331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_21 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (-585931903/2000000000 : ℝ)*x 0 + (1223331337/2000000000 : ℝ)*x 1 + (31151231/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-585931903/2000000000 : ℝ), (1223331337/2000000000 : ℝ), (31151231/125000000 : ℝ)] ![(746110862517/3125000000000 : ℝ), (14088771688387/25000000000000 : ℝ), (3953873126149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_22 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (1986273551/2500000000 : ℝ)*x 0 + (-120381553/2000000000 : ℝ)*x 1 + (2492098487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1986273551/2500000000 : ℝ), (-120381553/2000000000 : ℝ), (2492098487/10000000000 : ℝ)] ![(38231285147953/50000000000000 : ℝ), (58875999969/1562500000000 : ℝ), (1976936569553/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_23 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (810167419/2500000000 : ℝ)*x 0 + (577336199/1250000000 : ℝ)*x 1 + (-238720769/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(810167419/2500000000 : ℝ), (577336199/1250000000 : ℝ), (-238720769/625000000 : ℝ)] ![(6714503453501/25000000000000 : ℝ), (40607405118389/100000000000000 : ℝ), (32534581052723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_27 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (2556951/2500000000 : ℝ)*x 0 + (132556667/1250000000 : ℝ)*x 1 + (187369573/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2556951/2500000000 : ℝ), (132556667/1250000000 : ℝ), (187369573/200000000 : ℝ)] ![(32464804829/100000000000000 : ℝ), (1823952392251/25000000000000 : ℝ), (2316793140357/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_28 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (-46482767/2000000000 : ℝ)*x 0 + (4910618459/10000000000 : ℝ)*x 1 + (3001771411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-46482767/2000000000 : ℝ), (4910618459/10000000000 : ℝ), (3001771411/5000000000 : ℝ)] ![(77598320867/6250000000000 : ℝ), (5452163909981/12500000000000 : ℝ), (55141115571719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_29 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (345631559/400000000 : ℝ)*x 0 + (-60418441/400000000 : ℝ)*x 1 + (90062967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(345631559/400000000 : ℝ), (-60418441/400000000 : ℝ), (90062967/1250000000 : ℝ)] ![(16865878255567/20000000000000 : ℝ), (11022863871687/100000000000000 : ℝ), (4647744831647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_30 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (6938810447/10000000000 : ℝ)*x 0 + (3208640851/10000000000 : ℝ)*x 1 + (-1167682381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(6938810447/10000000000 : ℝ), (3208640851/10000000000 : ℝ), (-1167682381/10000000000 : ℝ)] ![(65287874140513/100000000000000 : ℝ), (2654857976727/10000000000000 : ℝ), (8163546078891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_34 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (251832527/10000000000 : ℝ)*x 0 + (163666337/1000000000 : ℝ)*x 1 + (4416936369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(251832527/10000000000 : ℝ), (163666337/1000000000 : ℝ), (4416936369/5000000000 : ℝ)] ![(1363422512357/100000000000000 : ℝ), (3026164960941/25000000000000 : ℝ), (86531917630331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_35 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (-220772753/10000000000 : ℝ)*x 0 + (8393810329/10000000000 : ℝ)*x 1 + (222351161/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-220772753/10000000000 : ℝ), (8393810329/10000000000 : ℝ), (222351161/1000000000 : ℝ)] ![(1169328097789/100000000000000 : ℝ), (81524036860697/100000000000000 : ℝ), (4326658755921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_36 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (1049226191/1250000000 : ℝ)*x 0 + (-220772691/10000000000 : ℝ)*x 1 + (555878163/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1049226191/1250000000 : ℝ), (-220772691/10000000000 : ℝ), (555878163/2500000000 : ℝ)] ![(4076201389223/5000000000000 : ℝ), (584663857337/50000000000000 : ℝ), (4326661121447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_37 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (104670253/500000000 : ℝ)*x 0 + (6741439651/10000000000 : ℝ)*x 1 + (-519376789/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(104670253/500000000 : ℝ), (6741439651/10000000000 : ℝ), (-519376789/2000000000 : ℝ)] ![(16131031818133/100000000000000 : ℝ), (31563229316293/50000000000000 : ℝ), (1296406845633/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_41 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (5820454927/10000000000 : ℝ)*x 0 + (824763/31250000 : ℝ)*x 1 + (50798177/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5820454927/10000000000 : ℝ), (824763/31250000 : ℝ), (50798177/100000000 : ℝ)] ![(332401597931/625000000000 : ℝ), (1440098968507/100000000000000 : ℝ), (22687822676391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_43 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (8393810329/10000000000 : ℝ)*x 0 + (-220772753/10000000000 : ℝ)*x 1 + (222351161/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(8393810329/10000000000 : ℝ), (-220772753/10000000000 : ℝ), (222351161/1000000000 : ℝ)] ![(81524036860697/100000000000000 : ℝ), (1169328097789/100000000000000 : ℝ), (4326658755921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_44 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (6741439651/10000000000 : ℝ)*x 0 + (104670253/500000000 : ℝ)*x 1 + (-519376789/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(6741439651/10000000000 : ℝ), (104670253/500000000 : ℝ), (-519376789/2000000000 : ℝ)] ![(31563229316293/50000000000000 : ℝ), (16131031818133/100000000000000 : ℝ), (1296406845633/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e007_c10_s0_48 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ)) (x : Fin 3 → ℝ) :
    (824763/31250000 : ℝ)*x 0 + (5820454927/10000000000 : ℝ)*x 1 + (50798177/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (7 : ℝ)) 7 6 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(824763/31250000 : ℝ), (5820454927/10000000000 : ℝ), (50798177/100000000 : ℝ)] ![(1440098968507/100000000000000 : ℝ), (332401597931/625000000000 : ℝ), (22687822676391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem sign_e007_c10_s0 (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (268667/100000 : ℝ) (146973/100000 : ℝ) (8523/10000 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : 0 ≤ (X 1 2+X 2 2))
    (sign2 : (X 0 0+X 2 0) ≤ 0)
    (sign3 : 0 ≤ (X 0 2+X 2 2))
    (sign4 : 0 ≤ (X 0 0+X 1 0))
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (2901/6250 : ℝ)*pair X i i := by
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
  have base7 : ((1 : ℝ)*T) ≤ (146973/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
  have base34 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1, f.sum]
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base43 : ((1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
  have base51 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [sign2]
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpow : (1 : ℝ) ^ (55/8 : ℝ) ≤ (1 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 55 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner1 : (2 : ℝ) ≤ (110607909/100000000 : ℝ) ^ (55/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (110607909/100000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 55 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner2 : (3 : ℝ) ≤ (60607909/50000000 : ℝ) ^ (55/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (60607909/50000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 55 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have major0 : P 0 ≤ (X 1 0+X 2 0)+(10607909/100000000 : ℝ)*(-(X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign0 sign1
    have hh := signed_majorant (p := p) (a := (55/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (10607909/100000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 0) (hratio 0 1 (by decide)) (hratio 0 2 (by decide))
    change lpNorm p (pair X 0) ≤ _
    rw [lpNorm_eq3 p _ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonpos sign0, abs_of_nonneg sign1] using hh
  have major1 : P 1 ≤ (X 0 1+X 2 1)+(10607909/100000000 : ℝ)*(-(X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign2 sign3
    have hh := signed_majorant (p := p) (a := (55/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (10607909/100000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 1) (hratio 1 0 (by decide)) (hratio 1 2 (by decide))
    change lpNorm p (pair X 1) ≤ _
    rw [lpNorm_eq3 p _ (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonpos sign2, abs_of_nonneg sign3] using hh
  have major2 : P 2 ≤ (X 0 2+X 1 2)+(10607909/100000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign4 sign5
    have hh := signed_majorant (p := p) (a := (55/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (10607909/100000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 2) (hratio 2 0 (by decide)) (hratio 2 1 (by decide))
    change lpNorm p (pair X 2) ≤ _
    rw [lpNorm_eq3 p _ (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonneg sign4, abs_of_nonneg sign5] using hh
  have sp0 : ((-220117967/5000000000 : ℝ)*X 0 0+(807364357/1250000000 : ℝ)*X 0 1+(4297578343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((6458913407/10000000000 : ℝ)*X 1 0+(-55029479/1250000000 : ℝ)*X 1 1+(4297579963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1304721521/10000000000 : ℝ)*X 0 0+(1304721839/10000000000 : ℝ)*X 0 1+(8384293829/10000000000 : ℝ)*X 0 2+(1304721521/10000000000 : ℝ)*X 1 0+(1304721839/10000000000 : ℝ)*X 1 1+(8384293829/10000000000 : ℝ)*X 1 2+(1304721521/10000000000 : ℝ)*X 2 0+(1304721839/10000000000 : ℝ)*X 2 1+(8384293829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((-120381553/2000000000 : ℝ)*X 0 0+(1986273551/2500000000 : ℝ)*X 0 1+(2492098487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((1223331337/2000000000 : ℝ)*X 1 0+(-585931903/2000000000 : ℝ)*X 1 1+(31151231/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((577336199/1250000000 : ℝ)*X 2 0+(810167419/2500000000 : ℝ)*X 2 1+(-238720769/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((132556667/1250000000 : ℝ)*X 0 0+(2556951/2500000000 : ℝ)*X 0 1+(187369573/200000000 : ℝ)*X 0 2+(132556667/1250000000 : ℝ)*X 1 0+(2556951/2500000000 : ℝ)*X 1 1+(187369573/200000000 : ℝ)*X 1 2+(132556667/1250000000 : ℝ)*X 2 0+(2556951/2500000000 : ℝ)*X 2 1+(187369573/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((-60418441/400000000 : ℝ)*X 0 0+(345631559/400000000 : ℝ)*X 0 1+(90062967/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4910618459/10000000000 : ℝ)*X 1 0+(-46482767/2000000000 : ℝ)*X 1 1+(3001771411/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp16 : ((3208640851/10000000000 : ℝ)*X 2 0+(6938810447/10000000000 : ℝ)*X 2 1+(-1167682381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp20 : ((163666337/1000000000 : ℝ)*X 0 0+(251832527/10000000000 : ℝ)*X 0 1+(4416936369/5000000000 : ℝ)*X 0 2+(163666337/1000000000 : ℝ)*X 1 0+(251832527/10000000000 : ℝ)*X 1 1+(4416936369/5000000000 : ℝ)*X 1 2+(163666337/1000000000 : ℝ)*X 2 0+(251832527/10000000000 : ℝ)*X 2 1+(4416936369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp21 : ((-585931903/2000000000 : ℝ)*X 0 0+(1223331337/2000000000 : ℝ)*X 0 1+(31151231/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp22 : ((1986273551/2500000000 : ℝ)*X 1 0+(-120381553/2000000000 : ℝ)*X 1 1+(2492098487/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp23 : ((810167419/2500000000 : ℝ)*X 2 0+(577336199/1250000000 : ℝ)*X 2 1+(-238720769/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp27 : ((2556951/2500000000 : ℝ)*X 0 0+(132556667/1250000000 : ℝ)*X 0 1+(187369573/200000000 : ℝ)*X 0 2+(2556951/2500000000 : ℝ)*X 1 0+(132556667/1250000000 : ℝ)*X 1 1+(187369573/200000000 : ℝ)*X 1 2+(2556951/2500000000 : ℝ)*X 2 0+(132556667/1250000000 : ℝ)*X 2 1+(187369573/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp28 : ((-46482767/2000000000 : ℝ)*X 0 0+(4910618459/10000000000 : ℝ)*X 0 1+(3001771411/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_28 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp29 : ((345631559/400000000 : ℝ)*X 1 0+(-60418441/400000000 : ℝ)*X 1 1+(90062967/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_29 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp30 : ((6938810447/10000000000 : ℝ)*X 2 0+(3208640851/10000000000 : ℝ)*X 2 1+(-1167682381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_30 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp34 : ((251832527/10000000000 : ℝ)*X 0 0+(163666337/1000000000 : ℝ)*X 0 1+(4416936369/5000000000 : ℝ)*X 0 2+(251832527/10000000000 : ℝ)*X 1 0+(163666337/1000000000 : ℝ)*X 1 1+(4416936369/5000000000 : ℝ)*X 1 2+(251832527/10000000000 : ℝ)*X 2 0+(163666337/1000000000 : ℝ)*X 2 1+(4416936369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_34 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp35 : ((-220772753/10000000000 : ℝ)*X 0 0+(8393810329/10000000000 : ℝ)*X 0 1+(222351161/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_35 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp36 : ((1049226191/1250000000 : ℝ)*X 1 0+(-220772691/10000000000 : ℝ)*X 1 1+(555878163/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_36 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp37 : ((104670253/500000000 : ℝ)*X 2 0+(6741439651/10000000000 : ℝ)*X 2 1+(-519376789/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_37 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp41 : ((5820454927/10000000000 : ℝ)*X 0 0+(824763/31250000 : ℝ)*X 0 1+(50798177/100000000 : ℝ)*X 0 2+(5820454927/10000000000 : ℝ)*X 1 0+(824763/31250000 : ℝ)*X 1 1+(50798177/100000000 : ℝ)*X 1 2+(5820454927/10000000000 : ℝ)*X 2 0+(824763/31250000 : ℝ)*X 2 1+(50798177/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_41 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp43 : ((8393810329/10000000000 : ℝ)*X 1 0+(-220772753/10000000000 : ℝ)*X 1 1+(222351161/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_43 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp44 : ((6741439651/10000000000 : ℝ)*X 2 0+(104670253/500000000 : ℝ)*X 2 1+(-519376789/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_44 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp48 : ((824763/31250000 : ℝ)*X 0 0+(5820454927/10000000000 : ℝ)*X 0 1+(50798177/100000000 : ℝ)*X 0 2+(824763/31250000 : ℝ)*X 1 0+(5820454927/10000000000 : ℝ)*X 1 1+(50798177/100000000 : ℝ)*X 1 2+(824763/31250000 : ℝ)*X 2 0+(5820454927/10000000000 : ℝ)*X 2 1+(50798177/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e007_c10_s0_48 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have r0 : (0 : ℝ) ≤ ((2901/6250 : ℝ)*X 1 0+(1 : ℝ)*X 1 1+(2901/6250 : ℝ)*X 2 0+(1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40131453069572307741/250000000000000000000 : ℝ) := by norm_num
    linear_combination (116584974159/125000000000 : ℝ)*(base7) + (388397146099/500000000000 : ℝ)*(base37) + (31588400377/500000000000 : ℝ)*(base61) + (143987922337/62500000000 : ℝ)*(major0) + (143987922337/62500000000 : ℝ)*(major1) + (143987922337/62500000000 : ℝ)*(major2) + (49715897531/125000000000 : ℝ)*(sp0) + (713981479137/1000000000000 : ℝ)*(sp7) + (1598973750457/500000000000 : ℝ)*(sp8) + (3177917031559/1000000000000 : ℝ)*(sp9) + (253345187217/250000000000 : ℝ)*(sp13) + (1304156389/31250000000 : ℝ)*(sp15) + (15440868451/250000000000 : ℝ)*(sp23) + (2127971845977/1000000000000 : ℝ)*(sp35) + (428747623897/500000000000 : ℝ)*(f.failure) + (3239680505363/1000000000000 : ℝ)*(f.sum) + (412853/1000000000000000000000 : ℝ)*base66 + (6683924259/10000000000000000000000 : ℝ)*base67 + (6478436847/10000000000000000000000 : ℝ)*base69 + (815289343/1000000000000000000000 : ℝ)*base71 + (1896045541/5000000000000000000000 : ℝ)*base74 + (901147703/1250000000000000000000 : ℝ)*base75 + (66946053/250000000000000000000 : ℝ)*base77 + (444447119/2500000000000000000000 : ℝ)*base79 + (254592969/1250000000000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base84 + (1/1000000000000 : ℝ)*base86 + (64701/50000000000000000 : ℝ)*base90 + (64701/50000000000000000 : ℝ)*base92 + (64701/50000000000000000 : ℝ)*base94 + hcertificate_margin
  have out0 : |(X 1 1+X 2 1)| ≤ (2901/6250 : ℝ)*(X 1 0+X 2 0) := by
    rw [abs_of_nonpos sign0]
    linarith only [r0]
  have r1 : (0 : ℝ) ≤ ((2901/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 2+(2901/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (156072624846259287/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (1181698051451/1000000000000 : ℝ)*(base7) + (8174859/1000000000000 : ℝ)*(base11) + (82393/250000000000 : ℝ)*(base34) + (6677/1000000000000 : ℝ)*(base51) + (75924696681/50000000000 : ℝ)*(major0) + (94905850253/62500000000 : ℝ)*(major1) + (75924696681/50000000000 : ℝ)*(major2) + (2082499/100000000000 : ℝ)*(sp6) + (40096709/500000000000 : ℝ)*(sp13) + (473202143483/250000000000 : ℝ)*(sp14) + (378572284091/200000000000 : ℝ)*(sp15) + (1892861090883/1000000000000 : ℝ)*(sp16) + (218349073127/125000000000 : ℝ)*(sp20) + (11085523/250000000000 : ℝ)*(sp35) + (565195551973/1000000000000 : ℝ)*(f.failure) + (378572284091/200000000000 : ℝ)*(f.sum) + (374450891/5000000000000000000000 : ℝ)*base66 + (555011959/5000000000000000000000 : ℝ)*base67 + (217045891/1000000000000000000000 : ℝ)*base69 + (447862997/10000000000000000000000 : ℝ)*base71 + (241028811/10000000000000000000000 : ℝ)*base73 + (755406943/2500000000000000000000 : ℝ)*base75 + (1508040791/10000000000000000000000 : ℝ)*base78 + (134024237/2000000000000000000000 : ℝ)*base79 + (640249481/2000000000000000000000 : ℝ)*base81 + (70009/100000000000000000 : ℝ)*base90 + (70009/100000000000000000 : ℝ)*base92 + (70009/100000000000000000 : ℝ)*base94 + hcertificate_margin
  have out1 : |(X 1 2+X 2 2)| ≤ (2901/6250 : ℝ)*(X 1 0+X 2 0) := by
    rw [abs_of_nonneg sign1]
    linarith only [r1]
  have r2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2901/6250 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2901/6250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (80262904159234008387/500000000000000000000 : ℝ) := by norm_num
    linear_combination (932679793029/1000000000000 : ℝ)*(base7) + (194198575813/250000000000 : ℝ)*(base37) + (63176799717/1000000000000 : ℝ)*(base59) + (2303806757227/1000000000000 : ℝ)*(major0) + (2303806757227/1000000000000 : ℝ)*(major1) + (2303806757227/1000000000000 : ℝ)*(major2) + (198863414863/500000000000 : ℝ)*(sp1) + (61763470063/1000000000000 : ℝ)*(sp9) + (399743438077/125000000000 : ℝ)*(sp21) + (713981755133/1000000000000 : ℝ)*(sp22) + (1588958518237/500000000000 : ℝ)*(sp23) + (1013380737511/1000000000000 : ℝ)*(sp27) + (41733001921/1000000000000 : ℝ)*(sp28) + (1063985960839/500000000000 : ℝ)*(sp43) + (857495247733/1000000000000 : ℝ)*(f.failure) + (3239680506537/1000000000000 : ℝ)*(f.sum) + (654842431/10000000000000000000000 : ℝ)*base65 + (1607854019/2000000000000000000000 : ℝ)*base68 + (115665239/78125000000000000000 : ℝ)*base70 + (415780961/500000000000000000000 : ℝ)*base72 + (19719477/2000000000000000000000 : ℝ)*base74 + (13714651339/10000000000000000000000 : ℝ)*base76 + (100128701/156250000000000000000 : ℝ)*base78 + (779651149/1250000000000000000000 : ℝ)*base80 + (3040650151/5000000000000000000000 : ℝ)*base82 + (18089/100000000000000000 : ℝ)*base90 + (18089/100000000000000000 : ℝ)*base92 + (18089/100000000000000000 : ℝ)*base94 + (1/1000000000000 : ℝ)*base95 + hcertificate_margin
  have out2 : |(X 0 0+X 2 0)| ≤ (2901/6250 : ℝ)*(X 0 1+X 2 1) := by
    rw [abs_of_nonpos sign2]
    linarith only [r2]
  have r3 : (0 : ℝ) ≤ ((2901/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(2901/6250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (39018156835626483/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (1181698051451/1000000000000 : ℝ)*(base7) + (8174859/1000000000000 : ℝ)*(base15) + (82393/250000000000 : ℝ)*(base29) + (6677/1000000000000 : ℝ)*(base43) + (94905850253/62500000000 : ℝ)*(major0) + (75924696681/50000000000 : ℝ)*(major1) + (75924696681/50000000000 : ℝ)*(major2) + (10412499/500000000000 : ℝ)*(sp6) + (3207737/40000000000 : ℝ)*(sp27) + (378572284091/200000000000 : ℝ)*(sp28) + (473202143483/250000000000 : ℝ)*(sp29) + (1892861090883/1000000000000 : ℝ)*(sp30) + (1746792585001/1000000000000 : ℝ)*(sp34) + (11085523/250000000000 : ℝ)*(sp43) + (565195551973/1000000000000 : ℝ)*(f.failure) + (378572284091/200000000000 : ℝ)*(f.sum) + (6574837/500000000000000000000 : ℝ)*base65 + (514518663/10000000000000000000000 : ℝ)*base67 + (143800883/500000000000000000000 : ℝ)*base69 + (1000491847/10000000000000000000000 : ℝ)*base71 + (170561529/2500000000000000000000 : ℝ)*base74 + (1012424399/5000000000000000000000 : ℝ)*base75 + (280294557/5000000000000000000000 : ℝ)*base77 + (11531081/80000000000000000000 : ℝ)*base80 + (3055637293/10000000000000000000000 : ℝ)*base81 + (70009/100000000000000000 : ℝ)*base90 + (70009/100000000000000000 : ℝ)*base92 + (70009/100000000000000000 : ℝ)*base94 + hcertificate_margin
  have out3 : |(X 0 2+X 2 2)| ≤ (2901/6250 : ℝ)*(X 0 1+X 2 1) := by
    rw [abs_of_nonneg sign3]
    linarith only [r3]
  have r4 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2901/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2901/6250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5989515564991229133/1000000000000000000000 : ℝ) := by norm_num
    linear_combination (1174383646519/1000000000000 : ℝ)*(base7) + (7690889/62500000000 : ℝ)*(base43) + (7898229/31250000000 : ℝ)*(base51) + (1679726274929/1000000000000 : ℝ)*(major0) + (1679726274929/1000000000000 : ℝ)*(major1) + (1679726274929/1000000000000 : ℝ)*(major2) + (638118903/500000000000 : ℝ)*(sp7) + (228063161/1000000000000 : ℝ)*(sp14) + (3668783797/200000000000 : ℝ)*(sp16) + (7413011/3125000000 : ℝ)*(sp23) + (1077700968103/500000000000 : ℝ)*(sp35) + (534047538667/250000000000 : ℝ)*(sp37) + (1799591161743/1000000000000 : ℝ)*(sp41) + (2156906237173/1000000000000 : ℝ)*(sp43) + (25008300609/40000000000 : ℝ)*(f.failure) + (2156906237173/1000000000000 : ℝ)*(f.sum) + (1594375243/2500000000000000000000 : ℝ)*base65 + (4065337047/10000000000000000000000 : ℝ)*base67 + (2238737161/5000000000000000000000 : ℝ)*base69 + (2815964211/5000000000000000000000 : ℝ)*base71 + (2891263611/10000000000000000000000 : ℝ)*base74 + (434801647/1000000000000000000000 : ℝ)*base75 + (566481269/625000000000000000000 : ℝ)*base77 + (909582017/10000000000000000000000 : ℝ)*base79 + (87627989/400000000000000000000 : ℝ)*base81 + (2203/4000000000000000 : ℝ)*base89 + (2203/4000000000000000 : ℝ)*base91 + (2203/4000000000000000 : ℝ)*base93 + (1/1000000000000 : ℝ)*base96 + hcertificate_margin
  have out4 : |(X 0 0+X 1 0)| ≤ (2901/6250 : ℝ)*(X 0 2+X 1 2) := by
    rw [abs_of_nonneg sign4]
    linarith only [r4]
  have r5 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 1+(2901/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 1+(2901/6250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (479160055072637373/80000000000000000000 : ℝ) := by norm_num
    linear_combination (587191818291/500000000000 : ℝ)*(base7) + (252734373/1000000000000 : ℝ)*(base43) + (15381821/125000000000 : ℝ)*(base51) + (167972626977/100000000000 : ℝ)*(major0) + (167972626977/100000000000 : ℝ)*(major1) + (167972626977/100000000000 : ℝ)*(major2) + (2372195939/1000000000000 : ℝ)*(sp9) + (1273045517/1000000000000 : ℝ)*(sp22) + (228986991/1000000000000 : ℝ)*(sp29) + (4585995947/250000000000 : ℝ)*(sp30) + (539226559649/250000000000 : ℝ)*(sp35) + (269425525761/125000000000 : ℝ)*(sp36) + (213619005887/100000000000 : ℝ)*(sp44) + (1799591149887/1000000000000 : ℝ)*(sp48) + (78150939163/125000000000 : ℝ)*(f.failure) + (539226559649/250000000000 : ℝ)*(f.sum) + (88301217/2500000000000000000000 : ℝ)*base65 + (5933191667/10000000000000000000000 : ℝ)*base67 + (199469677/500000000000000000000 : ℝ)*base69 + (7074408923/10000000000000000000000 : ℝ)*base71 + (2399964839/10000000000000000000000 : ℝ)*base73 + (3633336569/10000000000000000000000 : ℝ)*base75 + (9541293/5000000000000000000000 : ℝ)*base77 + (4192212199/10000000000000000000000 : ℝ)*base79 + (859890467/5000000000000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base87 + (19279/12500000000000000 : ℝ)*base90 + (19279/12500000000000000 : ℝ)*base92 + (19279/12500000000000000 : ℝ)*base94 + (1/1000000000000 : ℝ)*base95 + hcertificate_margin
  have out5 : |(X 0 1+X 1 1)| ≤ (2901/6250 : ℝ)*(X 0 2+X 1 2) := by
    rw [abs_of_nonneg sign5]
    linarith only [r5]
  intro i h hij
  fin_cases i <;> fin_cases h <;> try contradiction
  · change |pair X 0 1| ≤ (2901/6250 : ℝ)*pair X 0 0
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out0
  · change |pair X 0 2| ≤ (2901/6250 : ℝ)*pair X 0 0
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out1
  · change |pair X 1 0| ≤ (2901/6250 : ℝ)*pair X 1 1
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out2
  · change |pair X 1 2| ≤ (2901/6250 : ℝ)*pair X 1 1
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out3
  · change |pair X 2 0| ≤ (2901/6250 : ℝ)*pair X 2 2
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out4
  · change |pair X 2 1| ≤ (2901/6250 : ℝ)*pair X 2 2
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out5

end HlawkaSchatten.DiagonalCutoff6


open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem solution (p : ℝ) (hpa : (55/8 : ℝ) ≤ p) (hpb : p ≤ (7 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (268667/100000 : ℝ) (146973/100000 : ℝ) (8523/10000 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : 0 ≤ (X 1 2+X 2 2))
    (sign2 : (X 0 0+X 2 0) ≤ 0)
    (sign3 : 0 ≤ (X 0 2+X 2 2))
    (sign4 : 0 ≤ (X 0 0+X 1 0))
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (2901/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff6.sign_e007_c10_s0 p hpa hpb X hX sign0 sign1 sign2 sign3 sign4 sign5 hratio

#print axioms solution
