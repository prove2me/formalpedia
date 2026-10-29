-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1327_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:46:02.980392+00:00
-- url     : https://prove2.me/submissions/3d4ed9f9-c7cf-408f-8723-6891794f287f

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
theorem support_rectangle_w1327_s0_0 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1818047043/10000000000 : ℝ)*x 0 + (3001710273/5000000000 : ℝ)*x 1 + (961463509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1818047043/10000000000 : ℝ)^4287 ≤ (2661908918741/25000000000000 : ℝ)^3263 := by
    have hnat : (1818047043 : ℕ)^4287*25000000000000^3263 ≤ 2661908918741^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818047043 10000000000 2661908918741 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3001710273/5000000000 : ℝ)^4287 ≤ (12787790548927/25000000000000 : ℝ)^3263 := by
    have hnat : (3001710273 : ℕ)^4287*25000000000000^3263 ≤ 12787790548927^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3001710273 5000000000 12787790548927 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961463509/2000000000 : ℝ)^4287 ≤ (19100601057529/50000000000000 : ℝ)^3263 := by
    have hnat : (961463509 : ℕ)^4287*50000000000000^3263 ≤ 19100601057529^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961463509 2000000000 19100601057529 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1818047043/10000000000 : ℝ), (3001710273/5000000000 : ℝ), (961463509/2000000000 : ℝ)] ![(2661908918741/25000000000000 : ℝ), (12787790548927/25000000000000 : ℝ), (19100601057529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1818047043/10000000000 : ℝ)|^4287 ≤ (2661908918741/25000000000000 : ℝ)^3263
        have hw : |(-1818047043/10000000000 : ℝ)|=(1818047043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3001710273/5000000000 : ℝ)|^4287 ≤ (12787790548927/25000000000000 : ℝ)^3263
        have hw : |(3001710273/5000000000 : ℝ)|=(3001710273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(961463509/2000000000 : ℝ)|^4287 ≤ (19100601057529/50000000000000 : ℝ)^3263
        have hw : |(961463509/2000000000 : ℝ)|=(961463509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s0_1 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5503493333/10000000000 : ℝ)*x 0 + (-2498651041/10000000000 : ℝ)*x 1 + (1201829449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5503493333/10000000000 : ℝ)^4287 ≤ (4562944400931/10000000000000 : ℝ)^3263 := by
    have hnat : (5503493333 : ℕ)^4287*10000000000000^3263 ≤ 4562944400931^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503493333 10000000000 4562944400931 10000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2498651041/10000000000 : ℝ)^4287 ≤ (3233870248773/20000000000000 : ℝ)^3263 := by
    have hnat : (2498651041 : ℕ)^4287*20000000000000^3263 ≤ 3233870248773^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498651041 10000000000 3233870248773 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1201829449/2500000000 : ℝ)^4287 ≤ (38201204735559/100000000000000 : ℝ)^3263 := by
    have hnat : (1201829449 : ℕ)^4287*100000000000000^3263 ≤ 38201204735559^3263*2500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201829449 2500000000 38201204735559 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5503493333/10000000000 : ℝ), (-2498651041/10000000000 : ℝ), (1201829449/2500000000 : ℝ)] ![(4562944400931/10000000000000 : ℝ), (3233870248773/20000000000000 : ℝ), (38201204735559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5503493333/10000000000 : ℝ)|^4287 ≤ (4562944400931/10000000000000 : ℝ)^3263
        have hw : |(5503493333/10000000000 : ℝ)|=(5503493333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2498651041/10000000000 : ℝ)|^4287 ≤ (3233870248773/20000000000000 : ℝ)^3263
        have hw : |(-2498651041/10000000000 : ℝ)|=(2498651041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1201829449/2500000000 : ℝ)|^4287 ≤ (38201204735559/100000000000000 : ℝ)^3263
        have hw : |(1201829449/2500000000 : ℝ)|=(1201829449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s0_2 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5503492699/10000000000 : ℝ)*x 0 + (2403658997/5000000000 : ℝ)*x 1 + (-2498651611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5503492699/10000000000 : ℝ)^4287 ≤ (45629437103217/100000000000000 : ℝ)^3263 := by
    have hnat : (5503492699 : ℕ)^4287*100000000000000^3263 ≤ 45629437103217^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503492699 10000000000 45629437103217 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2403658997/5000000000 : ℝ)^4287 ≤ (38201206802727/100000000000000 : ℝ)^3263 := by
    have hnat : (2403658997 : ℕ)^4287*100000000000000^3263 ≤ 38201206802727^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403658997 5000000000 38201206802727 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2498651611/10000000000 : ℝ)^4287 ≤ (16169356090031/100000000000000 : ℝ)^3263 := by
    have hnat : (2498651611 : ℕ)^4287*100000000000000^3263 ≤ 16169356090031^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498651611 10000000000 16169356090031 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5503492699/10000000000 : ℝ), (2403658997/5000000000 : ℝ), (-2498651611/10000000000 : ℝ)] ![(45629437103217/100000000000000 : ℝ), (38201206802727/100000000000000 : ℝ), (16169356090031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5503492699/10000000000 : ℝ)|^4287 ≤ (45629437103217/100000000000000 : ℝ)^3263
        have hw : |(5503492699/10000000000 : ℝ)|=(5503492699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2403658997/5000000000 : ℝ)|^4287 ≤ (38201206802727/100000000000000 : ℝ)^3263
        have hw : |(2403658997/5000000000 : ℝ)|=(2403658997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2498651611/10000000000 : ℝ)|^4287 ≤ (16169356090031/100000000000000 : ℝ)^3263
        have hw : |(-2498651611/10000000000 : ℝ)|=(2498651611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s0_3 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (836200193/2000000000 : ℝ)*x 0 + (3107343923/10000000000 : ℝ)*x 1 + (559853507/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836200193/2000000000 : ℝ)^4287 ≤ (31800197821721/100000000000000 : ℝ)^3263 := by
    have hnat : (836200193 : ℕ)^4287*100000000000000^3263 ≤ 31800197821721^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836200193 2000000000 31800197821721 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3107343923/10000000000 : ℝ)^4287 ≤ (2153228457221/10000000000000 : ℝ)^3263 := by
    have hnat : (3107343923 : ℕ)^4287*10000000000000^3263 ≤ 2153228457221^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3107343923 10000000000 2153228457221 10000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559853507/1000000000 : ℝ)^4287 ≤ (46667517597209/100000000000000 : ℝ)^3263 := by
    have hnat : (559853507 : ℕ)^4287*100000000000000^3263 ≤ 46667517597209^3263*1000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559853507 1000000000 46667517597209 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836200193/2000000000 : ℝ), (3107343923/10000000000 : ℝ), (559853507/1000000000 : ℝ)] ![(31800197821721/100000000000000 : ℝ), (2153228457221/10000000000000 : ℝ), (46667517597209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836200193/2000000000 : ℝ)|^4287 ≤ (31800197821721/100000000000000 : ℝ)^3263
        have hw : |(836200193/2000000000 : ℝ)|=(836200193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3107343923/10000000000 : ℝ)|^4287 ≤ (2153228457221/10000000000000 : ℝ)^3263
        have hw : |(3107343923/10000000000 : ℝ)|=(3107343923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559853507/1000000000 : ℝ)|^4287 ≤ (46667517597209/100000000000000 : ℝ)^3263
        have hw : |(559853507/1000000000 : ℝ)|=(559853507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s0_4 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-455645713/2500000000 : ℝ)*x 0 + (604766151/1250000000 : ℝ)*x 1 + (5971509619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (455645713/2500000000 : ℝ)^4287 ≤ (1335318804951/12500000000000 : ℝ)^3263 := by
    have hnat : (455645713 : ℕ)^4287*12500000000000^3263 ≤ 1335318804951^3263*2500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455645713 2500000000 1335318804951 12500000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604766151/1250000000 : ℝ)^4287 ≤ (2407700401231/6250000000000 : ℝ)^3263 := by
    have hnat : (604766151 : ℕ)^4287*6250000000000^3263 ≤ 2407700401231^3263*1250000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604766151 1250000000 2407700401231 6250000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5971509619/10000000000 : ℝ)^4287 ≤ (12698560781727/25000000000000 : ℝ)^3263 := by
    have hnat : (5971509619 : ℕ)^4287*25000000000000^3263 ≤ 12698560781727^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5971509619 10000000000 12698560781727 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-455645713/2500000000 : ℝ), (604766151/1250000000 : ℝ), (5971509619/10000000000 : ℝ)] ![(1335318804951/12500000000000 : ℝ), (2407700401231/6250000000000 : ℝ), (12698560781727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-455645713/2500000000 : ℝ)|^4287 ≤ (1335318804951/12500000000000 : ℝ)^3263
        have hw : |(-455645713/2500000000 : ℝ)|=(455645713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(604766151/1250000000 : ℝ)|^4287 ≤ (2407700401231/6250000000000 : ℝ)^3263
        have hw : |(604766151/1250000000 : ℝ)|=(604766151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5971509619/10000000000 : ℝ)|^4287 ≤ (12698560781727/25000000000000 : ℝ)^3263
        have hw : |(5971509619/10000000000 : ℝ)|=(5971509619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s0_5 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (323600921/625000000 : ℝ)*x 0 + (-166807511/1250000000 : ℝ)*x 1 + (5971509531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323600921/625000000 : ℝ)^4287 ≤ (42113123719913/100000000000000 : ℝ)^3263 := by
    have hnat : (323600921 : ℕ)^4287*100000000000000^3263 ≤ 42113123719913^3263*625000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323600921 625000000 42113123719913 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166807511/1250000000 : ℝ)^4287 ≤ (1773158532811/25000000000000 : ℝ)^3263 := by
    have hnat : (166807511 : ℕ)^4287*25000000000000^3263 ≤ 1773158532811^3263*1250000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166807511 1250000000 1773158532811 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5971509531/10000000000 : ℝ)^4287 ≤ (10158848428693/20000000000000 : ℝ)^3263 := by
    have hnat : (5971509531 : ℕ)^4287*20000000000000^3263 ≤ 10158848428693^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5971509531 10000000000 10158848428693 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(323600921/625000000 : ℝ), (-166807511/1250000000 : ℝ), (5971509531/10000000000 : ℝ)] ![(42113123719913/100000000000000 : ℝ), (1773158532811/25000000000000 : ℝ), (10158848428693/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(323600921/625000000 : ℝ)|^4287 ≤ (42113123719913/100000000000000 : ℝ)^3263
        have hw : |(323600921/625000000 : ℝ)|=(323600921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-166807511/1250000000 : ℝ)|^4287 ≤ (1773158532811/25000000000000 : ℝ)^3263
        have hw : |(-166807511/1250000000 : ℝ)|=(166807511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5971509531/10000000000 : ℝ)|^4287 ≤ (10158848428693/20000000000000 : ℝ)^3263
        have hw : |(5971509531/10000000000 : ℝ)|=(5971509531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s0_6 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2588807383/5000000000 : ℝ)*x 0 + (1492877397/2500000000 : ℝ)*x 1 + (-1334459949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588807383/5000000000 : ℝ)^4287 ≤ (84226248081/200000000000 : ℝ)^3263 := by
    have hnat : (2588807383 : ℕ)^4287*200000000000^3263 ≤ 84226248081^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588807383 5000000000 84226248081 200000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1492877397/2500000000 : ℝ)^4287 ≤ (12698560695117/25000000000000 : ℝ)^3263 := by
    have hnat : (1492877397 : ℕ)^4287*25000000000000^3263 ≤ 12698560695117^3263*2500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492877397 2500000000 12698560695117 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1334459949/10000000000 : ℝ)^4287 ≤ (1418526632123/20000000000000 : ℝ)^3263 := by
    have hnat : (1334459949 : ℕ)^4287*20000000000000^3263 ≤ 1418526632123^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334459949 10000000000 1418526632123 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588807383/5000000000 : ℝ), (1492877397/2500000000 : ℝ), (-1334459949/10000000000 : ℝ)] ![(84226248081/200000000000 : ℝ), (12698560695117/25000000000000 : ℝ), (1418526632123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588807383/5000000000 : ℝ)|^4287 ≤ (84226248081/200000000000 : ℝ)^3263
        have hw : |(2588807383/5000000000 : ℝ)|=(2588807383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1492877397/2500000000 : ℝ)|^4287 ≤ (12698560695117/25000000000000 : ℝ)^3263
        have hw : |(1492877397/2500000000 : ℝ)|=(1492877397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1334459949/10000000000 : ℝ)|^4287 ≤ (1418526632123/20000000000000 : ℝ)^3263
        have hw : |(-1334459949/10000000000 : ℝ)|=(1334459949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s0_7 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1047611773/2500000000 : ℝ)*x 0 + (1383590627/2500000000 : ℝ)*x 1 + (1586902919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047611773/2500000000 : ℝ)^4287 ≤ (3986828032213/12500000000000 : ℝ)^3263 := by
    have hnat : (1047611773 : ℕ)^4287*12500000000000^3263 ≤ 3986828032213^3263*2500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047611773 2500000000 3986828032213 12500000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1383590627/2500000000 : ℝ)^4287 ≤ (45965994119463/100000000000000 : ℝ)^3263 := by
    have hnat : (1383590627 : ℕ)^4287*100000000000000^3263 ≤ 45965994119463^3263*2500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383590627 2500000000 45965994119463 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1586902919/5000000000 : ℝ)^4287 ≤ (5534845399201/25000000000000 : ℝ)^3263 := by
    have hnat : (1586902919 : ℕ)^4287*25000000000000^3263 ≤ 5534845399201^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586902919 5000000000 5534845399201 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047611773/2500000000 : ℝ), (1383590627/2500000000 : ℝ), (1586902919/5000000000 : ℝ)] ![(3986828032213/12500000000000 : ℝ), (45965994119463/100000000000000 : ℝ), (5534845399201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047611773/2500000000 : ℝ)|^4287 ≤ (3986828032213/12500000000000 : ℝ)^3263
        have hw : |(1047611773/2500000000 : ℝ)|=(1047611773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1383590627/2500000000 : ℝ)|^4287 ≤ (45965994119463/100000000000000 : ℝ)^3263
        have hw : |(1383590627/2500000000 : ℝ)|=(1383590627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1586902919/5000000000 : ℝ)|^4287 ≤ (5534845399201/25000000000000 : ℝ)^3263
        have hw : |(1586902919/5000000000 : ℝ)|=(1586902919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1327_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1301/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26979/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2143/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2143 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2143*1^512 ≤ 0^512*1^2143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2143 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2143/512 : ℝ) ≤ (2159749789087253171/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2143 ≤ (2159749789087253171/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2143*100000000000000000000^512 ≤ 2159749789087253171^512*5^2143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2159749789087253171 100000000000000000000 2143 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2159749789087253171/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2143 := by
      have hnat : (1 : ℕ)^512*1^2143 ≤ 1^2143*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102159749789087253171/100000000000000000000 : ℝ) ≤ (1256397673875081/1250000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (102159749789087253171/100000000000000000000 : ℝ)^512 ≤ (1256397673875081/1250000000000000 : ℝ)^2143 := by
      have hnat : (102159749789087253171 : ℕ)^512*1250000000000000^2143 ≤ 1256397673875081^2143*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102159749789087253171 100000000000000000000 1256397673875081 1250000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1256397673875081/1250000000000000 : ℝ)) (X := (102159749789087253171/100000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52159749789087253171/50000000000000000000 : ℝ) ≤ (631397673875081/625000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (52159749789087253171/50000000000000000000 : ℝ)^512 ≤ (631397673875081/625000000000000 : ℝ)^2143 := by
      have hnat : (52159749789087253171 : ℕ)^512*625000000000000^2143 ≤ 631397673875081^2143*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52159749789087253171 50000000000000000000 631397673875081 625000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631397673875081/625000000000000 : ℝ)) (X := (52159749789087253171/50000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6397673875081/500000000000000 : ℝ)*(0 : ℝ))^(2143/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(6397673875081/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2159749789087253171/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6397673875081/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2143/512 : ℝ) := by
    rw [show (1 : ℝ)+(6397673875081/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1256397673875081/1250000000000000 : ℝ) by norm_num, show 1+(2159749789087253171/100000000000000000000 : ℝ)+(0 : ℝ)=(102159749789087253171/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2159749789087253171/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6397673875081/500000000000000 : ℝ)*(2/5 : ℝ))^(2143/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(6397673875081/500000000000000 : ℝ)*(2/5 : ℝ)=(631397673875081/625000000000000 : ℝ) by norm_num, show 1+2*(2159749789087253171/100000000000000000000 : ℝ)=(52159749789087253171/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6397673875081/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6397673875081/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6397673875081/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6397673875081/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6397673875081/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6397673875081/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1818047043/10000000000 : ℝ)*X 0 0+(3001710273/5000000000 : ℝ)*X 0 1+(961463509/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5503493333/10000000000 : ℝ)*X 1 0+(-2498651041/10000000000 : ℝ)*X 1 1+(1201829449/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5503492699/10000000000 : ℝ)*X 2 0+(2403658997/5000000000 : ℝ)*X 2 1+(-2498651611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((836200193/2000000000 : ℝ)*X 0 0+(3107343923/10000000000 : ℝ)*X 0 1+(559853507/1000000000 : ℝ)*X 0 2+(836200193/2000000000 : ℝ)*X 1 0+(3107343923/10000000000 : ℝ)*X 1 1+(559853507/1000000000 : ℝ)*X 1 2+(836200193/2000000000 : ℝ)*X 2 0+(3107343923/10000000000 : ℝ)*X 2 1+(559853507/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-455645713/2500000000 : ℝ)*X 0 0+(604766151/1250000000 : ℝ)*X 0 1+(5971509619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((323600921/625000000 : ℝ)*X 1 0+(-166807511/1250000000 : ℝ)*X 1 1+(5971509531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2588807383/5000000000 : ℝ)*X 2 0+(1492877397/2500000000 : ℝ)*X 2 1+(-1334459949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1047611773/2500000000 : ℝ)*X 0 0+(1383590627/2500000000 : ℝ)*X 0 1+(1586902919/5000000000 : ℝ)*X 0 2+(1047611773/2500000000 : ℝ)*X 1 0+(1383590627/2500000000 : ℝ)*X 1 1+(1586902919/5000000000 : ℝ)*X 1 2+(1047611773/2500000000 : ℝ)*X 2 0+(1383590627/2500000000 : ℝ)*X 2 1+(1586902919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126185763452501441655171/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20009537/25000000000000 : ℝ)*(base1) + (319238609/25000000000000 : ℝ)*(base19) + (295160303/25000000000000 : ℝ)*(base23) + (216775471/100000000000000 : ℝ)*(upper3) + (41477179/100000000000000 : ℝ)*(upper5) + (618737548897901/100000000000000 : ℝ)*(major0) + (618737548897901/100000000000000 : ℝ)*(major1) + (618737548897901/100000000000000 : ℝ)*(major2) + (836053075877713/100000000000000 : ℝ)*(sp0) + (209013850562739/25000000000000 : ℝ)*(sp1) + (41802774928209/5000000000000 : ℝ)*(sp2) + (200708010499787/50000000000000 : ℝ)*(sp3) + (920841457/25000000000000 : ℝ)*(sp4) + (2149304997/100000000000000 : ℝ)*(sp7) + (1254432032321/312500000000 : ℝ)*(f.failure) + (52253542450337/6250000000000 : ℝ)*(f.sum) + (75174659129981/25000000000000000000000000000 : ℝ)*base65 + (168414657104981/50000000000000000000000000000 : ℝ)*base67 + (285613842045019/50000000000000000000000000000 : ℝ)*base70 + (94152298004981/50000000000000000000000000000 : ℝ)*base71 + (120119095054981/25000000000000000000000000000 : ℝ)*base73 + (161409215004981/50000000000000000000000000000 : ℝ)*base75 + (90450024404981/50000000000000000000000000000 : ℝ)*base77 + (254701687204981/50000000000000000000000000000 : ℝ)*base79 + (47771970045019/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (24603/7812500000000000000 : ℝ)*base89 + (24603/7812500000000000000 : ℝ)*base91 + (24603/7812500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11544970989585497162637/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (397256731/100000000000000 : ℝ)*(base19) + (221289679/50000000000000 : ℝ)*(base23) + (1877077/5000000000000 : ℝ)*(base39) + (47600051/100000000000000 : ℝ)*(upper3) + (7550107/12500000000000 : ℝ)*(upper5) + (326486255842537/50000000000000 : ℝ)*(major0) + (326486255842537/50000000000000 : ℝ)*(major1) + (326486237071767/50000000000000 : ℝ)*(major2) + (56192453/6250000000000 : ℝ)*(sp1) + (239055963/25000000000000 : ℝ)*(sp2) + (882316063150429/100000000000000 : ℝ)*(sp4) + (17646295336289/2000000000000 : ℝ)*(sp5) + (882314701888759/100000000000000 : ℝ)*(sp6) + (211814430552497/50000000000000 : ℝ)*(sp7) + (211814430552497/50000000000000 : ℝ)*(f.failure) + (882316100691969/100000000000000 : ℝ)*(f.sum) + (954162048707/781250000000000000000000000 : ℝ)*base65 + (113426310338127/25000000000000000000000000000 : ℝ)*base67 + (177824556045497/25000000000000000000000000000 : ℝ)*base69 + (12662034138127/25000000000000000000000000000 : ℝ)*base71 + (2102212960291/390625000000000000000000000 : ℝ)*base73 + (143055960870497/25000000000000000000000000000 : ℝ)*base75 + (90629109370497/25000000000000000000000000000 : ℝ)*base77 + (52098365820497/25000000000000000000000000000 : ℝ)*base79 + (69553892757997/12500000000000000000000000000 : ℝ)*base81 + (1758351/312500000000000000000 : ℝ)*base90 + (1758351/312500000000000000000 : ℝ)*base92 + (1758351/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1327_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1301/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26979/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1327_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1327_s1_0 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-401006497/2000000000 : ℝ)*x 0 + (8826439/15625000 : ℝ)*x 1 + (252104193/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (401006497/2000000000 : ℝ)^4287 ≤ (6054552055573/50000000000000 : ℝ)^3263 := by
    have hnat : (401006497 : ℕ)^4287*50000000000000^3263 ≤ 6054552055573^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401006497 2000000000 6054552055573 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8826439/15625000 : ℝ)^4287 ≤ (11805025063609/25000000000000 : ℝ)^3263 := by
    have hnat : (8826439 : ℕ)^4287*25000000000000^3263 ≤ 11805025063609^3263*15625000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8826439 15625000 11805025063609 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252104193/500000000 : ℝ)^4287 ≤ (20335397811241/50000000000000 : ℝ)^3263 := by
    have hnat : (252104193 : ℕ)^4287*50000000000000^3263 ≤ 20335397811241^3263*500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252104193 500000000 20335397811241 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-401006497/2000000000 : ℝ), (8826439/15625000 : ℝ), (252104193/500000000 : ℝ)] ![(6054552055573/50000000000000 : ℝ), (11805025063609/25000000000000 : ℝ), (20335397811241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-401006497/2000000000 : ℝ)|^4287 ≤ (6054552055573/50000000000000 : ℝ)^3263
        have hw : |(-401006497/2000000000 : ℝ)|=(401006497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8826439/15625000 : ℝ)|^4287 ≤ (11805025063609/25000000000000 : ℝ)^3263
        have hw : |(8826439/15625000 : ℝ)|=(8826439/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252104193/500000000 : ℝ)|^4287 ≤ (20335397811241/50000000000000 : ℝ)^3263
        have hw : |(252104193/500000000 : ℝ)|=(252104193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s1_1 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2703642399/5000000000 : ℝ)*x 0 + (-465854829/2000000000 : ℝ)*x 1 + (2521041939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2703642399/5000000000 : ℝ)^4287 ≤ (44584341191011/100000000000000 : ℝ)^3263 := by
    have hnat : (2703642399 : ℕ)^4287*100000000000000^3263 ≤ 44584341191011^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703642399 5000000000 44584341191011 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465854829/2000000000 : ℝ)^4287 ≤ (7372431488803/50000000000000 : ℝ)^3263 := by
    have hnat : (465854829 : ℕ)^4287*50000000000000^3263 ≤ 7372431488803^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465854829 2000000000 7372431488803 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2521041939/5000000000 : ℝ)^4287 ≤ (40670795813239/100000000000000 : ℝ)^3263 := by
    have hnat : (2521041939 : ℕ)^4287*100000000000000^3263 ≤ 40670795813239^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2521041939 5000000000 40670795813239 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2703642399/5000000000 : ℝ), (-465854829/2000000000 : ℝ), (2521041939/5000000000 : ℝ)] ![(44584341191011/100000000000000 : ℝ), (7372431488803/50000000000000 : ℝ), (40670795813239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2703642399/5000000000 : ℝ)|^4287 ≤ (44584341191011/100000000000000 : ℝ)^3263
        have hw : |(2703642399/5000000000 : ℝ)|=(2703642399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-465854829/2000000000 : ℝ)|^4287 ≤ (7372431488803/50000000000000 : ℝ)^3263
        have hw : |(-465854829/2000000000 : ℝ)|=(465854829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2521041939/5000000000 : ℝ)|^4287 ≤ (40670795813239/100000000000000 : ℝ)^3263
        have hw : |(2521041939/5000000000 : ℝ)|=(2521041939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s1_2 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2703642509/5000000000 : ℝ)*x 0 + (5042083473/10000000000 : ℝ)*x 1 + (-1164637187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2703642509/5000000000 : ℝ)^4287 ≤ (2229217178711/5000000000000 : ℝ)^3263 := by
    have hnat : (2703642509 : ℕ)^4287*5000000000000^3263 ≤ 2229217178711^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703642509 5000000000 2229217178711 5000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5042083473/10000000000 : ℝ)^4287 ≤ (40670791521197/100000000000000 : ℝ)^3263 := by
    have hnat : (5042083473 : ℕ)^4287*100000000000000^3263 ≤ 40670791521197^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5042083473 10000000000 40670791521197 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1164637187/5000000000 : ℝ)^4287 ≤ (2948972976431/20000000000000 : ℝ)^3263 := by
    have hnat : (1164637187 : ℕ)^4287*20000000000000^3263 ≤ 2948972976431^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164637187 5000000000 2948972976431 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2703642509/5000000000 : ℝ), (5042083473/10000000000 : ℝ), (-1164637187/5000000000 : ℝ)] ![(2229217178711/5000000000000 : ℝ), (40670791521197/100000000000000 : ℝ), (2948972976431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2703642509/5000000000 : ℝ)|^4287 ≤ (2229217178711/5000000000000 : ℝ)^3263
        have hw : |(2703642509/5000000000 : ℝ)|=(2703642509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5042083473/10000000000 : ℝ)|^4287 ≤ (40670791521197/100000000000000 : ℝ)^3263
        have hw : |(5042083473/10000000000 : ℝ)|=(5042083473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1164637187/5000000000 : ℝ)|^4287 ≤ (2948972976431/20000000000000 : ℝ)^3263
        have hw : |(-1164637187/5000000000 : ℝ)|=(1164637187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s1_3 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4294975689/10000000000 : ℝ)*x 0 + (370639669/1000000000 : ℝ)*x 1 + (4970291587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4294975689/10000000000 : ℝ)^4287 ≤ (32943962827731/100000000000000 : ℝ)^3263 := by
    have hnat : (4294975689 : ℕ)^4287*100000000000000^3263 ≤ 32943962827731^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4294975689 10000000000 32943962827731 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370639669/1000000000 : ℝ)^4287 ≤ (6786091132941/25000000000000 : ℝ)^3263 := by
    have hnat : (370639669 : ℕ)^4287*25000000000000^3263 ≤ 6786091132941^3263*1000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370639669 1000000000 6786091132941 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4970291587/10000000000 : ℝ)^4287 ≤ (39911672625781/100000000000000 : ℝ)^3263 := by
    have hnat : (4970291587 : ℕ)^4287*100000000000000^3263 ≤ 39911672625781^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4970291587 10000000000 39911672625781 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4294975689/10000000000 : ℝ), (370639669/1000000000 : ℝ), (4970291587/10000000000 : ℝ)] ![(32943962827731/100000000000000 : ℝ), (6786091132941/25000000000000 : ℝ), (39911672625781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4294975689/10000000000 : ℝ)|^4287 ≤ (32943962827731/100000000000000 : ℝ)^3263
        have hw : |(4294975689/10000000000 : ℝ)|=(4294975689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(370639669/1000000000 : ℝ)|^4287 ≤ (6786091132941/25000000000000 : ℝ)^3263
        have hw : |(370639669/1000000000 : ℝ)|=(370639669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4970291587/10000000000 : ℝ)|^4287 ≤ (39911672625781/100000000000000 : ℝ)^3263
        have hw : |(4970291587/10000000000 : ℝ)|=(4970291587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s1_4 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-401119471/2000000000 : ℝ)*x 0 + (2524892849/5000000000 : ℝ)*x 1 + (5641077343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (401119471/2000000000 : ℝ)^4287 ≤ (2422717269423/20000000000000 : ℝ)^3263 := by
    have hnat : (401119471 : ℕ)^4287*20000000000000^3263 ≤ 2422717269423^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401119471 2000000000 2422717269423 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2524892849/5000000000 : ℝ)^4287 ≤ (40752436457339/100000000000000 : ℝ)^3263 := by
    have hnat : (2524892849 : ℕ)^4287*100000000000000^3263 ≤ 40752436457339^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524892849 5000000000 40752436457339 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5641077343/10000000000 : ℝ)^4287 ≤ (9426795435639/20000000000000 : ℝ)^3263 := by
    have hnat : (5641077343 : ℕ)^4287*20000000000000^3263 ≤ 9426795435639^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5641077343 10000000000 9426795435639 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-401119471/2000000000 : ℝ), (2524892849/5000000000 : ℝ), (5641077343/10000000000 : ℝ)] ![(2422717269423/20000000000000 : ℝ), (40752436457339/100000000000000 : ℝ), (9426795435639/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-401119471/2000000000 : ℝ)|^4287 ≤ (2422717269423/20000000000000 : ℝ)^3263
        have hw : |(-401119471/2000000000 : ℝ)|=(401119471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2524892849/5000000000 : ℝ)|^4287 ≤ (40752436457339/100000000000000 : ℝ)^3263
        have hw : |(2524892849/5000000000 : ℝ)|=(2524892849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5641077343/10000000000 : ℝ)|^4287 ≤ (9426795435639/20000000000000 : ℝ)^3263
        have hw : |(5641077343/10000000000 : ℝ)|=(5641077343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s1_5 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250018873/10000000000 : ℝ)*x 0 + (-346056167/2000000000 : ℝ)*x 1 + (1128215373/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250018873/10000000000 : ℝ)^4287 ≤ (8577708530239/20000000000000 : ℝ)^3263 := by
    have hnat : (5250018873 : ℕ)^4287*20000000000000^3263 ≤ 8577708530239^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250018873 10000000000 8577708530239 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346056167/2000000000 : ℝ)^4287 ≤ (4988742703137/50000000000000 : ℝ)^3263 := by
    have hnat : (346056167 : ℕ)^4287*50000000000000^3263 ≤ 4988742703137^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346056167 2000000000 4988742703137 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128215373/2000000000 : ℝ)^4287 ≤ (4713397193089/10000000000000 : ℝ)^3263 := by
    have hnat : (1128215373 : ℕ)^4287*10000000000000^3263 ≤ 4713397193089^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128215373 2000000000 4713397193089 10000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250018873/10000000000 : ℝ), (-346056167/2000000000 : ℝ), (1128215373/2000000000 : ℝ)] ![(8577708530239/20000000000000 : ℝ), (4988742703137/50000000000000 : ℝ), (4713397193089/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250018873/10000000000 : ℝ)|^4287 ≤ (8577708530239/20000000000000 : ℝ)^3263
        have hw : |(5250018873/10000000000 : ℝ)|=(5250018873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-346056167/2000000000 : ℝ)|^4287 ≤ (4988742703137/50000000000000 : ℝ)^3263
        have hw : |(-346056167/2000000000 : ℝ)|=(346056167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1128215373/2000000000 : ℝ)|^4287 ≤ (4713397193089/10000000000000 : ℝ)^3263
        have hw : |(1128215373/2000000000 : ℝ)|=(1128215373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s1_6 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625009281/5000000000 : ℝ)*x 0 + (2820538347/5000000000 : ℝ)*x 1 + (-1730281523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625009281/5000000000 : ℝ)^4287 ≤ (8577707862653/20000000000000 : ℝ)^3263 := by
    have hnat : (2625009281 : ℕ)^4287*20000000000000^3263 ≤ 8577707862653^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625009281 5000000000 8577707862653 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2820538347/5000000000 : ℝ)^4287 ≤ (11783492513429/25000000000000 : ℝ)^3263 := by
    have hnat : (2820538347 : ℕ)^4287*25000000000000^3263 ≤ 11783492513429^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820538347 5000000000 11783492513429 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1730281523/10000000000 : ℝ)^4287 ≤ (4988745309287/50000000000000 : ℝ)^3263 := by
    have hnat : (1730281523 : ℕ)^4287*50000000000000^3263 ≤ 4988745309287^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730281523 10000000000 4988745309287 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625009281/5000000000 : ℝ), (2820538347/5000000000 : ℝ), (-1730281523/10000000000 : ℝ)] ![(8577707862653/20000000000000 : ℝ), (11783492513429/25000000000000 : ℝ), (4988745309287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625009281/5000000000 : ℝ)|^4287 ≤ (8577707862653/20000000000000 : ℝ)^3263
        have hw : |(2625009281/5000000000 : ℝ)|=(2625009281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2820538347/5000000000 : ℝ)|^4287 ≤ (11783492513429/25000000000000 : ℝ)^3263
        have hw : |(2820538347/5000000000 : ℝ)|=(2820538347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1730281523/10000000000 : ℝ)|^4287 ≤ (4988745309287/50000000000000 : ℝ)^3263
        have hw : |(-1730281523/10000000000 : ℝ)|=(1730281523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s1_7 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2148075673/5000000000 : ℝ)*x 0 + (4954249633/10000000000 : ℝ)*x 1 + (1861367191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148075673/5000000000 : ℝ)^4287 ≤ (32955810985399/100000000000000 : ℝ)^3263 := by
    have hnat : (2148075673 : ℕ)^4287*100000000000000^3263 ≤ 32955810985399^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148075673 5000000000 32955810985399 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4954249633/10000000000 : ℝ)^4287 ≤ (39742515002461/100000000000000 : ℝ)^3263 := by
    have hnat : (4954249633 : ℕ)^4287*100000000000000^3263 ≤ 39742515002461^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4954249633 10000000000 39742515002461 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1861367191/5000000000 : ℝ)^4287 ≤ (1365083700151/5000000000000 : ℝ)^3263 := by
    have hnat : (1861367191 : ℕ)^4287*5000000000000^3263 ≤ 1365083700151^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861367191 5000000000 1365083700151 5000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148075673/5000000000 : ℝ), (4954249633/10000000000 : ℝ), (1861367191/5000000000 : ℝ)] ![(32955810985399/100000000000000 : ℝ), (39742515002461/100000000000000 : ℝ), (1365083700151/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148075673/5000000000 : ℝ)|^4287 ≤ (32955810985399/100000000000000 : ℝ)^3263
        have hw : |(2148075673/5000000000 : ℝ)|=(2148075673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4954249633/10000000000 : ℝ)|^4287 ≤ (39742515002461/100000000000000 : ℝ)^3263
        have hw : |(4954249633/10000000000 : ℝ)|=(4954249633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1861367191/5000000000 : ℝ)|^4287 ≤ (1365083700151/5000000000000 : ℝ)^3263
        have hw : |(1861367191/5000000000 : ℝ)|=(1861367191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1327_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6749/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (783/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26979/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26979/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26979/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26979/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26979/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26979/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1301/100000 : ℝ) ^ (2143/512 : ℝ) ≤ (1280027297851/100000000000000000000 : ℝ) := by
    have hpowers : (1301/100000 : ℝ)^2143 ≤ (1280027297851/100000000000000000000 : ℝ)^512 := by
      have hnat : (1301 : ℕ)^2143*100000000000000000000^512 ≤ 1280027297851^512*100000^2143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1301 100000 1280027297851 100000000000000000000 2143 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1301/100000 : ℝ)) (X := (1280027297851/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26979/100000 : ℝ) ^ (2143/512 : ℝ) ≤ (51932834813515219/12500000000000000000 : ℝ) := by
    have hpowers : (26979/100000 : ℝ)^2143 ≤ (51932834813515219/12500000000000000000 : ℝ)^512 := by
      have hnat : (26979 : ℕ)^2143*12500000000000000000^512 ≤ 51932834813515219^512*100000^2143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26979 100000 51932834813515219 12500000000000000000 2143 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26979/100000 : ℝ)) (X := (51932834813515219/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000001280027297851/50000000000000000000 : ℝ) ≤ (15625000095569/15625000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (50000001280027297851/50000000000000000000 : ℝ)^512 ≤ (15625000095569/15625000000000 : ℝ)^2143 := by
      have hnat : (50000001280027297851 : ℕ)^512*15625000000000^2143 ≤ 15625000095569^2143*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000001280027297851 50000000000000000000 15625000095569 15625000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (15625000095569/15625000000000 : ℝ)) (X := (50000001280027297851/50000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100415463958535419603/100000000000000000000 : ℝ) ≤ (1251238812737193/1250000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (100415463958535419603/100000000000000000000 : ℝ)^512 ≤ (1251238812737193/1250000000000000 : ℝ)^2143 := by
      have hnat : (100415463958535419603 : ℕ)^512*1250000000000000^2143 ≤ 1251238812737193^2143*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100415463958535419603 100000000000000000000 1251238812737193 1250000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251238812737193/1250000000000000 : ℝ)) (X := (100415463958535419603/100000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6301932834813515219/6250000000000000000 : ℝ) ≤ (626238808914433/625000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (6301932834813515219/6250000000000000000 : ℝ)^512 ≤ (626238808914433/625000000000000 : ℝ)^2143 := by
      have hnat : (6301932834813515219 : ℕ)^512*625000000000000^2143 ≤ 626238808914433^2143*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6301932834813515219 6250000000000000000 626238808914433 625000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626238808914433/625000000000000 : ℝ)) (X := (6301932834813515219/6250000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1280027297851/100000000000000000000 : ℝ) ≤ ((16047138412736564707/16048750000000000000 : ℝ)+2*(1238805091673/320975000000000 : ℝ)*(1301/100000 : ℝ))^(2143/512 : ℝ) := by
    rw [show (16047138412736564707/16048750000000000000 : ℝ)+2*(1238805091673/320975000000000 : ℝ)*(1301/100000 : ℝ)=(15625000095569/15625000000000 : ℝ) by norm_num, show 1+2*(1280027297851/100000000000000000000 : ℝ)=(50000001280027297851/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(51932834813515219/12500000000000000000 : ℝ)+(1280027297851/100000000000000000000 : ℝ) ≤ ((16047138412736564707/16048750000000000000 : ℝ)+(1238805091673/320975000000000 : ℝ)*((26979/100000 : ℝ)+(1301/100000 : ℝ)))^(2143/512 : ℝ) := by
    rw [show (16047138412736564707/16048750000000000000 : ℝ)+(1238805091673/320975000000000 : ℝ)*((26979/100000 : ℝ)+(1301/100000 : ℝ))=(1251238812737193/1250000000000000 : ℝ) by norm_num, show 1+(51932834813515219/12500000000000000000 : ℝ)+(1280027297851/100000000000000000000 : ℝ)=(100415463958535419603/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(51932834813515219/12500000000000000000 : ℝ) ≤ ((16047138412736564707/16048750000000000000 : ℝ)+2*(1238805091673/320975000000000 : ℝ)*(26979/100000 : ℝ))^(2143/512 : ℝ) := by
    rw [show (16047138412736564707/16048750000000000000 : ℝ)+2*(1238805091673/320975000000000 : ℝ)*(26979/100000 : ℝ)=(626238808914433/625000000000000 : ℝ) by norm_num, show 1+2*(51932834813515219/12500000000000000000 : ℝ)=(6301932834813515219/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16047138412736564707/16048750000000000000 : ℝ)*(X 1 0+X 2 0)+(1238805091673/320975000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (1301/100000 : ℝ)) (hi := (26979/100000 : ℝ)) (c := (16047138412736564707/16048750000000000000 : ℝ)) (alpha := (1238805091673/320975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16047138412736564707/16048750000000000000 : ℝ)*(X 0 1+X 2 1)+(1238805091673/320975000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (1301/100000 : ℝ)) (hi := (26979/100000 : ℝ)) (c := (16047138412736564707/16048750000000000000 : ℝ)) (alpha := (1238805091673/320975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16047138412736564707/16048750000000000000 : ℝ)*(X 0 2+X 1 2)+(1238805091673/320975000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (1301/100000 : ℝ)) (hi := (26979/100000 : ℝ)) (c := (16047138412736564707/16048750000000000000 : ℝ)) (alpha := (1238805091673/320975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-401006497/2000000000 : ℝ)*X 0 0+(8826439/15625000 : ℝ)*X 0 1+(252104193/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2703642399/5000000000 : ℝ)*X 1 0+(-465854829/2000000000 : ℝ)*X 1 1+(2521041939/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2703642509/5000000000 : ℝ)*X 2 0+(5042083473/10000000000 : ℝ)*X 2 1+(-1164637187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4294975689/10000000000 : ℝ)*X 0 0+(370639669/1000000000 : ℝ)*X 0 1+(4970291587/10000000000 : ℝ)*X 0 2+(4294975689/10000000000 : ℝ)*X 1 0+(370639669/1000000000 : ℝ)*X 1 1+(4970291587/10000000000 : ℝ)*X 1 2+(4294975689/10000000000 : ℝ)*X 2 0+(370639669/1000000000 : ℝ)*X 2 1+(4970291587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-401119471/2000000000 : ℝ)*X 0 0+(2524892849/5000000000 : ℝ)*X 0 1+(5641077343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5250018873/10000000000 : ℝ)*X 1 0+(-346056167/2000000000 : ℝ)*X 1 1+(1128215373/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625009281/5000000000 : ℝ)*X 2 0+(2820538347/5000000000 : ℝ)*X 2 1+(-1730281523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148075673/5000000000 : ℝ)*X 0 0+(4954249633/10000000000 : ℝ)*X 0 1+(1861367191/5000000000 : ℝ)*X 0 2+(2148075673/5000000000 : ℝ)*X 1 0+(4954249633/10000000000 : ℝ)*X 1 1+(1861367191/5000000000 : ℝ)*X 1 2+(2148075673/5000000000 : ℝ)*X 2 0+(4954249633/10000000000 : ℝ)*X 2 1+(1861367191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (225944725233206621695531353/32097500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92396363/100000000000000 : ℝ)*(base1) + (222173469/20000000000000 : ℝ)*(base19) + (294478377/25000000000000 : ℝ)*(base23) + (94902497/50000000000000 : ℝ)*(upper3) + (56818277/50000000000000 : ℝ)*(upper5) + (48782214431269/4000000000000 : ℝ)*(major0) + (48782214431269/4000000000000 : ℝ)*(major1) + (48782214431269/4000000000000 : ℝ)*(major2) + (411973641369871/25000000000000 : ℝ)*(sp0) + (823949329992441/50000000000000 : ℝ)*(sp1) + (10299366205867/625000000000 : ℝ)*(sp2) + (791207573994031/100000000000000 : ℝ)*(sp3) + (2648884553/50000000000000 : ℝ)*(sp4) + (381209583/12500000000000 : ℝ)*(sp7) + (395605358033529/50000000000000 : ℝ)*(f.failure) + (411974942713057/25000000000000 : ℝ)*(f.sum) + (28408558961247/12839000000000000000000000000 : ℝ)*base66 + (268356317650123183/64195000000000000000000000000000 : ℝ)*base67 + (463032783496088183/64195000000000000000000000000000 : ℝ)*base69 + (205825662320368183/64195000000000000000000000000000 : ℝ)*base71 + (8311443802441/1604875000000000000000000000 : ℝ)*base74 + (750854994858478183/64195000000000000000000000000000 : ℝ)*base75 + (340656146125188183/64195000000000000000000000000000 : ℝ)*base77 + (126411932935383183/64195000000000000000000000000000 : ℝ)*base79 + (6210339211259/2567800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (919393/312500000000000000000 : ℝ)*base89 + (919393/312500000000000000000 : ℝ)*base91 + (919393/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1358201903599737403743199101/200609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (275568621/25000000000000 : ℝ)*(base19) + (941235019/100000000000000 : ℝ)*(base23) + (10754803/100000000000000 : ℝ)*(upper2) + (5045437/6250000000000 : ℝ)*(upper3) + (94502953/50000000000000 : ℝ)*(upper5) + (156451303979689/12500000000000 : ℝ)*(major0) + (156451303979689/12500000000000 : ℝ)*(major1) + (156451303979689/12500000000000 : ℝ)*(major2) + (5324035203/100000000000000 : ℝ)*(sp1) + (521723693/20000000000000 : ℝ)*(sp2) + (1691213559139969/100000000000000 : ℝ)*(sp4) + (845603566415141/50000000000000 : ℝ)*(sp5) + (845605004643243/50000000000000 : ℝ)*(sp6) + (812007078855683/100000000000000 : ℝ)*(sp7) + (812007078855683/100000000000000 : ℝ)*(f.failure) + (1691213559139969/100000000000000 : ℝ)*(f.sum) + (364268883900319/64195000000000000000000000000 : ℝ)*base65 + (3916938605591297/12538085937500000000000000000000 : ℝ)*base68 + (253682631714974563/50152343750000000000000000000000 : ℝ)*base70 + (178806941127992373/200609375000000000000000000000000 : ℝ)*base71 + (17354700199837/32097500000000000000000000000 : ℝ)*base73 + (818285962370570127/200609375000000000000000000000000 : ℝ)*base76 + (171006523561976377/200609375000000000000000000000000 : ℝ)*base78 + (1436147690961538877/200609375000000000000000000000000 : ℝ)*base80 + (21815046885603/32097500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1704589/625000000000000000000 : ℝ)*base90 + (1704589/625000000000000000000 : ℝ)*base92 + (1704589/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1327_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6749/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (783/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1327_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1327_s2_0 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2046506999/10000000000 : ℝ)*x 0 + (1370980257/2500000000 : ℝ)*x 1 + (5180539717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046506999/10000000000 : ℝ)^4287 ≤ (12439252396521/100000000000000 : ℝ)^3263 := by
    have hnat : (2046506999 : ℕ)^4287*100000000000000^3263 ≤ 12439252396521^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046506999 10000000000 12439252396521 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1370980257/2500000000 : ℝ)^4287 ≤ (45416364100161/100000000000000 : ℝ)^3263 := by
    have hnat : (1370980257 : ℕ)^4287*100000000000000^3263 ≤ 45416364100161^3263*2500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370980257 2500000000 45416364100161 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180539717/10000000000 : ℝ)^4287 ≤ (21072191741213/50000000000000 : ℝ)^3263 := by
    have hnat : (5180539717 : ℕ)^4287*50000000000000^3263 ≤ 21072191741213^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180539717 10000000000 21072191741213 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2046506999/10000000000 : ℝ), (1370980257/2500000000 : ℝ), (5180539717/10000000000 : ℝ)] ![(12439252396521/100000000000000 : ℝ), (45416364100161/100000000000000 : ℝ), (21072191741213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2046506999/10000000000 : ℝ)|^4287 ≤ (12439252396521/100000000000000 : ℝ)^3263
        have hw : |(-2046506999/10000000000 : ℝ)|=(2046506999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1370980257/2500000000 : ℝ)|^4287 ≤ (45416364100161/100000000000000 : ℝ)^3263
        have hw : |(1370980257/2500000000 : ℝ)|=(1370980257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180539717/10000000000 : ℝ)|^4287 ≤ (21072191741213/50000000000000 : ℝ)^3263
        have hw : |(5180539717/10000000000 : ℝ)|=(5180539717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s2_1 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073403607/2000000000 : ℝ)*x 0 + (-1101699333/5000000000 : ℝ)*x 1 + (5180539233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073403607/2000000000 : ℝ)^4287 ≤ (22074325586733/50000000000000 : ℝ)^3263 := by
    have hnat : (1073403607 : ℕ)^4287*50000000000000^3263 ≤ 22074325586733^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073403607 2000000000 22074325586733 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101699333/5000000000 : ℝ)^4287 ≤ (2741394100413/20000000000000 : ℝ)^3263 := by
    have hnat : (1101699333 : ℕ)^4287*20000000000000^3263 ≤ 2741394100413^3263*5000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101699333 5000000000 2741394100413 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180539233/10000000000 : ℝ)^4287 ≤ (42144378309379/100000000000000 : ℝ)^3263 := by
    have hnat : (5180539233 : ℕ)^4287*100000000000000^3263 ≤ 42144378309379^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180539233 10000000000 42144378309379 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073403607/2000000000 : ℝ), (-1101699333/5000000000 : ℝ), (5180539233/10000000000 : ℝ)] ![(22074325586733/50000000000000 : ℝ), (2741394100413/20000000000000 : ℝ), (42144378309379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073403607/2000000000 : ℝ)|^4287 ≤ (22074325586733/50000000000000 : ℝ)^3263
        have hw : |(1073403607/2000000000 : ℝ)|=(1073403607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101699333/5000000000 : ℝ)|^4287 ≤ (2741394100413/20000000000000 : ℝ)^3263
        have hw : |(-1101699333/5000000000 : ℝ)|=(1101699333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180539233/10000000000 : ℝ)|^4287 ≤ (42144378309379/100000000000000 : ℝ)^3263
        have hw : |(5180539233/10000000000 : ℝ)|=(5180539233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s2_2 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367017391/10000000000 : ℝ)*x 0 + (1295134967/2500000000 : ℝ)*x 1 + (-2203398687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367017391/10000000000 : ℝ)^4287 ≤ (11037161053377/25000000000000 : ℝ)^3263 := by
    have hnat : (5367017391 : ℕ)^4287*25000000000000^3263 ≤ 11037161053377^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367017391 10000000000 11037161053377 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295134967/2500000000 : ℝ)^4287 ≤ (42144385096331/100000000000000 : ℝ)^3263 := by
    have hnat : (1295134967 : ℕ)^4287*100000000000000^3263 ≤ 42144385096331^3263*2500000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295134967 2500000000 42144385096331 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203398687/10000000000 : ℝ)^4287 ≤ (137069706737/1000000000000 : ℝ)^3263 := by
    have hnat : (2203398687 : ℕ)^4287*1000000000000^3263 ≤ 137069706737^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203398687 10000000000 137069706737 1000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367017391/10000000000 : ℝ), (1295134967/2500000000 : ℝ), (-2203398687/10000000000 : ℝ)] ![(11037161053377/25000000000000 : ℝ), (42144385096331/100000000000000 : ℝ), (137069706737/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367017391/10000000000 : ℝ)|^4287 ≤ (11037161053377/25000000000000 : ℝ)^3263
        have hw : |(5367017391/10000000000 : ℝ)|=(5367017391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295134967/2500000000 : ℝ)|^4287 ≤ (42144385096331/100000000000000 : ℝ)^3263
        have hw : |(1295134967/2500000000 : ℝ)|=(1295134967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2203398687/10000000000 : ℝ)|^4287 ≤ (137069706737/1000000000000 : ℝ)^3263
        have hw : |(-2203398687/10000000000 : ℝ)|=(2203398687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s2_3 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4323929813/10000000000 : ℝ)*x 0 + (4018817241/10000000000 : ℝ)*x 1 + (4650696089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323929813/10000000000 : ℝ)^4287 ≤ (8309013833697/25000000000000 : ℝ)^3263 := by
    have hnat : (4323929813 : ℕ)^4287*25000000000000^3263 ≤ 8309013833697^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323929813 10000000000 8309013833697 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4018817241/10000000000 : ℝ)^4287 ≤ (7547371585039/25000000000000 : ℝ)^3263 := by
    have hnat : (4018817241 : ℕ)^4287*25000000000000^3263 ≤ 7547371585039^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018817241 10000000000 7547371585039 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4650696089/10000000000 : ℝ)^4287 ≤ (36574458306189/100000000000000 : ℝ)^3263 := by
    have hnat : (4650696089 : ℕ)^4287*100000000000000^3263 ≤ 36574458306189^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4650696089 10000000000 36574458306189 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323929813/10000000000 : ℝ), (4018817241/10000000000 : ℝ), (4650696089/10000000000 : ℝ)] ![(8309013833697/25000000000000 : ℝ), (7547371585039/25000000000000 : ℝ), (36574458306189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323929813/10000000000 : ℝ)|^4287 ≤ (8309013833697/25000000000000 : ℝ)^3263
        have hw : |(4323929813/10000000000 : ℝ)|=(4323929813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4018817241/10000000000 : ℝ)|^4287 ≤ (7547371585039/25000000000000 : ℝ)^3263
        have hw : |(4018817241/10000000000 : ℝ)|=(4018817241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4650696089/10000000000 : ℝ)|^4287 ≤ (36574458306189/100000000000000 : ℝ)^3263
        have hw : |(4650696089/10000000000 : ℝ)|=(4650696089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s2_4 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2046577183/10000000000 : ℝ)*x 0 + (5182473843/10000000000 : ℝ)*x 1 + (5481969407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046577183/10000000000 : ℝ)^4287 ≤ (12439812873667/100000000000000 : ℝ)^3263 := by
    have hnat : (2046577183 : ℕ)^4287*100000000000000^3263 ≤ 12439812873667^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046577183 10000000000 12439812873667 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182473843/10000000000 : ℝ)^4287 ≤ (10541264213483/25000000000000 : ℝ)^3263 := by
    have hnat : (5182473843 : ℕ)^4287*25000000000000^3263 ≤ 10541264213483^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182473843 10000000000 10541264213483 25000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5481969407/10000000000 : ℝ)^4287 ≤ (45395130247041/100000000000000 : ℝ)^3263 := by
    have hnat : (5481969407 : ℕ)^4287*100000000000000^3263 ≤ 45395130247041^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481969407 10000000000 45395130247041 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2046577183/10000000000 : ℝ), (5182473843/10000000000 : ℝ), (5481969407/10000000000 : ℝ)] ![(12439812873667/100000000000000 : ℝ), (10541264213483/25000000000000 : ℝ), (45395130247041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2046577183/10000000000 : ℝ)|^4287 ≤ (12439812873667/100000000000000 : ℝ)^3263
        have hw : |(-2046577183/10000000000 : ℝ)|=(2046577183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182473843/10000000000 : ℝ)|^4287 ≤ (10541264213483/25000000000000 : ℝ)^3263
        have hw : |(5182473843/10000000000 : ℝ)|=(5182473843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5481969407/10000000000 : ℝ)|^4287 ≤ (45395130247041/100000000000000 : ℝ)^3263
        have hw : |(5481969407/10000000000 : ℝ)|=(5481969407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s2_5 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288949823/10000000000 : ℝ)*x 0 + (-1901967917/10000000000 : ℝ)*x 1 + (5481969451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288949823/10000000000 : ℝ)^4287 ≤ (5413358720639/12500000000000 : ℝ)^3263 := by
    have hnat : (5288949823 : ℕ)^4287*12500000000000^3263 ≤ 5413358720639^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288949823 10000000000 5413358720639 12500000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1901967917/10000000000 : ℝ)^4287 ≤ (5648999752017/50000000000000 : ℝ)^3263 := by
    have hnat : (1901967917 : ℕ)^4287*50000000000000^3263 ≤ 5648999752017^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901967917 10000000000 5648999752017 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5481969451/10000000000 : ℝ)^4287 ≤ (45395130725739/100000000000000 : ℝ)^3263 := by
    have hnat : (5481969451 : ℕ)^4287*100000000000000^3263 ≤ 45395130725739^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481969451 10000000000 45395130725739 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288949823/10000000000 : ℝ), (-1901967917/10000000000 : ℝ), (5481969451/10000000000 : ℝ)] ![(5413358720639/12500000000000 : ℝ), (5648999752017/50000000000000 : ℝ), (45395130725739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288949823/10000000000 : ℝ)|^4287 ≤ (5413358720639/12500000000000 : ℝ)^3263
        have hw : |(5288949823/10000000000 : ℝ)|=(5288949823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1901967917/10000000000 : ℝ)|^4287 ≤ (5648999752017/50000000000000 : ℝ)^3263
        have hw : |(-1901967917/10000000000 : ℝ)|=(1901967917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5481969451/10000000000 : ℝ)|^4287 ≤ (45395130725739/100000000000000 : ℝ)^3263
        have hw : |(5481969451/10000000000 : ℝ)|=(5481969451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s2_6 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41319921/78125000 : ℝ)*x 0 + (1096393883/2000000000 : ℝ)*x 1 + (-1901967877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41319921/78125000 : ℝ)^4287 ≤ (4330687046437/10000000000000 : ℝ)^3263 := by
    have hnat : (41319921 : ℕ)^4287*10000000000000^3263 ≤ 4330687046437^3263*78125000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41319921 78125000 4330687046437 10000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096393883/2000000000 : ℝ)^4287 ≤ (45395130334077/100000000000000 : ℝ)^3263 := by
    have hnat : (1096393883 : ℕ)^4287*100000000000000^3263 ≤ 45395130334077^3263*2000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096393883 2000000000 45395130334077 100000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1901967877/10000000000 : ℝ)^4287 ≤ (5648999595931/50000000000000 : ℝ)^3263 := by
    have hnat : (1901967877 : ℕ)^4287*50000000000000^3263 ≤ 5648999595931^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901967877 10000000000 5648999595931 50000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41319921/78125000 : ℝ), (1096393883/2000000000 : ℝ), (-1901967877/10000000000 : ℝ)] ![(4330687046437/10000000000000 : ℝ), (45395130334077/100000000000000 : ℝ), (5648999595931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41319921/78125000 : ℝ)|^4287 ≤ (4330687046437/10000000000000 : ℝ)^3263
        have hw : |(41319921/78125000 : ℝ)|=(41319921/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1096393883/2000000000 : ℝ)|^4287 ≤ (45395130334077/100000000000000 : ℝ)^3263
        have hw : |(1096393883/2000000000 : ℝ)|=(1096393883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1901967877/10000000000 : ℝ)|^4287 ≤ (5648999595931/50000000000000 : ℝ)^3263
        have hw : |(-1901967877/10000000000 : ℝ)|=(1901967877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1327_s2_7 (p : ℝ) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324074199/10000000000 : ℝ)*x 0 + (580833167/1250000000 : ℝ)*x 1 + (4022888049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324074199/10000000000 : ℝ)^4287 ≤ (3323751345929/10000000000000 : ℝ)^3263 := by
    have hnat : (4324074199 : ℕ)^4287*10000000000000^3263 ≤ 3323751345929^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324074199 10000000000 3323751345929 10000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (580833167/1250000000 : ℝ)^4287 ≤ (365328170847/1000000000000 : ℝ)^3263 := by
    have hnat : (580833167 : ℕ)^4287*1000000000000^3263 ≤ 365328170847^3263*1250000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580833167 1250000000 365328170847 1000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022888049/10000000000 : ℝ)^4287 ≤ (6045933889207/20000000000000 : ℝ)^3263 := by
    have hnat : (4022888049 : ℕ)^4287*20000000000000^3263 ≤ 6045933889207^3263*10000000000^4287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022888049 10000000000 6045933889207 20000000000000 4287 3263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4287/1024 : ℝ)) 4287 3263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324074199/10000000000 : ℝ), (580833167/1250000000 : ℝ), (4022888049/10000000000 : ℝ)] ![(3323751345929/10000000000000 : ℝ), (365328170847/1000000000000 : ℝ), (6045933889207/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324074199/10000000000 : ℝ)|^4287 ≤ (3323751345929/10000000000000 : ℝ)^3263
        have hw : |(4324074199/10000000000 : ℝ)|=(4324074199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(580833167/1250000000 : ℝ)|^4287 ≤ (365328170847/1000000000000 : ℝ)^3263
        have hw : |(580833167/1250000000 : ℝ)|=(580833167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022888049/10000000000 : ℝ)|^4287 ≤ (6045933889207/20000000000000 : ℝ)^3263
        have hw : |(4022888049/10000000000 : ℝ)|=(4022888049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1327_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (783/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6749/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1219/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3233/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (783/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6749/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (783/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6749/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (783/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6749/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (783/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6749/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (783/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6749/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (783/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6749/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6749/100000 : ℝ) ^ (2143/512 : ℝ) ≤ (157266695006939/12500000000000000000 : ℝ) := by
    have hpowers : (6749/100000 : ℝ)^2143 ≤ (157266695006939/12500000000000000000 : ℝ)^512 := by
      have hnat : (6749 : ℕ)^2143*12500000000000000000^512 ≤ 157266695006939^512*100000^2143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6749 100000 157266695006939 12500000000000000000 2143 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6749/100000 : ℝ)) (X := (157266695006939/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hpowhi : (783/4000 : ℝ) ^ (2143/512 : ℝ) ≤ (10848871367712681/10000000000000000000 : ℝ) := by
    have hpowers : (783/4000 : ℝ)^2143 ≤ (10848871367712681/10000000000000000000 : ℝ)^512 := by
      have hnat : (783 : ℕ)^2143*10000000000000000000^512 ≤ 10848871367712681^512*4000^2143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        783 4000 10848871367712681 10000000000000000000 2143 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (783/4000 : ℝ)) (X := (10848871367712681/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250157266695006939/6250000000000000000 : ℝ) ≤ (10000060117425543/10000000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (6250157266695006939/6250000000000000000 : ℝ)^512 ≤ (10000060117425543/10000000000000000 : ℝ)^2143 := by
      have hnat : (6250157266695006939 : ℕ)^512*10000000000000000^2143 ≤ 10000060117425543^2143*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250157266695006939 6250000000000000000 10000060117425543 10000000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000060117425543/10000000000000000 : ℝ)) (X := (6250157266695006939/6250000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50054873423618591161/50000000000000000000 : ℝ) ≤ (250065523721401/250000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (50054873423618591161/50000000000000000000 : ℝ)^512 ≤ (250065523721401/250000000000000 : ℝ)^2143 := by
      have hnat : (50054873423618591161 : ℕ)^512*250000000000000^2143 ≤ 250065523721401^2143*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054873423618591161 50000000000000000000 250065523721401 250000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250065523721401/250000000000000 : ℝ)) (X := (50054873423618591161/50000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5010848871367712681/5000000000000000000 : ℝ) ≤ (10005181780286537/10000000000000000 : ℝ) ^ (2143/512 : ℝ) := by
    have hpowers : (5010848871367712681/5000000000000000000 : ℝ)^512 ≤ (10005181780286537/10000000000000000 : ℝ)^2143 := by
      have hnat : (5010848871367712681 : ℕ)^512*10000000000000000^2143 ≤ 10005181780286537^2143*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5010848871367712681 5000000000000000000 10005181780286537 10000000000000000 512 2143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005181780286537/10000000000000000 : ℝ)) (X := (5010848871367712681/5000000000000000000 : ℝ)) (by norm_num) 2143 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(157266695006939/12500000000000000000 : ℝ) ≤ ((32056551240862791503/32065000000000000000 : ℝ)+2*(2560831430497/1282600000000000 : ℝ)*(6749/100000 : ℝ))^(2143/512 : ℝ) := by
    rw [show (32056551240862791503/32065000000000000000 : ℝ)+2*(2560831430497/1282600000000000 : ℝ)*(6749/100000 : ℝ)=(10000060117425543/10000000000000000 : ℝ) by norm_num, show 1+2*(157266695006939/12500000000000000000 : ℝ)=(6250157266695006939/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10848871367712681/10000000000000000000 : ℝ)+(157266695006939/12500000000000000000 : ℝ) ≤ ((32056551240862791503/32065000000000000000 : ℝ)+(2560831430497/1282600000000000 : ℝ)*((783/4000 : ℝ)+(6749/100000 : ℝ)))^(2143/512 : ℝ) := by
    rw [show (32056551240862791503/32065000000000000000 : ℝ)+(2560831430497/1282600000000000 : ℝ)*((783/4000 : ℝ)+(6749/100000 : ℝ))=(250065523721401/250000000000000 : ℝ) by norm_num, show 1+(10848871367712681/10000000000000000000 : ℝ)+(157266695006939/12500000000000000000 : ℝ)=(50054873423618591161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10848871367712681/10000000000000000000 : ℝ) ≤ ((32056551240862791503/32065000000000000000 : ℝ)+2*(2560831430497/1282600000000000 : ℝ)*(783/4000 : ℝ))^(2143/512 : ℝ) := by
    rw [show (32056551240862791503/32065000000000000000 : ℝ)+2*(2560831430497/1282600000000000 : ℝ)*(783/4000 : ℝ)=(10005181780286537/10000000000000000 : ℝ) by norm_num, show 1+2*(10848871367712681/10000000000000000000 : ℝ)=(5010848871367712681/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32056551240862791503/32065000000000000000 : ℝ)*(X 1 0+X 2 0)+(2560831430497/1282600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (6749/100000 : ℝ)) (hi := (783/4000 : ℝ)) (c := (32056551240862791503/32065000000000000000 : ℝ)) (alpha := (2560831430497/1282600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32056551240862791503/32065000000000000000 : ℝ)*(X 0 1+X 2 1)+(2560831430497/1282600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (6749/100000 : ℝ)) (hi := (783/4000 : ℝ)) (c := (32056551240862791503/32065000000000000000 : ℝ)) (alpha := (2560831430497/1282600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32056551240862791503/32065000000000000000 : ℝ)*(X 0 2+X 1 2)+(2560831430497/1282600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2143/512 : ℝ)) (lo := (6749/100000 : ℝ)) (hi := (783/4000 : ℝ)) (c := (32056551240862791503/32065000000000000000 : ℝ)) (alpha := (2560831430497/1282600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2046506999/10000000000 : ℝ)*X 0 0+(1370980257/2500000000 : ℝ)*X 0 1+(5180539717/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073403607/2000000000 : ℝ)*X 1 0+(-1101699333/5000000000 : ℝ)*X 1 1+(5180539233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5367017391/10000000000 : ℝ)*X 2 0+(1295134967/2500000000 : ℝ)*X 2 1+(-2203398687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4323929813/10000000000 : ℝ)*X 0 0+(4018817241/10000000000 : ℝ)*X 0 1+(4650696089/10000000000 : ℝ)*X 0 2+(4323929813/10000000000 : ℝ)*X 1 0+(4018817241/10000000000 : ℝ)*X 1 1+(4650696089/10000000000 : ℝ)*X 1 2+(4323929813/10000000000 : ℝ)*X 2 0+(4018817241/10000000000 : ℝ)*X 2 1+(4650696089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2046577183/10000000000 : ℝ)*X 0 0+(5182473843/10000000000 : ℝ)*X 0 1+(5481969407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288949823/10000000000 : ℝ)*X 1 0+(-1901967917/10000000000 : ℝ)*X 1 1+(5481969451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41319921/78125000 : ℝ)*X 2 0+(1096393883/2000000000 : ℝ)*X 2 1+(-1901967877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324074199/10000000000 : ℝ)*X 0 0+(580833167/1250000000 : ℝ)*X 0 1+(4022888049/10000000000 : ℝ)*X 0 2+(4324074199/10000000000 : ℝ)*X 1 0+(580833167/1250000000 : ℝ)*X 1 1+(4022888049/10000000000 : ℝ)*X 1 2+(4324074199/10000000000 : ℝ)*X 2 0+(580833167/1250000000 : ℝ)*X 2 1+(4022888049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1327_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2215061291484445666110389331/801625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1398339339/100000000000000 : ℝ)*(base19) + (83026643/10000000000000 : ℝ)*(base23) + (10647383/5000000000000 : ℝ)*(lower2) + (128597169/25000000000000 : ℝ)*(upper3) + (60168167/50000000000000 : ℝ)*(lower4) + (55550807/20000000000000 : ℝ)*(upper5) + (1219698823256241/50000000000000 : ℝ)*(major0) + (1219698823256241/50000000000000 : ℝ)*(major1) + (1219698823256241/50000000000000 : ℝ)*(major2) + (659237524107039/20000000000000 : ℝ)*(sp0) + (206011638887241/6250000000000 : ℝ)*(sp1) + (659237358053753/20000000000000 : ℝ)*(sp2) + (79129690129747/5000000000000 : ℝ)*(sp3) + (6888893847/50000000000000 : ℝ)*(sp7) + (791303790191317/50000000000000 : ℝ)*(f.failure) + (659237524107039/20000000000000 : ℝ)*(f.sum) + (12969717919943/2004062500000000000000000000 : ℝ)*base66 + (8987429726072945223/1603250000000000000000000000000000 : ℝ)*base67 + (10058589433407695223/1603250000000000000000000000000000 : ℝ)*base69 + (4449729337458554777/1603250000000000000000000000000000 : ℝ)*base72 + (141137387389957/32065000000000000000000000000 : ℝ)*base73 + (13868599959949554777/1603250000000000000000000000000000 : ℝ)*base76 + (3783233319787695223/1603250000000000000000000000000000 : ℝ)*base77 + (7315171741752945223/1603250000000000000000000000000000 : ℝ)*base79 + (86672706933781/16032500000000000000000000000 : ℝ)*base81 + (1546411/312500000000000000000 : ℝ)*base90 + (1546411/312500000000000000000 : ℝ)*base92 + (1546411/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1431224836451313293838043227/160325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1762373627/100000000000000 : ℝ)*(base19) + (2038099917/100000000000000 : ℝ)*(base23) + (29085879/12500000000000 : ℝ)*(upper3) + (92209657/100000000000000 : ℝ)*(lower4) + (140232121/100000000000000 : ℝ)*(upper5) + (494208202750803/20000000000000 : ℝ)*(major0) + (494208202750803/20000000000000 : ℝ)*(major1) + (494208202750803/20000000000000 : ℝ)*(major2) + (1918354831/10000000000000 : ℝ)*(sp1) + (23272167039/100000000000000 : ℝ)*(sp2) + (1669472443890117/50000000000000 : ℝ)*(sp4) + (1669461970929149/50000000000000 : ℝ)*(sp5) + (1669459788756639/50000000000000 : ℝ)*(sp6) + (6262253289689/390625000000 : ℝ)*(sp7) + (6262253289689/390625000000 : ℝ)*(f.failure) + (1669472443890117/50000000000000 : ℝ)*(f.sum) + (30331561214447/12826000000000000000000000000 : ℝ)*base65 + (1116650521779698091/641300000000000000000000000000000 : ℝ)*base68 + (2483442802198098091/641300000000000000000000000000000 : ℝ)*base70 + (5511874612643898091/641300000000000000000000000000000 : ℝ)*base72 + (47301158222943/12826000000000000000000000000 : ℝ)*base73 + (550179431005098091/641300000000000000000000000000000 : ℝ)*base76 + (256852314784401909/641300000000000000000000000000000 : ℝ)*base77 + (481753235327698091/641300000000000000000000000000000 : ℝ)*base80 + (33914778596151/12826000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (107567/39062500000000000000 : ℝ)*base90 + (107567/39062500000000000000 : ℝ)*base92 + (107567/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1327_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (783/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6749/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1219/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3233/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1327_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1327_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1219/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3233/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1327_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1327_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1327_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2143/512 : ℝ) ≤ p) (hpb : p ≤ (4287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9633617/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1219/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3233/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1327_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
