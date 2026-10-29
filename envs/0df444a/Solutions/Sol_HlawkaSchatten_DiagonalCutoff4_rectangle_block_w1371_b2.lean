-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1371_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:20:40.498231+00:00
-- url     : https://prove2.me/submissions/658b72d9-9db6-4c58-bf40-5ba19a9e8783

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
theorem support_rectangle_w1371_s6_0 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2019179461/10000000000 : ℝ)*x 0 + (5411219401/10000000000 : ℝ)*x 1 + (5245447829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2019179461/10000000000 : ℝ)^4331 ≤ (768962193767/6250000000000 : ℝ)^3307 := by
    have hnat : (2019179461 : ℕ)^4331*6250000000000^3307 ≤ 768962193767^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019179461 10000000000 768962193767 6250000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411219401/10000000000 : ℝ)^4331 ≤ (2237077349161/5000000000000 : ℝ)^3307 := by
    have hnat : (5411219401 : ℕ)^4331*5000000000000^3307 ≤ 2237077349161^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411219401 10000000000 2237077349161 5000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245447829/10000000000 : ℝ)^4331 ≤ (10738764473959/25000000000000 : ℝ)^3307 := by
    have hnat : (5245447829 : ℕ)^4331*25000000000000^3307 ≤ 10738764473959^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245447829 10000000000 10738764473959 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2019179461/10000000000 : ℝ), (5411219401/10000000000 : ℝ), (5245447829/10000000000 : ℝ)] ![(768962193767/6250000000000 : ℝ), (2237077349161/5000000000000 : ℝ), (10738764473959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2019179461/10000000000 : ℝ)|^4331 ≤ (768962193767/6250000000000 : ℝ)^3307
        have hw : |(-2019179461/10000000000 : ℝ)|=(2019179461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411219401/10000000000 : ℝ)|^4331 ≤ (2237077349161/5000000000000 : ℝ)^3307
        have hw : |(5411219401/10000000000 : ℝ)|=(5411219401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245447829/10000000000 : ℝ)|^4331 ≤ (10738764473959/25000000000000 : ℝ)^3307
        have hw : |(5245447829/10000000000 : ℝ)|=(5245447829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s6_1 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348480223/10000000000 : ℝ)*x 0 + (-2103618969/10000000000 : ℝ)*x 1 + (2622723929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348480223/10000000000 : ℝ)^4331 ≤ (11015849042737/25000000000000 : ℝ)^3307 := by
    have hnat : (5348480223 : ℕ)^4331*25000000000000^3307 ≤ 11015849042737^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348480223 10000000000 11015849042737 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2103618969/10000000000 : ℝ)^4331 ≤ (12981545607273/100000000000000 : ℝ)^3307 := by
    have hnat : (2103618969 : ℕ)^4331*100000000000000^3307 ≤ 12981545607273^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103618969 10000000000 12981545607273 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622723929/5000000000 : ℝ)^4331 ≤ (42955058206853/100000000000000 : ℝ)^3307 := by
    have hnat : (2622723929 : ℕ)^4331*100000000000000^3307 ≤ 42955058206853^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622723929 5000000000 42955058206853 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348480223/10000000000 : ℝ), (-2103618969/10000000000 : ℝ), (2622723929/5000000000 : ℝ)] ![(11015849042737/25000000000000 : ℝ), (12981545607273/100000000000000 : ℝ), (42955058206853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348480223/10000000000 : ℝ)|^4331 ≤ (11015849042737/25000000000000 : ℝ)^3307
        have hw : |(5348480223/10000000000 : ℝ)|=(5348480223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2103618969/10000000000 : ℝ)|^4331 ≤ (12981545607273/100000000000000 : ℝ)^3307
        have hw : |(-2103618969/10000000000 : ℝ)|=(2103618969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622723929/5000000000 : ℝ)|^4331 ≤ (42955058206853/100000000000000 : ℝ)^3307
        have hw : |(2622723929/5000000000 : ℝ)|=(2622723929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s6_2 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348480189/10000000000 : ℝ)*x 0 + (655680981/1250000000 : ℝ)*x 1 + (-525904757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348480189/10000000000 : ℝ)^4331 ≤ (8812679160821/20000000000000 : ℝ)^3307 := by
    have hnat : (5348480189 : ℕ)^4331*20000000000000^3307 ≤ 8812679160821^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348480189 10000000000 8812679160821 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655680981/1250000000 : ℝ)^4331 ≤ (21477529049803/50000000000000 : ℝ)^3307 := by
    have hnat : (655680981 : ℕ)^4331*50000000000000^3307 ≤ 21477529049803^3307*1250000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655680981 1250000000 21477529049803 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525904757/2500000000 : ℝ)^4331 ≤ (2596309216821/20000000000000 : ℝ)^3307 := by
    have hnat : (525904757 : ℕ)^4331*20000000000000^3307 ≤ 2596309216821^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525904757 2500000000 2596309216821 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348480189/10000000000 : ℝ), (655680981/1250000000 : ℝ), (-525904757/2500000000 : ℝ)] ![(8812679160821/20000000000000 : ℝ), (21477529049803/50000000000000 : ℝ), (2596309216821/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348480189/10000000000 : ℝ)|^4331 ≤ (8812679160821/20000000000000 : ℝ)^3307
        have hw : |(5348480189/10000000000 : ℝ)|=(5348480189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655680981/1250000000 : ℝ)|^4331 ≤ (21477529049803/50000000000000 : ℝ)^3307
        have hw : |(655680981/1250000000 : ℝ)|=(655680981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525904757/2500000000 : ℝ)|^4331 ≤ (2596309216821/20000000000000 : ℝ)^3307
        have hw : |(-525904757/2500000000 : ℝ)|=(525904757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s6_3 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4319092119/10000000000 : ℝ)*x 0 + (4146875817/10000000000 : ℝ)*x 1 + (1124472211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319092119/10000000000 : ℝ)^4331 ≤ (1332149969913/4000000000000 : ℝ)^3307 := by
    have hnat : (4319092119 : ℕ)^4331*4000000000000^3307 ≤ 1332149969913^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319092119 10000000000 1332149969913 4000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4146875817/10000000000 : ℝ)^4331 ≤ (31575468115807/100000000000000 : ℝ)^3307 := by
    have hnat : (4146875817 : ℕ)^4331*100000000000000^3307 ≤ 31575468115807^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146875817 10000000000 31575468115807 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124472211/2500000000 : ℝ)^4331 ≤ (35120782623957/100000000000000 : ℝ)^3307 := by
    have hnat : (1124472211 : ℕ)^4331*100000000000000^3307 ≤ 35120782623957^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124472211 2500000000 35120782623957 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319092119/10000000000 : ℝ), (4146875817/10000000000 : ℝ), (1124472211/2500000000 : ℝ)] ![(1332149969913/4000000000000 : ℝ), (31575468115807/100000000000000 : ℝ), (35120782623957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319092119/10000000000 : ℝ)|^4331 ≤ (1332149969913/4000000000000 : ℝ)^3307
        have hw : |(4319092119/10000000000 : ℝ)|=(4319092119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4146875817/10000000000 : ℝ)|^4331 ≤ (31575468115807/100000000000000 : ℝ)^3307
        have hw : |(4146875817/10000000000 : ℝ)|=(4146875817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124472211/2500000000 : ℝ)|^4331 ≤ (35120782623957/100000000000000 : ℝ)^3307
        have hw : |(1124472211/2500000000 : ℝ)|=(1124472211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s6_4 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1009595731/5000000000 : ℝ)*x 0 + (262302139/500000000 : ℝ)*x 1 + (541062129/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009595731/5000000000 : ℝ)^4331 ≤ (6151745434297/50000000000000 : ℝ)^3307 := by
    have hnat : (1009595731 : ℕ)^4331*50000000000000^3307 ≤ 6151745434297^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009595731 5000000000 6151745434297 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262302139/500000000 : ℝ)^4331 ≤ (42961438687289/100000000000000 : ℝ)^3307 := by
    have hnat : (262302139 : ℕ)^4331*100000000000000^3307 ≤ 42961438687289^3307*500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262302139 500000000 42961438687289 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541062129/1000000000 : ℝ)^4331 ≤ (44735070426111/100000000000000 : ℝ)^3307 := by
    have hnat : (541062129 : ℕ)^4331*100000000000000^3307 ≤ 44735070426111^3307*1000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541062129 1000000000 44735070426111 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1009595731/5000000000 : ℝ), (262302139/500000000 : ℝ), (541062129/1000000000 : ℝ)] ![(6151745434297/50000000000000 : ℝ), (42961438687289/100000000000000 : ℝ), (44735070426111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1009595731/5000000000 : ℝ)|^4331 ≤ (6151745434297/50000000000000 : ℝ)^3307
        have hw : |(-1009595731/5000000000 : ℝ)|=(1009595731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262302139/500000000 : ℝ)|^4331 ≤ (42961438687289/100000000000000 : ℝ)^3307
        have hw : |(262302139/500000000 : ℝ)|=(262302139/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541062129/1000000000 : ℝ)|^4331 ≤ (44735070426111/100000000000000 : ℝ)^3307
        have hw : |(541062129/1000000000 : ℝ)|=(541062129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s6_5 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305641919/10000000000 : ℝ)*x 0 + (-77537821/400000000 : ℝ)*x 1 + (27053107/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305641919/10000000000 : ℝ)^4331 ≤ (43601766246129/100000000000000 : ℝ)^3307 := by
    have hnat : (5305641919 : ℕ)^4331*100000000000000^3307 ≤ 43601766246129^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305641919 10000000000 43601766246129 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77537821/400000000 : ℝ)^4331 ≤ (1457895264793/12500000000000 : ℝ)^3307 := by
    have hnat : (77537821 : ℕ)^4331*12500000000000^3307 ≤ 1457895264793^3307*400000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77537821 400000000 1457895264793 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27053107/50000000 : ℝ)^4331 ≤ (4473507161721/10000000000000 : ℝ)^3307 := by
    have hnat : (27053107 : ℕ)^4331*10000000000000^3307 ≤ 4473507161721^3307*50000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27053107 50000000 4473507161721 10000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305641919/10000000000 : ℝ), (-77537821/400000000 : ℝ), (27053107/50000000 : ℝ)] ![(43601766246129/100000000000000 : ℝ), (1457895264793/12500000000000 : ℝ), (4473507161721/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305641919/10000000000 : ℝ)|^4331 ≤ (43601766246129/100000000000000 : ℝ)^3307
        have hw : |(5305641919/10000000000 : ℝ)|=(5305641919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-77537821/400000000 : ℝ)|^4331 ≤ (1457895264793/12500000000000 : ℝ)^3307
        have hw : |(-77537821/400000000 : ℝ)|=(77537821/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27053107/50000000 : ℝ)|^4331 ≤ (4473507161721/10000000000000 : ℝ)^3307
        have hw : |(27053107/50000000 : ℝ)|=(27053107/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s6_6 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663205237/1250000000 : ℝ)*x 0 + (5410621417/10000000000 : ℝ)*x 1 + (-969222767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663205237/1250000000 : ℝ)^4331 ≤ (43601765998587/100000000000000 : ℝ)^3307 := by
    have hnat : (663205237 : ℕ)^4331*100000000000000^3307 ≤ 43601765998587^3307*1250000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663205237 1250000000 43601765998587 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410621417/10000000000 : ℝ)^4331 ≤ (5591883975161/12500000000000 : ℝ)^3307 := by
    have hnat : (5410621417 : ℕ)^4331*12500000000000^3307 ≤ 5591883975161^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410621417 10000000000 5591883975161 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (969222767/5000000000 : ℝ)^4331 ≤ (11663162189263/100000000000000 : ℝ)^3307 := by
    have hnat : (969222767 : ℕ)^4331*100000000000000^3307 ≤ 11663162189263^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969222767 5000000000 11663162189263 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663205237/1250000000 : ℝ), (5410621417/10000000000 : ℝ), (-969222767/5000000000 : ℝ)] ![(43601765998587/100000000000000 : ℝ), (5591883975161/12500000000000 : ℝ), (11663162189263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663205237/1250000000 : ℝ)|^4331 ≤ (43601765998587/100000000000000 : ℝ)^3307
        have hw : |(663205237/1250000000 : ℝ)|=(663205237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410621417/10000000000 : ℝ)|^4331 ≤ (5591883975161/12500000000000 : ℝ)^3307
        have hw : |(5410621417/10000000000 : ℝ)|=(5410621417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-969222767/5000000000 : ℝ)|^4331 ≤ (11663162189263/100000000000000 : ℝ)^3307
        have hw : |(-969222767/5000000000 : ℝ)|=(969222767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s6_7 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2159558801/5000000000 : ℝ)*x 0 + (4496628771/10000000000 : ℝ)*x 1 + (4148142073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159558801/5000000000 : ℝ)^4331 ≤ (1665200329341/5000000000000 : ℝ)^3307 := by
    have hnat : (2159558801 : ℕ)^4331*5000000000000^3307 ≤ 1665200329341^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159558801 5000000000 1665200329341 5000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496628771/10000000000 : ℝ)^4331 ≤ (8776974391897/25000000000000 : ℝ)^3307 := by
    have hnat : (4496628771 : ℕ)^4331*25000000000000^3307 ≤ 8776974391897^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496628771 10000000000 8776974391897 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4148142073/10000000000 : ℝ)^4331 ≤ (15794047915851/50000000000000 : ℝ)^3307 := by
    have hnat : (4148142073 : ℕ)^4331*50000000000000^3307 ≤ 15794047915851^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148142073 10000000000 15794047915851 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159558801/5000000000 : ℝ), (4496628771/10000000000 : ℝ), (4148142073/10000000000 : ℝ)] ![(1665200329341/5000000000000 : ℝ), (8776974391897/25000000000000 : ℝ), (15794047915851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159558801/5000000000 : ℝ)|^4331 ≤ (1665200329341/5000000000000 : ℝ)^3307
        have hw : |(2159558801/5000000000 : ℝ)|=(2159558801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496628771/10000000000 : ℝ)|^4331 ≤ (8776974391897/25000000000000 : ℝ)^3307
        have hw : |(4496628771/10000000000 : ℝ)|=(4496628771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4148142073/10000000000 : ℝ)|^4331 ≤ (15794047915851/50000000000000 : ℝ)^3307
        have hw : |(4148142073/10000000000 : ℝ)|=(4148142073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1371_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2243/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (589/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11209/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11209/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11209/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11209/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11209/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11209/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11209/100000 : ℝ) ^ (2165/512 : ℝ) ≤ (2393418614731413/25000000000000000000 : ℝ) := by
    have hpowers : (11209/100000 : ℝ)^2165 ≤ (2393418614731413/25000000000000000000 : ℝ)^512 := by
      have hnat : (11209 : ℕ)^2165*25000000000000000000^512 ≤ 2393418614731413^512*100000^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11209 100000 2393418614731413 25000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11209/100000 : ℝ)) (X := (2393418614731413/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14731/100000 : ℝ) ^ (2165/512 : ℝ) ≤ (3039883822186841/10000000000000000000 : ℝ) := by
    have hpowers : (14731/100000 : ℝ)^2165 ≤ (3039883822186841/10000000000000000000 : ℝ)^512 := by
      have hnat : (14731 : ℕ)^2165*10000000000000000000^512 ≤ 3039883822186841^512*100000^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14731 100000 3039883822186841 10000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14731/100000 : ℝ)) (X := (3039883822186841/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502393418614731413/12500000000000000000 : ℝ) ≤ (5000226390903791/5000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (12502393418614731413/12500000000000000000 : ℝ)^512 ≤ (5000226390903791/5000000000000000 : ℝ)^2165 := by
      have hnat : (12502393418614731413 : ℕ)^512*5000000000000000^2165 ≤ 5000226390903791^2165*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502393418614731413 12500000000000000000 5000226390903791 5000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000226390903791/5000000000000000 : ℝ)) (X := (12502393418614731413/12500000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019986256340397031/50000000000000000000 : ℝ) ≤ (2000189032833111/2000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (50019986256340397031/50000000000000000000 : ℝ)^512 ≤ (2000189032833111/2000000000000000 : ℝ)^2165 := by
      have hnat : (50019986256340397031 : ℕ)^512*2000000000000000^2165 ≤ 2000189032833111^2165*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019986256340397031 50000000000000000000 2000189032833111 2000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000189032833111/2000000000000000 : ℝ)) (X := (50019986256340397031/50000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003039883822186841/5000000000000000000 : ℝ) ≤ (1250179693315441/1250000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (5003039883822186841/5000000000000000000 : ℝ)^512 ≤ (1250179693315441/1250000000000000 : ℝ)^2165 := by
      have hnat : (5003039883822186841 : ℕ)^512*1250000000000000^2165 ≤ 1250179693315441^2165*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003039883822186841 5000000000000000000 1250179693315441 1250000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250179693315441/1250000000000000 : ℝ)) (X := (5003039883822186841/5000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2393418614731413/25000000000000000000 : ℝ) ≤ ((3521055646982526509/3522000000000000000 : ℝ)+2*(492382357973/352200000000000 : ℝ)*(11209/100000 : ℝ))^(2165/512 : ℝ) := by
    rw [show (3521055646982526509/3522000000000000000 : ℝ)+2*(492382357973/352200000000000 : ℝ)*(11209/100000 : ℝ)=(5000226390903791/5000000000000000 : ℝ) by norm_num, show 1+2*(2393418614731413/25000000000000000000 : ℝ)=(12502393418614731413/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3039883822186841/10000000000000000000 : ℝ)+(2393418614731413/25000000000000000000 : ℝ) ≤ ((3521055646982526509/3522000000000000000 : ℝ)+(492382357973/352200000000000 : ℝ)*((14731/100000 : ℝ)+(11209/100000 : ℝ)))^(2165/512 : ℝ) := by
    rw [show (3521055646982526509/3522000000000000000 : ℝ)+(492382357973/352200000000000 : ℝ)*((14731/100000 : ℝ)+(11209/100000 : ℝ))=(2000189032833111/2000000000000000 : ℝ) by norm_num, show 1+(3039883822186841/10000000000000000000 : ℝ)+(2393418614731413/25000000000000000000 : ℝ)=(50019986256340397031/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3039883822186841/10000000000000000000 : ℝ) ≤ ((3521055646982526509/3522000000000000000 : ℝ)+2*(492382357973/352200000000000 : ℝ)*(14731/100000 : ℝ))^(2165/512 : ℝ) := by
    rw [show (3521055646982526509/3522000000000000000 : ℝ)+2*(492382357973/352200000000000 : ℝ)*(14731/100000 : ℝ)=(1250179693315441/1250000000000000 : ℝ) by norm_num, show 1+2*(3039883822186841/10000000000000000000 : ℝ)=(5003039883822186841/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3521055646982526509/3522000000000000000 : ℝ)*(X 1 0+X 2 0)+(492382357973/352200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (11209/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (3521055646982526509/3522000000000000000 : ℝ)) (alpha := (492382357973/352200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3521055646982526509/3522000000000000000 : ℝ)*(X 0 1+X 2 1)+(492382357973/352200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (11209/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (3521055646982526509/3522000000000000000 : ℝ)) (alpha := (492382357973/352200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3521055646982526509/3522000000000000000 : ℝ)*(X 0 2+X 1 2)+(492382357973/352200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (11209/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (3521055646982526509/3522000000000000000 : ℝ)) (alpha := (492382357973/352200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2019179461/10000000000 : ℝ)*X 0 0+(5411219401/10000000000 : ℝ)*X 0 1+(5245447829/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348480223/10000000000 : ℝ)*X 1 0+(-2103618969/10000000000 : ℝ)*X 1 1+(2622723929/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348480189/10000000000 : ℝ)*X 2 0+(655680981/1250000000 : ℝ)*X 2 1+(-525904757/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319092119/10000000000 : ℝ)*X 0 0+(4146875817/10000000000 : ℝ)*X 0 1+(1124472211/2500000000 : ℝ)*X 0 2+(4319092119/10000000000 : ℝ)*X 1 0+(4146875817/10000000000 : ℝ)*X 1 1+(1124472211/2500000000 : ℝ)*X 1 2+(4319092119/10000000000 : ℝ)*X 2 0+(4146875817/10000000000 : ℝ)*X 2 1+(1124472211/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1009595731/5000000000 : ℝ)*X 0 0+(262302139/500000000 : ℝ)*X 0 1+(541062129/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305641919/10000000000 : ℝ)*X 1 0+(-77537821/400000000 : ℝ)*X 1 1+(27053107/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663205237/1250000000 : ℝ)*X 2 0+(5410621417/10000000000 : ℝ)*X 2 1+(-969222767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159558801/5000000000 : ℝ)*X 0 0+(4496628771/10000000000 : ℝ)*X 0 1+(4148142073/10000000000 : ℝ)*X 0 2+(2159558801/5000000000 : ℝ)*X 1 0+(4496628771/10000000000 : ℝ)*X 1 1+(4148142073/10000000000 : ℝ)*X 1 2+(2159558801/5000000000 : ℝ)*X 2 0+(4496628771/10000000000 : ℝ)*X 2 1+(4148142073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29284080983146360353947/2935000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1669923607/100000000000000 : ℝ)*(base19) + (149927243/10000000000000 : ℝ)*(base23) + (70762047/100000000000000 : ℝ)*(lower2) + (11932153/5000000000000 : ℝ)*(upper3) + (30937811/50000000000000 : ℝ)*(upper5) + (1110175765887823/25000000000000 : ℝ)*(major0) + (1110175765887823/25000000000000 : ℝ)*(major1) + (1110175765887823/25000000000000 : ℝ)*(major2) + (6032437235961459/100000000000000 : ℝ)*(sp0) + (1508117561561427/25000000000000 : ℝ)*(sp1) + (1508117604224221/25000000000000 : ℝ)*(sp2) + (5697827850647/200000000000 : ℝ)*(sp3) + (2167512991/6250000000000 : ℝ)*(sp4) + (19953025081/100000000000000 : ℝ)*(sp7) + (1424466939174291/50000000000000 : ℝ)*(f.failure) + (1206494383233863/20000000000000 : ℝ)*(f.sum) + (14670301478803/8805000000000000000000000000 : ℝ)*base65 + (666393915391089907/88050000000000000000000000000000 : ℝ)*base67 + (388162705969610093/88050000000000000000000000000000 : ℝ)*base70 + (993547089459710093/88050000000000000000000000000000 : ℝ)*base72 + (20585353364863/8805000000000000000000000000 : ℝ)*base73 + (630380612450739907/88050000000000000000000000000000 : ℝ)*base75 + (1146666809734689907/88050000000000000000000000000000 : ℝ)*base77 + (154105283187560093/88050000000000000000000000000000 : ℝ)*base80 + (2199241782047/8805000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (54357241/5000000000000000000000 : ℝ)*base89 + (54357241/5000000000000000000000 : ℝ)*base91 + (54357241/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33806590888099888154526849/7337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (733826203/100000000000000 : ℝ)*(base19) + (830776803/100000000000000 : ℝ)*(base23) + (134620717/100000000000000 : ℝ)*(upper3) + (27575121/50000000000000 : ℝ)*(lower4) + (22894703/20000000000000 : ℝ)*(upper5) + (1118209406447739/25000000000000 : ℝ)*(major0) + (1118209406447739/25000000000000 : ℝ)*(major1) + (1118209406447739/25000000000000 : ℝ)*(major2) + (2035717137/12500000000000 : ℝ)*(sp1) + (18681579453/100000000000000 : ℝ)*(sp2) + (6076125285258223/100000000000000 : ℝ)*(sp4) + (1519027066423731/25000000000000 : ℝ)*(sp5) + (6076105772901967/100000000000000 : ℝ)*(sp6) + (179346863296539/6250000000000 : ℝ)*(sp7) + (179346863296539/6250000000000 : ℝ)*(f.failure) + (6076125285258223/100000000000000 : ℝ)*(f.sum) + (158317158867/183437500000000000000000000 : ℝ)*base66 + (54292758365627717/29350000000000000000000000000000 : ℝ)*base67 + (39747597541327717/29350000000000000000000000000000 : ℝ)*base69 + (316194954334827717/29350000000000000000000000000000 : ℝ)*base71 + (4078279536301/1467500000000000000000000000 : ℝ)*base74 + (57657606304972283/29350000000000000000000000000000 : ℝ)*base76 + (86014806200077717/29350000000000000000000000000000 : ℝ)*base77 + (93424689463577717/29350000000000000000000000000000 : ℝ)*base79 + (290530782637/733750000000000000000000000 : ℝ)*base81 + (1252911/625000000000000000000 : ℝ)*base90 + (1252911/625000000000000000000 : ℝ)*base92 + (1252911/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1371_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (589/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1371_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1371_s7_0 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1009592199/5000000000 : ℝ)*x 0 + (5411172053/10000000000 : ℝ)*x 1 + (5245491963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009592199/5000000000 : ℝ)^4331 ≤ (12303434497651/100000000000000 : ℝ)^3307 := by
    have hnat : (1009592199 : ℕ)^4331*100000000000000^3307 ≤ 12303434497651^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009592199 5000000000 12303434497651 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411172053/10000000000 : ℝ)^4331 ≤ (22370517137139/50000000000000 : ℝ)^3307 := by
    have hnat : (5411172053 : ℕ)^4331*50000000000000^3307 ≤ 22370517137139^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411172053 10000000000 22370517137139 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245491963/10000000000 : ℝ)^4331 ≤ (42955531220987/100000000000000 : ℝ)^3307 := by
    have hnat : (5245491963 : ℕ)^4331*100000000000000^3307 ≤ 42955531220987^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245491963 10000000000 42955531220987 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1009592199/5000000000 : ℝ), (5411172053/10000000000 : ℝ), (5245491963/10000000000 : ℝ)] ![(12303434497651/100000000000000 : ℝ), (22370517137139/50000000000000 : ℝ), (42955531220987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1009592199/5000000000 : ℝ)|^4331 ≤ (12303434497651/100000000000000 : ℝ)^3307
        have hw : |(-1009592199/5000000000 : ℝ)|=(1009592199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411172053/10000000000 : ℝ)|^4331 ≤ (22370517137139/50000000000000 : ℝ)^3307
        have hw : |(5411172053/10000000000 : ℝ)|=(5411172053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245491963/10000000000 : ℝ)|^4331 ≤ (42955531220987/100000000000000 : ℝ)^3307
        have hw : |(5245491963/10000000000 : ℝ)|=(5245491963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s7_1 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348468361/10000000000 : ℝ)*x 0 + (-2103576231/10000000000 : ℝ)*x 1 + (2622745999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348468361/10000000000 : ℝ)^4331 ≤ (2753954261617/6250000000000 : ℝ)^3307 := by
    have hnat : (5348468361 : ℕ)^4331*6250000000000^3307 ≤ 2753954261617^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348468361 10000000000 2753954261617 6250000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2103576231/10000000000 : ℝ)^4331 ≤ (12981200204243/100000000000000 : ℝ)^3307 := by
    have hnat : (2103576231 : ℕ)^4331*100000000000000^3307 ≤ 12981200204243^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103576231 10000000000 12981200204243 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622745999/5000000000 : ℝ)^4331 ≤ (42955531596353/100000000000000 : ℝ)^3307 := by
    have hnat : (2622745999 : ℕ)^4331*100000000000000^3307 ≤ 42955531596353^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622745999 5000000000 42955531596353 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348468361/10000000000 : ℝ), (-2103576231/10000000000 : ℝ), (2622745999/5000000000 : ℝ)] ![(2753954261617/6250000000000 : ℝ), (12981200204243/100000000000000 : ℝ), (42955531596353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348468361/10000000000 : ℝ)|^4331 ≤ (2753954261617/6250000000000 : ℝ)^3307
        have hw : |(5348468361/10000000000 : ℝ)|=(5348468361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2103576231/10000000000 : ℝ)|^4331 ≤ (12981200204243/100000000000000 : ℝ)^3307
        have hw : |(-2103576231/10000000000 : ℝ)|=(2103576231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622745999/5000000000 : ℝ)|^4331 ≤ (42955531596353/100000000000000 : ℝ)^3307
        have hw : |(2622745999/5000000000 : ℝ)|=(2622745999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s7_2 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069693633/2000000000 : ℝ)*x 0 + (5245492291/10000000000 : ℝ)*x 1 + (-262947013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069693633/2000000000 : ℝ)^4331 ≤ (4406326607113/10000000000000 : ℝ)^3307 := by
    have hnat : (1069693633 : ℕ)^4331*10000000000000^3307 ≤ 4406326607113^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069693633 2000000000 4406326607113 10000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245492291/10000000000 : ℝ)^4331 ≤ (42955534738703/100000000000000 : ℝ)^3307 := by
    have hnat : (5245492291 : ℕ)^4331*100000000000000^3307 ≤ 42955534738703^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245492291 10000000000 42955534738703 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262947013/1250000000 : ℝ)^4331 ≤ (12981199177849/100000000000000 : ℝ)^3307 := by
    have hnat : (262947013 : ℕ)^4331*100000000000000^3307 ≤ 12981199177849^3307*1250000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262947013 1250000000 12981199177849 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069693633/2000000000 : ℝ), (5245492291/10000000000 : ℝ), (-262947013/1250000000 : ℝ)] ![(4406326607113/10000000000000 : ℝ), (42955534738703/100000000000000 : ℝ), (12981199177849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069693633/2000000000 : ℝ)|^4331 ≤ (4406326607113/10000000000000 : ℝ)^3307
        have hw : |(1069693633/2000000000 : ℝ)|=(1069693633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245492291/10000000000 : ℝ)|^4331 ≤ (42955534738703/100000000000000 : ℝ)^3307
        have hw : |(5245492291/10000000000 : ℝ)|=(5245492291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262947013/1250000000 : ℝ)|^4331 ≤ (12981199177849/100000000000000 : ℝ)^3307
        have hw : |(-262947013/1250000000 : ℝ)|=(262947013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s7_3 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (17276383/40000000 : ℝ)*x 0 + (829394553/2000000000 : ℝ)*x 1 + (4497790717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17276383/40000000 : ℝ)^4331 ≤ (6660757183059/20000000000000 : ℝ)^3307 := by
    have hnat : (17276383 : ℕ)^4331*20000000000000^3307 ≤ 6660757183059^3307*40000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17276383 40000000 6660757183059 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (829394553/2000000000 : ℝ)^4331 ≤ (15788217442923/50000000000000 : ℝ)^3307 := by
    have hnat : (829394553 : ℕ)^4331*50000000000000^3307 ≤ 15788217442923^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829394553 2000000000 15788217442923 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497790717/10000000000 : ℝ)^4331 ≤ (8779944793043/25000000000000 : ℝ)^3307 := by
    have hnat : (4497790717 : ℕ)^4331*25000000000000^3307 ≤ 8779944793043^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497790717 10000000000 8779944793043 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17276383/40000000 : ℝ), (829394553/2000000000 : ℝ), (4497790717/10000000000 : ℝ)] ![(6660757183059/20000000000000 : ℝ), (15788217442923/50000000000000 : ℝ), (8779944793043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17276383/40000000 : ℝ)|^4331 ≤ (6660757183059/20000000000000 : ℝ)^3307
        have hw : |(17276383/40000000 : ℝ)|=(17276383/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(829394553/2000000000 : ℝ)|^4331 ≤ (15788217442923/50000000000000 : ℝ)^3307
        have hw : |(829394553/2000000000 : ℝ)|=(829394553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497790717/10000000000 : ℝ)|^4331 ≤ (8779944793043/25000000000000 : ℝ)^3307
        have hw : |(4497790717/10000000000 : ℝ)|=(4497790717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s7_4 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-252399491/1250000000 : ℝ)*x 0 + (5246086511/10000000000 : ℝ)*x 1 + (1352643671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252399491/1250000000 : ℝ)^4331 ≤ (6151763253723/50000000000000 : ℝ)^3307 := by
    have hnat : (252399491 : ℕ)^4331*50000000000000^3307 ≤ 6151763253723^3307*1250000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252399491 1250000000 6151763253723 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246086511/10000000000 : ℝ)^4331 ≤ (1074047692671/2500000000000 : ℝ)^3307 := by
    have hnat : (5246086511 : ℕ)^4331*2500000000000^3307 ≤ 1074047692671^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246086511 10000000000 1074047692671 2500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352643671/2500000000 : ℝ)^4331 ≤ (11183641442299/25000000000000 : ℝ)^3307 := by
    have hnat : (1352643671 : ℕ)^4331*25000000000000^3307 ≤ 11183641442299^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352643671 2500000000 11183641442299 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-252399491/1250000000 : ℝ), (5246086511/10000000000 : ℝ), (1352643671/2500000000 : ℝ)] ![(6151763253723/50000000000000 : ℝ), (1074047692671/2500000000000 : ℝ), (11183641442299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-252399491/1250000000 : ℝ)|^4331 ≤ (6151763253723/50000000000000 : ℝ)^3307
        have hw : |(-252399491/1250000000 : ℝ)|=(252399491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246086511/10000000000 : ℝ)|^4331 ≤ (1074047692671/2500000000000 : ℝ)^3307
        have hw : |(5246086511/10000000000 : ℝ)|=(5246086511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352643671/2500000000 : ℝ)|^4331 ≤ (11183641442299/25000000000000 : ℝ)^3307
        have hw : |(1352643671/2500000000 : ℝ)|=(1352643671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s7_5 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652826879/5000000000 : ℝ)*x 0 + (-242311701/1250000000 : ℝ)*x 1 + (5410574643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652826879/5000000000 : ℝ)^4331 ≤ (8720378733091/20000000000000 : ℝ)^3307 := by
    have hnat : (2652826879 : ℕ)^4331*20000000000000^3307 ≤ 8720378733091^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652826879 5000000000 8720378733091 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242311701/1250000000 : ℝ)^4331 ≤ (11663541005537/100000000000000 : ℝ)^3307 := by
    have hnat : (242311701 : ℕ)^4331*100000000000000^3307 ≤ 11663541005537^3307*1250000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242311701 1250000000 11663541005537 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410574643/10000000000 : ℝ)^4331 ≤ (22367282662621/50000000000000 : ℝ)^3307 := by
    have hnat : (5410574643 : ℕ)^4331*50000000000000^3307 ≤ 22367282662621^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410574643 10000000000 22367282662621 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652826879/5000000000 : ℝ), (-242311701/1250000000 : ℝ), (5410574643/10000000000 : ℝ)] ![(8720378733091/20000000000000 : ℝ), (11663541005537/100000000000000 : ℝ), (22367282662621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652826879/5000000000 : ℝ)|^4331 ≤ (8720378733091/20000000000000 : ℝ)^3307
        have hw : |(2652826879/5000000000 : ℝ)|=(2652826879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-242311701/1250000000 : ℝ)|^4331 ≤ (11663541005537/100000000000000 : ℝ)^3307
        have hw : |(-242311701/1250000000 : ℝ)|=(242311701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410574643/10000000000 : ℝ)|^4331 ≤ (22367282662621/50000000000000 : ℝ)^3307
        have hw : |(5410574643/10000000000 : ℝ)|=(5410574643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s7_6 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305653767/10000000000 : ℝ)*x 0 + (5410574679/10000000000 : ℝ)*x 1 + (-387698709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305653767/10000000000 : ℝ)^4331 ≤ (43601893762319/100000000000000 : ℝ)^3307 := by
    have hnat : (5305653767 : ℕ)^4331*100000000000000^3307 ≤ 43601893762319^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305653767 10000000000 43601893762319 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410574679/10000000000 : ℝ)^4331 ≤ (8946913143011/20000000000000 : ℝ)^3307 := by
    have hnat : (5410574679 : ℕ)^4331*20000000000000^3307 ≤ 8946913143011^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410574679 10000000000 8946913143011 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387698709/2000000000 : ℝ)^4331 ≤ (728971281819/6250000000000 : ℝ)^3307 := by
    have hnat : (387698709 : ℕ)^4331*6250000000000^3307 ≤ 728971281819^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387698709 2000000000 728971281819 6250000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305653767/10000000000 : ℝ), (5410574679/10000000000 : ℝ), (-387698709/2000000000 : ℝ)] ![(43601893762319/100000000000000 : ℝ), (8946913143011/20000000000000 : ℝ), (728971281819/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305653767/10000000000 : ℝ)|^4331 ≤ (43601893762319/100000000000000 : ℝ)^3307
        have hw : |(5305653767/10000000000 : ℝ)|=(5305653767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410574679/10000000000 : ℝ)|^4331 ≤ (8946913143011/20000000000000 : ℝ)^3307
        have hw : |(5410574679/10000000000 : ℝ)|=(5410574679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387698709/2000000000 : ℝ)|^4331 ≤ (728971281819/6250000000000 : ℝ)^3307
        have hw : |(-387698709/2000000000 : ℝ)|=(387698709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s7_7 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4319120703/10000000000 : ℝ)*x 0 + (1124133171/2500000000 : ℝ)*x 1 + (4148237449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319120703/10000000000 : ℝ)^4331 ≤ (33304037902169/100000000000000 : ℝ)^3307 := by
    have hnat : (4319120703 : ℕ)^4331*100000000000000^3307 ≤ 33304037902169^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319120703 10000000000 33304037902169 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124133171/2500000000 : ℝ)^4331 ≤ (280855320497/800000000000 : ℝ)^3307 := by
    have hnat : (1124133171 : ℕ)^4331*800000000000^3307 ≤ 280855320497^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124133171 2500000000 280855320497 800000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4148237449/10000000000 : ℝ)^4331 ≤ (15794523507771/50000000000000 : ℝ)^3307 := by
    have hnat : (4148237449 : ℕ)^4331*50000000000000^3307 ≤ 15794523507771^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148237449 10000000000 15794523507771 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319120703/10000000000 : ℝ), (1124133171/2500000000 : ℝ), (4148237449/10000000000 : ℝ)] ![(33304037902169/100000000000000 : ℝ), (280855320497/800000000000 : ℝ), (15794523507771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319120703/10000000000 : ℝ)|^4331 ≤ (33304037902169/100000000000000 : ℝ)^3307
        have hw : |(4319120703/10000000000 : ℝ)|=(4319120703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124133171/2500000000 : ℝ)|^4331 ≤ (280855320497/800000000000 : ℝ)^3307
        have hw : |(1124133171/2500000000 : ℝ)|=(1124133171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4148237449/10000000000 : ℝ)|^4331 ≤ (15794523507771/50000000000000 : ℝ)^3307
        have hw : |(4148237449/10000000000 : ℝ)|=(4148237449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1371_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (701/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3681/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2243/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2243/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2243/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2243/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2243/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2243/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2243/20000 : ℝ) ^ (2165/512 : ℝ) ≤ (9595362794875743/100000000000000000000 : ℝ) := by
    have hpowers : (2243/20000 : ℝ)^2165 ≤ (9595362794875743/100000000000000000000 : ℝ)^512 := by
      have hnat : (2243 : ℕ)^2165*100000000000000000000^512 ≤ 9595362794875743^512*20000^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2243 20000 9595362794875743 100000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2243/20000 : ℝ)) (X := (9595362794875743/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hpowhi : (589/4000 : ℝ) ^ (2165/512 : ℝ) ≤ (379331461723641/1250000000000000000 : ℝ) := by
    have hpowers : (589/4000 : ℝ)^2165 ≤ (379331461723641/1250000000000000000 : ℝ)^512 := by
      have hnat : (589 : ℕ)^2165*1250000000000000000^512 ≤ 379331461723641^512*4000^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        589 4000 379331461723641 1250000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (589/4000 : ℝ)) (X := (379331461723641/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009595362794875743/50000000000000000000 : ℝ) ≤ (10000453807470683/10000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (50009595362794875743/50000000000000000000 : ℝ)^512 ≤ (10000453807470683/10000000000000000 : ℝ)^2165 := by
      have hnat : (50009595362794875743 : ℕ)^512*10000000000000000^2165 ≤ 10000453807470683^2165*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009595362794875743 50000000000000000000 10000453807470683 10000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000453807470683/10000000000000000 : ℝ)) (X := (50009595362794875743/50000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039941879732767023/100000000000000000000 : ℝ) ≤ (5000472219974551/5000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (100039941879732767023/100000000000000000000 : ℝ)^512 ≤ (5000472219974551/5000000000000000 : ℝ)^2165 := by
      have hnat : (100039941879732767023 : ℕ)^512*5000000000000000^2165 ≤ 5000472219974551^2165*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039941879732767023 100000000000000000000 5000472219974551 5000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000472219974551/5000000000000000 : ℝ)) (X := (100039941879732767023/100000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (625379331461723641/625000000000000000 : ℝ) ≤ (10001435072427521/10000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (625379331461723641/625000000000000000 : ℝ)^512 ≤ (10001435072427521/10000000000000000 : ℝ)^2165 := by
      have hnat : (625379331461723641 : ℕ)^512*10000000000000000^2165 ≤ 10001435072427521^2165*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625379331461723641 625000000000000000 10001435072427521 10000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001435072427521/10000000000000000 : ℝ)) (X := (625379331461723641/625000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9595362794875743/100000000000000000000 : ℝ) ≤ ((292421566481092993/292500000000000000 : ℝ)+2*(163544159473/117000000000000 : ℝ)*(2243/20000 : ℝ))^(2165/512 : ℝ) := by
    rw [show (292421566481092993/292500000000000000 : ℝ)+2*(163544159473/117000000000000 : ℝ)*(2243/20000 : ℝ)=(10000453807470683/10000000000000000 : ℝ) by norm_num, show 1+2*(9595362794875743/100000000000000000000 : ℝ)=(50009595362794875743/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(379331461723641/1250000000000000000 : ℝ)+(9595362794875743/100000000000000000000 : ℝ) ≤ ((292421566481092993/292500000000000000 : ℝ)+(163544159473/117000000000000 : ℝ)*((589/4000 : ℝ)+(2243/20000 : ℝ)))^(2165/512 : ℝ) := by
    rw [show (292421566481092993/292500000000000000 : ℝ)+(163544159473/117000000000000 : ℝ)*((589/4000 : ℝ)+(2243/20000 : ℝ))=(5000472219974551/5000000000000000 : ℝ) by norm_num, show 1+(379331461723641/1250000000000000000 : ℝ)+(9595362794875743/100000000000000000000 : ℝ)=(100039941879732767023/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(379331461723641/1250000000000000000 : ℝ) ≤ ((292421566481092993/292500000000000000 : ℝ)+2*(163544159473/117000000000000 : ℝ)*(589/4000 : ℝ))^(2165/512 : ℝ) := by
    rw [show (292421566481092993/292500000000000000 : ℝ)+2*(163544159473/117000000000000 : ℝ)*(589/4000 : ℝ)=(10001435072427521/10000000000000000 : ℝ) by norm_num, show 1+2*(379331461723641/1250000000000000000 : ℝ)=(625379331461723641/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (292421566481092993/292500000000000000 : ℝ)*(X 1 0+X 2 0)+(163544159473/117000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (2243/20000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (292421566481092993/292500000000000000 : ℝ)) (alpha := (163544159473/117000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (292421566481092993/292500000000000000 : ℝ)*(X 0 1+X 2 1)+(163544159473/117000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (2243/20000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (292421566481092993/292500000000000000 : ℝ)) (alpha := (163544159473/117000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (292421566481092993/292500000000000000 : ℝ)*(X 0 2+X 1 2)+(163544159473/117000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (2243/20000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (292421566481092993/292500000000000000 : ℝ)) (alpha := (163544159473/117000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1009592199/5000000000 : ℝ)*X 0 0+(5411172053/10000000000 : ℝ)*X 0 1+(5245491963/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348468361/10000000000 : ℝ)*X 1 0+(-2103576231/10000000000 : ℝ)*X 1 1+(2622745999/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069693633/2000000000 : ℝ)*X 2 0+(5245492291/10000000000 : ℝ)*X 2 1+(-262947013/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((17276383/40000000 : ℝ)*X 0 0+(829394553/2000000000 : ℝ)*X 0 1+(4497790717/10000000000 : ℝ)*X 0 2+(17276383/40000000 : ℝ)*X 1 0+(829394553/2000000000 : ℝ)*X 1 1+(4497790717/10000000000 : ℝ)*X 1 2+(17276383/40000000 : ℝ)*X 2 0+(829394553/2000000000 : ℝ)*X 2 1+(4497790717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-252399491/1250000000 : ℝ)*X 0 0+(5246086511/10000000000 : ℝ)*X 0 1+(1352643671/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652826879/5000000000 : ℝ)*X 1 0+(-242311701/1250000000 : ℝ)*X 1 1+(5410574643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305653767/10000000000 : ℝ)*X 2 0+(5410574679/10000000000 : ℝ)*X 2 1+(-387698709/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319120703/10000000000 : ℝ)*X 0 0+(1124133171/2500000000 : ℝ)*X 0 1+(4148237449/10000000000 : ℝ)*X 0 2+(4319120703/10000000000 : ℝ)*X 1 0+(1124133171/2500000000 : ℝ)*X 1 1+(4148237449/10000000000 : ℝ)*X 1 2+(4319120703/10000000000 : ℝ)*X 2 0+(1124133171/2500000000 : ℝ)*X 2 1+(4148237449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7942663813594659633683/975000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62407783/3125000000000 : ℝ)*(base19) + (417269253/25000000000000 : ℝ)*(base23) + (262755163/100000000000000 : ℝ)*(upper3) + (57112921/100000000000000 : ℝ)*(upper4) + (306130051/100000000000000 : ℝ)*(upper5) + (1110790505180477/25000000000000 : ℝ)*(major0) + (1110790505180477/25000000000000 : ℝ)*(major1) + (1110790505180477/25000000000000 : ℝ)*(major2) + (6035769467480701/100000000000000 : ℝ)*(sp0) + (3017905175035427/50000000000000 : ℝ)*(sp1) + (3017905339021449/50000000000000 : ℝ)*(sp2) + (142524840042991/5000000000000 : ℝ)*(sp3) + (42879639209/100000000000000 : ℝ)*(sp4) + (14621920019/100000000000000 : ℝ)*(sp7) + (8907848196187/312500000000 : ℝ)*(f.failure) + (603581234711991/10000000000000 : ℝ)*(f.sum) + (2963063276767/2925000000000000000000000000 : ℝ)*base65 + (39063301268150161/7312500000000000000000000000000 : ℝ)*base67 + (11693994061025161/7312500000000000000000000000000 : ℝ)*base69 + (19332176803787339/7312500000000000000000000000000 : ℝ)*base72 + (70679313223/731250000000000000000000000 : ℝ)*base73 + (11470070122787339/7312500000000000000000000000000 : ℝ)*base76 + (2733473647037339/7312500000000000000000000000000 : ℝ)*base78 + (24609118591775161/7312500000000000000000000000000 : ℝ)*base79 + (13298762838833/2925000000000000000000000000 : ℝ)*base82 + (294337/31250000000000000000 : ℝ)*base89 + (294337/31250000000000000000 : ℝ)*base91 + (294337/31250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3667486372507106601706091/812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (684676401/100000000000000 : ℝ)*(base19) + (173556763/20000000000000 : ℝ)*(base23) + (108339301/50000000000000 : ℝ)*(lower1) + (2904911/4000000000000 : ℝ)*(upper3) + (723417/1000000000000 : ℝ)*(lower4) + (9898981/10000000000000 : ℝ)*(upper5) + (4475285772071289/100000000000000 : ℝ)*(major0) + (4475285772071289/100000000000000 : ℝ)*(major1) + (4475285772071289/100000000000000 : ℝ)*(major2) + (4516529739/100000000000000 : ℝ)*(sp2) + (303972548611719/5000000000000 : ℝ)*(sp4) + (6079450287557979/100000000000000 : ℝ)*(sp5) + (243177823516833/4000000000000 : ℝ)*(sp6) + (1435560210723603/50000000000000 : ℝ)*(sp7) + (1435560210723603/50000000000000 : ℝ)*(f.failure) + (303972548611719/5000000000000 : ℝ)*(f.sum) + (10816163740201/1950000000000000000000000000 : ℝ)*base66 + (493510489068040159/9750000000000000000000000000000 : ℝ)*base67 + (98827598149459841/9750000000000000000000000000000 : ℝ)*base70 + (102507098862040159/9750000000000000000000000000000 : ℝ)*base71 + (12064322653501/1950000000000000000000000000 : ℝ)*base74 + (132956318724790159/9750000000000000000000000000000 : ℝ)*base75 + (22049887989040159/9750000000000000000000000000000 : ℝ)*base77 + (49397169639040159/9750000000000000000000000000000 : ℝ)*base79 + (10831344168451/1950000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (33160953/5000000000000000000000 : ℝ)*base89 + (33160953/5000000000000000000000 : ℝ)*base91 + (33160953/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1371_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1371_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1371_box_0 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1854197569/10000000000 : ℝ)*x 0 + (2694361131/5000000000 : ℝ)*x 1 + (5262424/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1854197569/10000000000 : ℝ)^4331 ≤ (1375476913281/12500000000000 : ℝ)^3307 := by
    have hnat : (1854197569 : ℕ)^4331*12500000000000^3307 ≤ 1375476913281^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854197569 10000000000 1375476913281 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694361131/5000000000 : ℝ)^4331 ≤ (5562261600779/12500000000000 : ℝ)^3307 := by
    have hnat : (2694361131 : ℕ)^4331*12500000000000^3307 ≤ 5562261600779^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694361131 5000000000 5562261600779 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262424/9765625 : ℝ)^4331 ≤ (22249045938089/50000000000000 : ℝ)^3307 := by
    have hnat : (5262424 : ℕ)^4331*50000000000000^3307 ≤ 22249045938089^3307*9765625^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262424 9765625 22249045938089 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1854197569/10000000000 : ℝ), (2694361131/5000000000 : ℝ), (5262424/9765625 : ℝ)] ![(1375476913281/12500000000000 : ℝ), (5562261600779/12500000000000 : ℝ), (22249045938089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1854197569/10000000000 : ℝ)|^4331 ≤ (1375476913281/12500000000000 : ℝ)^3307
        have hw : |(-1854197569/10000000000 : ℝ)|=(1854197569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694361131/5000000000 : ℝ)|^4331 ≤ (5562261600779/12500000000000 : ℝ)^3307
        have hw : |(2694361131/5000000000 : ℝ)|=(2694361131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262424/9765625 : ℝ)|^4331 ≤ (22249045938089/50000000000000 : ℝ)^3307
        have hw : |(5262424/9765625 : ℝ)|=(5262424/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_1 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285528679/10000000000 : ℝ)*x 0 + (-1995715047/10000000000 : ℝ)*x 1 + (5388722227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285528679/10000000000 : ℝ)^4331 ≤ (43385421189259/100000000000000 : ℝ)^3307 := by
    have hnat : (5285528679 : ℕ)^4331*100000000000000^3307 ≤ 43385421189259^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285528679 10000000000 43385421189259 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1995715047/10000000000 : ℝ)^4331 ≤ (6058243186927/50000000000000 : ℝ)^3307 := by
    have hnat : (1995715047 : ℕ)^4331*50000000000000^3307 ≤ 6058243186927^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995715047 10000000000 6058243186927 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388722227/10000000000 : ℝ)^4331 ≤ (22249046213861/50000000000000 : ℝ)^3307 := by
    have hnat : (5388722227 : ℕ)^4331*50000000000000^3307 ≤ 22249046213861^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388722227 10000000000 22249046213861 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285528679/10000000000 : ℝ), (-1995715047/10000000000 : ℝ), (5388722227/10000000000 : ℝ)] ![(43385421189259/100000000000000 : ℝ), (6058243186927/50000000000000 : ℝ), (22249046213861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285528679/10000000000 : ℝ)|^4331 ≤ (43385421189259/100000000000000 : ℝ)^3307
        have hw : |(5285528679/10000000000 : ℝ)|=(5285528679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1995715047/10000000000 : ℝ)|^4331 ≤ (6058243186927/50000000000000 : ℝ)^3307
        have hw : |(-1995715047/10000000000 : ℝ)|=(1995715047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388722227/10000000000 : ℝ)|^4331 ≤ (22249046213861/50000000000000 : ℝ)^3307
        have hw : |(5388722227/10000000000 : ℝ)|=(5388722227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_2 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52855289/100000000 : ℝ)*x 0 + (538872207/1000000000 : ℝ)*x 1 + (-24946437/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52855289/100000000 : ℝ)^4331 ≤ (21692711782507/50000000000000 : ℝ)^3307 := by
    have hnat : (52855289 : ℕ)^4331*50000000000000^3307 ≤ 21692711782507^3307*100000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52855289 100000000 21692711782507 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538872207/1000000000 : ℝ)^4331 ≤ (44498090729833/100000000000000 : ℝ)^3307 := by
    have hnat : (538872207 : ℕ)^4331*100000000000000^3307 ≤ 44498090729833^3307*1000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538872207 1000000000 44498090729833 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24946437/125000000 : ℝ)^4331 ≤ (121164856821/1000000000000 : ℝ)^3307 := by
    have hnat : (24946437 : ℕ)^4331*1000000000000^3307 ≤ 121164856821^3307*125000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24946437 125000000 121164856821 1000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52855289/100000000 : ℝ), (538872207/1000000000 : ℝ), (-24946437/125000000 : ℝ)] ![(21692711782507/50000000000000 : ℝ), (44498090729833/100000000000000 : ℝ), (121164856821/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52855289/100000000 : ℝ)|^4331 ≤ (21692711782507/50000000000000 : ℝ)^3307
        have hw : |(52855289/100000000 : ℝ)|=(52855289/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538872207/1000000000 : ℝ)|^4331 ≤ (44498090729833/100000000000000 : ℝ)^3307
        have hw : |(538872207/1000000000 : ℝ)|=(538872207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24946437/125000000 : ℝ)|^4331 ≤ (121164856821/1000000000000 : ℝ)^3307
        have hw : |(-24946437/125000000 : ℝ)|=(24946437/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_3 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2233309823/5000000000 : ℝ)*x 0 + (849831979/2000000000 : ℝ)*x 1 + (4249159461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2233309823/5000000000 : ℝ)^4331 ≤ (4350170728143/12500000000000 : ℝ)^3307 := by
    have hnat : (2233309823 : ℕ)^4331*12500000000000^3307 ≤ 4350170728143^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233309823 5000000000 4350170728143 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849831979/2000000000 : ℝ)^4331 ≤ (3259931925873/10000000000000 : ℝ)^3307 := by
    have hnat : (849831979 : ℕ)^4331*10000000000000^3307 ≤ 3259931925873^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849831979 2000000000 3259931925873 10000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249159461/10000000000 : ℝ)^4331 ≤ (32599314898101/100000000000000 : ℝ)^3307 := by
    have hnat : (4249159461 : ℕ)^4331*100000000000000^3307 ≤ 32599314898101^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249159461 10000000000 32599314898101 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2233309823/5000000000 : ℝ), (849831979/2000000000 : ℝ), (4249159461/10000000000 : ℝ)] ![(4350170728143/12500000000000 : ℝ), (3259931925873/10000000000000 : ℝ), (32599314898101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2233309823/5000000000 : ℝ)|^4331 ≤ (4350170728143/12500000000000 : ℝ)^3307
        have hw : |(2233309823/5000000000 : ℝ)|=(2233309823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849831979/2000000000 : ℝ)|^4331 ≤ (3259931925873/10000000000000 : ℝ)^3307
        have hw : |(849831979/2000000000 : ℝ)|=(849831979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249159461/10000000000 : ℝ)|^4331 ≤ (32599314898101/100000000000000 : ℝ)^3307
        have hw : |(4249159461/10000000000 : ℝ)|=(4249159461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_4 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2186916439/10000000000 : ℝ)*x 0 + (2632765893/5000000000 : ℝ)*x 1 + (1053106401/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186916439/10000000000 : ℝ)^4331 ≤ (6829418650103/50000000000000 : ℝ)^3307 := by
    have hnat : (2186916439 : ℕ)^4331*50000000000000^3307 ≤ 6829418650103^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186916439 10000000000 6829418650103 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632765893/5000000000 : ℝ)^4331 ≤ (21585290082829/50000000000000 : ℝ)^3307 := by
    have hnat : (2632765893 : ℕ)^4331*50000000000000^3307 ≤ 21585290082829^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632765893 5000000000 21585290082829 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053106401/2000000000 : ℝ)^4331 ≤ (43170582517151/100000000000000 : ℝ)^3307 := by
    have hnat : (1053106401 : ℕ)^4331*100000000000000^3307 ≤ 43170582517151^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053106401 2000000000 43170582517151 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2186916439/10000000000 : ℝ), (2632765893/5000000000 : ℝ), (1053106401/2000000000 : ℝ)] ![(6829418650103/50000000000000 : ℝ), (21585290082829/50000000000000 : ℝ), (43170582517151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2186916439/10000000000 : ℝ)|^4331 ≤ (6829418650103/50000000000000 : ℝ)^3307
        have hw : |(-2186916439/10000000000 : ℝ)|=(2186916439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632765893/5000000000 : ℝ)|^4331 ≤ (21585290082829/50000000000000 : ℝ)^3307
        have hw : |(2632765893/5000000000 : ℝ)|=(2632765893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053106401/2000000000 : ℝ)|^4331 ≤ (43170582517151/100000000000000 : ℝ)^3307
        have hw : |(1053106401/2000000000 : ℝ)|=(1053106401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_5 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537195013/1000000000 : ℝ)*x 0 + (-409069211/2000000000 : ℝ)*x 1 + (1053106363/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537195013/1000000000 : ℝ)^4331 ≤ (8863359348111/20000000000000 : ℝ)^3307 := by
    have hnat : (537195013 : ℕ)^4331*20000000000000^3307 ≤ 8863359348111^3307*1000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537195013 1000000000 8863359348111 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409069211/2000000000 : ℝ)^4331 ≤ (3128155694281/25000000000000 : ℝ)^3307 := by
    have hnat : (409069211 : ℕ)^4331*25000000000000^3307 ≤ 3128155694281^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409069211 2000000000 3128155694281 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053106363/2000000000 : ℝ)^4331 ≤ (43170580477043/100000000000000 : ℝ)^3307 := by
    have hnat : (1053106363 : ℕ)^4331*100000000000000^3307 ≤ 43170580477043^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053106363 2000000000 43170580477043 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537195013/1000000000 : ℝ), (-409069211/2000000000 : ℝ), (1053106363/2000000000 : ℝ)] ![(8863359348111/20000000000000 : ℝ), (3128155694281/25000000000000 : ℝ), (43170580477043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537195013/1000000000 : ℝ)|^4331 ≤ (8863359348111/20000000000000 : ℝ)^3307
        have hw : |(537195013/1000000000 : ℝ)|=(537195013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409069211/2000000000 : ℝ)|^4331 ≤ (3128155694281/25000000000000 : ℝ)^3307
        have hw : |(-409069211/2000000000 : ℝ)|=(409069211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053106363/2000000000 : ℝ)|^4331 ≤ (43170580477043/100000000000000 : ℝ)^3307
        have hw : |(1053106363/2000000000 : ℝ)|=(1053106363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_6 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41968359/78125000 : ℝ)*x 0 + (2632765921/5000000000 : ℝ)*x 1 + (-1022673129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41968359/78125000 : ℝ)^4331 ≤ (22158397408709/50000000000000 : ℝ)^3307 := by
    have hnat : (41968359 : ℕ)^4331*50000000000000^3307 ≤ 22158397408709^3307*78125000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41968359 78125000 22158397408709 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632765921/5000000000 : ℝ)^4331 ≤ (43170580766953/100000000000000 : ℝ)^3307 := by
    have hnat : (2632765921 : ℕ)^4331*100000000000000^3307 ≤ 43170580766953^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632765921 5000000000 43170580766953 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022673129/5000000000 : ℝ)^4331 ≤ (625631220177/5000000000000 : ℝ)^3307 := by
    have hnat : (1022673129 : ℕ)^4331*5000000000000^3307 ≤ 625631220177^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022673129 5000000000 625631220177 5000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41968359/78125000 : ℝ), (2632765921/5000000000 : ℝ), (-1022673129/5000000000 : ℝ)] ![(22158397408709/50000000000000 : ℝ), (43170580766953/100000000000000 : ℝ), (625631220177/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41968359/78125000 : ℝ)|^4331 ≤ (22158397408709/50000000000000 : ℝ)^3307
        have hw : |(41968359/78125000 : ℝ)|=(41968359/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632765921/5000000000 : ℝ)|^4331 ≤ (43170580766953/100000000000000 : ℝ)^3307
        have hw : |(2632765921/5000000000 : ℝ)|=(2632765921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022673129/5000000000 : ℝ)|^4331 ≤ (625631220177/5000000000000 : ℝ)^3307
        have hw : |(-1022673129/5000000000 : ℝ)|=(1022673129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_7 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4170603721/10000000000 : ℝ)*x 0 + (4397115001/10000000000 : ℝ)*x 1 + (274819687/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4170603721/10000000000 : ℝ)^4331 ≤ (31812292376379/100000000000000 : ℝ)^3307 := by
    have hnat : (4170603721 : ℕ)^4331*100000000000000^3307 ≤ 31812292376379^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170603721 10000000000 31812292376379 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4397115001/10000000000 : ℝ)^4331 ≤ (6818770769881/20000000000000 : ℝ)^3307 := by
    have hnat : (4397115001 : ℕ)^4331*20000000000000^3307 ≤ 6818770769881^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4397115001 10000000000 6818770769881 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274819687/625000000 : ℝ)^4331 ≤ (17046926879007/50000000000000 : ℝ)^3307 := by
    have hnat : (274819687 : ℕ)^4331*50000000000000^3307 ≤ 17046926879007^3307*625000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274819687 625000000 17046926879007 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4170603721/10000000000 : ℝ), (4397115001/10000000000 : ℝ), (274819687/625000000 : ℝ)] ![(31812292376379/100000000000000 : ℝ), (6818770769881/20000000000000 : ℝ), (17046926879007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4170603721/10000000000 : ℝ)|^4331 ≤ (31812292376379/100000000000000 : ℝ)^3307
        have hw : |(4170603721/10000000000 : ℝ)|=(4170603721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4397115001/10000000000 : ℝ)|^4331 ≤ (6818770769881/20000000000000 : ℝ)^3307
        have hw : |(4397115001/10000000000 : ℝ)|=(4397115001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274819687/625000000 : ℝ)|^4331 ≤ (17046926879007/50000000000000 : ℝ)^3307
        have hw : |(274819687/625000000 : ℝ)|=(274819687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_8 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-132310769/625000000 : ℝ)*x 0 + (5180589147/10000000000 : ℝ)*x 1 + (270136427/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132310769/625000000 : ℝ)^4331 ≤ (13089571793911/100000000000000 : ℝ)^3307 := by
    have hnat : (132310769 : ℕ)^4331*100000000000000^3307 ≤ 13089571793911^3307*625000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132310769 625000000 13089571793911 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180589147/10000000000 : ℝ)^4331 ≤ (21130401242099/50000000000000 : ℝ)^3307 := by
    have hnat : (5180589147 : ℕ)^4331*50000000000000^3307 ≤ 21130401242099^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180589147 10000000000 21130401242099 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270136427/500000000 : ℝ)^4331 ≤ (11162406428281/25000000000000 : ℝ)^3307 := by
    have hnat : (270136427 : ℕ)^4331*25000000000000^3307 ≤ 11162406428281^3307*500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270136427 500000000 11162406428281 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132310769/625000000 : ℝ), (5180589147/10000000000 : ℝ), (270136427/500000000 : ℝ)] ![(13089571793911/100000000000000 : ℝ), (21130401242099/50000000000000 : ℝ), (11162406428281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132310769/625000000 : ℝ)|^4331 ≤ (13089571793911/100000000000000 : ℝ)^3307
        have hw : |(-132310769/625000000 : ℝ)|=(132310769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180589147/10000000000 : ℝ)|^4331 ≤ (21130401242099/50000000000000 : ℝ)^3307
        have hw : |(5180589147/10000000000 : ℝ)|=(5180589147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270136427/500000000 : ℝ)|^4331 ≤ (11162406428281/25000000000000 : ℝ)^3307
        have hw : |(270136427/500000000 : ℝ)|=(270136427/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_9 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275698443/10000000000 : ℝ)*x 0 + (-994970629/5000000000 : ℝ)*x 1 + (5402728489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275698443/10000000000 : ℝ)^4331 ≤ (21639888186457/50000000000000 : ℝ)^3307 := by
    have hnat : (5275698443 : ℕ)^4331*50000000000000^3307 ≤ 21639888186457^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275698443 10000000000 21639888186457 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994970629/5000000000 : ℝ)^4331 ≤ (12070598454899/100000000000000 : ℝ)^3307 := by
    have hnat : (994970629 : ℕ)^4331*100000000000000^3307 ≤ 12070598454899^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994970629 5000000000 12070598454899 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402728489/10000000000 : ℝ)^4331 ≤ (44649625161137/100000000000000 : ℝ)^3307 := by
    have hnat : (5402728489 : ℕ)^4331*100000000000000^3307 ≤ 44649625161137^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402728489 10000000000 44649625161137 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275698443/10000000000 : ℝ), (-994970629/5000000000 : ℝ), (5402728489/10000000000 : ℝ)] ![(21639888186457/50000000000000 : ℝ), (12070598454899/100000000000000 : ℝ), (44649625161137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275698443/10000000000 : ℝ)|^4331 ≤ (21639888186457/50000000000000 : ℝ)^3307
        have hw : |(5275698443/10000000000 : ℝ)|=(5275698443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-994970629/5000000000 : ℝ)|^4331 ≤ (12070598454899/100000000000000 : ℝ)^3307
        have hw : |(-994970629/5000000000 : ℝ)|=(994970629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402728489/10000000000 : ℝ)|^4331 ≤ (44649625161137/100000000000000 : ℝ)^3307
        have hw : |(5402728489/10000000000 : ℝ)|=(5402728489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_10 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318924561/2500000000 : ℝ)*x 0 + (2701364041/5000000000 : ℝ)*x 1 + (-1989942081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318924561/2500000000 : ℝ)^4331 ≤ (43279774234893/100000000000000 : ℝ)^3307 := by
    have hnat : (1318924561 : ℕ)^4331*100000000000000^3307 ≤ 43279774234893^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318924561 2500000000 43279774234893 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701364041/5000000000 : ℝ)^4331 ≤ (8929924151213/20000000000000 : ℝ)^3307 := by
    have hnat : (2701364041 : ℕ)^4331*20000000000000^3307 ≤ 8929924151213^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701364041 5000000000 8929924151213 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989942081/10000000000 : ℝ)^4331 ≤ (6035302496431/50000000000000 : ℝ)^3307 := by
    have hnat : (1989942081 : ℕ)^4331*50000000000000^3307 ≤ 6035302496431^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989942081 10000000000 6035302496431 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318924561/2500000000 : ℝ), (2701364041/5000000000 : ℝ), (-1989942081/10000000000 : ℝ)] ![(43279774234893/100000000000000 : ℝ), (8929924151213/20000000000000 : ℝ), (6035302496431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318924561/2500000000 : ℝ)|^4331 ≤ (43279774234893/100000000000000 : ℝ)^3307
        have hw : |(1318924561/2500000000 : ℝ)|=(1318924561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701364041/5000000000 : ℝ)|^4331 ≤ (8929924151213/20000000000000 : ℝ)^3307
        have hw : |(2701364041/5000000000 : ℝ)|=(2701364041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1989942081/10000000000 : ℝ)|^4331 ≤ (6035302496431/50000000000000 : ℝ)^3307
        have hw : |(-1989942081/10000000000 : ℝ)|=(1989942081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_11 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (449971777/1000000000 : ℝ)*x 0 + (2116161437/5000000000 : ℝ)*x 1 + (4232323691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449971777/1000000000 : ℝ)^4331 ≤ (35139486556451/100000000000000 : ℝ)^3307 := by
    have hnat : (449971777 : ℕ)^4331*100000000000000^3307 ≤ 35139486556451^3307*1000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449971777 1000000000 35139486556451 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116161437/5000000000 : ℝ)^4331 ≤ (1621512630481/5000000000000 : ℝ)^3307 := by
    have hnat : (2116161437 : ℕ)^4331*5000000000000^3307 ≤ 1621512630481^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116161437 5000000000 1621512630481 5000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232323691/10000000000 : ℝ)^4331 ≤ (32430260808369/100000000000000 : ℝ)^3307 := by
    have hnat : (4232323691 : ℕ)^4331*100000000000000^3307 ≤ 32430260808369^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232323691 10000000000 32430260808369 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(449971777/1000000000 : ℝ), (2116161437/5000000000 : ℝ), (4232323691/10000000000 : ℝ)] ![(35139486556451/100000000000000 : ℝ), (1621512630481/5000000000000 : ℝ), (32430260808369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(449971777/1000000000 : ℝ)|^4331 ≤ (35139486556451/100000000000000 : ℝ)^3307
        have hw : |(449971777/1000000000 : ℝ)|=(449971777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2116161437/5000000000 : ℝ)|^4331 ≤ (1621512630481/5000000000000 : ℝ)^3307
        have hw : |(2116161437/5000000000 : ℝ)|=(2116161437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232323691/10000000000 : ℝ)|^4331 ≤ (32430260808369/100000000000000 : ℝ)^3307
        have hw : |(4232323691/10000000000 : ℝ)|=(4232323691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_12 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-481106051/2500000000 : ℝ)*x 0 + (218860927/400000000 : ℝ)*x 1 + (5254440471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (481106051/2500000000 : ℝ)^4331 ≤ (11552800467133/100000000000000 : ℝ)^3307 := by
    have hnat : (481106051 : ℕ)^4331*100000000000000^3307 ≤ 11552800467133^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481106051 2500000000 11552800467133 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218860927/400000000 : ℝ)^4331 ≤ (11348918129607/25000000000000 : ℝ)^3307 := by
    have hnat : (218860927 : ℕ)^4331*25000000000000^3307 ≤ 11348918129607^3307*400000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218860927 400000000 11348918129607 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254440471/10000000000 : ℝ)^4331 ≤ (21525763499549/50000000000000 : ℝ)^3307 := by
    have hnat : (5254440471 : ℕ)^4331*50000000000000^3307 ≤ 21525763499549^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254440471 10000000000 21525763499549 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-481106051/2500000000 : ℝ), (218860927/400000000 : ℝ), (5254440471/10000000000 : ℝ)] ![(11552800467133/100000000000000 : ℝ), (11348918129607/25000000000000 : ℝ), (21525763499549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-481106051/2500000000 : ℝ)|^4331 ≤ (11552800467133/100000000000000 : ℝ)^3307
        have hw : |(-481106051/2500000000 : ℝ)|=(481106051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218860927/400000000 : ℝ)|^4331 ≤ (11348918129607/25000000000000 : ℝ)^3307
        have hw : |(218860927/400000000 : ℝ)|=(218860927/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254440471/10000000000 : ℝ)|^4331 ≤ (21525763499549/50000000000000 : ℝ)^3307
        have hw : |(5254440471/10000000000 : ℝ)|=(5254440471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_13 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268986433/500000000 : ℝ)*x 0 + (-2049712429/10000000000 : ℝ)*x 1 + (5254440449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268986433/500000000 : ℝ)^4331 ≤ (44400855935629/100000000000000 : ℝ)^3307 := by
    have hnat : (268986433 : ℕ)^4331*100000000000000^3307 ≤ 44400855935629^3307*500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268986433 500000000 44400855935629 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2049712429/10000000000 : ℝ)^4331 ≤ (1568452160941/12500000000000 : ℝ)^3307 := by
    have hnat : (2049712429 : ℕ)^4331*12500000000000^3307 ≤ 1568452160941^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049712429 10000000000 1568452160941 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254440449/10000000000 : ℝ)^4331 ≤ (43051526763029/100000000000000 : ℝ)^3307 := by
    have hnat : (5254440449 : ℕ)^4331*100000000000000^3307 ≤ 43051526763029^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254440449 10000000000 43051526763029 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268986433/500000000 : ℝ), (-2049712429/10000000000 : ℝ), (5254440449/10000000000 : ℝ)] ![(44400855935629/100000000000000 : ℝ), (1568452160941/12500000000000 : ℝ), (43051526763029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268986433/500000000 : ℝ)|^4331 ≤ (44400855935629/100000000000000 : ℝ)^3307
        have hw : |(268986433/500000000 : ℝ)|=(268986433/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2049712429/10000000000 : ℝ)|^4331 ≤ (1568452160941/12500000000000 : ℝ)^3307
        have hw : |(-2049712429/10000000000 : ℝ)|=(2049712429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254440449/10000000000 : ℝ)|^4331 ≤ (43051526763029/100000000000000 : ℝ)^3307
        have hw : |(5254440449/10000000000 : ℝ)|=(5254440449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_14 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379728643/10000000000 : ℝ)*x 0 + (2627220243/5000000000 : ℝ)*x 1 + (-2049712403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379728643/10000000000 : ℝ)^4331 ≤ (11100213937969/25000000000000 : ℝ)^3307 := by
    have hnat : (5379728643 : ℕ)^4331*25000000000000^3307 ≤ 11100213937969^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379728643 10000000000 11100213937969 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627220243/5000000000 : ℝ)^4331 ≤ (21525763580027/50000000000000 : ℝ)^3307 := by
    have hnat : (2627220243 : ℕ)^4331*50000000000000^3307 ≤ 21525763580027^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627220243 5000000000 21525763580027 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2049712403/10000000000 : ℝ)^4331 ≤ (12547617079081/100000000000000 : ℝ)^3307 := by
    have hnat : (2049712403 : ℕ)^4331*100000000000000^3307 ≤ 12547617079081^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049712403 10000000000 12547617079081 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379728643/10000000000 : ℝ), (2627220243/5000000000 : ℝ), (-2049712403/10000000000 : ℝ)] ![(11100213937969/25000000000000 : ℝ), (21525763580027/50000000000000 : ℝ), (12547617079081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379728643/10000000000 : ℝ)|^4331 ≤ (11100213937969/25000000000000 : ℝ)^3307
        have hw : |(5379728643/10000000000 : ℝ)|=(5379728643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627220243/5000000000 : ℝ)|^4331 ≤ (21525763580027/50000000000000 : ℝ)^3307
        have hw : |(2627220243/5000000000 : ℝ)|=(2627220243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2049712403/10000000000 : ℝ)|^4331 ≤ (12547617079081/100000000000000 : ℝ)^3307
        have hw : |(-2049712403/10000000000 : ℝ)|=(2049712403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_box_15 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2071751463/5000000000 : ℝ)*x 0 + (882085129/2000000000 : ℝ)*x 1 + (4410425611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071751463/5000000000 : ℝ)^4331 ≤ (3154183784533/10000000000000 : ℝ)^3307 := by
    have hnat : (2071751463 : ℕ)^4331*10000000000000^3307 ≤ 3154183784533^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071751463 5000000000 3154183784533 10000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882085129/2000000000 : ℝ)^4331 ≤ (17114540621811/50000000000000 : ℝ)^3307 := by
    have hnat : (882085129 : ℕ)^4331*50000000000000^3307 ≤ 17114540621811^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882085129 2000000000 17114540621811 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4410425611/10000000000 : ℝ)^4331 ≤ (34229080898043/100000000000000 : ℝ)^3307 := by
    have hnat : (4410425611 : ℕ)^4331*100000000000000^3307 ≤ 34229080898043^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410425611 10000000000 34229080898043 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2071751463/5000000000 : ℝ), (882085129/2000000000 : ℝ), (4410425611/10000000000 : ℝ)] ![(3154183784533/10000000000000 : ℝ), (17114540621811/50000000000000 : ℝ), (34229080898043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2071751463/5000000000 : ℝ)|^4331 ≤ (3154183784533/10000000000000 : ℝ)^3307
        have hw : |(2071751463/5000000000 : ℝ)|=(2071751463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(882085129/2000000000 : ℝ)|^4331 ≤ (17114540621811/50000000000000 : ℝ)^3307
        have hw : |(882085129/2000000000 : ℝ)|=(882085129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4410425611/10000000000 : ℝ)|^4331 ≤ (34229080898043/100000000000000 : ℝ)^3307
        have hw : |(4410425611/10000000000 : ℝ)|=(4410425611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1371_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(15717/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29499/50000 : ℝ) ∧ (40061/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (5279/6250 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3681/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (701/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3681/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (701/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3681/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (701/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3681/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (701/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3681/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (701/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3681/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (701/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (701/6250 : ℝ) ^ (2165/512 : ℝ) ≤ (1199872645191261/12500000000000000000 : ℝ) := by
    have hpowers : (701/6250 : ℝ)^2165 ≤ (1199872645191261/12500000000000000000 : ℝ)^512 := by
      have hnat : (701 : ℕ)^2165*12500000000000000000^512 ≤ 1199872645191261^512*6250^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 6250 1199872645191261 12500000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/6250 : ℝ)) (X := (1199872645191261/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3681/25000 : ℝ) ^ (2165/512 : ℝ) ≤ (6067560682595871/20000000000000000000 : ℝ) := by
    have hpowers : (3681/25000 : ℝ)^2165 ≤ (6067560682595871/20000000000000000000 : ℝ)^512 := by
      have hnat : (3681 : ℕ)^2165*20000000000000000000^512 ≤ 6067560682595871^512*25000^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3681 25000 6067560682595871 20000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3681/25000 : ℝ)) (X := (6067560682595871/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251199872645191261/6250000000000000000 : ℝ) ≤ (2500113494646707/2500000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (6251199872645191261/6250000000000000000 : ℝ)^512 ≤ (2500113494646707/2500000000000000 : ℝ)^2165 := by
      have hnat : (6251199872645191261 : ℕ)^512*2500000000000000^2165 ≤ 2500113494646707^2165*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251199872645191261 6250000000000000000 2500113494646707 2500000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500113494646707/2500000000000000 : ℝ)) (X := (6251199872645191261/6250000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039936784574509443/100000000000000000000 : ℝ) ≤ (2000188863898127/2000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (100039936784574509443/100000000000000000000 : ℝ)^512 ≤ (2000188863898127/2000000000000000 : ℝ)^2165 := by
      have hnat : (100039936784574509443 : ℕ)^512*2000000000000000^2165 ≤ 2000188863898127^2165*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039936784574509443 100000000000000000000 2000188863898127 2000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000188863898127/2000000000000000 : ℝ)) (X := (100039936784574509443/100000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006067560682595871/10000000000000000000 : ℝ) ≤ (5000717330197221/5000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (10006067560682595871/10000000000000000000 : ℝ)^512 ≤ (5000717330197221/5000000000000000 : ℝ)^2165 := by
      have hnat : (10006067560682595871 : ℕ)^512*5000000000000000^2165 ≤ 5000717330197221^2165*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006067560682595871 10000000000000000000 5000717330197221 5000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000717330197221/5000000000000000 : ℝ)) (X := (10006067560682595871/10000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1199872645191261/12500000000000000000 : ℝ) ≤ ((17535296614864197/17540000000000000 : ℝ)+2*(490340903807/350800000000000 : ℝ)*(701/6250 : ℝ))^(2165/512 : ℝ) := by
    rw [show (17535296614864197/17540000000000000 : ℝ)+2*(490340903807/350800000000000 : ℝ)*(701/6250 : ℝ)=(2500113494646707/2500000000000000 : ℝ) by norm_num, show 1+2*(1199872645191261/12500000000000000000 : ℝ)=(6251199872645191261/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6067560682595871/20000000000000000000 : ℝ)+(1199872645191261/12500000000000000000 : ℝ) ≤ ((17535296614864197/17540000000000000 : ℝ)+(490340903807/350800000000000 : ℝ)*((3681/25000 : ℝ)+(701/6250 : ℝ)))^(2165/512 : ℝ) := by
    rw [show (17535296614864197/17540000000000000 : ℝ)+(490340903807/350800000000000 : ℝ)*((3681/25000 : ℝ)+(701/6250 : ℝ))=(2000188863898127/2000000000000000 : ℝ) by norm_num, show 1+(6067560682595871/20000000000000000000 : ℝ)+(1199872645191261/12500000000000000000 : ℝ)=(100039936784574509443/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6067560682595871/20000000000000000000 : ℝ) ≤ ((17535296614864197/17540000000000000 : ℝ)+2*(490340903807/350800000000000 : ℝ)*(3681/25000 : ℝ))^(2165/512 : ℝ) := by
    rw [show (17535296614864197/17540000000000000 : ℝ)+2*(490340903807/350800000000000 : ℝ)*(3681/25000 : ℝ)=(5000717330197221/5000000000000000 : ℝ) by norm_num, show 1+2*(6067560682595871/20000000000000000000 : ℝ)=(10006067560682595871/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17535296614864197/17540000000000000 : ℝ)*(X 1 0+X 2 0)+(490340903807/350800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (17535296614864197/17540000000000000 : ℝ)) (alpha := (490340903807/350800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17535296614864197/17540000000000000 : ℝ)*(X 0 1+X 2 1)+(490340903807/350800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (17535296614864197/17540000000000000 : ℝ)) (alpha := (490340903807/350800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17535296614864197/17540000000000000 : ℝ)*(X 0 2+X 1 2)+(490340903807/350800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (17535296614864197/17540000000000000 : ℝ)) (alpha := (490340903807/350800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1854197569/10000000000 : ℝ)*X 0 0+(2694361131/5000000000 : ℝ)*X 0 1+(5262424/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285528679/10000000000 : ℝ)*X 1 0+(-1995715047/10000000000 : ℝ)*X 1 1+(5388722227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((52855289/100000000 : ℝ)*X 2 0+(538872207/1000000000 : ℝ)*X 2 1+(-24946437/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2233309823/5000000000 : ℝ)*X 0 0+(849831979/2000000000 : ℝ)*X 0 1+(4249159461/10000000000 : ℝ)*X 0 2+(2233309823/5000000000 : ℝ)*X 1 0+(849831979/2000000000 : ℝ)*X 1 1+(4249159461/10000000000 : ℝ)*X 1 2+(2233309823/5000000000 : ℝ)*X 2 0+(849831979/2000000000 : ℝ)*X 2 1+(4249159461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2186916439/10000000000 : ℝ)*X 0 0+(2632765893/5000000000 : ℝ)*X 0 1+(1053106401/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((537195013/1000000000 : ℝ)*X 1 0+(-409069211/2000000000 : ℝ)*X 1 1+(1053106363/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41968359/78125000 : ℝ)*X 2 0+(2632765921/5000000000 : ℝ)*X 2 1+(-1022673129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4170603721/10000000000 : ℝ)*X 0 0+(4397115001/10000000000 : ℝ)*X 0 1+(274819687/625000000 : ℝ)*X 0 2+(4170603721/10000000000 : ℝ)*X 1 0+(4397115001/10000000000 : ℝ)*X 1 1+(274819687/625000000 : ℝ)*X 1 2+(4170603721/10000000000 : ℝ)*X 2 0+(4397115001/10000000000 : ℝ)*X 2 1+(274819687/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-132310769/625000000 : ℝ)*X 0 0+(5180589147/10000000000 : ℝ)*X 0 1+(270136427/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275698443/10000000000 : ℝ)*X 1 0+(-994970629/5000000000 : ℝ)*X 1 1+(5402728489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1318924561/2500000000 : ℝ)*X 2 0+(2701364041/5000000000 : ℝ)*X 2 1+(-1989942081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((449971777/1000000000 : ℝ)*X 0 0+(2116161437/5000000000 : ℝ)*X 0 1+(4232323691/10000000000 : ℝ)*X 0 2+(449971777/1000000000 : ℝ)*X 1 0+(2116161437/5000000000 : ℝ)*X 1 1+(4232323691/10000000000 : ℝ)*X 1 2+(449971777/1000000000 : ℝ)*X 2 0+(2116161437/5000000000 : ℝ)*X 2 1+(4232323691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-481106051/2500000000 : ℝ)*X 0 0+(218860927/400000000 : ℝ)*X 0 1+(5254440471/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((268986433/500000000 : ℝ)*X 1 0+(-2049712429/10000000000 : ℝ)*X 1 1+(5254440449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5379728643/10000000000 : ℝ)*X 2 0+(2627220243/5000000000 : ℝ)*X 2 1+(-2049712403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2071751463/5000000000 : ℝ)*X 0 0+(882085129/2000000000 : ℝ)*X 0 1+(4410425611/10000000000 : ℝ)*X 0 2+(2071751463/5000000000 : ℝ)*X 1 0+(882085129/2000000000 : ℝ)*X 1 1+(4410425611/10000000000 : ℝ)*X 1 2+(2071751463/5000000000 : ℝ)*X 2 0+(882085129/2000000000 : ℝ)*X 2 1+(4410425611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15717/25000 : ℝ) ≤ (-551329026374726686876980432837/877000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4596699/6250000000000 : ℝ)*(lower0) + (19216319/100000000000000 : ℝ)*(lower3) + (122679449/100000000000000 : ℝ)*(lower4) + (2952995708269993/100000000000000 : ℝ)*(major0) + (2952995708269993/100000000000000 : ℝ)*(major1) + (2952995708269993/100000000000000 : ℝ)*(major2) + (1082961541/25000000000000 : ℝ)*(sp1) + (10221844237/100000000000000 : ℝ)*(sp2) + (1008111985898497/25000000000000 : ℝ)*(sp4) + (40324472506221/1000000000000 : ℝ)*(sp5) + (2016220680312013/50000000000000 : ℝ)*(sp6) + (473623400108371/25000000000000 : ℝ)*(sp7) + (909718569/25000000000000 : ℝ)*(sp12) + (1346765359/100000000000000 : ℝ)*(sp15) + (1894494947198843/100000000000000 : ℝ)*(f.failure) + (504056447808533/12500000000000 : ℝ)*(f.sum) + (59027616153871/17540000000000000000000000000 : ℝ)*base65 + (3932335249569829/1754000000000000000000000000000 : ℝ)*base68 + (5179495035093829/1754000000000000000000000000000 : ℝ)*base70 + (6126555084792171/1754000000000000000000000000000 : ℝ)*base71 + (87015518672389/17540000000000000000000000000 : ℝ)*base74 + (6492870576261829/1754000000000000000000000000000 : ℝ)*base76 + (3304920374008171/1754000000000000000000000000000 : ℝ)*base77 + (2142549464525829/1754000000000000000000000000000 : ℝ)*base80 + (59411793144109/17540000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (57225807/10000000000000000000000 : ℝ)*base90 + (57225807/10000000000000000000000 : ℝ)*base92 + (57225807/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29499/50000 : ℝ) ≤ (517433180763239964351650230377/877000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6559671/25000000000000 : ℝ)*(upper3) + (22072553/20000000000000 : ℝ)*(upper4) + (2123379/6250000000000 : ℝ)*(lower5) + (3022654670748351/100000000000000 : ℝ)*(major0) + (3022654670748351/100000000000000 : ℝ)*(major1) + (3022654670748351/100000000000000 : ℝ)*(major2) + (204322742010467/5000000000000 : ℝ)*(sp0) + (25540318664849/625000000000 : ℝ)*(sp1) + (2043228175479393/50000000000000 : ℝ)*(sp2) + (1939183694395029/100000000000000 : ℝ)*(sp3) + (383852887/25000000000000 : ℝ)*(sp6) + (486584531/50000000000000 : ℝ)*(sp7) + (1523080497/50000000000000 : ℝ)*(sp8) + (3449997247/50000000000000 : ℝ)*(sp9) + (1939184667564091/100000000000000 : ℝ)*(f.failure) + (817291577274067/20000000000000 : ℝ)*(f.sum) + (28673007280257/17540000000000000000000000000 : ℝ)*base65 + (12771984313191997/1754000000000000000000000000000 : ℝ)*base67 + (14312927234659997/1754000000000000000000000000000 : ℝ)*base69 + (9086501573249997/1754000000000000000000000000000 : ℝ)*base71 + (84423050361357/17540000000000000000000000000 : ℝ)*base73 + (8696895233575997/1754000000000000000000000000000 : ℝ)*base75 + (11903999317173997/1754000000000000000000000000000 : ℝ)*base77 + (6426610009739997/1754000000000000000000000000000 : ℝ)*base79 + (21501670777597/17540000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (36242959/10000000000000000000000 : ℝ)*base90 + (36242959/10000000000000000000000 : ℝ)*base92 + (36242959/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40061/50000 : ℝ) ≤ (351347670844706019425335603461/438500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (315430173/100000000000000 : ℝ)*(upper0) + (21714609/12500000000000 : ℝ)*(upper2) + (230892377/50000000000000 : ℝ)*(lower5) + (1666740748127457/50000000000000 : ℝ)*(major0) + (1666740748127457/50000000000000 : ℝ)*(major1) + (1666740748127457/50000000000000 : ℝ)*(major2) + (85586814161/100000000000000 : ℝ)*(sp1) + (11721601739/20000000000000 : ℝ)*(sp3) + (700277003/10000000000000 : ℝ)*(sp4) + (2250824431161613/50000000000000 : ℝ)*(sp8) + (281348339466697/6250000000000 : ℝ)*(sp9) + (2250829509140657/50000000000000 : ℝ)*(sp10) + (1069268533704933/50000000000000 : ℝ)*(sp11) + (1576594029/50000000000000 : ℝ)*(sp12) + (6683111485683/312500000000 : ℝ)*(f.failure) + (2250829509140657/50000000000000 : ℝ)*(f.sum) + (39164004462119/8770000000000000000000000000 : ℝ)*base65 + (55232066365700021/877000000000000000000000000000 : ℝ)*base68 + (16965238190596021/877000000000000000000000000000 : ℝ)*base70 + (14050251677868021/877000000000000000000000000000 : ℝ)*base72 + (80059717056221/8770000000000000000000000000 : ℝ)*base74 + (11363992110455021/877000000000000000000000000000 : ℝ)*base76 + (13126722408665021/877000000000000000000000000000 : ℝ)*base78 + (17704020664792021/877000000000000000000000000000 : ℝ)*base80 + (4917634330209/8770000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5967/31250000000000000000 : ℝ)*base90 + (5967/31250000000000000000 : ℝ)*base92 + (5967/31250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-5279/6250 : ℝ) ≤ (-740730916913044160517953352609/877000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2786169/20000000000000 : ℝ)*(lower0) + (90473/6250000000000 : ℝ)*(upper1) + (106767/100000000000000 : ℝ)*(lower2) + (1161259/50000000000000 : ℝ)*(upper3) + (17870567/100000000000000 : ℝ)*(upper5) + (3370300742630367/100000000000000 : ℝ)*(major0) + (3370300742630367/100000000000000 : ℝ)*(major1) + (3370300742630367/100000000000000 : ℝ)*(major2) + (139408503/50000000000000 : ℝ)*(sp4) + (2040972211/20000000000000 : ℝ)*(sp5) + (4606538105364199/100000000000000 : ℝ)*(sp12) + (4606528179320151/100000000000000 : ℝ)*(sp13) + (2303269192090603/50000000000000 : ℝ)*(sp14) + (1081108534897667/50000000000000 : ℝ)*(sp15) + (1081108534897667/50000000000000 : ℝ)*(f.failure) + (2303269192090603/50000000000000 : ℝ)*(f.sum) + (38222286859991/17540000000000000000000000000 : ℝ)*base66 + (6714124640505251/1754000000000000000000000000000 : ℝ)*base68 + (135517624453251/1754000000000000000000000000000 : ℝ)*base70 + (9196485634247251/1754000000000000000000000000000 : ℝ)*base72 + (328935822827129/17540000000000000000000000000 : ℝ)*base73 + (2662641999663251/1754000000000000000000000000000 : ℝ)*base76 + (1007180042839251/1754000000000000000000000000000 : ℝ)*base78 + (35747282563055251/1754000000000000000000000000000 : ℝ)*base80 + (19679217584929/17540000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (39471817/5000000000000000000000 : ℝ)*base89 + (39471817/5000000000000000000000 : ℝ)*base91 + (39471817/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1371_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15717/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29499/50000 : ℝ) else (40061/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5279/6250 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1371_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1371_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15717/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29499/50000 : ℝ) else (40061/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5279/6250 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1371_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1371_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1371_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15717/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29499/50000 : ℝ) else (40061/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5279/6250 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1371_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
