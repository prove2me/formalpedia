-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1525_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:03.864463+00:00
-- url     : https://prove2.me/submissions/553d44bd-d15c-49af-8c36-2a161fe78043

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
theorem support_rectangle_w1525_s0_0 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1672132863/10000000000 : ℝ)*x 0 + (5902889101/10000000000 : ℝ)*x 1 + (1215209643/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1672132863/10000000000 : ℝ)^4547 ≤ (994272906399/10000000000000 : ℝ)^3523 := by
    have hnat : (1672132863 : ℕ)^4547*10000000000000^3523 ≤ 994272906399^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1672132863 10000000000 994272906399 10000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5902889101/10000000000 : ℝ)^4547 ≤ (1012865900317/2000000000000 : ℝ)^3523 := by
    have hnat : (5902889101 : ℕ)^4547*2000000000000^3523 ≤ 1012865900317^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5902889101 10000000000 1012865900317 2000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1215209643/2500000000 : ℝ)^4547 ≤ (1970698795209/5000000000000 : ℝ)^3523 := by
    have hnat : (1215209643 : ℕ)^4547*5000000000000^3523 ≤ 1970698795209^3523*2500000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215209643 2500000000 1970698795209 5000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1672132863/10000000000 : ℝ), (5902889101/10000000000 : ℝ), (1215209643/2500000000 : ℝ)] ![(994272906399/10000000000000 : ℝ), (1012865900317/2000000000000 : ℝ), (1970698795209/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1672132863/10000000000 : ℝ)|^4547 ≤ (994272906399/10000000000000 : ℝ)^3523
        have hw : |(-1672132863/10000000000 : ℝ)|=(1672132863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5902889101/10000000000 : ℝ)|^4547 ≤ (1012865900317/2000000000000 : ℝ)^3523
        have hw : |(5902889101/10000000000 : ℝ)|=(5902889101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1215209643/2500000000 : ℝ)|^4547 ≤ (1970698795209/5000000000000 : ℝ)^3523
        have hw : |(1215209643/2500000000 : ℝ)|=(1215209643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s0_1 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5475156787/10000000000 : ℝ)*x 0 + (-281906457/1250000000 : ℝ)*x 1 + (4860838467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5475156787/10000000000 : ℝ)^4547 ≤ (22978863788469/50000000000000 : ℝ)^3523 := by
    have hnat : (5475156787 : ℕ)^4547*50000000000000^3523 ≤ 22978863788469^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475156787 10000000000 22978863788469 50000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281906457/1250000000 : ℝ)^4547 ≤ (14628297602731/100000000000000 : ℝ)^3523 := by
    have hnat : (281906457 : ℕ)^4547*100000000000000^3523 ≤ 14628297602731^3523*1250000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281906457 1250000000 14628297602731 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4860838467/10000000000 : ℝ)^4547 ≤ (9853493701331/25000000000000 : ℝ)^3523 := by
    have hnat : (4860838467 : ℕ)^4547*25000000000000^3523 ≤ 9853493701331^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4860838467 10000000000 9853493701331 25000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5475156787/10000000000 : ℝ), (-281906457/1250000000 : ℝ), (4860838467/10000000000 : ℝ)] ![(22978863788469/50000000000000 : ℝ), (14628297602731/100000000000000 : ℝ), (9853493701331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5475156787/10000000000 : ℝ)|^4547 ≤ (22978863788469/50000000000000 : ℝ)^3523
        have hw : |(5475156787/10000000000 : ℝ)|=(5475156787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-281906457/1250000000 : ℝ)|^4547 ≤ (14628297602731/100000000000000 : ℝ)^3523
        have hw : |(-281906457/1250000000 : ℝ)|=(281906457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4860838467/10000000000 : ℝ)|^4547 ≤ (9853493701331/25000000000000 : ℝ)^3523
        have hw : |(4860838467/10000000000 : ℝ)|=(4860838467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s0_2 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2737578467/5000000000 : ℝ)*x 0 + (2430419273/5000000000 : ℝ)*x 1 + (-2255251367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2737578467/5000000000 : ℝ)^4547 ≤ (45957729169483/100000000000000 : ℝ)^3523 := by
    have hnat : (2737578467 : ℕ)^4547*100000000000000^3523 ≤ 45957729169483^3523*5000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737578467 5000000000 45957729169483 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2430419273/5000000000 : ℝ)^4547 ≤ (19706987816041/50000000000000 : ℝ)^3523 := by
    have hnat : (2430419273 : ℕ)^4547*50000000000000^3523 ≤ 19706987816041^3523*5000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2430419273 5000000000 19706987816041 50000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255251367/10000000000 : ℝ)^4547 ≤ (3657073795831/25000000000000 : ℝ)^3523 := by
    have hnat : (2255251367 : ℕ)^4547*25000000000000^3523 ≤ 3657073795831^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255251367 10000000000 3657073795831 25000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2737578467/5000000000 : ℝ), (2430419273/5000000000 : ℝ), (-2255251367/10000000000 : ℝ)] ![(45957729169483/100000000000000 : ℝ), (19706987816041/50000000000000 : ℝ), (3657073795831/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2737578467/5000000000 : ℝ)|^4547 ≤ (45957729169483/100000000000000 : ℝ)^3523
        have hw : |(2737578467/5000000000 : ℝ)|=(2737578467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2430419273/5000000000 : ℝ)|^4547 ≤ (19706987816041/50000000000000 : ℝ)^3523
        have hw : |(2430419273/5000000000 : ℝ)|=(2430419273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2255251367/10000000000 : ℝ)|^4547 ≤ (3657073795831/25000000000000 : ℝ)^3523
        have hw : |(-2255251367/10000000000 : ℝ)|=(2255251367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s0_3 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20708283/50000000 : ℝ)*x 0 + (3091449541/10000000000 : ℝ)*x 1 + (5476050021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20708283/50000000 : ℝ)^4547 ≤ (32055413502419/100000000000000 : ℝ)^3523 := by
    have hnat : (20708283 : ℕ)^4547*100000000000000^3523 ≤ 32055413502419^3523*50000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20708283 50000000 32055413502419 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091449541/10000000000 : ℝ)^4547 ≤ (21977181702317/100000000000000 : ℝ)^3523 := by
    have hnat : (3091449541 : ℕ)^4547*100000000000000^3523 ≤ 21977181702317^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091449541 10000000000 21977181702317 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476050021/10000000000 : ℝ)^4547 ≤ (5745925597459/12500000000000 : ℝ)^3523 := by
    have hnat : (5476050021 : ℕ)^4547*12500000000000^3523 ≤ 5745925597459^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476050021 10000000000 5745925597459 12500000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20708283/50000000 : ℝ), (3091449541/10000000000 : ℝ), (5476050021/10000000000 : ℝ)] ![(32055413502419/100000000000000 : ℝ), (21977181702317/100000000000000 : ℝ), (5745925597459/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20708283/50000000 : ℝ)|^4547 ≤ (32055413502419/100000000000000 : ℝ)^3523
        have hw : |(20708283/50000000 : ℝ)|=(20708283/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091449541/10000000000 : ℝ)|^4547 ≤ (21977181702317/100000000000000 : ℝ)^3523
        have hw : |(3091449541/10000000000 : ℝ)|=(3091449541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476050021/10000000000 : ℝ)|^4547 ≤ (5745925597459/12500000000000 : ℝ)^3523
        have hw : |(5476050021/10000000000 : ℝ)|=(5476050021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s0_4 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-104721473/625000000 : ℝ)*x 0 + (977470297/2000000000 : ℝ)*x 1 + (1175085707/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104721473/625000000 : ℝ)^4547 ≤ (1246114012109/12500000000000 : ℝ)^3523 := by
    have hnat : (104721473 : ℕ)^4547*12500000000000^3523 ≤ 1246114012109^3523*625000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104721473 625000000 1246114012109 12500000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977470297/2000000000 : ℝ)^4547 ≤ (39691660947321/100000000000000 : ℝ)^3523 := by
    have hnat : (977470297 : ℕ)^4547*100000000000000^3523 ≤ 39691660947321^3523*2000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977470297 2000000000 39691660947321 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1175085707/2000000000 : ℝ)^4547 ≤ (12584856733897/25000000000000 : ℝ)^3523 := by
    have hnat : (1175085707 : ℕ)^4547*25000000000000^3523 ≤ 12584856733897^3523*2000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175085707 2000000000 12584856733897 25000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104721473/625000000 : ℝ), (977470297/2000000000 : ℝ), (1175085707/2000000000 : ℝ)] ![(1246114012109/12500000000000 : ℝ), (39691660947321/100000000000000 : ℝ), (12584856733897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104721473/625000000 : ℝ)|^4547 ≤ (1246114012109/12500000000000 : ℝ)^3523
        have hw : |(-104721473/625000000 : ℝ)|=(104721473/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(977470297/2000000000 : ℝ)|^4547 ≤ (39691660947321/100000000000000 : ℝ)^3523
        have hw : |(977470297/2000000000 : ℝ)|=(977470297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1175085707/2000000000 : ℝ)|^4547 ≤ (12584856733897/25000000000000 : ℝ)^3523
        have hw : |(1175085707/2000000000 : ℝ)|=(1175085707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s0_5 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038080609/2000000000 : ℝ)*x 0 + (-620330871/5000000000 : ℝ)*x 1 + (2937714293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038080609/2000000000 : ℝ)^4547 ≤ (42896419136707/100000000000000 : ℝ)^3523 := by
    have hnat : (1038080609 : ℕ)^4547*100000000000000^3523 ≤ 42896419136707^3523*2000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038080609 2000000000 42896419136707 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620330871/5000000000 : ℝ)^4547 ≤ (135283066891/2000000000000 : ℝ)^3523 := by
    have hnat : (620330871 : ℕ)^4547*2000000000000^3523 ≤ 135283066891^3523*5000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620330871 5000000000 135283066891 2000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2937714293/5000000000 : ℝ)^4547 ≤ (1573107109361/3125000000000 : ℝ)^3523 := by
    have hnat : (2937714293 : ℕ)^4547*3125000000000^3523 ≤ 1573107109361^3523*5000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2937714293 5000000000 1573107109361 3125000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038080609/2000000000 : ℝ), (-620330871/5000000000 : ℝ), (2937714293/5000000000 : ℝ)] ![(42896419136707/100000000000000 : ℝ), (135283066891/2000000000000 : ℝ), (1573107109361/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038080609/2000000000 : ℝ)|^4547 ≤ (42896419136707/100000000000000 : ℝ)^3523
        have hw : |(1038080609/2000000000 : ℝ)|=(1038080609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-620330871/5000000000 : ℝ)|^4547 ≤ (135283066891/2000000000000 : ℝ)^3523
        have hw : |(-620330871/5000000000 : ℝ)|=(620330871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2937714293/5000000000 : ℝ)|^4547 ≤ (1573107109361/3125000000000 : ℝ)^3523
        have hw : |(2937714293/5000000000 : ℝ)|=(2937714293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s0_6 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5190403/10000000 : ℝ)*x 0 + (5875428793/10000000000 : ℝ)*x 1 + (-248132297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5190403/10000000 : ℝ)^4547 ≤ (42896418656703/100000000000000 : ℝ)^3523 := by
    have hnat : (5190403 : ℕ)^4547*100000000000000^3523 ≤ 42896418656703^3523*10000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190403 10000000 42896418656703 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5875428793/10000000000 : ℝ)^4547 ≤ (50339429788581/100000000000000 : ℝ)^3523 := by
    have hnat : (5875428793 : ℕ)^4547*100000000000000^3523 ≤ 50339429788581^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5875428793 10000000000 50339429788581 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248132297/2000000000 : ℝ)^4547 ≤ (845518942013/12500000000000 : ℝ)^3523 := by
    have hnat : (248132297 : ℕ)^4547*12500000000000^3523 ≤ 845518942013^3523*2000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248132297 2000000000 845518942013 12500000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5190403/10000000 : ℝ), (5875428793/10000000000 : ℝ), (-248132297/2000000000 : ℝ)] ![(42896418656703/100000000000000 : ℝ), (50339429788581/100000000000000 : ℝ), (845518942013/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5190403/10000000 : ℝ)|^4547 ≤ (42896418656703/100000000000000 : ℝ)^3523
        have hw : |(5190403/10000000 : ℝ)|=(5190403/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5875428793/10000000000 : ℝ)|^4547 ≤ (50339429788581/100000000000000 : ℝ)^3523
        have hw : |(5875428793/10000000000 : ℝ)|=(5875428793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-248132297/2000000000 : ℝ)|^4547 ≤ (845518942013/12500000000000 : ℝ)^3523
        have hw : |(-248132297/2000000000 : ℝ)|=(248132297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s0_7 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4149461397/10000000000 : ℝ)*x 0 + (5415378587/10000000000 : ℝ)*x 1 + (1577144887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4149461397/10000000000 : ℝ)^4547 ≤ (16066700060503/50000000000000 : ℝ)^3523 := by
    have hnat : (4149461397 : ℕ)^4547*50000000000000^3523 ≤ 16066700060503^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149461397 10000000000 16066700060503 50000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415378587/10000000000 : ℝ)^4547 ≤ (362489139909/800000000000 : ℝ)^3523 := by
    have hnat : (5415378587 : ℕ)^4547*800000000000^3523 ≤ 362489139909^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415378587 10000000000 362489139909 800000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577144887/5000000000 : ℝ)^4547 ≤ (4511091474279/20000000000000 : ℝ)^3523 := by
    have hnat : (1577144887 : ℕ)^4547*20000000000000^3523 ≤ 4511091474279^3523*5000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577144887 5000000000 4511091474279 20000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4149461397/10000000000 : ℝ), (5415378587/10000000000 : ℝ), (1577144887/5000000000 : ℝ)] ![(16066700060503/50000000000000 : ℝ), (362489139909/800000000000 : ℝ), (4511091474279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4149461397/10000000000 : ℝ)|^4547 ≤ (16066700060503/50000000000000 : ℝ)^3523
        have hw : |(4149461397/10000000000 : ℝ)|=(4149461397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415378587/10000000000 : ℝ)|^4547 ≤ (362489139909/800000000000 : ℝ)^3523
        have hw : |(5415378587/10000000000 : ℝ)|=(5415378587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577144887/5000000000 : ℝ)|^4547 ≤ (4511091474279/20000000000000 : ℝ)^3523
        have hw : |(1577144887/5000000000 : ℝ)|=(1577144887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1525_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164418641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2993/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25317/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4545/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4545 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4545*1^1024 ≤ 0^1024*1^4545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4545 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4545/1024 : ℝ) ≤ (214122650801838843/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4545 ≤ (214122650801838843/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4545*12500000000000000000^1024 ≤ 214122650801838843^1024*5^4545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 214122650801838843 12500000000000000000 4545 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (214122650801838843/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4545/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4545 := by
      have hnat : (1 : ℕ)^1024*1^4545 ≤ 1^4545*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12714122650801838843/12500000000000000000 : ℝ) ≤ (2509585096461601/2500000000000000 : ℝ) ^ (4545/1024 : ℝ) := by
    have hpowers : (12714122650801838843/12500000000000000000 : ℝ)^1024 ≤ (2509585096461601/2500000000000000 : ℝ)^4545 := by
      have hnat : (12714122650801838843 : ℕ)^1024*2500000000000000^4545 ≤ 2509585096461601^4545*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12714122650801838843 12500000000000000000 2509585096461601 2500000000000000 1024 4545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509585096461601/2500000000000000 : ℝ)) (X := (12714122650801838843/12500000000000000000 : ℝ)) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6464122650801838843/6250000000000000000 : ℝ) ≤ (1259585096461601/1250000000000000 : ℝ) ^ (4545/1024 : ℝ) := by
    have hpowers : (6464122650801838843/6250000000000000000 : ℝ)^1024 ≤ (1259585096461601/1250000000000000 : ℝ)^4545 := by
      have hnat : (6464122650801838843 : ℕ)^1024*1250000000000000^4545 ≤ 1259585096461601^4545*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6464122650801838843 6250000000000000000 1259585096461601 1250000000000000 1024 4545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1259585096461601/1250000000000000 : ℝ)) (X := (6464122650801838843/6250000000000000000 : ℝ)) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9585096461601/1000000000000000 : ℝ)*(0 : ℝ))^(4545/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9585096461601/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(214122650801838843/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9585096461601/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4545/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9585096461601/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2509585096461601/2500000000000000 : ℝ) by norm_num, show 1+(214122650801838843/12500000000000000000 : ℝ)+(0 : ℝ)=(12714122650801838843/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(214122650801838843/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9585096461601/1000000000000000 : ℝ)*(2/5 : ℝ))^(4545/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9585096461601/1000000000000000 : ℝ)*(2/5 : ℝ)=(1259585096461601/1250000000000000 : ℝ) by norm_num, show 1+2*(214122650801838843/12500000000000000000 : ℝ)=(6464122650801838843/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9585096461601/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4545/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9585096461601/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9585096461601/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4545/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9585096461601/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9585096461601/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4545/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9585096461601/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1672132863/10000000000 : ℝ)*X 0 0+(5902889101/10000000000 : ℝ)*X 0 1+(1215209643/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5475156787/10000000000 : ℝ)*X 1 0+(-281906457/1250000000 : ℝ)*X 1 1+(4860838467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2737578467/5000000000 : ℝ)*X 2 0+(2430419273/5000000000 : ℝ)*X 2 1+(-2255251367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((20708283/50000000 : ℝ)*X 0 0+(3091449541/10000000000 : ℝ)*X 0 1+(5476050021/10000000000 : ℝ)*X 0 2+(20708283/50000000 : ℝ)*X 1 0+(3091449541/10000000000 : ℝ)*X 1 1+(5476050021/10000000000 : ℝ)*X 1 2+(20708283/50000000 : ℝ)*X 2 0+(3091449541/10000000000 : ℝ)*X 2 1+(5476050021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-104721473/625000000 : ℝ)*X 0 0+(977470297/2000000000 : ℝ)*X 0 1+(1175085707/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1038080609/2000000000 : ℝ)*X 1 0+(-620330871/5000000000 : ℝ)*X 1 1+(2937714293/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5190403/10000000 : ℝ)*X 2 0+(5875428793/10000000000 : ℝ)*X 2 1+(-248132297/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4149461397/10000000000 : ℝ)*X 0 0+(5415378587/10000000000 : ℝ)*X 0 1+(1577144887/5000000000 : ℝ)*X 0 2+(4149461397/10000000000 : ℝ)*X 1 0+(5415378587/10000000000 : ℝ)*X 1 1+(1577144887/5000000000 : ℝ)*X 1 2+(4149461397/10000000000 : ℝ)*X 2 0+(5415378587/10000000000 : ℝ)*X 2 1+(1577144887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1771999734463667157/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (15733339/50000000000000 : ℝ)*(base1) + (1693782061/100000000000000 : ℝ)*(base19) + (1719547449/100000000000000 : ℝ)*(base23) + (3564671/2000000000000 : ℝ)*(upper3) + (134422909/50000000000000 : ℝ)*(upper5) + (344755405135899/50000000000000 : ℝ)*(major0) + (344755405135899/50000000000000 : ℝ)*(major1) + (344755405135899/50000000000000 : ℝ)*(major2) + (959651925293139/100000000000000 : ℝ)*(sp0) + (479828386357457/50000000000000 : ℝ)*(sp1) + (479828373474763/50000000000000 : ℝ)*(sp2) + (4193602237757/1000000000000 : ℝ)*(sp3) + (3286335257/50000000000000 : ℝ)*(sp4) + (1331268803/50000000000000 : ℝ)*(sp7) + (26210182361249/6250000000000 : ℝ)*(f.failure) + (38386338659879/4000000000000 : ℝ)*(f.sum) + (23824073289299/25000000000000000000000000000 : ℝ)*base65 + (69058052564299/50000000000000000000000000000 : ℝ)*base67 + (62642821985701/50000000000000000000000000000 : ℝ)*base70 + (85445595114299/50000000000000000000000000000 : ℝ)*base71 + (31577530835701/25000000000000000000000000000 : ℝ)*base74 + (15911061014299/50000000000000000000000000000 : ℝ)*base75 + (55739003185701/50000000000000000000000000000 : ℝ)*base78 + (46536159214299/50000000000000000000000000000 : ℝ)*base79 + (39998277435701/25000000000000000000000000000 : ℝ)*base82 + (5857391/625000000000000000000 : ℝ)*base90 + (5857391/625000000000000000000 : ℝ)*base92 + (5857391/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (328696178050283082061269/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1470548677/100000000000000 : ℝ)*(base19) + (148075163/10000000000000 : ℝ)*(base23) + (8560663/50000000000000 : ℝ)*(base32) + (219629911/100000000000000 : ℝ)*(upper3) + (23754209/12500000000000 : ℝ)*(upper5) + (727165841843623/100000000000000 : ℝ)*(major0) + (727165841843623/100000000000000 : ℝ)*(major1) + (727165841843623/100000000000000 : ℝ)*(major2) + (193215923/5000000000000 : ℝ)*(sp1) + (842045969/20000000000000 : ℝ)*(sp2) + (4048266492643/400000000000 : ℝ)*(sp4) + (1012061288293613/100000000000000 : ℝ)*(sp5) + (506030466089637/50000000000000 : ℝ)*(sp6) + (442264824274379/100000000000000 : ℝ)*(sp7) + (88452968279141/20000000000000 : ℝ)*(f.failure) + (4048266492643/400000000000 : ℝ)*(f.sum) + (62000906929577/50000000000000000000000000000 : ℝ)*base66 + (147650043920423/100000000000000000000000000000 : ℝ)*base67 + (1085986493379577/100000000000000000000000000000 : ℝ)*base70 + (513225040579577/100000000000000000000000000000 : ℝ)*base72 + (147658722870423/50000000000000000000000000000 : ℝ)*base73 + (850548572179577/100000000000000000000000000000 : ℝ)*base76 + (14247196920423/100000000000000000000000000000 : ℝ)*base77 + (358967253720423/100000000000000000000000000000 : ℝ)*base79 + (324915850829577/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (11867381/2000000000000000000000 : ℝ)*base89 + (11867381/2000000000000000000000 : ℝ)*base91 + (11867381/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1525_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164418641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2993/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25317/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1525_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1525_s1_0 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1822380797/10000000000 : ℝ)*x 0 + (2781010679/5000000000 : ℝ)*x 1 + (638135249/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1822380797/10000000000 : ℝ)^4547 ≤ (5555274110067/50000000000000 : ℝ)^3523 := by
    have hnat : (1822380797 : ℕ)^4547*50000000000000^3523 ≤ 5555274110067^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822380797 10000000000 5555274110067 50000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2781010679/5000000000 : ℝ)^4547 ≤ (46900948564171/100000000000000 : ℝ)^3523 := by
    have hnat : (2781010679 : ℕ)^4547*100000000000000^3523 ≤ 46900948564171^3523*5000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2781010679 5000000000 46900948564171 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638135249/1250000000 : ℝ)^4547 ≤ (4198850319449/10000000000000 : ℝ)^3523 := by
    have hnat : (638135249 : ℕ)^4547*10000000000000^3523 ≤ 4198850319449^3523*1250000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638135249 1250000000 4198850319449 10000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1822380797/10000000000 : ℝ), (2781010679/5000000000 : ℝ), (638135249/1250000000 : ℝ)] ![(5555274110067/50000000000000 : ℝ), (46900948564171/100000000000000 : ℝ), (4198850319449/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1822380797/10000000000 : ℝ)|^4547 ≤ (5555274110067/50000000000000 : ℝ)^3523
        have hw : |(-1822380797/10000000000 : ℝ)|=(1822380797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2781010679/5000000000 : ℝ)|^4547 ≤ (46900948564171/100000000000000 : ℝ)^3523
        have hw : |(2781010679/5000000000 : ℝ)|=(2781010679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(638135249/1250000000 : ℝ)|^4547 ≤ (4198850319449/10000000000000 : ℝ)^3523
        have hw : |(638135249/1250000000 : ℝ)|=(638135249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s1_1 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692136053/5000000000 : ℝ)*x 0 + (-2062606449/10000000000 : ℝ)*x 1 + (5105083491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692136053/5000000000 : ℝ)^4547 ≤ (5621937571567/12500000000000 : ℝ)^3523 := by
    have hnat : (2692136053 : ℕ)^4547*12500000000000^3523 ≤ 5621937571567^3523*5000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692136053 5000000000 5621937571567 12500000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062606449/10000000000 : ℝ)^4547 ≤ (6517990154543/50000000000000 : ℝ)^3523 := by
    have hnat : (2062606449 : ℕ)^4547*50000000000000^3523 ≤ 6517990154543^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062606449 10000000000 6517990154543 50000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5105083491/10000000000 : ℝ)^4547 ≤ (10497129776777/25000000000000 : ℝ)^3523 := by
    have hnat : (5105083491 : ℕ)^4547*25000000000000^3523 ≤ 10497129776777^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5105083491 10000000000 10497129776777 25000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692136053/5000000000 : ℝ), (-2062606449/10000000000 : ℝ), (5105083491/10000000000 : ℝ)] ![(5621937571567/12500000000000 : ℝ), (6517990154543/50000000000000 : ℝ), (10497129776777/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692136053/5000000000 : ℝ)|^4547 ≤ (5621937571567/12500000000000 : ℝ)^3523
        have hw : |(2692136053/5000000000 : ℝ)|=(2692136053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2062606449/10000000000 : ℝ)|^4547 ≤ (6517990154543/50000000000000 : ℝ)^3523
        have hw : |(-2062606449/10000000000 : ℝ)|=(2062606449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5105083491/10000000000 : ℝ)|^4547 ≤ (10497129776777/25000000000000 : ℝ)^3523
        have hw : |(5105083491/10000000000 : ℝ)|=(5105083491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s1_2 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384273557/10000000000 : ℝ)*x 0 + (5105081681/10000000000 : ℝ)*x 1 + (-1031303443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384273557/10000000000 : ℝ)^4547 ≤ (44975516215849/100000000000000 : ℝ)^3523 := by
    have hnat : (5384273557 : ℕ)^4547*100000000000000^3523 ≤ 44975516215849^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384273557 10000000000 44975516215849 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5105081681/10000000000 : ℝ)^4547 ≤ (41988499893073/100000000000000 : ℝ)^3523 := by
    have hnat : (5105081681 : ℕ)^4547*100000000000000^3523 ≤ 41988499893073^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5105081681 10000000000 41988499893073 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031303443/5000000000 : ℝ)^4547 ≤ (1303598387377/10000000000000 : ℝ)^3523 := by
    have hnat : (1031303443 : ℕ)^4547*10000000000000^3523 ≤ 1303598387377^3523*5000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031303443 5000000000 1303598387377 10000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384273557/10000000000 : ℝ), (5105081681/10000000000 : ℝ), (-1031303443/5000000000 : ℝ)] ![(44975516215849/100000000000000 : ℝ), (41988499893073/100000000000000 : ℝ), (1303598387377/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384273557/10000000000 : ℝ)|^4547 ≤ (44975516215849/100000000000000 : ℝ)^3523
        have hw : |(5384273557/10000000000 : ℝ)|=(5384273557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5105081681/10000000000 : ℝ)|^4547 ≤ (41988499893073/100000000000000 : ℝ)^3523
        have hw : |(5105081681/10000000000 : ℝ)|=(5105081681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1031303443/5000000000 : ℝ)|^4547 ≤ (1303598387377/10000000000000 : ℝ)^3523
        have hw : |(-1031303443/5000000000 : ℝ)|=(1031303443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s1_3 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212243333/500000000 : ℝ)*x 0 + (749789253/2000000000 : ℝ)*x 1 + (1198648233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212243333/500000000 : ℝ)^4547 ≤ (33090132725611/100000000000000 : ℝ)^3523 := by
    have hnat : (212243333 : ℕ)^4547*100000000000000^3523 ≤ 33090132725611^3523*500000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212243333 500000000 33090132725611 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (749789253/2000000000 : ℝ)^4547 ≤ (3523474219567/12500000000000 : ℝ)^3523 := by
    have hnat : (749789253 : ℕ)^4547*12500000000000^3523 ≤ 3523474219567^3523*2000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749789253 2000000000 3523474219567 12500000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198648233/2500000000 : ℝ)^4547 ≤ (38722073505693/100000000000000 : ℝ)^3523 := by
    have hnat : (1198648233 : ℕ)^4547*100000000000000^3523 ≤ 38722073505693^3523*2500000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198648233 2500000000 38722073505693 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212243333/500000000 : ℝ), (749789253/2000000000 : ℝ), (1198648233/2500000000 : ℝ)] ![(33090132725611/100000000000000 : ℝ), (3523474219567/12500000000000 : ℝ), (38722073505693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212243333/500000000 : ℝ)|^4547 ≤ (33090132725611/100000000000000 : ℝ)^3523
        have hw : |(212243333/500000000 : ℝ)|=(212243333/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(749789253/2000000000 : ℝ)|^4547 ≤ (3523474219567/12500000000000 : ℝ)^3523
        have hw : |(749789253/2000000000 : ℝ)|=(749789253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198648233/2500000000 : ℝ)|^4547 ≤ (38722073505693/100000000000000 : ℝ)^3523
        have hw : |(1198648233/2500000000 : ℝ)|=(1198648233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s1_4 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1822659503/10000000000 : ℝ)*x 0 + (5110099841/10000000000 : ℝ)*x 1 + (5556924103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1822659503/10000000000 : ℝ)^4547 ≤ (2778185337867/25000000000000 : ℝ)^3523 := by
    have hnat : (1822659503 : ℕ)^4547*25000000000000^3523 ≤ 2778185337867^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822659503 10000000000 2778185337867 25000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5110099841/10000000000 : ℝ)^4547 ≤ (525522221499/1250000000000 : ℝ)^3523 := by
    have hnat : (5110099841 : ℕ)^4547*1250000000000^3523 ≤ 525522221499^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5110099841 10000000000 525522221499 1250000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5556924103/10000000000 : ℝ)^4547 ≤ (46845480911547/100000000000000 : ℝ)^3523 := by
    have hnat : (5556924103 : ℕ)^4547*100000000000000^3523 ≤ 46845480911547^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5556924103 10000000000 46845480911547 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1822659503/10000000000 : ℝ), (5110099841/10000000000 : ℝ), (5556924103/10000000000 : ℝ)] ![(2778185337867/25000000000000 : ℝ), (525522221499/1250000000000 : ℝ), (46845480911547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1822659503/10000000000 : ℝ)|^4547 ≤ (2778185337867/25000000000000 : ℝ)^3523
        have hw : |(-1822659503/10000000000 : ℝ)|=(1822659503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5110099841/10000000000 : ℝ)|^4547 ≤ (525522221499/1250000000000 : ℝ)^3523
        have hw : |(5110099841/10000000000 : ℝ)|=(5110099841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5556924103/10000000000 : ℝ)|^4547 ≤ (46845480911547/100000000000000 : ℝ)^3523
        have hw : |(5556924103/10000000000 : ℝ)|=(5556924103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s1_5 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263734493/10000000000 : ℝ)*x 0 + (-402690933/2500000000 : ℝ)*x 1 + (694615531/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263734493/10000000000 : ℝ)^4547 ≤ (8736045677303/20000000000000 : ℝ)^3523 := by
    have hnat : (5263734493 : ℕ)^4547*20000000000000^3523 ≤ 8736045677303^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263734493 10000000000 8736045677303 20000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402690933/2500000000 : ℝ)^4547 ≤ (9474289103503/100000000000000 : ℝ)^3523 := by
    have hnat : (402690933 : ℕ)^4547*100000000000000^3523 ≤ 9474289103503^3523*2500000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402690933 2500000000 9474289103503 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694615531/1250000000 : ℝ)^4547 ≤ (5855685311151/12500000000000 : ℝ)^3523 := by
    have hnat : (694615531 : ℕ)^4547*12500000000000^3523 ≤ 5855685311151^3523*1250000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694615531 1250000000 5855685311151 12500000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263734493/10000000000 : ℝ), (-402690933/2500000000 : ℝ), (694615531/1250000000 : ℝ)] ![(8736045677303/20000000000000 : ℝ), (9474289103503/100000000000000 : ℝ), (5855685311151/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263734493/10000000000 : ℝ)|^4547 ≤ (8736045677303/20000000000000 : ℝ)^3523
        have hw : |(5263734493/10000000000 : ℝ)|=(5263734493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-402690933/2500000000 : ℝ)|^4547 ≤ (9474289103503/100000000000000 : ℝ)^3523
        have hw : |(-402690933/2500000000 : ℝ)|=(402690933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(694615531/1250000000 : ℝ)|^4547 ≤ (5855685311151/12500000000000 : ℝ)^3523
        have hw : |(694615531/1250000000 : ℝ)|=(694615531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s1_6 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263734203/10000000000 : ℝ)*x 0 + (1111384883/2000000000 : ℝ)*x 1 + (-805381951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263734203/10000000000 : ℝ)^4547 ≤ (10920056320129/25000000000000 : ℝ)^3523 := by
    have hnat : (5263734203 : ℕ)^4547*25000000000000^3523 ≤ 10920056320129^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263734203 10000000000 10920056320129 25000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111384883/2000000000 : ℝ)^4547 ≤ (23422742153119/50000000000000 : ℝ)^3523 := by
    have hnat : (1111384883 : ℕ)^4547*50000000000000^3523 ≤ 23422742153119^3523*2000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111384883 2000000000 23422742153119 50000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805381951/5000000000 : ℝ)^4547 ≤ (1184286299257/12500000000000 : ℝ)^3523 := by
    have hnat : (805381951 : ℕ)^4547*12500000000000^3523 ≤ 1184286299257^3523*5000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805381951 5000000000 1184286299257 12500000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263734203/10000000000 : ℝ), (1111384883/2000000000 : ℝ), (-805381951/5000000000 : ℝ)] ![(10920056320129/25000000000000 : ℝ), (23422742153119/50000000000000 : ℝ), (1184286299257/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263734203/10000000000 : ℝ)|^4547 ≤ (10920056320129/25000000000000 : ℝ)^3523
        have hw : |(5263734203/10000000000 : ℝ)|=(5263734203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1111384883/2000000000 : ℝ)|^4547 ≤ (23422742153119/50000000000000 : ℝ)^3523
        have hw : |(1111384883/2000000000 : ℝ)|=(1111384883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-805381951/5000000000 : ℝ)|^4547 ≤ (1184286299257/12500000000000 : ℝ)^3523
        have hw : |(-805381951/5000000000 : ℝ)|=(805381951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s1_7 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849100961/2000000000 : ℝ)*x 0 + (4783110357/10000000000 : ℝ)*x 1 + (1880304401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849100961/2000000000 : ℝ)^4547 ≤ (16548276662893/50000000000000 : ℝ)^3523 := by
    have hnat : (849100961 : ℕ)^4547*50000000000000^3523 ≤ 16548276662893^3523*2000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849100961 2000000000 16548276662893 50000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4783110357/10000000000 : ℝ)^4547 ≤ (7720485004539/20000000000000 : ℝ)^3523 := by
    have hnat : (4783110357 : ℕ)^4547*20000000000000^3523 ≤ 7720485004539^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4783110357 10000000000 7720485004539 20000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1880304401/5000000000 : ℝ)^4547 ≤ (5660204327217/20000000000000 : ℝ)^3523 := by
    have hnat : (1880304401 : ℕ)^4547*20000000000000^3523 ≤ 5660204327217^3523*5000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880304401 5000000000 5660204327217 20000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849100961/2000000000 : ℝ), (4783110357/10000000000 : ℝ), (1880304401/5000000000 : ℝ)] ![(16548276662893/50000000000000 : ℝ), (7720485004539/20000000000000 : ℝ), (5660204327217/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849100961/2000000000 : ℝ)|^4547 ≤ (16548276662893/50000000000000 : ℝ)^3523
        have hw : |(849100961/2000000000 : ℝ)|=(849100961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4783110357/10000000000 : ℝ)|^4547 ≤ (7720485004539/20000000000000 : ℝ)^3523
        have hw : |(4783110357/10000000000 : ℝ)|=(4783110357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1880304401/5000000000 : ℝ)|^4547 ≤ (5660204327217/20000000000000 : ℝ)^3523
        have hw : |(1880304401/5000000000 : ℝ)|=(1880304401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1525_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164418641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8527/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3639/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25317/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2993/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25317/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2993/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25317/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2993/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25317/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2993/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25317/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2993/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25317/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2993/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2993/100000 : ℝ) ^ (4545/1024 : ℝ) ≤ (1722802046337/10000000000000000000 : ℝ) := by
    have hpowers : (2993/100000 : ℝ)^4545 ≤ (1722802046337/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2993 : ℕ)^4545*10000000000000000000^1024 ≤ 1722802046337^1024*100000^4545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2993 100000 1722802046337 10000000000000000000 4545 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2993/100000 : ℝ)) (X := (1722802046337/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25317/100000 : ℝ) ^ (4545/1024 : ℝ) ≤ (112468064483085971/50000000000000000000 : ℝ) := by
    have hpowers : (25317/100000 : ℝ)^4545 ≤ (112468064483085971/50000000000000000000 : ℝ)^1024 := by
      have hnat : (25317 : ℕ)^4545*50000000000000000000^1024 ≤ 112468064483085971^1024*100000^4545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25317 100000 112468064483085971 50000000000000000000 4545 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25317/100000 : ℝ)) (X := (112468064483085971/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000001722802046337/5000000000000000000 : ℝ) ≤ (10000000776303217/10000000000000000 : ℝ) ^ (4545/1024 : ℝ) := by
    have hpowers : (5000001722802046337/5000000000000000000 : ℝ)^1024 ≤ (10000000776303217/10000000000000000 : ℝ)^4545 := by
      have hnat : (5000001722802046337 : ℕ)^1024*10000000000000000^4545 ≤ 10000000776303217^4545*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000001722802046337 5000000000000000000 10000000776303217 10000000000000000 1024 4545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000776303217/10000000000000000 : ℝ)) (X := (5000001722802046337/5000000000000000000 : ℝ)) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6264059584811664707/6250000000000000000 : ℝ) ≤ (10005063845674457/10000000000000000 : ℝ) ^ (4545/1024 : ℝ) := by
    have hpowers : (6264059584811664707/6250000000000000000 : ℝ)^1024 ≤ (10005063845674457/10000000000000000 : ℝ)^4545 := by
      have hnat : (6264059584811664707 : ℕ)^1024*10000000000000000^4545 ≤ 10005063845674457^4545*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6264059584811664707 6250000000000000000 10005063845674457 10000000000000000 1024 4545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005063845674457/10000000000000000 : ℝ)) (X := (6264059584811664707/6250000000000000000 : ℝ)) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25112468064483085971/25000000000000000000 : ℝ) ≤ (10010126915045697/10000000000000000 : ℝ) ^ (4545/1024 : ℝ) := by
    have hpowers : (25112468064483085971/25000000000000000000 : ℝ)^1024 ≤ (10010126915045697/10000000000000000 : ℝ)^4545 := by
      have hnat : (25112468064483085971 : ℕ)^1024*10000000000000000^4545 ≤ 10010126915045697^4545*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25112468064483085971 25000000000000000000 10010126915045697 10000000000000000 1024 4545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010126915045697/10000000000000000 : ℝ)) (X := (25112468064483085971/25000000000000000000 : ℝ)) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1722802046337/10000000000000000000 : ℝ) ≤ ((55802427449234193417/55810000000000000000 : ℝ)+2*(126576734281/55810000000000 : ℝ)*(2993/100000 : ℝ))^(4545/1024 : ℝ) := by
    rw [show (55802427449234193417/55810000000000000000 : ℝ)+2*(126576734281/55810000000000 : ℝ)*(2993/100000 : ℝ)=(10000000776303217/10000000000000000 : ℝ) by norm_num, show 1+2*(1722802046337/10000000000000000000 : ℝ)=(5000001722802046337/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(112468064483085971/50000000000000000000 : ℝ)+(1722802046337/10000000000000000000 : ℝ) ≤ ((55802427449234193417/55810000000000000000 : ℝ)+(126576734281/55810000000000 : ℝ)*((25317/100000 : ℝ)+(2993/100000 : ℝ)))^(4545/1024 : ℝ) := by
    rw [show (55802427449234193417/55810000000000000000 : ℝ)+(126576734281/55810000000000 : ℝ)*((25317/100000 : ℝ)+(2993/100000 : ℝ))=(10005063845674457/10000000000000000 : ℝ) by norm_num, show 1+(112468064483085971/50000000000000000000 : ℝ)+(1722802046337/10000000000000000000 : ℝ)=(6264059584811664707/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(112468064483085971/50000000000000000000 : ℝ) ≤ ((55802427449234193417/55810000000000000000 : ℝ)+2*(126576734281/55810000000000 : ℝ)*(25317/100000 : ℝ))^(4545/1024 : ℝ) := by
    rw [show (55802427449234193417/55810000000000000000 : ℝ)+2*(126576734281/55810000000000 : ℝ)*(25317/100000 : ℝ)=(10010126915045697/10000000000000000 : ℝ) by norm_num, show 1+2*(112468064483085971/50000000000000000000 : ℝ)=(25112468064483085971/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55802427449234193417/55810000000000000000 : ℝ)*(X 1 0+X 2 0)+(126576734281/55810000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4545/1024 : ℝ)) (lo := (2993/100000 : ℝ)) (hi := (25317/100000 : ℝ)) (c := (55802427449234193417/55810000000000000000 : ℝ)) (alpha := (126576734281/55810000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55802427449234193417/55810000000000000000 : ℝ)*(X 0 1+X 2 1)+(126576734281/55810000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4545/1024 : ℝ)) (lo := (2993/100000 : ℝ)) (hi := (25317/100000 : ℝ)) (c := (55802427449234193417/55810000000000000000 : ℝ)) (alpha := (126576734281/55810000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55802427449234193417/55810000000000000000 : ℝ)*(X 0 2+X 1 2)+(126576734281/55810000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4545/1024 : ℝ)) (lo := (2993/100000 : ℝ)) (hi := (25317/100000 : ℝ)) (c := (55802427449234193417/55810000000000000000 : ℝ)) (alpha := (126576734281/55810000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1822380797/10000000000 : ℝ)*X 0 0+(2781010679/5000000000 : ℝ)*X 0 1+(638135249/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2692136053/5000000000 : ℝ)*X 1 0+(-2062606449/10000000000 : ℝ)*X 1 1+(5105083491/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5384273557/10000000000 : ℝ)*X 2 0+(5105081681/10000000000 : ℝ)*X 2 1+(-1031303443/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((212243333/500000000 : ℝ)*X 0 0+(749789253/2000000000 : ℝ)*X 0 1+(1198648233/2500000000 : ℝ)*X 0 2+(212243333/500000000 : ℝ)*X 1 0+(749789253/2000000000 : ℝ)*X 1 1+(1198648233/2500000000 : ℝ)*X 1 2+(212243333/500000000 : ℝ)*X 2 0+(749789253/2000000000 : ℝ)*X 2 1+(1198648233/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1822659503/10000000000 : ℝ)*X 0 0+(5110099841/10000000000 : ℝ)*X 0 1+(5556924103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5263734493/10000000000 : ℝ)*X 1 0+(-402690933/2500000000 : ℝ)*X 1 1+(694615531/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5263734203/10000000000 : ℝ)*X 2 0+(1111384883/2000000000 : ℝ)*X 2 1+(-805381951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((849100961/2000000000 : ℝ)*X 0 0+(4783110357/10000000000 : ℝ)*X 0 1+(1880304401/5000000000 : ℝ)*X 0 2+(849100961/2000000000 : ℝ)*X 1 0+(4783110357/10000000000 : ℝ)*X 1 1+(1880304401/5000000000 : ℝ)*X 1 2+(849100961/2000000000 : ℝ)*X 2 0+(4783110357/10000000000 : ℝ)*X 2 1+(1880304401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2756904181149074075782013283/279050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20187529/25000000000000 : ℝ)*(base1) + (27448547/12500000000000 : ℝ)*(base19) + (809359953/100000000000000 : ℝ)*(base23) + (230937/160000000000 : ℝ)*(upper3) + (176591/500000000000 : ℝ)*(upper5) + (157241770915033/10000000000000 : ℝ)*(major0) + (157241770915033/10000000000000 : ℝ)*(major1) + (157241770915033/10000000000000 : ℝ)*(major2) + (68389987980431/3125000000000 : ℝ)*(sp0) + (1094242423764537/50000000000000 : ℝ)*(sp1) + (2188484257757497/100000000000000 : ℝ)*(sp2) + (478173646018003/50000000000000 : ℝ)*(sp3) + (2766246887/50000000000000 : ℝ)*(sp4) + (662269217/25000000000000 : ℝ)*(sp7) + (956350021862989/100000000000000 : ℝ)*(f.failure) + (43769701342349/2000000000000 : ℝ)*(f.sum) + (197626870993/2790500000000000000000000000 : ℝ)*base65 + (1303047858113662239/558100000000000000000000000000000 : ℝ)*base68 + (614856553444537761/558100000000000000000000000000000 : ℝ)*base69 + (3494077470461537761/558100000000000000000000000000000 : ℝ)*base71 + (734157046749/279050000000000000000000000 : ℝ)*base74 + (1335105192434262239/558100000000000000000000000000000 : ℝ)*base76 + (442423386866962239/558100000000000000000000000000000 : ℝ)*base78 + (726403862158362239/558100000000000000000000000000000 : ℝ)*base80 + (3847117467097/2790500000000000000000000000 : ℝ)*base81 + (60422051/10000000000000000000000 : ℝ)*base90 + (60422051/10000000000000000000000 : ℝ)*base92 + (60422051/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (496024852327430752080371427/43601562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1072155237/50000000000000 : ℝ)*(base19) + (69618677/3125000000000 : ℝ)*(base23) + (146739421/50000000000000 : ℝ)*(upper3) + (93211281/100000000000000 : ℝ)*(lower4) + (199575323/100000000000000 : ℝ)*(upper5) + (100500249724979/6250000000000 : ℝ)*(major0) + (100500249724979/6250000000000 : ℝ)*(major1) + (100500249724979/6250000000000 : ℝ)*(major2) + (15308617817/100000000000000 : ℝ)*(sp1) + (16605607633/100000000000000 : ℝ)*(sp2) + (1119006942311741/50000000000000 : ℝ)*(sp4) + (2237996431695191/100000000000000 : ℝ)*(sp5) + (1118997525609093/50000000000000 : ℝ)*(sp6) + (977993727365539/100000000000000 : ℝ)*(sp7) + (977993727365539/100000000000000 : ℝ)*(f.failure) + (1119006942311741/50000000000000 : ℝ)*(f.sum) + (22689903107701/5581000000000000000000000000 : ℝ)*base66 + (1003618276139049257/348812500000000000000000000000000 : ℝ)*base68 + (298426533688513243/348812500000000000000000000000000 : ℝ)*base69 + (60114254849986757/348812500000000000000000000000000 : ℝ)*base72 + (407141720217/111620000000000000000000000 : ℝ)*base74 + (400057894617049257/348812500000000000000000000000000 : ℝ)*base76 + (34455807568361757/348812500000000000000000000000000 : ℝ)*base78 + (2630624847606611757/348812500000000000000000000000000 : ℝ)*base80 + (656908396797/279050000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (32612499/10000000000000000000000 : ℝ)*base89 + (32612499/10000000000000000000000 : ℝ)*base91 + (32612499/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1525_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164418641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3639/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1525_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1525_s2_0 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1845442731/10000000000 : ℝ)*x 0 + (5453878773/10000000000 : ℝ)*x 1 + (5198265981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1845442731/10000000000 : ℝ)^4547 ≤ (141154384857/1250000000000 : ℝ)^3523 := by
    have hnat : (1845442731 : ℕ)^4547*1250000000000^3523 ≤ 141154384857^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845442731 10000000000 141154384857 1250000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453878773/10000000000 : ℝ)^4547 ≤ (11431834900889/25000000000000 : ℝ)^3523 := by
    have hnat : (5453878773 : ℕ)^4547*25000000000000^3523 ≤ 11431834900889^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453878773 10000000000 11431834900889 25000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5198265981/10000000000 : ℝ)^4547 ≤ (42980309597329/100000000000000 : ℝ)^3523 := by
    have hnat : (5198265981 : ℕ)^4547*100000000000000^3523 ≤ 42980309597329^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198265981 10000000000 42980309597329 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1845442731/10000000000 : ℝ), (5453878773/10000000000 : ℝ), (5198265981/10000000000 : ℝ)] ![(141154384857/1250000000000 : ℝ), (11431834900889/25000000000000 : ℝ), (42980309597329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1845442731/10000000000 : ℝ)|^4547 ≤ (141154384857/1250000000000 : ℝ)^3523
        have hw : |(-1845442731/10000000000 : ℝ)|=(1845442731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453878773/10000000000 : ℝ)|^4547 ≤ (11431834900889/25000000000000 : ℝ)^3523
        have hw : |(5453878773/10000000000 : ℝ)|=(5453878773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5198265981/10000000000 : ℝ)|^4547 ≤ (42980309597329/100000000000000 : ℝ)^3523
        have hw : |(5198265981/10000000000 : ℝ)|=(5198265981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s2_1 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356687431/10000000000 : ℝ)*x 0 + (-1976929669/10000000000 : ℝ)*x 1 + (5198265873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356687431/10000000000 : ℝ)^4547 ≤ (22339165165257/50000000000000 : ℝ)^3523 := by
    have hnat : (5356687431 : ℕ)^4547*50000000000000^3523 ≤ 22339165165257^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356687431 10000000000 22339165165257 50000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1976929669/10000000000 : ℝ)^4547 ≤ (12341361216309/100000000000000 : ℝ)^3523 := by
    have hnat : (1976929669 : ℕ)^4547*100000000000000^3523 ≤ 12341361216309^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976929669 10000000000 12341361216309 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5198265873/10000000000 : ℝ)^4547 ≤ (42980308444813/100000000000000 : ℝ)^3523 := by
    have hnat : (5198265873 : ℕ)^4547*100000000000000^3523 ≤ 42980308444813^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198265873 10000000000 42980308444813 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356687431/10000000000 : ℝ), (-1976929669/10000000000 : ℝ), (5198265873/10000000000 : ℝ)] ![(22339165165257/50000000000000 : ℝ), (12341361216309/100000000000000 : ℝ), (42980308444813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356687431/10000000000 : ℝ)|^4547 ≤ (22339165165257/50000000000000 : ℝ)^3523
        have hw : |(5356687431/10000000000 : ℝ)|=(5356687431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1976929669/10000000000 : ℝ)|^4547 ≤ (12341361216309/100000000000000 : ℝ)^3523
        have hw : |(-1976929669/10000000000 : ℝ)|=(1976929669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5198265873/10000000000 : ℝ)|^4547 ≤ (42980308444813/100000000000000 : ℝ)^3523
        have hw : |(5198265873/10000000000 : ℝ)|=(5198265873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s2_2 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535668737/1000000000 : ℝ)*x 0 + (1039653189/2000000000 : ℝ)*x 1 + (-395385931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535668737/1000000000 : ℝ)^4547 ≤ (44678329673851/100000000000000 : ℝ)^3523 := by
    have hnat : (535668737 : ℕ)^4547*100000000000000^3523 ≤ 44678329673851^3523*1000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535668737 1000000000 44678329673851 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039653189/2000000000 : ℝ)^4547 ≤ (42980309213157/100000000000000 : ℝ)^3523 := by
    have hnat : (1039653189 : ℕ)^4547*100000000000000^3523 ≤ 42980309213157^3523*2000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039653189 2000000000 42980309213157 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (395385931/2000000000 : ℝ)^4547 ≤ (12341361103509/100000000000000 : ℝ)^3523 := by
    have hnat : (395385931 : ℕ)^4547*100000000000000^3523 ≤ 12341361103509^3523*2000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395385931 2000000000 12341361103509 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535668737/1000000000 : ℝ), (1039653189/2000000000 : ℝ), (-395385931/2000000000 : ℝ)] ![(44678329673851/100000000000000 : ℝ), (42980309213157/100000000000000 : ℝ), (12341361103509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535668737/1000000000 : ℝ)|^4547 ≤ (44678329673851/100000000000000 : ℝ)^3523
        have hw : |(535668737/1000000000 : ℝ)|=(535668737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039653189/2000000000 : ℝ)|^4547 ≤ (42980309213157/100000000000000 : ℝ)^3523
        have hw : |(1039653189/2000000000 : ℝ)|=(1039653189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-395385931/2000000000 : ℝ)|^4547 ≤ (12341361103509/100000000000000 : ℝ)^3523
        have hw : |(-395385931/2000000000 : ℝ)|=(395385931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s2_3 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261461669/10000000000 : ℝ)*x 0 + (3977414883/10000000000 : ℝ)*x 1 + (285147037/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261461669/10000000000 : ℝ)^4547 ≤ (6651438409243/20000000000000 : ℝ)^3523 := by
    have hnat : (4261461669 : ℕ)^4547*20000000000000^3523 ≤ 6651438409243^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261461669 10000000000 6651438409243 20000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3977414883/10000000000 : ℝ)^4547 ≤ (3042428233657/10000000000000 : ℝ)^3523 := by
    have hnat : (3977414883 : ℕ)^4547*10000000000000^3523 ≤ 3042428233657^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3977414883 10000000000 3042428233657 10000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285147037/625000000 : ℝ)^4547 ≤ (18159262799779/50000000000000 : ℝ)^3523 := by
    have hnat : (285147037 : ℕ)^4547*50000000000000^3523 ≤ 18159262799779^3523*625000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285147037 625000000 18159262799779 50000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261461669/10000000000 : ℝ), (3977414883/10000000000 : ℝ), (285147037/625000000 : ℝ)] ![(6651438409243/20000000000000 : ℝ), (3042428233657/10000000000000 : ℝ), (18159262799779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261461669/10000000000 : ℝ)|^4547 ≤ (6651438409243/20000000000000 : ℝ)^3523
        have hw : |(4261461669/10000000000 : ℝ)|=(4261461669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3977414883/10000000000 : ℝ)|^4547 ≤ (3042428233657/10000000000000 : ℝ)^3523
        have hw : |(3977414883/10000000000 : ℝ)|=(3977414883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(285147037/625000000 : ℝ)|^4547 ≤ (18159262799779/50000000000000 : ℝ)^3523
        have hw : |(285147037/625000000 : ℝ)|=(285147037/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s2_4 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1845490747/10000000000 : ℝ)*x 0 + (2599922721/5000000000 : ℝ)*x 1 + (85191969/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1845490747/10000000000 : ℝ)^4547 ≤ (11292730001999/100000000000000 : ℝ)^3523 := by
    have hnat : (1845490747 : ℕ)^4547*100000000000000^3523 ≤ 11292730001999^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845490747 10000000000 11292730001999 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2599922721/5000000000 : ℝ)^4547 ≤ (42997165477517/100000000000000 : ℝ)^3523 := by
    have hnat : (2599922721 : ℕ)^4547*100000000000000^3523 ≤ 42997165477517^3523*5000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599922721 5000000000 42997165477517 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85191969/156250000 : ℝ)^4547 ≤ (11427526125429/25000000000000 : ℝ)^3523 := by
    have hnat : (85191969 : ℕ)^4547*25000000000000^3523 ≤ 11427526125429^3523*156250000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85191969 156250000 11427526125429 25000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1845490747/10000000000 : ℝ), (2599922721/5000000000 : ℝ), (85191969/156250000 : ℝ)] ![(11292730001999/100000000000000 : ℝ), (42997165477517/100000000000000 : ℝ), (11427526125429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1845490747/10000000000 : ℝ)|^4547 ≤ (11292730001999/100000000000000 : ℝ)^3523
        have hw : |(-1845490747/10000000000 : ℝ)|=(1845490747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2599922721/5000000000 : ℝ)|^4547 ≤ (42997165477517/100000000000000 : ℝ)^3523
        have hw : |(2599922721/5000000000 : ℝ)|=(2599922721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85191969/156250000 : ℝ)|^4547 ≤ (11427526125429/25000000000000 : ℝ)^3523
        have hw : |(85191969/156250000 : ℝ)|=(85191969/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s2_5 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644720997/5000000000 : ℝ)*x 0 + (-1722910317/10000000000 : ℝ)*x 1 + (5452286963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644720997/5000000000 : ℝ)^4547 ≤ (70329215443/160000000000 : ℝ)^3523 := by
    have hnat : (2644720997 : ℕ)^4547*160000000000^3523 ≤ 70329215443^3523*5000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644720997 5000000000 70329215443 160000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1722910317/10000000000 : ℝ)^4547 ≤ (5167062790777/50000000000000 : ℝ)^3523 := by
    have hnat : (1722910317 : ℕ)^4547*50000000000000^3523 ≤ 5167062790777^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722910317 10000000000 5167062790777 50000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452286963/10000000000 : ℝ)^4547 ≤ (5713764343587/12500000000000 : ℝ)^3523 := by
    have hnat : (5452286963 : ℕ)^4547*12500000000000^3523 ≤ 5713764343587^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452286963 10000000000 5713764343587 12500000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644720997/5000000000 : ℝ), (-1722910317/10000000000 : ℝ), (5452286963/10000000000 : ℝ)] ![(70329215443/160000000000 : ℝ), (5167062790777/50000000000000 : ℝ), (5713764343587/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644720997/5000000000 : ℝ)|^4547 ≤ (70329215443/160000000000 : ℝ)^3523
        have hw : |(2644720997/5000000000 : ℝ)|=(2644720997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1722910317/10000000000 : ℝ)|^4547 ≤ (5167062790777/50000000000000 : ℝ)^3523
        have hw : |(-1722910317/10000000000 : ℝ)|=(1722910317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452286963/10000000000 : ℝ)|^4547 ≤ (5713764343587/12500000000000 : ℝ)^3523
        have hw : |(5452286963/10000000000 : ℝ)|=(5452286963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s2_6 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330590177/625000000 : ℝ)*x 0 + (5452286791/10000000000 : ℝ)*x 1 + (-430727349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330590177/625000000 : ℝ)^4547 ≤ (43955768639859/100000000000000 : ℝ)^3523 := by
    have hnat : (330590177 : ℕ)^4547*100000000000000^3523 ≤ 43955768639859^3523*625000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330590177 625000000 43955768639859 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452286791/10000000000 : ℝ)^4547 ≤ (5713764110947/12500000000000 : ℝ)^3523 := by
    have hnat : (5452286791 : ℕ)^4547*12500000000000^3523 ≤ 5713764110947^3523*10000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452286791 10000000000 5713764110947 12500000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430727349/2500000000 : ℝ)^4547 ≤ (5167059225831/50000000000000 : ℝ)^3523 := by
    have hnat : (430727349 : ℕ)^4547*50000000000000^3523 ≤ 5167059225831^3523*2500000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430727349 2500000000 5167059225831 50000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330590177/625000000 : ℝ), (5452286791/10000000000 : ℝ), (-430727349/2500000000 : ℝ)] ![(43955768639859/100000000000000 : ℝ), (5713764110947/12500000000000 : ℝ), (5167059225831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330590177/625000000 : ℝ)|^4547 ≤ (43955768639859/100000000000000 : ℝ)^3523
        have hw : |(330590177/625000000 : ℝ)|=(330590177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452286791/10000000000 : ℝ)|^4547 ≤ (5713764110947/12500000000000 : ℝ)^3523
        have hw : |(5452286791/10000000000 : ℝ)|=(5452286791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-430727349/2500000000 : ℝ)|^4547 ≤ (5167059225831/50000000000000 : ℝ)^3523
        have hw : |(-430727349/2500000000 : ℝ)|=(430727349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1525_s2_7 (p : ℝ) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1065393467/2500000000 : ℝ)*x 0 + (142460637/312500000 : ℝ)*x 1 + (398105867/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065393467/2500000000 : ℝ)^4547 ≤ (33258322180241/100000000000000 : ℝ)^3523 := by
    have hnat : (1065393467 : ℕ)^4547*100000000000000^3523 ≤ 33258322180241^3523*2500000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065393467 2500000000 33258322180241 100000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142460637/312500000 : ℝ)^4547 ≤ (18140708505303/50000000000000 : ℝ)^3523 := by
    have hnat : (142460637 : ℕ)^4547*50000000000000^3523 ≤ 18140708505303^3523*312500000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142460637 312500000 18140708505303 50000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398105867/1000000000 : ℝ)^4547 ≤ (7615065198663/25000000000000 : ℝ)^3523 := by
    have hnat : (398105867 : ℕ)^4547*25000000000000^3523 ≤ 7615065198663^3523*1000000000^4547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398105867 1000000000 7615065198663 25000000000000 4547 3523 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4547/1024 : ℝ)) 4547 3523 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065393467/2500000000 : ℝ), (142460637/312500000 : ℝ), (398105867/1000000000 : ℝ)] ![(33258322180241/100000000000000 : ℝ), (18140708505303/50000000000000 : ℝ), (7615065198663/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065393467/2500000000 : ℝ)|^4547 ≤ (33258322180241/100000000000000 : ℝ)^3523
        have hw : |(1065393467/2500000000 : ℝ)|=(1065393467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142460637/312500000 : ℝ)|^4547 ≤ (18140708505303/50000000000000 : ℝ)^3523
        have hw : |(142460637/312500000 : ℝ)|=(142460637/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398105867/1000000000 : ℝ)|^4547 ≤ (7615065198663/25000000000000 : ℝ)^3523
        have hw : |(398105867/1000000000 : ℝ)|=(398105867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1525_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164418641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3639/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10537/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15949/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3639/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3639/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3639/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3639/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3639/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3639/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (8527/100000 : ℝ) ^ (4545/1024 : ℝ) ≤ (1796239625124101/100000000000000000000 : ℝ) := by
    have hpowers : (8527/100000 : ℝ)^4545 ≤ (1796239625124101/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8527 : ℕ)^4545*100000000000000000000^1024 ≤ 1796239625124101^1024*100000^4545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8527 100000 1796239625124101 100000000000000000000 4545 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8527/100000 : ℝ)) (X := (1796239625124101/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3639/20000 : ℝ) ^ (4545/1024 : ℝ) ≤ (10383518918261843/20000000000000000000 : ℝ) := by
    have hpowers : (3639/20000 : ℝ)^4545 ≤ (10383518918261843/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3639 : ℕ)^4545*20000000000000000000^1024 ≤ 10383518918261843^1024*20000^4545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3639 20000 10383518918261843 20000000000000000000 4545 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3639/20000 : ℝ)) (X := (10383518918261843/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001796239625124101/50000000000000000000 : ℝ) ≤ (5000040469170107/5000000000000000 : ℝ) ^ (4545/1024 : ℝ) := by
    have hpowers : (50001796239625124101/50000000000000000000 : ℝ)^1024 ≤ (5000040469170107/5000000000000000 : ℝ)^4545 := by
      have hnat : (50001796239625124101 : ℕ)^1024*5000000000000000^4545 ≤ 5000040469170107^4545*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001796239625124101 50000000000000000000 5000040469170107 5000000000000000 1024 4545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000040469170107/5000000000000000 : ℝ)) (X := (50001796239625124101/50000000000000000000 : ℝ)) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013428458554108329/25000000000000000000 : ℝ) ≤ (200024198691293/200000000000000 : ℝ) ^ (4545/1024 : ℝ) := by
    have hpowers : (25013428458554108329/25000000000000000000 : ℝ)^1024 ≤ (200024198691293/200000000000000 : ℝ)^4545 := by
      have hnat : (25013428458554108329 : ℕ)^1024*200000000000000^4545 ≤ 200024198691293^4545*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013428458554108329 25000000000000000000 200024198691293 200000000000000 1024 4545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200024198691293/200000000000000 : ℝ)) (X := (25013428458554108329/25000000000000000000 : ℝ)) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10010383518918261843/10000000000000000000 : ℝ) ≤ (5001169465394543/5000000000000000 : ℝ) ^ (4545/1024 : ℝ) := by
    have hpowers : (10010383518918261843/10000000000000000000 : ℝ)^1024 ≤ (5001169465394543/5000000000000000 : ℝ)^4545 := by
      have hnat : (10010383518918261843 : ℕ)^1024*5000000000000000^4545 ≤ 5001169465394543^4545*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10010383518918261843 10000000000000000000 5001169465394543 5000000000000000 1024 4545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001169465394543/5000000000000000 : ℝ)) (X := (10010383518918261843/10000000000000000000 : ℝ)) (by norm_num) 4545 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1796239625124101/100000000000000000000 : ℝ) ≤ ((1510336384535338397/1510625000000000000 : ℝ)+2*(282249056109/241700000000000 : ℝ)*(8527/100000 : ℝ))^(4545/1024 : ℝ) := by
    rw [show (1510336384535338397/1510625000000000000 : ℝ)+2*(282249056109/241700000000000 : ℝ)*(8527/100000 : ℝ)=(5000040469170107/5000000000000000 : ℝ) by norm_num, show 1+2*(1796239625124101/100000000000000000000 : ℝ)=(50001796239625124101/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10383518918261843/20000000000000000000 : ℝ)+(1796239625124101/100000000000000000000 : ℝ) ≤ ((1510336384535338397/1510625000000000000 : ℝ)+(282249056109/241700000000000 : ℝ)*((3639/20000 : ℝ)+(8527/100000 : ℝ)))^(4545/1024 : ℝ) := by
    rw [show (1510336384535338397/1510625000000000000 : ℝ)+(282249056109/241700000000000 : ℝ)*((3639/20000 : ℝ)+(8527/100000 : ℝ))=(200024198691293/200000000000000 : ℝ) by norm_num, show 1+(10383518918261843/20000000000000000000 : ℝ)+(1796239625124101/100000000000000000000 : ℝ)=(25013428458554108329/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10383518918261843/20000000000000000000 : ℝ) ≤ ((1510336384535338397/1510625000000000000 : ℝ)+2*(282249056109/241700000000000 : ℝ)*(3639/20000 : ℝ))^(4545/1024 : ℝ) := by
    rw [show (1510336384535338397/1510625000000000000 : ℝ)+2*(282249056109/241700000000000 : ℝ)*(3639/20000 : ℝ)=(5001169465394543/5000000000000000 : ℝ) by norm_num, show 1+2*(10383518918261843/20000000000000000000 : ℝ)=(10010383518918261843/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1510336384535338397/1510625000000000000 : ℝ)*(X 1 0+X 2 0)+(282249056109/241700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4545/1024 : ℝ)) (lo := (8527/100000 : ℝ)) (hi := (3639/20000 : ℝ)) (c := (1510336384535338397/1510625000000000000 : ℝ)) (alpha := (282249056109/241700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1510336384535338397/1510625000000000000 : ℝ)*(X 0 1+X 2 1)+(282249056109/241700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4545/1024 : ℝ)) (lo := (8527/100000 : ℝ)) (hi := (3639/20000 : ℝ)) (c := (1510336384535338397/1510625000000000000 : ℝ)) (alpha := (282249056109/241700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1510336384535338397/1510625000000000000 : ℝ)*(X 0 2+X 1 2)+(282249056109/241700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4545/1024 : ℝ)) (lo := (8527/100000 : ℝ)) (hi := (3639/20000 : ℝ)) (c := (1510336384535338397/1510625000000000000 : ℝ)) (alpha := (282249056109/241700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1845442731/10000000000 : ℝ)*X 0 0+(5453878773/10000000000 : ℝ)*X 0 1+(5198265981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356687431/10000000000 : ℝ)*X 1 0+(-1976929669/10000000000 : ℝ)*X 1 1+(5198265873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535668737/1000000000 : ℝ)*X 2 0+(1039653189/2000000000 : ℝ)*X 2 1+(-395385931/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4261461669/10000000000 : ℝ)*X 0 0+(3977414883/10000000000 : ℝ)*X 0 1+(285147037/625000000 : ℝ)*X 0 2+(4261461669/10000000000 : ℝ)*X 1 0+(3977414883/10000000000 : ℝ)*X 1 1+(285147037/625000000 : ℝ)*X 1 2+(4261461669/10000000000 : ℝ)*X 2 0+(3977414883/10000000000 : ℝ)*X 2 1+(285147037/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1845490747/10000000000 : ℝ)*X 0 0+(2599922721/5000000000 : ℝ)*X 0 1+(85191969/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644720997/5000000000 : ℝ)*X 1 0+(-1722910317/10000000000 : ℝ)*X 1 1+(5452286963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330590177/625000000 : ℝ)*X 2 0+(5452286791/10000000000 : ℝ)*X 2 1+(-430727349/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1065393467/2500000000 : ℝ)*X 0 0+(142460637/312500000 : ℝ)*X 0 1+(398105867/1000000000 : ℝ)*X 0 2+(1065393467/2500000000 : ℝ)*X 1 0+(142460637/312500000 : ℝ)*X 1 1+(398105867/1000000000 : ℝ)*X 1 2+(1065393467/2500000000 : ℝ)*X 2 0+(142460637/312500000 : ℝ)*X 2 1+(398105867/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1525_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98307783393054813467819673/37765625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (514919707/100000000000000 : ℝ)*(base19) + (382724797/100000000000000 : ℝ)*(base23) + (46948401/100000000000000 : ℝ)*(lower2) + (8901903/10000000000000 : ℝ)*(upper3) + (25499109/100000000000000 : ℝ)*(upper5) + (702720847053837/25000000000000 : ℝ)*(major0) + (702720847053837/25000000000000 : ℝ)*(major1) + (702720847053837/25000000000000 : ℝ)*(major2) + (195608644402611/5000000000000 : ℝ)*(sp0) + (3912176938922231/100000000000000 : ℝ)*(sp1) + (3912177071117141/100000000000000 : ℝ)*(sp2) + (854793052667771/50000000000000 : ℝ)*(sp3) + (2282894859/50000000000000 : ℝ)*(sp4) + (313048313/10000000000000 : ℝ)*(sp7) + (1709589235818673/100000000000000 : ℝ)*(f.failure) + (1956088726920969/50000000000000 : ℝ)*(f.sum) + (30427934445953/3021250000000000000000000000 : ℝ)*base65 + (107384087203829289/37765625000000000000000000000000 : ℝ)*base67 + (298731619360860539/37765625000000000000000000000000 : ℝ)*base69 + (85307397402094041/9441406250000000000000000000000 : ℝ)*base71 + (12417111510263/12085000000000000000000000000 : ℝ)*base74 + (33646032410273583/4720703125000000000000000000000 : ℝ)*base75 + (284542230515360539/37765625000000000000000000000000 : ℝ)*base77 + (74810519806062791/9441406250000000000000000000000 : ℝ)*base79 + (63076389276167/12085000000000000000000000000 : ℝ)*base81 + (62916607/10000000000000000000000 : ℝ)*base90 + (62916607/10000000000000000000000 : ℝ)*base92 + (62916607/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72839563660158293219345151/9441406250000000000000000000000 : ℝ) := by norm_num
    linear_combination (156195027/25000000000000 : ℝ)*(base15) + (63393347/100000000000000 : ℝ)*(base29) + (292101659/100000000000000 : ℝ)*(lower2) + (188294741/100000000000000 : ℝ)*(lower4) + (592241/1250000000000 : ℝ)*(upper5) + (88943714399589/3125000000000 : ℝ)*(major0) + (569239784836039/20000000000000 : ℝ)*(major1) + (569239784836039/20000000000000 : ℝ)*(major2) + (9837798287/100000000000000 : ℝ)*(sp2) + (5922888783/100000000000000 : ℝ)*(sp3) + (1980664660639783/50000000000000 : ℝ)*(sp4) + (396132863310611/10000000000000 : ℝ)*(sp5) + (990329855021983/25000000000000 : ℝ)*(sp6) + (432765586757123/25000000000000 : ℝ)*(sp7) + (69242730796691/4000000000000 : ℝ)*(f.failure) + (1980664660639783/50000000000000 : ℝ)*(f.sum) + (5182716803237/1208500000000000000000000000 : ℝ)*base65 + (434264353946254267/30212500000000000000000000000000 : ℝ)*base68 + (387173149656641767/30212500000000000000000000000000 : ℝ)*base70 + (533965073937295547/75531250000000000000000000000000 : ℝ)*base72 + (85867952958303/24170000000000000000000000000 : ℝ)*base74 + (109499233920895517/30212500000000000000000000000000 : ℝ)*base76 + (867485036351608047/75531250000000000000000000000000 : ℝ)*base78 + (491961556633970517/30212500000000000000000000000000 : ℝ)*base80 + (26966074469457/24170000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1516931/400000000000000000000 : ℝ)*base89 + (1516931/400000000000000000000 : ℝ)*base91 + (1516931/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1525_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164418641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3639/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10537/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15949/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1525_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1525_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164418641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10537/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15949/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1525_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1525_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1525_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4545/1024 : ℝ) ≤ p) (hpb : p ≤ (4547/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164418641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10537/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15949/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1525_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
