-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1699_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:44:20.684883+00:00
-- url     : https://prove2.me/submissions/614cf3ce-ea87-472a-ba50-d44a11c44504

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
theorem support_rectangle_w1699_s3_0 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-726414767/5000000000 : ℝ)*x 0 + (1369294553/2500000000 : ℝ)*x 1 + (321048639/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (726414767/5000000000 : ℝ)^5215 ≤ (9068093198547/100000000000000 : ℝ)^4191 := by
    have hnat : (726414767 : ℕ)^5215*100000000000000^4191 ≤ 9068093198547^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726414767 5000000000 9068093198547 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369294553/2500000000 : ℝ)^5215 ≤ (23640010637337/50000000000000 : ℝ)^4191 := by
    have hnat : (1369294553 : ℕ)^5215*50000000000000^4191 ≤ 23640010637337^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369294553 2500000000 23640010637337 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321048639/625000000 : ℝ)^5215 ≤ (10912971379277/25000000000000 : ℝ)^4191 := by
    have hnat : (321048639 : ℕ)^5215*25000000000000^4191 ≤ 10912971379277^4191*625000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321048639 625000000 10912971379277 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-726414767/5000000000 : ℝ), (1369294553/2500000000 : ℝ), (321048639/625000000 : ℝ)] ![(9068093198547/100000000000000 : ℝ), (23640010637337/50000000000000 : ℝ), (10912971379277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-726414767/5000000000 : ℝ)|^5215 ≤ (9068093198547/100000000000000 : ℝ)^4191
        have hw : |(-726414767/5000000000 : ℝ)|=(726414767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369294553/2500000000 : ℝ)|^5215 ≤ (23640010637337/50000000000000 : ℝ)^4191
        have hw : |(1369294553/2500000000 : ℝ)|=(1369294553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(321048639/625000000 : ℝ)|^5215 ≤ (10912971379277/25000000000000 : ℝ)^4191
        have hw : |(321048639/625000000 : ℝ)|=(321048639/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s3_1 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336802313/2500000000 : ℝ)*x 0 + (-1629502673/10000000000 : ℝ)*x 1 + (5136778429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336802313/2500000000 : ℝ)^5215 ≤ (22944027600349/50000000000000 : ℝ)^4191 := by
    have hnat : (1336802313 : ℕ)^5215*50000000000000^4191 ≤ 22944027600349^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336802313 2500000000 22944027600349 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1629502673/10000000000 : ℝ)^5215 ≤ (10460057111029/100000000000000 : ℝ)^4191 := by
    have hnat : (1629502673 : ℕ)^5215*100000000000000^4191 ≤ 10460057111029^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629502673 10000000000 10460057111029 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136778429/10000000000 : ℝ)^5215 ≤ (21825943842413/50000000000000 : ℝ)^4191 := by
    have hnat : (5136778429 : ℕ)^5215*50000000000000^4191 ≤ 21825943842413^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136778429 10000000000 21825943842413 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336802313/2500000000 : ℝ), (-1629502673/10000000000 : ℝ), (5136778429/10000000000 : ℝ)] ![(22944027600349/50000000000000 : ℝ), (10460057111029/100000000000000 : ℝ), (21825943842413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336802313/2500000000 : ℝ)|^5215 ≤ (22944027600349/50000000000000 : ℝ)^4191
        have hw : |(1336802313/2500000000 : ℝ)|=(1336802313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1629502673/10000000000 : ℝ)|^5215 ≤ (10460057111029/100000000000000 : ℝ)^4191
        have hw : |(-1629502673/10000000000 : ℝ)|=(1629502673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136778429/10000000000 : ℝ)|^5215 ≤ (21825943842413/50000000000000 : ℝ)^4191
        have hw : |(5136778429/10000000000 : ℝ)|=(5136778429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s3_2 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673604661/5000000000 : ℝ)*x 0 + (5136778367/10000000000 : ℝ)*x 1 + (-81475133/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673604661/5000000000 : ℝ)^5215 ≤ (1434001748381/3125000000000 : ℝ)^4191 := by
    have hnat : (2673604661 : ℕ)^5215*3125000000000^4191 ≤ 1434001748381^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673604661 5000000000 1434001748381 3125000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136778367/10000000000 : ℝ)^5215 ≤ (43651887029223/100000000000000 : ℝ)^4191 := by
    have hnat : (5136778367 : ℕ)^5215*100000000000000^4191 ≤ 43651887029223^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136778367 10000000000 43651887029223 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81475133/500000000 : ℝ)^5215 ≤ (1046005700719/10000000000000 : ℝ)^4191 := by
    have hnat : (81475133 : ℕ)^5215*10000000000000^4191 ≤ 1046005700719^4191*500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81475133 500000000 1046005700719 10000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673604661/5000000000 : ℝ), (5136778367/10000000000 : ℝ), (-81475133/500000000 : ℝ)] ![(1434001748381/3125000000000 : ℝ), (43651887029223/100000000000000 : ℝ), (1046005700719/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673604661/5000000000 : ℝ)|^5215 ≤ (1434001748381/3125000000000 : ℝ)^4191
        have hw : |(2673604661/5000000000 : ℝ)|=(2673604661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136778367/10000000000 : ℝ)|^5215 ≤ (43651887029223/100000000000000 : ℝ)^4191
        have hw : |(5136778367/10000000000 : ℝ)|=(5136778367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-81475133/500000000 : ℝ)|^5215 ≤ (1046005700719/10000000000000 : ℝ)^4191
        have hw : |(-81475133/500000000 : ℝ)|=(81475133/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s3_3 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4119084721/10000000000 : ℝ)*x 0 + (3656296339/10000000000 : ℝ)*x 1 + (4618468069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119084721/10000000000 : ℝ)^5215 ≤ (8291322392613/25000000000000 : ℝ)^4191 := by
    have hnat : (4119084721 : ℕ)^5215*25000000000000^4191 ≤ 8291322392613^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119084721 10000000000 8291322392613 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3656296339/10000000000 : ℝ)^5215 ≤ (14297099574563/50000000000000 : ℝ)^4191 := by
    have hnat : (3656296339 : ℕ)^5215*50000000000000^4191 ≤ 14297099574563^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3656296339 10000000000 14297099574563 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4618468069/10000000000 : ℝ)^5215 ≤ (19120255633501/50000000000000 : ℝ)^4191 := by
    have hnat : (4618468069 : ℕ)^5215*50000000000000^4191 ≤ 19120255633501^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4618468069 10000000000 19120255633501 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119084721/10000000000 : ℝ), (3656296339/10000000000 : ℝ), (4618468069/10000000000 : ℝ)] ![(8291322392613/25000000000000 : ℝ), (14297099574563/50000000000000 : ℝ), (19120255633501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119084721/10000000000 : ℝ)|^5215 ≤ (8291322392613/25000000000000 : ℝ)^4191
        have hw : |(4119084721/10000000000 : ℝ)|=(4119084721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3656296339/10000000000 : ℝ)|^5215 ≤ (14297099574563/50000000000000 : ℝ)^4191
        have hw : |(3656296339/10000000000 : ℝ)|=(3656296339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4618468069/10000000000 : ℝ)|^5215 ≤ (19120255633501/50000000000000 : ℝ)^4191
        have hw : |(4618468069/10000000000 : ℝ)|=(4618468069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s3_4 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-90811607/625000000 : ℝ)*x 0 + (5140511999/10000000000 : ℝ)*x 1 + (273669447/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90811607/625000000 : ℝ)^5215 ≤ (4534653103081/50000000000000 : ℝ)^4191 := by
    have hnat : (90811607 : ℕ)^5215*50000000000000^4191 ≤ 4534653103081^4191*625000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90811607 625000000 4534653103081 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140511999/10000000000 : ℝ)^5215 ≤ (21845685413163/50000000000000 : ℝ)^4191 := by
    have hnat : (5140511999 : ℕ)^5215*50000000000000^4191 ≤ 21845685413163^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140511999 10000000000 21845685413163 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273669447/500000000 : ℝ)^5215 ≤ (11809830738011/25000000000000 : ℝ)^4191 := by
    have hnat : (273669447 : ℕ)^5215*25000000000000^4191 ≤ 11809830738011^4191*500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273669447 500000000 11809830738011 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-90811607/625000000 : ℝ), (5140511999/10000000000 : ℝ), (273669447/500000000 : ℝ)] ![(4534653103081/50000000000000 : ℝ), (21845685413163/50000000000000 : ℝ), (11809830738011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-90811607/625000000 : ℝ)|^5215 ≤ (4534653103081/50000000000000 : ℝ)^4191
        have hw : |(-90811607/625000000 : ℝ)|=(90811607/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140511999/10000000000 : ℝ)|^5215 ≤ (21845685413163/50000000000000 : ℝ)^4191
        have hw : |(5140511999/10000000000 : ℝ)|=(5140511999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(273669447/500000000 : ℝ)|^5215 ≤ (11809830738011/25000000000000 : ℝ)^4191
        have hw : |(273669447/500000000 : ℝ)|=(273669447/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s3_5 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256137703/10000000000 : ℝ)*x 0 + (-32322297/250000000 : ℝ)*x 1 + (2736694471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256137703/10000000000 : ℝ)^5215 ≤ (44917582419799/100000000000000 : ℝ)^4191 := by
    have hnat : (5256137703 : ℕ)^5215*100000000000000^4191 ≤ 44917582419799^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256137703 10000000000 44917582419799 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32322297/250000000 : ℝ)^5215 ≤ (7843094588169/100000000000000 : ℝ)^4191 := by
    have hnat : (32322297 : ℕ)^5215*100000000000000^4191 ≤ 7843094588169^4191*250000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32322297 250000000 7843094588169 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736694471/5000000000 : ℝ)^5215 ≤ (47239322973523/100000000000000 : ℝ)^4191 := by
    have hnat : (2736694471 : ℕ)^5215*100000000000000^4191 ≤ 47239322973523^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736694471 5000000000 47239322973523 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256137703/10000000000 : ℝ), (-32322297/250000000 : ℝ), (2736694471/5000000000 : ℝ)] ![(44917582419799/100000000000000 : ℝ), (7843094588169/100000000000000 : ℝ), (47239322973523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256137703/10000000000 : ℝ)|^5215 ≤ (44917582419799/100000000000000 : ℝ)^4191
        have hw : |(5256137703/10000000000 : ℝ)|=(5256137703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32322297/250000000 : ℝ)|^5215 ≤ (7843094588169/100000000000000 : ℝ)^4191
        have hw : |(-32322297/250000000 : ℝ)|=(32322297/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736694471/5000000000 : ℝ)|^5215 ≤ (47239322973523/100000000000000 : ℝ)^4191
        have hw : |(2736694471/5000000000 : ℝ)|=(2736694471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s3_6 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525613767/1000000000 : ℝ)*x 0 + (42760851/78125000 : ℝ)*x 1 + (-1292891947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525613767/1000000000 : ℝ)^5215 ≤ (8983516413777/20000000000000 : ℝ)^4191 := by
    have hnat : (525613767 : ℕ)^5215*20000000000000^4191 ≤ 8983516413777^4191*1000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525613767 1000000000 8983516413777 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42760851/78125000 : ℝ)^5215 ≤ (47239322823171/100000000000000 : ℝ)^4191 := by
    have hnat : (42760851 : ℕ)^5215*100000000000000^4191 ≤ 47239322823171^4191*78125000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42760851 78125000 47239322823171 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292891947/10000000000 : ℝ)^5215 ≤ (49019344337/625000000000 : ℝ)^4191 := by
    have hnat : (1292891947 : ℕ)^5215*625000000000^4191 ≤ 49019344337^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292891947 10000000000 49019344337 625000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525613767/1000000000 : ℝ), (42760851/78125000 : ℝ), (-1292891947/10000000000 : ℝ)] ![(8983516413777/20000000000000 : ℝ), (47239322823171/100000000000000 : ℝ), (49019344337/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525613767/1000000000 : ℝ)|^5215 ≤ (8983516413777/20000000000000 : ℝ)^4191
        have hw : |(525613767/1000000000 : ℝ)|=(525613767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42760851/78125000 : ℝ)|^5215 ≤ (47239322823171/100000000000000 : ℝ)^4191
        have hw : |(42760851/78125000 : ℝ)|=(42760851/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1292891947/10000000000 : ℝ)|^5215 ≤ (49019344337/625000000000 : ℝ)^4191
        have hw : |(-1292891947/10000000000 : ℝ)|=(1292891947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s3_7 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (823905433/2000000000 : ℝ)*x 0 + (4607914281/10000000000 : ℝ)*x 1 + (1833503789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823905433/2000000000 : ℝ)^5215 ≤ (6633944485507/20000000000000 : ℝ)^4191 := by
    have hnat : (823905433 : ℕ)^5215*20000000000000^4191 ≤ 6633944485507^4191*2000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823905433 2000000000 6633944485507 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4607914281/10000000000 : ℝ)^5215 ≤ (38131806288239/100000000000000 : ℝ)^4191 := by
    have hnat : (4607914281 : ℕ)^5215*100000000000000^4191 ≤ 38131806288239^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4607914281 10000000000 38131806288239 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1833503789/5000000000 : ℝ)^5215 ≤ (5739694253633/20000000000000 : ℝ)^4191 := by
    have hnat : (1833503789 : ℕ)^5215*20000000000000^4191 ≤ 5739694253633^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833503789 5000000000 5739694253633 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(823905433/2000000000 : ℝ), (4607914281/10000000000 : ℝ), (1833503789/5000000000 : ℝ)] ![(6633944485507/20000000000000 : ℝ), (38131806288239/100000000000000 : ℝ), (5739694253633/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(823905433/2000000000 : ℝ)|^5215 ≤ (6633944485507/20000000000000 : ℝ)^4191
        have hw : |(823905433/2000000000 : ℝ)|=(823905433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4607914281/10000000000 : ℝ)|^5215 ≤ (38131806288239/100000000000000 : ℝ)^4191
        have hw : |(4607914281/10000000000 : ℝ)|=(4607914281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1833503789/5000000000 : ℝ)|^5215 ≤ (5739694253633/20000000000000 : ℝ)^4191
        have hw : |(1833503789/5000000000 : ℝ)|=(1833503789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1699_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4297/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4951/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2479/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17171/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4297/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4951/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4297/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4951/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4297/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4951/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4297/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4951/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4297/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4951/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4297/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4951/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4951/50000 : ℝ) ^ (5207/1024 : ℝ) ≤ (391075214568033/50000000000000000000 : ℝ) := by
    have hpowers : (4951/50000 : ℝ)^5207 ≤ (391075214568033/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4951 : ℕ)^5207*50000000000000000000^1024 ≤ 391075214568033^1024*50000^5207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4951 50000 391075214568033 50000000000000000000 5207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4951/50000 : ℝ)) (X := (391075214568033/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4297/25000 : ℝ) ^ (5207/1024 : ℝ) ≤ (1291667562703723/10000000000000000000 : ℝ) := by
    have hpowers : (4297/25000 : ℝ)^5207 ≤ (1291667562703723/10000000000000000000 : ℝ)^1024 := by
      have hnat : (4297 : ℕ)^5207*10000000000000000000^1024 ≤ 1291667562703723^1024*25000^5207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4297 25000 1291667562703723 10000000000000000000 5207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4297/25000 : ℝ)) (X := (1291667562703723/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000391075214568033/25000000000000000000 : ℝ) ≤ (10000030763088421/10000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (25000391075214568033/25000000000000000000 : ℝ)^1024 ≤ (10000030763088421/10000000000000000 : ℝ)^5207 := by
      have hnat : (25000391075214568033 : ℕ)^1024*10000000000000000^5207 ≤ 10000030763088421^5207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000391075214568033 25000000000000000000 10000030763088421 10000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000030763088421/10000000000000000 : ℝ)) (X := (25000391075214568033/25000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6250856176628510831/6250000000000000000 : ℝ) ≤ (5000134692011599/5000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (6250856176628510831/6250000000000000000 : ℝ)^1024 ≤ (5000134692011599/5000000000000000 : ℝ)^5207 := by
      have hnat : (6250856176628510831 : ℕ)^1024*5000000000000000^5207 ≤ 5000134692011599^5207*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250856176628510831 6250000000000000000 5000134692011599 5000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000134692011599/5000000000000000 : ℝ)) (X := (6250856176628510831/6250000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001291667562703723/5000000000000000000 : ℝ) ≤ (400020320198319/400000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (5001291667562703723/5000000000000000000 : ℝ)^1024 ≤ (400020320198319/400000000000000 : ℝ)^5207 := by
      have hnat : (5001291667562703723 : ℕ)^1024*400000000000000^5207 ≤ 400020320198319^5207*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001291667562703723 5000000000000000000 400020320198319 400000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400020320198319/400000000000000 : ℝ)) (X := (5001291667562703723/5000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(391075214568033/50000000000000000000 : ℝ) ≤ ((36427749245434955849/36430000000000000000 : ℝ)+2*(238620934777/728600000000000 : ℝ)*(4951/50000 : ℝ))^(5207/1024 : ℝ) := by
    rw [show (36427749245434955849/36430000000000000000 : ℝ)+2*(238620934777/728600000000000 : ℝ)*(4951/50000 : ℝ)=(10000030763088421/10000000000000000 : ℝ) by norm_num, show 1+2*(391075214568033/50000000000000000000 : ℝ)=(25000391075214568033/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1291667562703723/10000000000000000000 : ℝ)+(391075214568033/50000000000000000000 : ℝ) ≤ ((36427749245434955849/36430000000000000000 : ℝ)+(238620934777/728600000000000 : ℝ)*((4297/25000 : ℝ)+(4951/50000 : ℝ)))^(5207/1024 : ℝ) := by
    rw [show (36427749245434955849/36430000000000000000 : ℝ)+(238620934777/728600000000000 : ℝ)*((4297/25000 : ℝ)+(4951/50000 : ℝ))=(5000134692011599/5000000000000000 : ℝ) by norm_num, show 1+(1291667562703723/10000000000000000000 : ℝ)+(391075214568033/50000000000000000000 : ℝ)=(6250856176628510831/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1291667562703723/10000000000000000000 : ℝ) ≤ ((36427749245434955849/36430000000000000000 : ℝ)+2*(238620934777/728600000000000 : ℝ)*(4297/25000 : ℝ))^(5207/1024 : ℝ) := by
    rw [show (36427749245434955849/36430000000000000000 : ℝ)+2*(238620934777/728600000000000 : ℝ)*(4297/25000 : ℝ)=(400020320198319/400000000000000 : ℝ) by norm_num, show 1+2*(1291667562703723/10000000000000000000 : ℝ)=(5001291667562703723/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36427749245434955849/36430000000000000000 : ℝ)*(X 1 0+X 2 0)+(238620934777/728600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (4951/50000 : ℝ)) (hi := (4297/25000 : ℝ)) (c := (36427749245434955849/36430000000000000000 : ℝ)) (alpha := (238620934777/728600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36427749245434955849/36430000000000000000 : ℝ)*(X 0 1+X 2 1)+(238620934777/728600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (4951/50000 : ℝ)) (hi := (4297/25000 : ℝ)) (c := (36427749245434955849/36430000000000000000 : ℝ)) (alpha := (238620934777/728600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36427749245434955849/36430000000000000000 : ℝ)*(X 0 2+X 1 2)+(238620934777/728600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (4951/50000 : ℝ)) (hi := (4297/25000 : ℝ)) (c := (36427749245434955849/36430000000000000000 : ℝ)) (alpha := (238620934777/728600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-726414767/5000000000 : ℝ)*X 0 0+(1369294553/2500000000 : ℝ)*X 0 1+(321048639/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336802313/2500000000 : ℝ)*X 1 0+(-1629502673/10000000000 : ℝ)*X 1 1+(5136778429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673604661/5000000000 : ℝ)*X 2 0+(5136778367/10000000000 : ℝ)*X 2 1+(-81475133/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4119084721/10000000000 : ℝ)*X 0 0+(3656296339/10000000000 : ℝ)*X 0 1+(4618468069/10000000000 : ℝ)*X 0 2+(4119084721/10000000000 : ℝ)*X 1 0+(3656296339/10000000000 : ℝ)*X 1 1+(4618468069/10000000000 : ℝ)*X 1 2+(4119084721/10000000000 : ℝ)*X 2 0+(3656296339/10000000000 : ℝ)*X 2 1+(4618468069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-90811607/625000000 : ℝ)*X 0 0+(5140511999/10000000000 : ℝ)*X 0 1+(273669447/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256137703/10000000000 : ℝ)*X 1 0+(-32322297/250000000 : ℝ)*X 1 1+(2736694471/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((525613767/1000000000 : ℝ)*X 2 0+(42760851/78125000 : ℝ)*X 2 1+(-1292891947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((823905433/2000000000 : ℝ)*X 0 0+(4607914281/10000000000 : ℝ)*X 0 1+(1833503789/5000000000 : ℝ)*X 0 2+(823905433/2000000000 : ℝ)*X 1 0+(4607914281/10000000000 : ℝ)*X 1 1+(1833503789/5000000000 : ℝ)*X 1 2+(823905433/2000000000 : ℝ)*X 2 0+(4607914281/10000000000 : ℝ)*X 2 1+(1833503789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11301180087409570538678787063/910750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1829537993/100000000000000 : ℝ)*(base19) + (71687709/4000000000000 : ℝ)*(base23) + (16387643/5000000000000 : ℝ)*(upper3) + (40533583/100000000000000 : ℝ)*(upper4) + (7237579/2500000000000 : ℝ)*(upper5) + (1988543327625629/100000000000000 : ℝ)*(major0) + (1988543327625629/100000000000000 : ℝ)*(major1) + (1988543327625629/100000000000000 : ℝ)*(major2) + (293773856384577/10000000000000 : ℝ)*(sp0) + (1468877609521903/50000000000000 : ℝ)*(sp1) + (117510210255563/4000000000000 : ℝ)*(sp2) + (519661042401339/50000000000000 : ℝ)*(sp3) + (1848473603/10000000000000 : ℝ)*(sp4) + (710824503/10000000000000 : ℝ)*(sp7) + (1039329193047707/100000000000000 : ℝ)*(f.failure) + (14688785242909/500000000000 : ℝ)*(f.sum) + (47448835925093/36430000000000000000000000000 : ℝ)*base65 + (622450838323495979/3643000000000000000000000000000000 : ℝ)*base68 + (49887068874083495979/3643000000000000000000000000000000 : ℝ)*base70 + (10352598801902504021/3643000000000000000000000000000000 : ℝ)*base71 + (30704602967113/36430000000000000000000000000 : ℝ)*base73 + (21525731336525495979/3643000000000000000000000000000000 : ℝ)*base76 + (11004357688531495979/3643000000000000000000000000000000 : ℝ)*base78 + (22699589364868495979/3643000000000000000000000000000000 : ℝ)*base80 + (216294833039727/36430000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (14819457/5000000000000000000000 : ℝ)*base90 + (14819457/5000000000000000000000 : ℝ)*base92 + (14819457/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13108627124295039005529/4553750000000000000000000000 : ℝ) := by norm_num
    linear_combination (43570733/10000000000000 : ℝ)*(base19) + (13903103/3125000000000 : ℝ)*(base23) + (61729229/50000000000000 : ℝ)*(lower1) + (67750843/100000000000000 : ℝ)*(upper3) + (826793/5000000000000 : ℝ)*(lower4) + (14708921/25000000000000 : ℝ)*(upper5) + (508364045721537/25000000000000 : ℝ)*(major0) + (508364045721537/25000000000000 : ℝ)*(major1) + (508364045721537/25000000000000 : ℝ)*(major2) + (98322579/50000000000000 : ℝ)*(sp1) + (3004108988492739/100000000000000 : ℝ)*(sp4) + (751027089035063/25000000000000 : ℝ)*(sp5) + (3004108543593443/100000000000000 : ℝ)*(sp6) + (531401640662369/50000000000000 : ℝ)*(sp7) + (531401640662369/50000000000000 : ℝ)*(f.failure) + (3004108988492739/100000000000000 : ℝ)*(f.sum) + (9197459602733/4553750000000000000000000000 : ℝ)*base66 + (1349015455086619913/910750000000000000000000000000000 : ℝ)*base67 + (1060933768297869913/910750000000000000000000000000000 : ℝ)*base69 + (6999440087720630087/910750000000000000000000000000000 : ℝ)*base72 + (8121023490719/9107500000000000000000000000 : ℝ)*base73 + (2551723234791630087/910750000000000000000000000000000 : ℝ)*base76 + (2086467371429130087/910750000000000000000000000000000 : ℝ)*base78 + (2719034965074369913/910750000000000000000000000000000 : ℝ)*base79 + (35461808986253/18215000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (24130381/2500000000000000000000 : ℝ)*base89 + (24130381/2500000000000000000000 : ℝ)*base91 + (24130381/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1699_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4297/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4951/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2479/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17171/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1699_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1699_s4_0 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-36320953/250000000 : ℝ)*x 0 + (5477144759/10000000000 : ℝ)*x 1 + (5136805899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36320953/250000000 : ℝ)^5215 ≤ (4534079941851/50000000000000 : ℝ)^4191 := by
    have hnat : (36320953 : ℕ)^5215*50000000000000^4191 ≤ 4534079941851^4191*250000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36320953 250000000 4534079941851 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5477144759/10000000000 : ℝ)^5215 ≤ (2363983097287/5000000000000 : ℝ)^4191 := by
    have hnat : (5477144759 : ℕ)^5215*5000000000000^4191 ≤ 2363983097287^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477144759 10000000000 2363983097287 5000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136805899/10000000000 : ℝ)^5215 ≤ (43652178159177/100000000000000 : ℝ)^4191 := by
    have hnat : (5136805899 : ℕ)^5215*100000000000000^4191 ≤ 43652178159177^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136805899 10000000000 43652178159177 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-36320953/250000000 : ℝ), (5477144759/10000000000 : ℝ), (5136805899/10000000000 : ℝ)] ![(4534079941851/50000000000000 : ℝ), (2363983097287/5000000000000 : ℝ), (43652178159177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-36320953/250000000 : ℝ)|^5215 ≤ (4534079941851/50000000000000 : ℝ)^4191
        have hw : |(-36320953/250000000 : ℝ)|=(36320953/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5477144759/10000000000 : ℝ)|^5215 ≤ (2363983097287/5000000000000 : ℝ)^4191
        have hw : |(5477144759/10000000000 : ℝ)|=(5477144759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136805899/10000000000 : ℝ)|^5215 ≤ (43652178159177/100000000000000 : ℝ)^4191
        have hw : |(5136805899/10000000000 : ℝ)|=(5136805899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s4_1 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347200809/10000000000 : ℝ)*x 0 + (-407369871/2500000000 : ℝ)*x 1 + (5136804471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347200809/10000000000 : ℝ)^5215 ≤ (22943982521187/50000000000000 : ℝ)^4191 := by
    have hnat : (5347200809 : ℕ)^5215*50000000000000^4191 ≤ 22943982521187^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347200809 10000000000 22943982521187 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (407369871/2500000000 : ℝ)^5215 ≤ (653741992949/6250000000000 : ℝ)^4191 := by
    have hnat : (407369871 : ℕ)^5215*6250000000000^4191 ≤ 653741992949^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407369871 2500000000 653741992949 6250000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136804471/10000000000 : ℝ)^5215 ≤ (21826081529577/50000000000000 : ℝ)^4191 := by
    have hnat : (5136804471 : ℕ)^5215*50000000000000^4191 ≤ 21826081529577^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136804471 10000000000 21826081529577 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347200809/10000000000 : ℝ), (-407369871/2500000000 : ℝ), (5136804471/10000000000 : ℝ)] ![(22943982521187/50000000000000 : ℝ), (653741992949/6250000000000 : ℝ), (21826081529577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347200809/10000000000 : ℝ)|^5215 ≤ (22943982521187/50000000000000 : ℝ)^4191
        have hw : |(5347200809/10000000000 : ℝ)|=(5347200809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-407369871/2500000000 : ℝ)|^5215 ≤ (653741992949/6250000000000 : ℝ)^4191
        have hw : |(-407369871/2500000000 : ℝ)|=(407369871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136804471/10000000000 : ℝ)|^5215 ≤ (21826081529577/50000000000000 : ℝ)^4191
        have hw : |(5136804471/10000000000 : ℝ)|=(5136804471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s4_2 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673599733/5000000000 : ℝ)*x 0 + (1284201443/2500000000 : ℝ)*x 1 + (-1629479557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673599733/5000000000 : ℝ)^5215 ≤ (5735993837649/12500000000000 : ℝ)^4191 := by
    have hnat : (2673599733 : ℕ)^5215*12500000000000^4191 ≤ 5735993837649^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673599733 5000000000 5735993837649 12500000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284201443/2500000000 : ℝ)^5215 ≤ (5456522102031/12500000000000 : ℝ)^4191 := by
    have hnat : (1284201443 : ℕ)^5215*12500000000000^4191 ≤ 5456522102031^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284201443 2500000000 5456522102031 12500000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1629479557/10000000000 : ℝ)^5215 ≤ (2614968117569/25000000000000 : ℝ)^4191 := by
    have hnat : (1629479557 : ℕ)^5215*25000000000000^4191 ≤ 2614968117569^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629479557 10000000000 2614968117569 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673599733/5000000000 : ℝ), (1284201443/2500000000 : ℝ), (-1629479557/10000000000 : ℝ)] ![(5735993837649/12500000000000 : ℝ), (5456522102031/12500000000000 : ℝ), (2614968117569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673599733/5000000000 : ℝ)|^5215 ≤ (5735993837649/12500000000000 : ℝ)^4191
        have hw : |(2673599733/5000000000 : ℝ)|=(2673599733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284201443/2500000000 : ℝ)|^5215 ≤ (5456522102031/12500000000000 : ℝ)^4191
        have hw : |(1284201443/2500000000 : ℝ)|=(1284201443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1629479557/10000000000 : ℝ)|^5215 ≤ (2614968117569/25000000000000 : ℝ)^4191
        have hw : |(-1629479557/10000000000 : ℝ)|=(1629479557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s4_3 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4119090959/10000000000 : ℝ)*x 0 + (457047703/1250000000 : ℝ)*x 1 + (4618381449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119090959/10000000000 : ℝ)^5215 ≤ (8291338017079/25000000000000 : ℝ)^4191 := by
    have hnat : (4119090959 : ℕ)^5215*25000000000000^4191 ≤ 8291338017079^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119090959 10000000000 8291338017079 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457047703/1250000000 : ℝ)^5215 ≤ (5719005817977/20000000000000 : ℝ)^4191 := by
    have hnat : (457047703 : ℕ)^5215*20000000000000^4191 ≤ 5719005817977^4191*1250000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457047703 1250000000 5719005817977 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4618381449/10000000000 : ℝ)^5215 ≤ (4779952353233/12500000000000 : ℝ)^4191 := by
    have hnat : (4618381449 : ℕ)^5215*12500000000000^4191 ≤ 4779952353233^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4618381449 10000000000 4779952353233 12500000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119090959/10000000000 : ℝ), (457047703/1250000000 : ℝ), (4618381449/10000000000 : ℝ)] ![(8291338017079/25000000000000 : ℝ), (5719005817977/20000000000000 : ℝ), (4779952353233/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119090959/10000000000 : ℝ)|^5215 ≤ (8291338017079/25000000000000 : ℝ)^4191
        have hw : |(4119090959/10000000000 : ℝ)|=(4119090959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(457047703/1250000000 : ℝ)|^5215 ≤ (5719005817977/20000000000000 : ℝ)^4191
        have hw : |(457047703/1250000000 : ℝ)|=(457047703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4618381449/10000000000 : ℝ)|^5215 ≤ (4779952353233/12500000000000 : ℝ)^4191
        have hw : |(4618381449/10000000000 : ℝ)|=(4618381449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s4_4 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-290598923/2000000000 : ℝ)*x 0 + (2570268857/5000000000 : ℝ)*x 1 + (2736678589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (290598923/2000000000 : ℝ)^5215 ≤ (9069375355189/100000000000000 : ℝ)^4191 := by
    have hnat : (290598923 : ℕ)^5215*100000000000000^4191 ≤ 9069375355189^4191*2000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290598923 2000000000 9069375355189 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570268857/5000000000 : ℝ)^5215 ≤ (2730727674447/6250000000000 : ℝ)^4191 := by
    have hnat : (2570268857 : ℕ)^5215*6250000000000^4191 ≤ 2730727674447^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570268857 5000000000 2730727674447 6250000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736678589/5000000000 : ℝ)^5215 ≤ (47238981844331/100000000000000 : ℝ)^4191 := by
    have hnat : (2736678589 : ℕ)^5215*100000000000000^4191 ≤ 47238981844331^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736678589 5000000000 47238981844331 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-290598923/2000000000 : ℝ), (2570268857/5000000000 : ℝ), (2736678589/5000000000 : ℝ)] ![(9069375355189/100000000000000 : ℝ), (2730727674447/6250000000000 : ℝ), (47238981844331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-290598923/2000000000 : ℝ)|^5215 ≤ (9069375355189/100000000000000 : ℝ)^4191
        have hw : |(-290598923/2000000000 : ℝ)|=(290598923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570268857/5000000000 : ℝ)|^5215 ≤ (2730727674447/6250000000000 : ℝ)^4191
        have hw : |(2570268857/5000000000 : ℝ)|=(2570268857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736678589/5000000000 : ℝ)|^5215 ≤ (47238981844331/100000000000000 : ℝ)^4191
        have hw : |(2736678589/5000000000 : ℝ)|=(2736678589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s4_5 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (128735413/312500000 : ℝ)*x 0 + (2303915951/5000000000 : ℝ)*x 1 + (3667088459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128735413/312500000 : ℝ)^5215 ≤ (2073111440841/6250000000000 : ℝ)^4191 := by
    have hnat : (128735413 : ℕ)^5215*6250000000000^4191 ≤ 2073111440841^4191*312500000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128735413 312500000 2073111440841 6250000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2303915951/5000000000 : ℝ)^5215 ≤ (7626191603219/20000000000000 : ℝ)^4191 := by
    have hnat : (2303915951 : ℕ)^5215*20000000000000^4191 ≤ 7626191603219^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303915951 5000000000 7626191603219 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3667088459/10000000000 : ℝ)^5215 ≤ (28699258914561/100000000000000 : ℝ)^4191 := by
    have hnat : (3667088459 : ℕ)^5215*100000000000000^4191 ≤ 28699258914561^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3667088459 10000000000 28699258914561 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(128735413/312500000 : ℝ), (2303915951/5000000000 : ℝ), (3667088459/10000000000 : ℝ)] ![(2073111440841/6250000000000 : ℝ), (7626191603219/20000000000000 : ℝ), (28699258914561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(128735413/312500000 : ℝ)|^5215 ≤ (2073111440841/6250000000000 : ℝ)^4191
        have hw : |(128735413/312500000 : ℝ)|=(128735413/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2303915951/5000000000 : ℝ)|^5215 ≤ (7626191603219/20000000000000 : ℝ)^4191
        have hw : |(2303915951/5000000000 : ℝ)|=(2303915951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3667088459/10000000000 : ℝ)|^5215 ≤ (28699258914561/100000000000000 : ℝ)^4191
        have hw : |(3667088459/10000000000 : ℝ)|=(3667088459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1699_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17171/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2479/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (9917/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17171/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17171/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2479/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17171/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2479/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17171/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2479/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17171/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2479/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17171/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2479/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17171/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2479/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2479/25000 : ℝ) ^ (5207/1024 : ℝ) ≤ (196947471173631/25000000000000000000 : ℝ) := by
    have hpowers : (2479/25000 : ℝ)^5207 ≤ (196947471173631/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2479 : ℕ)^5207*25000000000000000000^1024 ≤ 196947471173631^1024*25000^5207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2479 25000 196947471173631 25000000000000000000 5207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2479/25000 : ℝ)) (X := (196947471173631/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17171/100000 : ℝ) ^ (5207/1024 : ℝ) ≤ (6425922171638499/50000000000000000000 : ℝ) := by
    have hpowers : (17171/100000 : ℝ)^5207 ≤ (6425922171638499/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17171 : ℕ)^5207*50000000000000000000^1024 ≤ 6425922171638499^1024*100000^5207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17171 100000 6425922171638499 50000000000000000000 5207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17171/100000 : ℝ)) (X := (6425922171638499/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500196947471173631/12500000000000000000 : ℝ) ≤ (5000015492447411/5000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (12500196947471173631/12500000000000000000 : ℝ)^1024 ≤ (5000015492447411/5000000000000000 : ℝ)^5207 := by
      have hnat : (12500196947471173631 : ℕ)^1024*5000000000000000^5207 ≤ 5000015492447411^5207*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500196947471173631 12500000000000000000 5000015492447411 5000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000015492447411/5000000000000000 : ℝ)) (X := (12500196947471173631/12500000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50006819817113985761/50000000000000000000 : ℝ) ≤ (5000134110047157/5000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (50006819817113985761/50000000000000000000 : ℝ)^1024 ≤ (5000134110047157/5000000000000000 : ℝ)^5207 := by
      have hnat : (50006819817113985761 : ℕ)^1024*5000000000000000^5207 ≤ 5000134110047157^5207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006819817113985761 50000000000000000000 5000134110047157 5000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000134110047157/5000000000000000 : ℝ)) (X := (50006819817113985761/50000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25006425922171638499/25000000000000000000 : ℝ) ≤ (5000252727646903/5000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (25006425922171638499/25000000000000000000 : ℝ)^1024 ≤ (5000252727646903/5000000000000000 : ℝ)^5207 := by
      have hnat : (25006425922171638499 : ℕ)^1024*5000000000000000^5207 ≤ 5000252727646903^5207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006425922171638499 25000000000000000000 5000252727646903 5000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000252727646903/5000000000000000 : ℝ)) (X := (25006425922171638499/25000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(196947471173631/25000000000000000000 : ℝ) ≤ ((36272759973467804133/36275000000000000000 : ℝ)+2*(59308799873/181375000000000 : ℝ)*(2479/25000 : ℝ))^(5207/1024 : ℝ) := by
    rw [show (36272759973467804133/36275000000000000000 : ℝ)+2*(59308799873/181375000000000 : ℝ)*(2479/25000 : ℝ)=(5000015492447411/5000000000000000 : ℝ) by norm_num, show 1+2*(196947471173631/25000000000000000000 : ℝ)=(12500196947471173631/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6425922171638499/50000000000000000000 : ℝ)+(196947471173631/25000000000000000000 : ℝ) ≤ ((36272759973467804133/36275000000000000000 : ℝ)+(59308799873/181375000000000 : ℝ)*((17171/100000 : ℝ)+(2479/25000 : ℝ)))^(5207/1024 : ℝ) := by
    rw [show (36272759973467804133/36275000000000000000 : ℝ)+(59308799873/181375000000000 : ℝ)*((17171/100000 : ℝ)+(2479/25000 : ℝ))=(5000134110047157/5000000000000000 : ℝ) by norm_num, show 1+(6425922171638499/50000000000000000000 : ℝ)+(196947471173631/25000000000000000000 : ℝ)=(50006819817113985761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6425922171638499/50000000000000000000 : ℝ) ≤ ((36272759973467804133/36275000000000000000 : ℝ)+2*(59308799873/181375000000000 : ℝ)*(17171/100000 : ℝ))^(5207/1024 : ℝ) := by
    rw [show (36272759973467804133/36275000000000000000 : ℝ)+2*(59308799873/181375000000000 : ℝ)*(17171/100000 : ℝ)=(5000252727646903/5000000000000000 : ℝ) by norm_num, show 1+2*(6425922171638499/50000000000000000000 : ℝ)=(25006425922171638499/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36272759973467804133/36275000000000000000 : ℝ)*(X 1 0+X 2 0)+(59308799873/181375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (2479/25000 : ℝ)) (hi := (17171/100000 : ℝ)) (c := (36272759973467804133/36275000000000000000 : ℝ)) (alpha := (59308799873/181375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36272759973467804133/36275000000000000000 : ℝ)*(X 0 1+X 2 1)+(59308799873/181375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (2479/25000 : ℝ)) (hi := (17171/100000 : ℝ)) (c := (36272759973467804133/36275000000000000000 : ℝ)) (alpha := (59308799873/181375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36272759973467804133/36275000000000000000 : ℝ)*(X 0 2+X 1 2)+(59308799873/181375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (2479/25000 : ℝ)) (hi := (17171/100000 : ℝ)) (c := (36272759973467804133/36275000000000000000 : ℝ)) (alpha := (59308799873/181375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-36320953/250000000 : ℝ)*X 0 0+(5477144759/10000000000 : ℝ)*X 0 1+(5136805899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347200809/10000000000 : ℝ)*X 1 0+(-407369871/2500000000 : ℝ)*X 1 1+(5136804471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673599733/5000000000 : ℝ)*X 2 0+(1284201443/2500000000 : ℝ)*X 2 1+(-1629479557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4119090959/10000000000 : ℝ)*X 0 0+(457047703/1250000000 : ℝ)*X 0 1+(4618381449/10000000000 : ℝ)*X 0 2+(4119090959/10000000000 : ℝ)*X 1 0+(457047703/1250000000 : ℝ)*X 1 1+(4618381449/10000000000 : ℝ)*X 1 2+(4119090959/10000000000 : ℝ)*X 2 0+(457047703/1250000000 : ℝ)*X 2 1+(4618381449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-290598923/2000000000 : ℝ)*X 0 0+(2570268857/5000000000 : ℝ)*X 0 1+(2736678589/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((128735413/312500000 : ℝ)*X 0 0+(2303915951/5000000000 : ℝ)*X 0 1+(3667088459/10000000000 : ℝ)*X 0 2+(128735413/312500000 : ℝ)*X 1 0+(2303915951/5000000000 : ℝ)*X 1 1+(3667088459/10000000000 : ℝ)*X 1 2+(128735413/312500000 : ℝ)*X 2 0+(2303915951/5000000000 : ℝ)*X 2 1+(3667088459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s4_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14854645956532006360117732239/1813750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1522535789/100000000000000 : ℝ)*(base19) + (12102609/2000000000000 : ℝ)*(base23) + (47973731/50000000000000 : ℝ)*(lower2) + (303223997/100000000000000 : ℝ)*(upper3) + (390077/1250000000000 : ℝ)*(upper5) + (1988880444528613/100000000000000 : ℝ)*(major0) + (1988880444528613/100000000000000 : ℝ)*(major1) + (1988880444528613/100000000000000 : ℝ)*(major2) + (1469127351034469/50000000000000 : ℝ)*(sp0) + (2938253703437881/100000000000000 : ℝ)*(sp1) + (146912731042161/5000000000000 : ℝ)*(sp2) + (1039502754867229/100000000000000 : ℝ)*(sp3) + (130976183/25000000000000 : ℝ)*(sp4) + (2635215701/100000000000000 : ℝ)*(sp5) + (103950539008293/10000000000000 : ℝ)*(f.failure) + (293825522597367/10000000000000 : ℝ)*(f.sum) + (189639957353671/36275000000000000000000000000 : ℝ)*base65 + (29372892303657957529/3627500000000000000000000000000000 : ℝ)*base67 + (10240335136532957529/3627500000000000000000000000000000 : ℝ)*base69 + (25380825042237957529/3627500000000000000000000000000000 : ℝ)*base71 + (29771875268623/18137500000000000000000000000 : ℝ)*base73 + (4842127625925457529/3627500000000000000000000000000000 : ℝ)*base75 + (43194480737885457529/3627500000000000000000000000000000 : ℝ)*base77 + (27955964504282957529/3627500000000000000000000000000000 : ℝ)*base79 + (29149339071601/9068750000000000000000000000 : ℝ)*base82 + (6236543/500000000000000000000 : ℝ)*base90 + (6236543/500000000000000000000 : ℝ)*base92 + (6236543/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1699_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17171/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2479/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9917/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17171/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1699_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1699_box_0 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1125447129/10000000000 : ℝ)*x 0 + (2118407/3906250 : ℝ)*x 1 + (5423121923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1125447129/10000000000 : ℝ)^5215 ≤ (6599825043109/100000000000000 : ℝ)^4191 := by
    have hnat : (1125447129 : ℕ)^5215*100000000000000^4191 ≤ 6599825043109^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125447129 10000000000 6599825043109 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118407/3906250 : ℝ)^5215 ≤ (5837510931451/12500000000000 : ℝ)^4191 := by
    have hnat : (2118407 : ℕ)^5215*12500000000000^4191 ≤ 5837510931451^4191*3906250^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118407 3906250 5837510931451 12500000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423121923/10000000000 : ℝ)^5215 ≤ (23350043741877/50000000000000 : ℝ)^4191 := by
    have hnat : (5423121923 : ℕ)^5215*50000000000000^4191 ≤ 23350043741877^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423121923 10000000000 23350043741877 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1125447129/10000000000 : ℝ), (2118407/3906250 : ℝ), (5423121923/10000000000 : ℝ)] ![(6599825043109/100000000000000 : ℝ), (5837510931451/12500000000000 : ℝ), (23350043741877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1125447129/10000000000 : ℝ)|^5215 ≤ (6599825043109/100000000000000 : ℝ)^4191
        have hw : |(-1125447129/10000000000 : ℝ)|=(1125447129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2118407/3906250 : ℝ)|^5215 ≤ (5837510931451/12500000000000 : ℝ)^4191
        have hw : |(2118407/3906250 : ℝ)|=(2118407/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423121923/10000000000 : ℝ)|^5215 ≤ (23350043741877/50000000000000 : ℝ)^4191
        have hw : |(5423121923/10000000000 : ℝ)|=(5423121923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_1 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653229803/1250000000 : ℝ)*x 0 + (-1405801807/10000000000 : ℝ)*x 1 + (5423121887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653229803/1250000000 : ℝ)^5215 ≤ (44595614808109/100000000000000 : ℝ)^4191 := by
    have hnat : (653229803 : ℕ)^5215*100000000000000^4191 ≤ 44595614808109^4191*1250000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653229803 1250000000 44595614808109 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1405801807/10000000000 : ℝ)^5215 ≤ (8704298077193/100000000000000 : ℝ)^4191 := by
    have hnat : (1405801807 : ℕ)^5215*100000000000000^4191 ≤ 8704298077193^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405801807 10000000000 8704298077193 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423121887/10000000000 : ℝ)^5215 ≤ (46700087098003/100000000000000 : ℝ)^4191 := by
    have hnat : (5423121887 : ℕ)^5215*100000000000000^4191 ≤ 46700087098003^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423121887 10000000000 46700087098003 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653229803/1250000000 : ℝ), (-1405801807/10000000000 : ℝ), (5423121887/10000000000 : ℝ)] ![(44595614808109/100000000000000 : ℝ), (8704298077193/100000000000000 : ℝ), (46700087098003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653229803/1250000000 : ℝ)|^5215 ≤ (44595614808109/100000000000000 : ℝ)^4191
        have hw : |(653229803/1250000000 : ℝ)|=(653229803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1405801807/10000000000 : ℝ)|^5215 ≤ (8704298077193/100000000000000 : ℝ)^4191
        have hw : |(-1405801807/10000000000 : ℝ)|=(1405801807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423121887/10000000000 : ℝ)|^5215 ≤ (46700087098003/100000000000000 : ℝ)^4191
        have hw : |(5423121887/10000000000 : ℝ)|=(5423121887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_2 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306459607/2500000000 : ℝ)*x 0 + (5423121867/10000000000 : ℝ)*x 1 + (-1405801829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306459607/2500000000 : ℝ)^5215 ≤ (5574451856323/12500000000000 : ℝ)^4191 := by
    have hnat : (1306459607 : ℕ)^5215*12500000000000^4191 ≤ 5574451856323^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306459607 2500000000 5574451856323 12500000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423121867/10000000000 : ℝ)^5215 ≤ (2918755430231/6250000000000 : ℝ)^4191 := by
    have hnat : (5423121867 : ℕ)^5215*6250000000000^4191 ≤ 2918755430231^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423121867 10000000000 2918755430231 6250000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1405801829/10000000000 : ℝ)^5215 ≤ (8704298246693/100000000000000 : ℝ)^4191 := by
    have hnat : (1405801829 : ℕ)^5215*100000000000000^4191 ≤ 8704298246693^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405801829 10000000000 8704298246693 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306459607/2500000000 : ℝ), (5423121867/10000000000 : ℝ), (-1405801829/10000000000 : ℝ)] ![(5574451856323/12500000000000 : ℝ), (2918755430231/6250000000000 : ℝ), (8704298246693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306459607/2500000000 : ℝ)|^5215 ≤ (5574451856323/12500000000000 : ℝ)^4191
        have hw : |(1306459607/2500000000 : ℝ)|=(1306459607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423121867/10000000000 : ℝ)|^5215 ≤ (2918755430231/6250000000000 : ℝ)^4191
        have hw : |(5423121867/10000000000 : ℝ)|=(5423121867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1405801829/10000000000 : ℝ)|^5215 ≤ (8704298246693/100000000000000 : ℝ)^4191
        have hw : |(-1405801829/10000000000 : ℝ)|=(1405801829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_3 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (56277693/125000000 : ℝ)*x 0 + (3949690599/10000000000 : ℝ)*x 1 + (1974845313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56277693/125000000 : ℝ)^5215 ≤ (7409294162701/20000000000000 : ℝ)^4191 := by
    have hnat : (56277693 : ℕ)^5215*20000000000000^4191 ≤ 7409294162701^4191*125000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56277693 125000000 7409294162701 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3949690599/10000000000 : ℝ)^5215 ≤ (983648889217/3125000000000 : ℝ)^4191 := by
    have hnat : (3949690599 : ℕ)^5215*3125000000000^4191 ≤ 983648889217^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3949690599 10000000000 983648889217 3125000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1974845313/5000000000 : ℝ)^5215 ≤ (31476764722693/100000000000000 : ℝ)^4191 := by
    have hnat : (1974845313 : ℕ)^5215*100000000000000^4191 ≤ 31476764722693^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974845313 5000000000 31476764722693 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(56277693/125000000 : ℝ), (3949690599/10000000000 : ℝ), (1974845313/5000000000 : ℝ)] ![(7409294162701/20000000000000 : ℝ), (983648889217/3125000000000 : ℝ), (31476764722693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(56277693/125000000 : ℝ)|^5215 ≤ (7409294162701/20000000000000 : ℝ)^4191
        have hw : |(56277693/125000000 : ℝ)|=(56277693/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3949690599/10000000000 : ℝ)|^5215 ≤ (983648889217/3125000000000 : ℝ)^4191
        have hw : |(3949690599/10000000000 : ℝ)|=(3949690599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1974845313/5000000000 : ℝ)|^5215 ≤ (31476764722693/100000000000000 : ℝ)^4191
        have hw : |(1974845313/5000000000 : ℝ)|=(1974845313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_4 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-900518553/5000000000 : ℝ)*x 0 + (258843889/500000000 : ℝ)*x 1 + (5176877851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (900518553/5000000000 : ℝ)^5215 ≤ (5923688495237/50000000000000 : ℝ)^4191 := by
    have hnat : (900518553 : ℕ)^5215*50000000000000^4191 ≤ 5923688495237^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900518553 5000000000 5923688495237 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258843889/500000000 : ℝ)^5215 ≤ (11019077780371/25000000000000 : ℝ)^4191 := by
    have hnat : (258843889 : ℕ)^5215*25000000000000^4191 ≤ 11019077780371^4191*500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258843889 500000000 11019077780371 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176877851/10000000000 : ℝ)^5215 ≤ (44076311873683/100000000000000 : ℝ)^4191 := by
    have hnat : (5176877851 : ℕ)^5215*100000000000000^4191 ≤ 44076311873683^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176877851 10000000000 44076311873683 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-900518553/5000000000 : ℝ), (258843889/500000000 : ℝ), (5176877851/10000000000 : ℝ)] ![(5923688495237/50000000000000 : ℝ), (11019077780371/25000000000000 : ℝ), (44076311873683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-900518553/5000000000 : ℝ)|^5215 ≤ (5923688495237/50000000000000 : ℝ)^4191
        have hw : |(-900518553/5000000000 : ℝ)|=(900518553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258843889/500000000 : ℝ)|^5215 ≤ (11019077780371/25000000000000 : ℝ)^4191
        have hw : |(258843889/500000000 : ℝ)|=(258843889/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176877851/10000000000 : ℝ)|^5215 ≤ (44076311873683/100000000000000 : ℝ)^4191
        have hw : |(5176877851/10000000000 : ℝ)|=(5176877851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_5 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337080107/625000000 : ℝ)*x 0 + (-756842541/5000000000 : ℝ)*x 1 + (5176877617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337080107/625000000 : ℝ)^5215 ≤ (46380555433267/100000000000000 : ℝ)^4191 := by
    have hnat : (337080107 : ℕ)^5215*100000000000000^4191 ≤ 46380555433267^4191*625000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337080107 625000000 46380555433267 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (756842541/5000000000 : ℝ)^5215 ≤ (9543135152481/100000000000000 : ℝ)^4191 := by
    have hnat : (756842541 : ℕ)^5215*100000000000000^4191 ≤ 9543135152481^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756842541 5000000000 9543135152481 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176877617/10000000000 : ℝ)^5215 ≤ (44076309394607/100000000000000 : ℝ)^4191 := by
    have hnat : (5176877617 : ℕ)^5215*100000000000000^4191 ≤ 44076309394607^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176877617 10000000000 44076309394607 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337080107/625000000 : ℝ), (-756842541/5000000000 : ℝ), (5176877617/10000000000 : ℝ)] ![(46380555433267/100000000000000 : ℝ), (9543135152481/100000000000000 : ℝ), (44076309394607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337080107/625000000 : ℝ)|^5215 ≤ (46380555433267/100000000000000 : ℝ)^4191
        have hw : |(337080107/625000000 : ℝ)|=(337080107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-756842541/5000000000 : ℝ)|^5215 ≤ (9543135152481/100000000000000 : ℝ)^4191
        have hw : |(-756842541/5000000000 : ℝ)|=(756842541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176877617/10000000000 : ℝ)|^5215 ≤ (44076309394607/100000000000000 : ℝ)^4191
        have hw : |(5176877617/10000000000 : ℝ)|=(5176877617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_6 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539328133/1000000000 : ℝ)*x 0 + (2588439099/5000000000 : ℝ)*x 1 + (-1513684819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539328133/1000000000 : ℝ)^5215 ≤ (46380551345531/100000000000000 : ℝ)^4191 := by
    have hnat : (539328133 : ℕ)^5215*100000000000000^4191 ≤ 46380551345531^4191*1000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539328133 1000000000 46380551345531 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588439099/5000000000 : ℝ)^5215 ≤ (44076315549919/100000000000000 : ℝ)^4191 := by
    have hnat : (2588439099 : ℕ)^5215*100000000000000^4191 ≤ 44076315549919^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588439099 5000000000 44076315549919 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1513684819/10000000000 : ℝ)^5215 ≤ (9543133089249/100000000000000 : ℝ)^4191 := by
    have hnat : (1513684819 : ℕ)^5215*100000000000000^4191 ≤ 9543133089249^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513684819 10000000000 9543133089249 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539328133/1000000000 : ℝ), (2588439099/5000000000 : ℝ), (-1513684819/10000000000 : ℝ)] ![(46380551345531/100000000000000 : ℝ), (44076315549919/100000000000000 : ℝ), (9543133089249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539328133/1000000000 : ℝ)|^5215 ≤ (46380551345531/100000000000000 : ℝ)^4191
        have hw : |(539328133/1000000000 : ℝ)|=(539328133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588439099/5000000000 : ℝ)|^5215 ≤ (44076315549919/100000000000000 : ℝ)^4191
        have hw : |(2588439099/5000000000 : ℝ)|=(2588439099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1513684819/10000000000 : ℝ)|^5215 ≤ (9543133089249/100000000000000 : ℝ)^4191
        have hw : |(-1513684819/10000000000 : ℝ)|=(1513684819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_7 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3720898377/10000000000 : ℝ)*x 0 + (271218989/625000000 : ℝ)*x 1 + (2169751993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3720898377/10000000000 : ℝ)^5215 ≤ (7306053836577/25000000000000 : ℝ)^4191 := by
    have hnat : (3720898377 : ℕ)^5215*25000000000000^4191 ≤ 7306053836577^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3720898377 10000000000 7306053836577 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271218989/625000000 : ℝ)^5215 ≤ (8846972874219/25000000000000 : ℝ)^4191 := by
    have hnat : (271218989 : ℕ)^5215*25000000000000^4191 ≤ 8846972874219^4191*625000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271218989 625000000 8846972874219 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2169751993/5000000000 : ℝ)^5215 ≤ (17693946570371/50000000000000 : ℝ)^4191 := by
    have hnat : (2169751993 : ℕ)^5215*50000000000000^4191 ≤ 17693946570371^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169751993 5000000000 17693946570371 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3720898377/10000000000 : ℝ), (271218989/625000000 : ℝ), (2169751993/5000000000 : ℝ)] ![(7306053836577/25000000000000 : ℝ), (8846972874219/25000000000000 : ℝ), (17693946570371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3720898377/10000000000 : ℝ)|^5215 ≤ (7306053836577/25000000000000 : ℝ)^4191
        have hw : |(3720898377/10000000000 : ℝ)|=(3720898377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271218989/625000000 : ℝ)|^5215 ≤ (8846972874219/25000000000000 : ℝ)^4191
        have hw : |(271218989/625000000 : ℝ)|=(271218989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2169751993/5000000000 : ℝ)|^5215 ≤ (17693946570371/50000000000000 : ℝ)^4191
        have hw : |(2169751993/5000000000 : ℝ)|=(2169751993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_8 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1655909429/10000000000 : ℝ)*x 0 + (1248925881/2500000000 : ℝ)*x 1 + (5466321273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1655909429/10000000000 : ℝ)^5215 ≤ (2667849819161/25000000000000 : ℝ)^4191 := by
    have hnat : (1655909429 : ℕ)^5215*25000000000000^4191 ≤ 2667849819161^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655909429 10000000000 2667849819161 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1248925881/2500000000 : ℝ)^5215 ≤ (4216516897889/10000000000000 : ℝ)^4191 := by
    have hnat : (1248925881 : ℕ)^5215*10000000000000^4191 ≤ 4216516897889^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248925881 2500000000 4216516897889 10000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466321273/10000000000 : ℝ)^5215 ≤ (11790857932453/25000000000000 : ℝ)^4191 := by
    have hnat : (5466321273 : ℕ)^5215*25000000000000^4191 ≤ 11790857932453^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466321273 10000000000 11790857932453 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1655909429/10000000000 : ℝ), (1248925881/2500000000 : ℝ), (5466321273/10000000000 : ℝ)] ![(2667849819161/25000000000000 : ℝ), (4216516897889/10000000000000 : ℝ), (11790857932453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1655909429/10000000000 : ℝ)|^5215 ≤ (2667849819161/25000000000000 : ℝ)^4191
        have hw : |(-1655909429/10000000000 : ℝ)|=(1655909429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1248925881/2500000000 : ℝ)|^5215 ≤ (4216516897889/10000000000000 : ℝ)^4191
        have hw : |(1248925881/2500000000 : ℝ)|=(1248925881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466321273/10000000000 : ℝ)|^5215 ≤ (11790857932453/25000000000000 : ℝ)^4191
        have hw : |(5466321273/10000000000 : ℝ)|=(5466321273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_9 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196478307/10000000000 : ℝ)*x 0 + (-693033231/5000000000 : ℝ)*x 1 + (5466321117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196478307/10000000000 : ℝ)^5215 ≤ (44284061761621/100000000000000 : ℝ)^4191 := by
    have hnat : (5196478307 : ℕ)^5215*100000000000000^4191 ≤ 44284061761621^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196478307 10000000000 44284061761621 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693033231/5000000000 : ℝ)^5215 ≤ (8552508165541/100000000000000 : ℝ)^4191 := by
    have hnat : (693033231 : ℕ)^5215*100000000000000^4191 ≤ 8552508165541^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693033231 5000000000 8552508165541 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466321117/10000000000 : ℝ)^5215 ≤ (47163430054979/100000000000000 : ℝ)^4191 := by
    have hnat : (5466321117 : ℕ)^5215*100000000000000^4191 ≤ 47163430054979^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466321117 10000000000 47163430054979 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196478307/10000000000 : ℝ), (-693033231/5000000000 : ℝ), (5466321117/10000000000 : ℝ)] ![(44284061761621/100000000000000 : ℝ), (8552508165541/100000000000000 : ℝ), (47163430054979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196478307/10000000000 : ℝ)|^5215 ≤ (44284061761621/100000000000000 : ℝ)^4191
        have hw : |(5196478307/10000000000 : ℝ)|=(5196478307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-693033231/5000000000 : ℝ)|^5215 ≤ (8552508165541/100000000000000 : ℝ)^4191
        have hw : |(-693033231/5000000000 : ℝ)|=(693033231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466321117/10000000000 : ℝ)|^5215 ≤ (47163430054979/100000000000000 : ℝ)^4191
        have hw : |(5466321117/10000000000 : ℝ)|=(5466321117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_10 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598239209/5000000000 : ℝ)*x 0 + (1366580283/2500000000 : ℝ)*x 1 + (-1386066289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598239209/5000000000 : ℝ)^5215 ≤ (44284062938679/100000000000000 : ℝ)^4191 := by
    have hnat : (2598239209 : ℕ)^5215*100000000000000^4191 ≤ 44284062938679^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598239209 5000000000 44284062938679 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366580283/2500000000 : ℝ)^5215 ≤ (47163430216021/100000000000000 : ℝ)^4191 := by
    have hnat : (1366580283 : ℕ)^5215*100000000000000^4191 ≤ 47163430216021^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366580283 2500000000 47163430216021 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1386066289/10000000000 : ℝ)^5215 ≤ (8552506837253/100000000000000 : ℝ)^4191 := by
    have hnat : (1386066289 : ℕ)^5215*100000000000000^4191 ≤ 8552506837253^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386066289 10000000000 8552506837253 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598239209/5000000000 : ℝ), (1366580283/2500000000 : ℝ), (-1386066289/10000000000 : ℝ)] ![(44284062938679/100000000000000 : ℝ), (47163430216021/100000000000000 : ℝ), (8552506837253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598239209/5000000000 : ℝ)|^5215 ≤ (44284062938679/100000000000000 : ℝ)^4191
        have hw : |(2598239209/5000000000 : ℝ)|=(2598239209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366580283/2500000000 : ℝ)|^5215 ≤ (47163430216021/100000000000000 : ℝ)^4191
        have hw : |(1366580283/2500000000 : ℝ)|=(1366580283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1386066289/10000000000 : ℝ)|^5215 ≤ (8552506837253/100000000000000 : ℝ)^4191
        have hw : |(-1386066289/10000000000 : ℝ)|=(1386066289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_11 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2317137937/5000000000 : ℝ)*x 0 + (31049011/80000000 : ℝ)*x 1 + (19405621/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2317137937/5000000000 : ℝ)^5215 ≤ (1536137865463/4000000000000 : ℝ)^4191 := by
    have hnat : (2317137937 : ℕ)^5215*4000000000000^4191 ≤ 1536137865463^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317137937 5000000000 1536137865463 4000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31049011/80000000 : ℝ)^5215 ≤ (7699571853677/25000000000000 : ℝ)^4191 := by
    have hnat : (31049011 : ℕ)^5215*25000000000000^4191 ≤ 7699571853677^4191*80000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31049011 80000000 7699571853677 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19405621/50000000 : ℝ)^5215 ≤ (30798265938151/100000000000000 : ℝ)^4191 := by
    have hnat : (19405621 : ℕ)^5215*100000000000000^4191 ≤ 30798265938151^4191*50000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19405621 50000000 30798265938151 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2317137937/5000000000 : ℝ), (31049011/80000000 : ℝ), (19405621/50000000 : ℝ)] ![(1536137865463/4000000000000 : ℝ), (7699571853677/25000000000000 : ℝ), (30798265938151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2317137937/5000000000 : ℝ)|^5215 ≤ (1536137865463/4000000000000 : ℝ)^4191
        have hw : |(2317137937/5000000000 : ℝ)|=(2317137937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31049011/80000000 : ℝ)|^5215 ≤ (7699571853677/25000000000000 : ℝ)^4191
        have hw : |(31049011/80000000 : ℝ)|=(31049011/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19405621/50000000 : ℝ)|^5215 ≤ (30798265938151/100000000000000 : ℝ)^4191
        have hw : |(19405621/50000000 : ℝ)|=(19405621/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_12 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-126545797/1000000000 : ℝ)*x 0 + (5595499449/10000000000 : ℝ)*x 1 + (1030329423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126545797/1000000000 : ℝ)^5215 ≤ (1527309768641/20000000000000 : ℝ)^4191 := by
    have hnat : (126545797 : ℕ)^5215*20000000000000^4191 ≤ 1527309768641^4191*1000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126545797 1000000000 1527309768641 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5595499449/10000000000 : ℝ)^5215 ≤ (48554282961769/100000000000000 : ℝ)^4191 := by
    have hnat : (5595499449 : ℕ)^5215*100000000000000^4191 ≤ 48554282961769^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595499449 10000000000 48554282961769 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030329423/2000000000 : ℝ)^5215 ≤ (43809168181953/100000000000000 : ℝ)^4191 := by
    have hnat : (1030329423 : ℕ)^5215*100000000000000^4191 ≤ 43809168181953^4191*2000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030329423 2000000000 43809168181953 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126545797/1000000000 : ℝ), (5595499449/10000000000 : ℝ), (1030329423/2000000000 : ℝ)] ![(1527309768641/20000000000000 : ℝ), (48554282961769/100000000000000 : ℝ), (43809168181953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126545797/1000000000 : ℝ)|^5215 ≤ (1527309768641/20000000000000 : ℝ)^4191
        have hw : |(-126545797/1000000000 : ℝ)|=(126545797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5595499449/10000000000 : ℝ)|^5215 ≤ (48554282961769/100000000000000 : ℝ)^4191
        have hw : |(5595499449/10000000000 : ℝ)|=(5595499449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030329423/2000000000 : ℝ)|^5215 ≤ (43809168181953/100000000000000 : ℝ)^4191
        have hw : |(1030329423/2000000000 : ℝ)|=(1030329423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_13 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10567319/19531250 : ℝ)*x 0 + (-1524277641/10000000000 : ℝ)*x 1 + (1287911757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10567319/19531250 : ℝ)^5215 ≤ (5820566022351/12500000000000 : ℝ)^4191 := by
    have hnat : (10567319 : ℕ)^5215*12500000000000^4191 ≤ 5820566022351^4191*19531250^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10567319 19531250 5820566022351 12500000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1524277641/10000000000 : ℝ)^5215 ≤ (120328806879/1250000000000 : ℝ)^4191 := by
    have hnat : (1524277641 : ℕ)^5215*1250000000000^4191 ≤ 120328806879^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1524277641 10000000000 120328806879 1250000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287911757/2500000000 : ℝ)^5215 ≤ (8761833452269/20000000000000 : ℝ)^4191 := by
    have hnat : (1287911757 : ℕ)^5215*20000000000000^4191 ≤ 8761833452269^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287911757 2500000000 8761833452269 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10567319/19531250 : ℝ), (-1524277641/10000000000 : ℝ), (1287911757/2500000000 : ℝ)] ![(5820566022351/12500000000000 : ℝ), (120328806879/1250000000000 : ℝ), (8761833452269/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10567319/19531250 : ℝ)|^5215 ≤ (5820566022351/12500000000000 : ℝ)^4191
        have hw : |(10567319/19531250 : ℝ)|=(10567319/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1524277641/10000000000 : ℝ)|^5215 ≤ (120328806879/1250000000000 : ℝ)^4191
        have hw : |(-1524277641/10000000000 : ℝ)|=(1524277641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1287911757/2500000000 : ℝ)|^5215 ≤ (8761833452269/20000000000000 : ℝ)^4191
        have hw : |(1287911757/2500000000 : ℝ)|=(1287911757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_14 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2705233519/5000000000 : ℝ)*x 0 + (643955927/1250000000 : ℝ)*x 1 + (-762138757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705233519/5000000000 : ℝ)^5215 ≤ (2328226253657/5000000000000 : ℝ)^4191 := by
    have hnat : (2705233519 : ℕ)^5215*5000000000000^4191 ≤ 2328226253657^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705233519 5000000000 2328226253657 5000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643955927/1250000000 : ℝ)^5215 ≤ (21904585683523/50000000000000 : ℝ)^4191 := by
    have hnat : (643955927 : ℕ)^5215*50000000000000^4191 ≤ 21904585683523^4191*1250000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643955927 1250000000 21904585683523 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (762138757/5000000000 : ℝ)^5215 ≤ (2406575888077/25000000000000 : ℝ)^4191 := by
    have hnat : (762138757 : ℕ)^5215*25000000000000^4191 ≤ 2406575888077^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762138757 5000000000 2406575888077 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705233519/5000000000 : ℝ), (643955927/1250000000 : ℝ), (-762138757/5000000000 : ℝ)] ![(2328226253657/5000000000000 : ℝ), (21904585683523/50000000000000 : ℝ), (2406575888077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705233519/5000000000 : ℝ)|^5215 ≤ (2328226253657/5000000000000 : ℝ)^4191
        have hw : |(2705233519/5000000000 : ℝ)|=(2705233519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643955927/1250000000 : ℝ)|^5215 ≤ (21904585683523/50000000000000 : ℝ)^4191
        have hw : |(643955927/1250000000 : ℝ)|=(643955927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-762138757/5000000000 : ℝ)|^5215 ≤ (2406575888077/25000000000000 : ℝ)^4191
        have hw : |(-762138757/5000000000 : ℝ)|=(762138757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_box_15 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (145514349/400000000 : ℝ)*x 0 + (4379338187/10000000000 : ℝ)*x 1 + (875867671/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (145514349/400000000 : ℝ)^5215 ≤ (28414886903163/100000000000000 : ℝ)^4191 := by
    have hnat : (145514349 : ℕ)^5215*100000000000000^4191 ≤ 28414886903163^4191*400000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145514349 400000000 28414886903163 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4379338187/10000000000 : ℝ)^5215 ≤ (8948138922067/25000000000000 : ℝ)^4191 := by
    have hnat : (4379338187 : ℕ)^5215*25000000000000^4191 ≤ 8948138922067^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379338187 10000000000 8948138922067 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (875867671/2000000000 : ℝ)^5215 ≤ (8948139349207/25000000000000 : ℝ)^4191 := by
    have hnat : (875867671 : ℕ)^5215*25000000000000^4191 ≤ 8948139349207^4191*2000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875867671 2000000000 8948139349207 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(145514349/400000000 : ℝ), (4379338187/10000000000 : ℝ), (875867671/2000000000 : ℝ)] ![(28414886903163/100000000000000 : ℝ), (8948138922067/25000000000000 : ℝ), (8948139349207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(145514349/400000000 : ℝ)|^5215 ≤ (28414886903163/100000000000000 : ℝ)^4191
        have hw : |(145514349/400000000 : ℝ)|=(145514349/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4379338187/10000000000 : ℝ)|^5215 ≤ (8948138922067/25000000000000 : ℝ)^4191
        have hw : |(4379338187/10000000000 : ℝ)|=(4379338187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(875867671/2000000000 : ℝ)|^5215 ≤ (8948139349207/25000000000000 : ℝ)^4191
        have hw : |(875867671/2000000000 : ℝ)|=(875867671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1699_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17171/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9917/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(8331/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1817/3125 : ℝ) ∧ (20279/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (18053/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17171/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9917/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17171/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9917/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17171/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9917/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17171/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9917/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17171/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9917/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17171/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9917/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9917/100000 : ℝ) ^ (5207/1024 : ℝ) ≤ (78819394943843/10000000000000000000 : ℝ) := by
    have hpowers : (9917/100000 : ℝ)^5207 ≤ (78819394943843/10000000000000000000 : ℝ)^1024 := by
      have hnat : (9917 : ℕ)^5207*10000000000000000000^1024 ≤ 78819394943843^1024*100000^5207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9917 100000 78819394943843 10000000000000000000 5207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9917/100000 : ℝ)) (X := (78819394943843/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17171/100000 : ℝ) ^ (5207/1024 : ℝ) ≤ (6425922171638499/50000000000000000000 : ℝ) := by
    have hpowers : (17171/100000 : ℝ)^5207 ≤ (6425922171638499/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17171 : ℕ)^5207*50000000000000000000^1024 ≤ 6425922171638499^1024*100000^5207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17171 100000 6425922171638499 50000000000000000000 5207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17171/100000 : ℝ)) (X := (6425922171638499/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000078819394943843/5000000000000000000 : ℝ) ≤ (5000015500393581/5000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (5000078819394943843/5000000000000000000 : ℝ)^1024 ≤ (5000015500393581/5000000000000000 : ℝ)^5207 := by
      have hnat : (5000078819394943843 : ℕ)^1024*5000000000000000^5207 ≤ 5000015500393581^5207*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000078819394943843 5000000000000000000 5000015500393581 5000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000015500393581/5000000000000000 : ℝ)) (X := (5000078819394943843/5000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25003410009573178857/25000000000000000000 : ℝ) ≤ (10000268228039713/10000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (25003410009573178857/25000000000000000000 : ℝ)^1024 ≤ (10000268228039713/10000000000000000 : ℝ)^5207 := by
      have hnat : (25003410009573178857 : ℕ)^1024*10000000000000000^5207 ≤ 10000268228039713^5207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003410009573178857 25000000000000000000 10000268228039713 10000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000268228039713/10000000000000000 : ℝ)) (X := (25003410009573178857/25000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25006425922171638499/25000000000000000000 : ℝ) ≤ (1250063181911533/1250000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (25006425922171638499/25000000000000000000 : ℝ)^1024 ≤ (1250063181911533/1250000000000000 : ℝ)^5207 := by
      have hnat : (25006425922171638499 : ℕ)^1024*1250000000000000^5207 ≤ 1250063181911533^5207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006425922171638499 25000000000000000000 1250063181911533 1250000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250063181911533/1250000000000000 : ℝ)) (X := (25006425922171638499/25000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(78819394943843/10000000000000000000 : ℝ) ≤ ((36267759857191488307/36270000000000000000 : ℝ)+2*(237227252551/725400000000000 : ℝ)*(9917/100000 : ℝ))^(5207/1024 : ℝ) := by
    rw [show (36267759857191488307/36270000000000000000 : ℝ)+2*(237227252551/725400000000000 : ℝ)*(9917/100000 : ℝ)=(5000015500393581/5000000000000000 : ℝ) by norm_num, show 1+2*(78819394943843/10000000000000000000 : ℝ)=(5000078819394943843/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6425922171638499/50000000000000000000 : ℝ)+(78819394943843/10000000000000000000 : ℝ) ≤ ((36267759857191488307/36270000000000000000 : ℝ)+(237227252551/725400000000000 : ℝ)*((17171/100000 : ℝ)+(9917/100000 : ℝ)))^(5207/1024 : ℝ) := by
    rw [show (36267759857191488307/36270000000000000000 : ℝ)+(237227252551/725400000000000 : ℝ)*((17171/100000 : ℝ)+(9917/100000 : ℝ))=(10000268228039713/10000000000000000 : ℝ) by norm_num, show 1+(6425922171638499/50000000000000000000 : ℝ)+(78819394943843/10000000000000000000 : ℝ)=(25003410009573178857/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6425922171638499/50000000000000000000 : ℝ) ≤ ((36267759857191488307/36270000000000000000 : ℝ)+2*(237227252551/725400000000000 : ℝ)*(17171/100000 : ℝ))^(5207/1024 : ℝ) := by
    rw [show (36267759857191488307/36270000000000000000 : ℝ)+2*(237227252551/725400000000000 : ℝ)*(17171/100000 : ℝ)=(1250063181911533/1250000000000000 : ℝ) by norm_num, show 1+2*(6425922171638499/50000000000000000000 : ℝ)=(25006425922171638499/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36267759857191488307/36270000000000000000 : ℝ)*(X 1 0+X 2 0)+(237227252551/725400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (9917/100000 : ℝ)) (hi := (17171/100000 : ℝ)) (c := (36267759857191488307/36270000000000000000 : ℝ)) (alpha := (237227252551/725400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36267759857191488307/36270000000000000000 : ℝ)*(X 0 1+X 2 1)+(237227252551/725400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (9917/100000 : ℝ)) (hi := (17171/100000 : ℝ)) (c := (36267759857191488307/36270000000000000000 : ℝ)) (alpha := (237227252551/725400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36267759857191488307/36270000000000000000 : ℝ)*(X 0 2+X 1 2)+(237227252551/725400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (9917/100000 : ℝ)) (hi := (17171/100000 : ℝ)) (c := (36267759857191488307/36270000000000000000 : ℝ)) (alpha := (237227252551/725400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1125447129/10000000000 : ℝ)*X 0 0+(2118407/3906250 : ℝ)*X 0 1+(5423121923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((653229803/1250000000 : ℝ)*X 1 0+(-1405801807/10000000000 : ℝ)*X 1 1+(5423121887/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1306459607/2500000000 : ℝ)*X 2 0+(5423121867/10000000000 : ℝ)*X 2 1+(-1405801829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((56277693/125000000 : ℝ)*X 0 0+(3949690599/10000000000 : ℝ)*X 0 1+(1974845313/5000000000 : ℝ)*X 0 2+(56277693/125000000 : ℝ)*X 1 0+(3949690599/10000000000 : ℝ)*X 1 1+(1974845313/5000000000 : ℝ)*X 1 2+(56277693/125000000 : ℝ)*X 2 0+(3949690599/10000000000 : ℝ)*X 2 1+(1974845313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-900518553/5000000000 : ℝ)*X 0 0+(258843889/500000000 : ℝ)*X 0 1+(5176877851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((337080107/625000000 : ℝ)*X 1 0+(-756842541/5000000000 : ℝ)*X 1 1+(5176877617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((539328133/1000000000 : ℝ)*X 2 0+(2588439099/5000000000 : ℝ)*X 2 1+(-1513684819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3720898377/10000000000 : ℝ)*X 0 0+(271218989/625000000 : ℝ)*X 0 1+(2169751993/5000000000 : ℝ)*X 0 2+(3720898377/10000000000 : ℝ)*X 1 0+(271218989/625000000 : ℝ)*X 1 1+(2169751993/5000000000 : ℝ)*X 1 2+(3720898377/10000000000 : ℝ)*X 2 0+(271218989/625000000 : ℝ)*X 2 1+(2169751993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1655909429/10000000000 : ℝ)*X 0 0+(1248925881/2500000000 : ℝ)*X 0 1+(5466321273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196478307/10000000000 : ℝ)*X 1 0+(-693033231/5000000000 : ℝ)*X 1 1+(5466321117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2598239209/5000000000 : ℝ)*X 2 0+(1366580283/2500000000 : ℝ)*X 2 1+(-1386066289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2317137937/5000000000 : ℝ)*X 0 0+(31049011/80000000 : ℝ)*X 0 1+(19405621/50000000 : ℝ)*X 0 2+(2317137937/5000000000 : ℝ)*X 1 0+(31049011/80000000 : ℝ)*X 1 1+(19405621/50000000 : ℝ)*X 1 2+(2317137937/5000000000 : ℝ)*X 2 0+(31049011/80000000 : ℝ)*X 2 1+(19405621/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-126545797/1000000000 : ℝ)*X 0 0+(5595499449/10000000000 : ℝ)*X 0 1+(1030329423/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((10567319/19531250 : ℝ)*X 1 0+(-1524277641/10000000000 : ℝ)*X 1 1+(1287911757/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2705233519/5000000000 : ℝ)*X 2 0+(643955927/1250000000 : ℝ)*X 2 1+(-762138757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((145514349/400000000 : ℝ)*X 0 0+(4379338187/10000000000 : ℝ)*X 0 1+(875867671/2000000000 : ℝ)*X 0 2+(145514349/400000000 : ℝ)*X 1 0+(4379338187/10000000000 : ℝ)*X 1 1+(875867671/2000000000 : ℝ)*X 1 2+(145514349/400000000 : ℝ)*X 2 0+(4379338187/10000000000 : ℝ)*X 2 1+(875867671/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-8331/12500 : ℝ) ≤ (-25179402279844419140117157166199/37781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (704097/20000000000000 : ℝ)*(lower0) + (45787521/100000000000000 : ℝ)*(lower2) + (23615011/100000000000000 : ℝ)*(lower3) + (64961/125000000000 : ℝ)*(lower4) + (166081487845093/12500000000000 : ℝ)*(major0) + (166081487845093/12500000000000 : ℝ)*(major1) + (166081487845093/12500000000000 : ℝ)*(major2) + (28980419/3125000000000 : ℝ)*(sp1) + (397017518498279/20000000000000 : ℝ)*(sp4) + (1985086665117987/100000000000000 : ℝ)*(sp5) + (1985056100730123/100000000000000 : ℝ)*(sp6) + (34721140946799/5000000000000 : ℝ)*(sp7) + (3936470159/12500000000000 : ℝ)*(sp14) + (847192579/10000000000000 : ℝ)*(sp15) + (69443129086177/10000000000000 : ℝ)*(f.failure) + (397017518498279/20000000000000 : ℝ)*(f.sum) + (9172211175241/2266875000000000000000000000 : ℝ)*base66 + (8724849914056693/4875000000000000000000000000000 : ℝ)*base68 + (5931103776568307/4875000000000000000000000000000 : ℝ)*base69 + (28515261444556693/4875000000000000000000000000000 : ℝ)*base72 + (6461465547391/2266875000000000000000000000 : ℝ)*base74 + (52401657181693/4875000000000000000000000000000 : ℝ)*base76 + (8692893245806693/4875000000000000000000000000000 : ℝ)*base78 + (9756050893306693/4875000000000000000000000000000 : ℝ)*base80 + (53376315588997/18135000000000000000000000000 : ℝ)*base81 + (2074573/500000000000000000000 : ℝ)*base89 + (2074573/500000000000000000000 : ℝ)*base91 + (2074573/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1817/3125 : ℝ) ≤ (58582178369639510814932626857653/100750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21759/20000000000000 : ℝ)*(lower0) + (731583/12500000000000 : ℝ)*(lower1) + (3274183/50000000000000 : ℝ)*(lower3) + (7158457/50000000000000 : ℝ)*(lower5) + (715141724780837/50000000000000 : ℝ)*(major0) + (715141724780837/50000000000000 : ℝ)*(major1) + (715141724780837/50000000000000 : ℝ)*(major2) + (130852170670081/6250000000000 : ℝ)*(sp0) + (2093634982729317/100000000000000 : ℝ)*(sp1) + (2093634697493017/100000000000000 : ℝ)*(sp2) + (186887396664463/25000000000000 : ℝ)*(sp3) + (75538291/25000000000000 : ℝ)*(sp7) + (2852363/1000000000000 : ℝ)*(sp10) + (12600401/5000000000000 : ℝ)*(sp12) + (93443736101377/12500000000000 : ℝ)*(f.failure) + (2093634982729317/100000000000000 : ℝ)*(f.sum) + (39390321168553/18135000000000000000000000000 : ℝ)*base66 + (85691848877435237/19500000000000000000000000000000 : ℝ)*base68 + (47520065412564763/19500000000000000000000000000000 : ℝ)*base69 + (144484433351435237/19500000000000000000000000000000 : ℝ)*base72 + (1441035488647/4533750000000000000000000000 : ℝ)*base74 + (147187945328064763/19500000000000000000000000000000 : ℝ)*base75 + (131040241577435237/19500000000000000000000000000000 : ℝ)*base78 + (477134947137935237/19500000000000000000000000000000 : ℝ)*base80 + (8110677992159/9067500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (6759373/625000000000000000000 : ℝ)*base89 + (6759373/625000000000000000000 : ℝ)*base91 + (6759373/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20279/25000 : ℝ) ≤ (10215905424225311270250314009349/12593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87618207/100000000000000 : ℝ)*(upper1) + (30951701/50000000000000 : ℝ)*(upper3) + (79668657/100000000000000 : ℝ)*(upper4) + (4250167/25000000000000 : ℝ)*(lower5) + (182076218704821/12500000000000 : ℝ)*(major0) + (182076218704821/12500000000000 : ℝ)*(major1) + (182076218704821/12500000000000 : ℝ)*(major2) + (860333733/50000000000000 : ℝ)*(sp0) + (4775423849/25000000000000 : ℝ)*(sp2) + (296431569/12500000000000 : ℝ)*(sp3) + (1062434303181691/50000000000000 : ℝ)*(sp8) + (33201098859857/1562500000000 : ℝ)*(sp9) + (2124851225335453/100000000000000 : ℝ)*(sp10) + (761307183459137/100000000000000 : ℝ)*(sp11) + (761309554911689/100000000000000 : ℝ)*(f.failure) + (33201098859857/1562500000000 : ℝ)*(f.sum) + (11427123545671/3022500000000000000000000000 : ℝ)*base66 + (28931260344355007/1625000000000000000000000000000 : ℝ)*base68 + (12966554192480007/1625000000000000000000000000000 : ℝ)*base70 + (545804085769993/1625000000000000000000000000000 : ℝ)*base71 + (13327010460287/6045000000000000000000000000 : ℝ)*base74 + (4972423261980007/1625000000000000000000000000000 : ℝ)*base76 + (14632372736480007/1625000000000000000000000000000 : ℝ)*base78 + (14576179734355007/1625000000000000000000000000000 : ℝ)*base80 + (23242578646967/6045000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (45351061/5000000000000000000000 : ℝ)*base89 + (45351061/5000000000000000000000 : ℝ)*base91 + (45351061/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-18053/20000 : ℝ) ≤ (-90939059044960870813212349502119/100750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51270729/100000000000000 : ℝ)*(lower0) + (3692807/6250000000000 : ℝ)*(lower1) + (2031351/20000000000000 : ℝ)*(lower4) + (752336402651283/50000000000000 : ℝ)*(major0) + (752336402651283/50000000000000 : ℝ)*(major1) + (752336402651283/50000000000000 : ℝ)*(major2) + (243587541/25000000000000 : ℝ)*(sp0) + (41670525267/100000000000000 : ℝ)*(sp5) + (9562036399/100000000000000 : ℝ)*(sp6) + (1797018699/100000000000000 : ℝ)*(sp7) + (112650093915323/5000000000000 : ℝ)*(sp12) + (2252961182131357/100000000000000 : ℝ)*(sp13) + (90119731624809/4000000000000 : ℝ)*(sp14) + (786428325378093/100000000000000 : ℝ)*(sp15) + (786430122396791/100000000000000 : ℝ)*(f.failure) + (140812678291039/6250000000000 : ℝ)*(f.sum) + (8564490219329/6045000000000000000000000000 : ℝ)*base66 + (47269875672346961/6500000000000000000000000000000 : ℝ)*base68 + (49862216813346961/6500000000000000000000000000000 : ℝ)*base70 + (24805267018846961/6500000000000000000000000000000 : ℝ)*base72 + (66584598009691/6045000000000000000000000000 : ℝ)*base73 + (79424200322846961/6500000000000000000000000000000 : ℝ)*base76 + (44616961648846961/6500000000000000000000000000000 : ℝ)*base78 + (31000259855346961/6500000000000000000000000000000 : ℝ)*base80 + (52923584034599/6045000000000000000000000000 : ℝ)*base82 + (10579541/5000000000000000000000 : ℝ)*base90 + (10579541/5000000000000000000000 : ℝ)*base92 + (10579541/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1699_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17171/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9917/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8331/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(1817/3125 : ℝ) else (20279/25000 : ℝ) ≤ X j i ∧ X j i ≤ (18053/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1699_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1699_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4297/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4951/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8331/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(1817/3125 : ℝ) else (20279/25000 : ℝ) ≤ X j i ∧ X j i ≤ (18053/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1699_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1699_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1699_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4297/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4951/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8331/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(1817/3125 : ℝ) else (20279/25000 : ℝ) ≤ X j i ∧ X j i ≤ (18053/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1699_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
