-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1447_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:17.873194+00:00
-- url     : https://prove2.me/submissions/2763190e-35f3-4c72-9f7b-2073385c3616

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
theorem support_rectangle_w1447_s3_0 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1955666657/10000000000 : ℝ)*x 0 + (5415502859/10000000000 : ℝ)*x 1 + (5239710681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1955666657/10000000000 : ℝ)^4407 ≤ (5966874791723/50000000000000 : ℝ)^3383 := by
    have hnat : (1955666657 : ℕ)^4407*50000000000000^3383 ≤ 5966874791723^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955666657 10000000000 5966874791723 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415502859/10000000000 : ℝ)^4407 ≤ (562242859889/1250000000000 : ℝ)^3383 := by
    have hnat : (5415502859 : ℕ)^4407*1250000000000^3383 ≤ 562242859889^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415502859 10000000000 562242859889 1250000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239710681/10000000000 : ℝ)^4407 ≤ (43086821613103/100000000000000 : ℝ)^3383 := by
    have hnat : (5239710681 : ℕ)^4407*100000000000000^3383 ≤ 43086821613103^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239710681 10000000000 43086821613103 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1955666657/10000000000 : ℝ), (5415502859/10000000000 : ℝ), (5239710681/10000000000 : ℝ)] ![(5966874791723/50000000000000 : ℝ), (562242859889/1250000000000 : ℝ), (43086821613103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1955666657/10000000000 : ℝ)|^4407 ≤ (5966874791723/50000000000000 : ℝ)^3383
        have hw : |(-1955666657/10000000000 : ℝ)|=(1955666657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415502859/10000000000 : ℝ)|^4407 ≤ (562242859889/1250000000000 : ℝ)^3383
        have hw : |(5415502859/10000000000 : ℝ)|=(5415502859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239710681/10000000000 : ℝ)|^4407 ≤ (43086821613103/100000000000000 : ℝ)^3383
        have hw : |(5239710681/10000000000 : ℝ)|=(5239710681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s3_1 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349067633/10000000000 : ℝ)*x 0 + (-2045308509/10000000000 : ℝ)*x 1 + (5239710703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349067633/10000000000 : ℝ)^4407 ≤ (22130978176183/50000000000000 : ℝ)^3383 := by
    have hnat : (5349067633 : ℕ)^4407*50000000000000^3383 ≤ 22130978176183^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349067633 10000000000 22130978176183 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045308509/10000000000 : ℝ)^4407 ≤ (12651221774037/100000000000000 : ℝ)^3383 := by
    have hnat : (2045308509 : ℕ)^4407*100000000000000^3383 ≤ 12651221774037^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045308509 10000000000 12651221774037 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239710703/10000000000 : ℝ)^4407 ≤ (43086821848771/100000000000000 : ℝ)^3383 := by
    have hnat : (5239710703 : ℕ)^4407*100000000000000^3383 ≤ 43086821848771^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239710703 10000000000 43086821848771 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349067633/10000000000 : ℝ), (-2045308509/10000000000 : ℝ), (5239710703/10000000000 : ℝ)] ![(22130978176183/50000000000000 : ℝ), (12651221774037/100000000000000 : ℝ), (43086821848771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349067633/10000000000 : ℝ)|^4407 ≤ (22130978176183/50000000000000 : ℝ)^3383
        have hw : |(5349067633/10000000000 : ℝ)|=(5349067633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045308509/10000000000 : ℝ)|^4407 ≤ (12651221774037/100000000000000 : ℝ)^3383
        have hw : |(-2045308509/10000000000 : ℝ)|=(2045308509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239710703/10000000000 : ℝ)|^4407 ≤ (43086821848771/100000000000000 : ℝ)^3383
        have hw : |(5239710703/10000000000 : ℝ)|=(5239710703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s3_2 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674533933/5000000000 : ℝ)*x 0 + (1047942117/2000000000 : ℝ)*x 1 + (-511327089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674533933/5000000000 : ℝ)^4407 ≤ (44261958863961/100000000000000 : ℝ)^3383 := by
    have hnat : (2674533933 : ℕ)^4407*100000000000000^3383 ≤ 44261958863961^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674533933 5000000000 44261958863961 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047942117/2000000000 : ℝ)^4407 ≤ (43086820584733/100000000000000 : ℝ)^3383 := by
    have hnat : (1047942117 : ℕ)^4407*100000000000000^3383 ≤ 43086820584733^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047942117 2000000000 43086820584733 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511327089/2500000000 : ℝ)^4407 ≤ (6325610270599/50000000000000 : ℝ)^3383 := by
    have hnat : (511327089 : ℕ)^4407*50000000000000^3383 ≤ 6325610270599^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511327089 2500000000 6325610270599 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674533933/5000000000 : ℝ), (1047942117/2000000000 : ℝ), (-511327089/2500000000 : ℝ)] ![(44261958863961/100000000000000 : ℝ), (43086820584733/100000000000000 : ℝ), (6325610270599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674533933/5000000000 : ℝ)|^4407 ≤ (44261958863961/100000000000000 : ℝ)^3383
        have hw : |(2674533933/5000000000 : ℝ)|=(2674533933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047942117/2000000000 : ℝ)|^4407 ≤ (43086820584733/100000000000000 : ℝ)^3383
        have hw : |(1047942117/2000000000 : ℝ)|=(1047942117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511327089/2500000000 : ℝ)|^4407 ≤ (6325610270599/50000000000000 : ℝ)^3383
        have hw : |(-511327089/2500000000 : ℝ)|=(511327089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s3_3 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4299310749/10000000000 : ℝ)*x 0 + (2055854283/5000000000 : ℝ)*x 1 + (4494515601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299310749/10000000000 : ℝ)^4407 ≤ (16649544784761/50000000000000 : ℝ)^3383 := by
    have hnat : (4299310749 : ℕ)^4407*50000000000000^3383 ≤ 16649544784761^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299310749 10000000000 16649544784761 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2055854283/5000000000 : ℝ)^4407 ≤ (31418885312663/100000000000000 : ℝ)^3383 := by
    have hnat : (2055854283 : ℕ)^4407*100000000000000^3383 ≤ 31418885312663^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055854283 5000000000 31418885312663 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494515601/10000000000 : ℝ)^4407 ≤ (8820506275771/25000000000000 : ℝ)^3383 := by
    have hnat : (4494515601 : ℕ)^4407*25000000000000^3383 ≤ 8820506275771^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494515601 10000000000 8820506275771 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299310749/10000000000 : ℝ), (2055854283/5000000000 : ℝ), (4494515601/10000000000 : ℝ)] ![(16649544784761/50000000000000 : ℝ), (31418885312663/100000000000000 : ℝ), (8820506275771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299310749/10000000000 : ℝ)|^4407 ≤ (16649544784761/50000000000000 : ℝ)^3383
        have hw : |(4299310749/10000000000 : ℝ)|=(4299310749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2055854283/5000000000 : ℝ)|^4407 ≤ (31418885312663/100000000000000 : ℝ)^3383
        have hw : |(2055854283/5000000000 : ℝ)|=(2055854283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494515601/10000000000 : ℝ)|^4407 ≤ (8820506275771/25000000000000 : ℝ)^3383
        have hw : |(4494515601/10000000000 : ℝ)|=(4494515601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s3_4 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-488920247/2500000000 : ℝ)*x 0 + (1048081627/2000000000 : ℝ)*x 1 + (270740089/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (488920247/2500000000 : ℝ)^4407 ≤ (2983465875871/25000000000000 : ℝ)^3383 := by
    have hnat : (488920247 : ℕ)^4407*25000000000000^3383 ≤ 2983465875871^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488920247 2500000000 2983465875871 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048081627/2000000000 : ℝ)^4407 ≤ (43094293022289/100000000000000 : ℝ)^3383 := by
    have hnat : (1048081627 : ℕ)^4407*100000000000000^3383 ≤ 43094293022289^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048081627 2000000000 43094293022289 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270740089/500000000 : ℝ)^4407 ≤ (11242960864543/25000000000000 : ℝ)^3383 := by
    have hnat : (270740089 : ℕ)^4407*25000000000000^3383 ≤ 11242960864543^3383*500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270740089 500000000 11242960864543 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-488920247/2500000000 : ℝ), (1048081627/2000000000 : ℝ), (270740089/500000000 : ℝ)] ![(2983465875871/25000000000000 : ℝ), (43094293022289/100000000000000 : ℝ), (11242960864543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-488920247/2500000000 : ℝ)|^4407 ≤ (2983465875871/25000000000000 : ℝ)^3383
        have hw : |(-488920247/2500000000 : ℝ)|=(488920247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048081627/2000000000 : ℝ)|^4407 ≤ (43094293022289/100000000000000 : ℝ)^3383
        have hw : |(1048081627/2000000000 : ℝ)|=(1048081627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270740089/500000000 : ℝ)|^4407 ≤ (11242960864543/25000000000000 : ℝ)^3383
        have hw : |(270740089/500000000 : ℝ)|=(270740089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s3_5 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303287889/10000000000 : ℝ)*x 0 + (-935108839/5000000000 : ℝ)*x 1 + (2707400869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303287889/10000000000 : ℝ)^4407 ≤ (5471139975491/12500000000000 : ℝ)^3383 := by
    have hnat : (5303287889 : ℕ)^4407*12500000000000^3383 ≤ 5471139975491^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303287889 10000000000 5471139975491 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935108839/5000000000 : ℝ)^4407 ≤ (1407379647079/12500000000000 : ℝ)^3383 := by
    have hnat : (935108839 : ℕ)^4407*12500000000000^3383 ≤ 1407379647079^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935108839 5000000000 1407379647079 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707400869/5000000000 : ℝ)^4407 ≤ (22485921501881/50000000000000 : ℝ)^3383 := by
    have hnat : (2707400869 : ℕ)^4407*50000000000000^3383 ≤ 22485921501881^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707400869 5000000000 22485921501881 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303287889/10000000000 : ℝ), (-935108839/5000000000 : ℝ), (2707400869/5000000000 : ℝ)] ![(5471139975491/12500000000000 : ℝ), (1407379647079/12500000000000 : ℝ), (22485921501881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303287889/10000000000 : ℝ)|^4407 ≤ (5471139975491/12500000000000 : ℝ)^3383
        have hw : |(5303287889/10000000000 : ℝ)|=(5303287889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-935108839/5000000000 : ℝ)|^4407 ≤ (1407379647079/12500000000000 : ℝ)^3383
        have hw : |(-935108839/5000000000 : ℝ)|=(935108839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707400869/5000000000 : ℝ)|^4407 ≤ (22485921501881/50000000000000 : ℝ)^3383
        have hw : |(2707400869/5000000000 : ℝ)|=(2707400869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s3_6 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325821673/2500000000 : ℝ)*x 0 + (1082960539/2000000000 : ℝ)*x 1 + (-1870217999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325821673/2500000000 : ℝ)^4407 ≤ (21884553467271/50000000000000 : ℝ)^3383 := by
    have hnat : (1325821673 : ℕ)^4407*50000000000000^3383 ≤ 21884553467271^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325821673 2500000000 21884553467271 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082960539/2000000000 : ℝ)^4407 ≤ (44971853357833/100000000000000 : ℝ)^3383 := by
    have hnat : (1082960539 : ℕ)^4407*100000000000000^3383 ≤ 44971853357833^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082960539 2000000000 44971853357833 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870217999/10000000000 : ℝ)^4407 ≤ (225180793881/2000000000000 : ℝ)^3383 := by
    have hnat : (1870217999 : ℕ)^4407*2000000000000^3383 ≤ 225180793881^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870217999 10000000000 225180793881 2000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325821673/2500000000 : ℝ), (1082960539/2000000000 : ℝ), (-1870217999/10000000000 : ℝ)] ![(21884553467271/50000000000000 : ℝ), (44971853357833/100000000000000 : ℝ), (225180793881/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325821673/2500000000 : ℝ)|^4407 ≤ (21884553467271/50000000000000 : ℝ)^3383
        have hw : |(1325821673/2500000000 : ℝ)|=(1325821673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082960539/2000000000 : ℝ)|^4407 ≤ (44971853357833/100000000000000 : ℝ)^3383
        have hw : |(1082960539/2000000000 : ℝ)|=(1082960539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1870217999/10000000000 : ℝ)|^4407 ≤ (225180793881/2000000000000 : ℝ)^3383
        have hw : |(-1870217999/10000000000 : ℝ)|=(1870217999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s3_7 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149670959/5000000000 : ℝ)*x 0 + (2246498781/5000000000 : ℝ)*x 1 + (4113236307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149670959/5000000000 : ℝ)^4407 ≤ (33299404053063/100000000000000 : ℝ)^3383 := by
    have hnat : (2149670959 : ℕ)^4407*100000000000000^3383 ≤ 33299404053063^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149670959 5000000000 33299404053063 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246498781/5000000000 : ℝ)^4407 ≤ (17633251109901/50000000000000 : ℝ)^3383 := by
    have hnat : (2246498781 : ℕ)^4407*50000000000000^3383 ≤ 17633251109901^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246498781 5000000000 17633251109901 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4113236307/10000000000 : ℝ)^4407 ≤ (3143409371713/10000000000000 : ℝ)^3383 := by
    have hnat : (4113236307 : ℕ)^4407*10000000000000^3383 ≤ 3143409371713^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4113236307 10000000000 3143409371713 10000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149670959/5000000000 : ℝ), (2246498781/5000000000 : ℝ), (4113236307/10000000000 : ℝ)] ![(33299404053063/100000000000000 : ℝ), (17633251109901/50000000000000 : ℝ), (3143409371713/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149670959/5000000000 : ℝ)|^4407 ≤ (33299404053063/100000000000000 : ℝ)^3383
        have hw : |(2149670959/5000000000 : ℝ)|=(2149670959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246498781/5000000000 : ℝ)|^4407 ≤ (17633251109901/50000000000000 : ℝ)^3383
        have hw : |(2246498781/5000000000 : ℝ)|=(2246498781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4113236307/10000000000 : ℝ)|^4407 ≤ (3143409371713/10000000000000 : ℝ)^3383
        have hw : |(4113236307/10000000000 : ℝ)|=(4113236307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1447_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7873/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5607/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7469/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7873/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5231/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7873/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5231/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7873/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5231/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7873/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5231/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7873/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5231/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7873/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5231/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (5231/50000 : ℝ) ^ (2203/512 : ℝ) ≤ (6048706842820779/100000000000000000000 : ℝ) := by
    have hpowers : (5231/50000 : ℝ)^2203 ≤ (6048706842820779/100000000000000000000 : ℝ)^512 := by
      have hnat : (5231 : ℕ)^2203*100000000000000000000^512 ≤ 6048706842820779^512*50000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5231 50000 6048706842820779 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5231/50000 : ℝ)) (X := (6048706842820779/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7873/50000 : ℝ) ^ (2203/512 : ℝ) ≤ (35126657400254123/100000000000000000000 : ℝ) := by
    have hpowers : (7873/50000 : ℝ)^2203 ≤ (35126657400254123/100000000000000000000 : ℝ)^512 := by
      have hnat : (7873 : ℕ)^2203*100000000000000000000^512 ≤ 35126657400254123^512*50000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7873 50000 35126657400254123 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7873/50000 : ℝ)) (X := (35126657400254123/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006048706842820779/50000000000000000000 : ℝ) ≤ (10000281143361351/10000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50006048706842820779/50000000000000000000 : ℝ)^512 ≤ (10000281143361351/10000000000000000 : ℝ)^2203 := by
      have hnat : (50006048706842820779 : ℕ)^512*10000000000000000^2203 ≤ 10000281143361351^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006048706842820779 50000000000000000000 10000281143361351 10000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281143361351/10000000000000000 : ℝ)) (X := (50006048706842820779/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020587682121537451/50000000000000000000 : ℝ) ≤ (5000478403444589/5000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50020587682121537451/50000000000000000000 : ℝ)^512 ≤ (5000478403444589/5000000000000000 : ℝ)^2203 := by
      have hnat : (50020587682121537451 : ℕ)^512*5000000000000000^2203 ≤ 5000478403444589^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020587682121537451 50000000000000000000 5000478403444589 5000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000478403444589/5000000000000000 : ℝ)) (X := (50020587682121537451/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035126657400254123/50000000000000000000 : ℝ) ≤ (2000326494083401/2000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50035126657400254123/50000000000000000000 : ℝ)^512 ≤ (2000326494083401/2000000000000000 : ℝ)^2203 := by
      have hnat : (50035126657400254123 : ℕ)^512*2000000000000000^2203 ≤ 2000326494083401^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035126657400254123 50000000000000000000 2000326494083401 2000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000326494083401/2000000000000000 : ℝ)) (X := (50035126657400254123/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6048706842820779/100000000000000000000 : ℝ) ≤ ((6603418497233140817/6605000000000000000 : ℝ)+2*(675663527827/528400000000000 : ℝ)*(5231/50000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (6603418497233140817/6605000000000000000 : ℝ)+2*(675663527827/528400000000000 : ℝ)*(5231/50000 : ℝ)=(10000281143361351/10000000000000000 : ℝ) by norm_num, show 1+2*(6048706842820779/100000000000000000000 : ℝ)=(50006048706842820779/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35126657400254123/100000000000000000000 : ℝ)+(6048706842820779/100000000000000000000 : ℝ) ≤ ((6603418497233140817/6605000000000000000 : ℝ)+(675663527827/528400000000000 : ℝ)*((7873/50000 : ℝ)+(5231/50000 : ℝ)))^(2203/512 : ℝ) := by
    rw [show (6603418497233140817/6605000000000000000 : ℝ)+(675663527827/528400000000000 : ℝ)*((7873/50000 : ℝ)+(5231/50000 : ℝ))=(5000478403444589/5000000000000000 : ℝ) by norm_num, show 1+(35126657400254123/100000000000000000000 : ℝ)+(6048706842820779/100000000000000000000 : ℝ)=(50020587682121537451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35126657400254123/100000000000000000000 : ℝ) ≤ ((6603418497233140817/6605000000000000000 : ℝ)+2*(675663527827/528400000000000 : ℝ)*(7873/50000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (6603418497233140817/6605000000000000000 : ℝ)+2*(675663527827/528400000000000 : ℝ)*(7873/50000 : ℝ)=(2000326494083401/2000000000000000 : ℝ) by norm_num, show 1+2*(35126657400254123/100000000000000000000 : ℝ)=(50035126657400254123/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6603418497233140817/6605000000000000000 : ℝ)*(X 1 0+X 2 0)+(675663527827/528400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (5231/50000 : ℝ)) (hi := (7873/50000 : ℝ)) (c := (6603418497233140817/6605000000000000000 : ℝ)) (alpha := (675663527827/528400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6603418497233140817/6605000000000000000 : ℝ)*(X 0 1+X 2 1)+(675663527827/528400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (5231/50000 : ℝ)) (hi := (7873/50000 : ℝ)) (c := (6603418497233140817/6605000000000000000 : ℝ)) (alpha := (675663527827/528400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6603418497233140817/6605000000000000000 : ℝ)*(X 0 2+X 1 2)+(675663527827/528400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (5231/50000 : ℝ)) (hi := (7873/50000 : ℝ)) (c := (6603418497233140817/6605000000000000000 : ℝ)) (alpha := (675663527827/528400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1955666657/10000000000 : ℝ)*X 0 0+(5415502859/10000000000 : ℝ)*X 0 1+(5239710681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349067633/10000000000 : ℝ)*X 1 0+(-2045308509/10000000000 : ℝ)*X 1 1+(5239710703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674533933/5000000000 : ℝ)*X 2 0+(1047942117/2000000000 : ℝ)*X 2 1+(-511327089/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4299310749/10000000000 : ℝ)*X 0 0+(2055854283/5000000000 : ℝ)*X 0 1+(4494515601/10000000000 : ℝ)*X 0 2+(4299310749/10000000000 : ℝ)*X 1 0+(2055854283/5000000000 : ℝ)*X 1 1+(4494515601/10000000000 : ℝ)*X 1 2+(4299310749/10000000000 : ℝ)*X 2 0+(2055854283/5000000000 : ℝ)*X 2 1+(4494515601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-488920247/2500000000 : ℝ)*X 0 0+(1048081627/2000000000 : ℝ)*X 0 1+(270740089/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303287889/10000000000 : ℝ)*X 1 0+(-935108839/5000000000 : ℝ)*X 1 1+(2707400869/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325821673/2500000000 : ℝ)*X 2 0+(1082960539/2000000000 : ℝ)*X 2 1+(-1870217999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2149670959/5000000000 : ℝ)*X 0 0+(2246498781/5000000000 : ℝ)*X 0 1+(4113236307/10000000000 : ℝ)*X 0 2+(2149670959/5000000000 : ℝ)*X 1 0+(2246498781/5000000000 : ℝ)*X 1 1+(4113236307/10000000000 : ℝ)*X 1 2+(2149670959/5000000000 : ℝ)*X 2 0+(2246498781/5000000000 : ℝ)*X 2 1+(4113236307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1804908129161890030144532091/165125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1930199987/100000000000000 : ℝ)*(base19) + (402621741/20000000000000 : ℝ)*(base23) + (88196227/100000000000000 : ℝ)*(lower2) + (86944953/50000000000000 : ℝ)*(upper3) + (137720923/50000000000000 : ℝ)*(upper5) + (2075233730619453/50000000000000 : ℝ)*(major0) + (2075233730619453/50000000000000 : ℝ)*(major1) + (2075233730619453/50000000000000 : ℝ)*(major2) + (1422142702336737/25000000000000 : ℝ)*(sp0) + (2844306069915717/50000000000000 : ℝ)*(sp1) + (5688612056922717/100000000000000 : ℝ)*(sp2) + (52246024617909/2000000000000 : ℝ)*(sp3) + (43260684473/100000000000000 : ℝ)*(sp4) + (19257199047/100000000000000 : ℝ)*(sp7) + (1306160244047249/50000000000000 : ℝ)*(f.failure) + (5688614070031421/100000000000000 : ℝ)*(f.sum) + (18095792823071/13210000000000000000000000000 : ℝ)*base65 + (5037481666516150601/330250000000000000000000000000000 : ℝ)*base67 + (1728585349509650601/330250000000000000000000000000000 : ℝ)*base69 + (5508728728001900601/330250000000000000000000000000000 : ℝ)*base71 + (127824074310951/13210000000000000000000000000 : ℝ)*base73 + (1445718108946150601/330250000000000000000000000000000 : ℝ)*base75 + (3968199597951900601/330250000000000000000000000000000 : ℝ)*base77 + (7019791684561650601/330250000000000000000000000000000 : ℝ)*base79 + (11635315625961/13210000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3192847/1000000000000000000000 : ℝ)*base90 + (3192847/1000000000000000000000 : ℝ)*base92 + (3192847/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8117478194342249069580543/660500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7176923/20000000000000 : ℝ)*(base8) + (27144383/4000000000000 : ℝ)*(base21) + (14955211/10000000000000 : ℝ)*(upper2) + (207791383/100000000000000 : ℝ)*(lower4) + (16734759479057/400000000000 : ℝ)*(major0) + (16734759479057/400000000000 : ℝ)*(major1) + (16734759479057/400000000000 : ℝ)*(major2) + (169609979/12500000000000 : ℝ)*(sp0) + (1091154769/100000000000000 : ℝ)*(sp1) + (334327381/10000000000000 : ℝ)*(sp2) + (5734147134863299/100000000000000 : ℝ)*(sp4) + (5734147436472977/100000000000000 : ℝ)*(sp5) + (5734144505744361/100000000000000 : ℝ)*(sp6) + (2633230802237449/100000000000000 : ℝ)*(sp7) + (2633230802237449/100000000000000 : ℝ)*(f.failure) + (5734148527627747/100000000000000 : ℝ)*(f.sum) + (15702614520743/2642000000000000000000000000 : ℝ)*base65 + (10350995257585069/2642000000000000000000000000000 : ℝ)*base67 + (1901503396097069/2642000000000000000000000000000 : ℝ)*base69 + (4743672261903069/2642000000000000000000000000000 : ℝ)*base71 + (6634963084413/2642000000000000000000000000 : ℝ)*base73 + (3812267628984931/2642000000000000000000000000000 : ℝ)*base76 + (62063537443139069/2642000000000000000000000000000 : ℝ)*base77 + (20849894561321069/2642000000000000000000000000000 : ℝ)*base79 + (3833085651373/2642000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3543447/2000000000000000000000 : ℝ)*base90 + (3543447/2000000000000000000000 : ℝ)*base92 + (3543447/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1447_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7873/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7469/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1447_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1447_s4_0 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-978241477/5000000000 : ℝ)*x 0 + (5408500507/10000000000 : ℝ)*x 1 + (1311543737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (978241477/5000000000 : ℝ)^4407 ≤ (5970119448609/50000000000000 : ℝ)^3383 := by
    have hnat : (978241477 : ℕ)^4407*50000000000000^3383 ≤ 5970119448609^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978241477 5000000000 5970119448609 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408500507/10000000000 : ℝ)^4407 ≤ (44903680102999/100000000000000 : ℝ)^3383 := by
    have hnat : (5408500507 : ℕ)^4407*100000000000000^3383 ≤ 44903680102999^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408500507 10000000000 44903680102999 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311543737/2500000000 : ℝ)^4407 ≤ (10789020246257/25000000000000 : ℝ)^3383 := by
    have hnat : (1311543737 : ℕ)^4407*25000000000000^3383 ≤ 10789020246257^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311543737 2500000000 10789020246257 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-978241477/5000000000 : ℝ), (5408500507/10000000000 : ℝ), (1311543737/2500000000 : ℝ)] ![(5970119448609/50000000000000 : ℝ), (44903680102999/100000000000000 : ℝ), (10789020246257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-978241477/5000000000 : ℝ)|^4407 ≤ (5970119448609/50000000000000 : ℝ)^3383
        have hw : |(-978241477/5000000000 : ℝ)|=(978241477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408500507/10000000000 : ℝ)|^4407 ≤ (44903680102999/100000000000000 : ℝ)^3383
        have hw : |(5408500507/10000000000 : ℝ)|=(5408500507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311543737/2500000000 : ℝ)|^4407 ≤ (10789020246257/25000000000000 : ℝ)^3383
        have hw : |(1311543737/2500000000 : ℝ)|=(1311543737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s4_1 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069451109/2000000000 : ℝ)*x 0 + (-509783623/2500000000 : ℝ)*x 1 + (5246174863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069451109/2000000000 : ℝ)^4407 ≤ (44242424178357/100000000000000 : ℝ)^3383 := by
    have hnat : (1069451109 : ℕ)^4407*100000000000000^3383 ≤ 44242424178357^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069451109 2000000000 44242424178357 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509783623/2500000000 : ℝ)^4407 ≤ (2520299145691/20000000000000 : ℝ)^3383 := by
    have hnat : (509783623 : ℕ)^4407*20000000000000^3383 ≤ 2520299145691^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509783623 2500000000 2520299145691 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246174863/10000000000 : ℝ)^4407 ≤ (5394510009269/12500000000000 : ℝ)^3383 := by
    have hnat : (5246174863 : ℕ)^4407*12500000000000^3383 ≤ 5394510009269^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246174863 10000000000 5394510009269 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069451109/2000000000 : ℝ), (-509783623/2500000000 : ℝ), (5246174863/10000000000 : ℝ)] ![(44242424178357/100000000000000 : ℝ), (2520299145691/20000000000000 : ℝ), (5394510009269/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069451109/2000000000 : ℝ)|^4407 ≤ (44242424178357/100000000000000 : ℝ)^3383
        have hw : |(1069451109/2000000000 : ℝ)|=(1069451109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509783623/2500000000 : ℝ)|^4407 ≤ (2520299145691/20000000000000 : ℝ)^3383
        have hw : |(-509783623/2500000000 : ℝ)|=(509783623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246174863/10000000000 : ℝ)|^4407 ≤ (5394510009269/12500000000000 : ℝ)^3383
        have hw : |(5246174863/10000000000 : ℝ)|=(5246174863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s4_2 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347255499/10000000000 : ℝ)*x 0 + (5246174893/10000000000 : ℝ)*x 1 + (-407826903/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347255499/10000000000 : ℝ)^4407 ≤ (44242423682557/100000000000000 : ℝ)^3383 := by
    have hnat : (5347255499 : ℕ)^4407*100000000000000^3383 ≤ 44242423682557^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347255499 10000000000 44242423682557 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246174893/10000000000 : ℝ)^4407 ≤ (43156080395637/100000000000000 : ℝ)^3383 := by
    have hnat : (5246174893 : ℕ)^4407*100000000000000^3383 ≤ 43156080395637^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246174893 10000000000 43156080395637 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407826903/2000000000 : ℝ)^4407 ≤ (6300747956807/50000000000000 : ℝ)^3383 := by
    have hnat : (407826903 : ℕ)^4407*50000000000000^3383 ≤ 6300747956807^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407826903 2000000000 6300747956807 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347255499/10000000000 : ℝ), (5246174893/10000000000 : ℝ), (-407826903/2000000000 : ℝ)] ![(44242423682557/100000000000000 : ℝ), (43156080395637/100000000000000 : ℝ), (6300747956807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347255499/10000000000 : ℝ)|^4407 ≤ (44242423682557/100000000000000 : ℝ)^3383
        have hw : |(5347255499/10000000000 : ℝ)|=(5347255499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246174893/10000000000 : ℝ)|^4407 ≤ (43156080395637/100000000000000 : ℝ)^3383
        have hw : |(5246174893/10000000000 : ℝ)|=(5246174893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407826903/2000000000 : ℝ)|^4407 ≤ (6300747956807/50000000000000 : ℝ)^3383
        have hw : |(-407826903/2000000000 : ℝ)|=(407826903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s4_3 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33592269/78125000 : ℝ)*x 0 + (4126311267/10000000000 : ℝ)*x 1 + (111994829/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33592269/78125000 : ℝ)^4407 ≤ (33304131267073/100000000000000 : ℝ)^3383 := by
    have hnat : (33592269 : ℕ)^4407*100000000000000^3383 ≤ 33304131267073^3383*78125000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33592269 78125000 33304131267073 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4126311267/10000000000 : ℝ)^4407 ≤ (31564322635729/100000000000000 : ℝ)^3383 := by
    have hnat : (4126311267 : ℕ)^4407*100000000000000^3383 ≤ 31564322635729^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126311267 10000000000 31564322635729 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111994829/250000000 : ℝ)^4407 ≤ (17565773039241/50000000000000 : ℝ)^3383 := by
    have hnat : (111994829 : ℕ)^4407*50000000000000^3383 ≤ 17565773039241^3383*250000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111994829 250000000 17565773039241 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33592269/78125000 : ℝ), (4126311267/10000000000 : ℝ), (111994829/250000000 : ℝ)] ![(33304131267073/100000000000000 : ℝ), (31564322635729/100000000000000 : ℝ), (17565773039241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33592269/78125000 : ℝ)|^4407 ≤ (33304131267073/100000000000000 : ℝ)^3383
        have hw : |(33592269/78125000 : ℝ)|=(33592269/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4126311267/10000000000 : ℝ)|^4407 ≤ (31564322635729/100000000000000 : ℝ)^3383
        have hw : |(4126311267/10000000000 : ℝ)|=(4126311267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(111994829/250000000 : ℝ)|^4407 ≤ (17565773039241/50000000000000 : ℝ)^3383
        have hw : |(111994829/250000000 : ℝ)|=(111994829/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s4_4 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-978247293/5000000000 : ℝ)*x 0 + (655846221/1250000000 : ℝ)*x 1 + (5407902577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (978247293/5000000000 : ℝ)^4407 ≤ (186567677719/1562500000000 : ℝ)^3383 := by
    have hnat : (978247293 : ℕ)^4407*1562500000000^3383 ≤ 186567677719^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978247293 5000000000 186567677719 1562500000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655846221/1250000000 : ℝ)^4407 ≤ (21581227648373/50000000000000 : ℝ)^3383 := by
    have hnat : (655846221 : ℕ)^4407*50000000000000^3383 ≤ 21581227648373^3383*1250000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655846221 1250000000 21581227648373 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407902577/10000000000 : ℝ)^4407 ≤ (22448606653281/50000000000000 : ℝ)^3383 := by
    have hnat : (5407902577 : ℕ)^4407*50000000000000^3383 ≤ 22448606653281^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407902577 10000000000 22448606653281 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-978247293/5000000000 : ℝ), (655846221/1250000000 : ℝ), (5407902577/10000000000 : ℝ)] ![(186567677719/1562500000000 : ℝ), (21581227648373/50000000000000 : ℝ), (22448606653281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-978247293/5000000000 : ℝ)|^4407 ≤ (186567677719/1562500000000 : ℝ)^3383
        have hw : |(-978247293/5000000000 : ℝ)|=(978247293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655846221/1250000000 : ℝ)|^4407 ≤ (21581227648373/50000000000000 : ℝ)^3383
        have hw : |(655846221/1250000000 : ℝ)|=(655846221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407902577/10000000000 : ℝ)|^4407 ≤ (22448606653281/50000000000000 : ℝ)^3383
        have hw : |(5407902577/10000000000 : ℝ)|=(5407902577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s4_5 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304982131/10000000000 : ℝ)*x 0 + (-1877406901/10000000000 : ℝ)*x 1 + (5407902551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304982131/10000000000 : ℝ)^4407 ≤ (21893668050541/50000000000000 : ℝ)^3383 := by
    have hnat : (5304982131 : ℕ)^4407*50000000000000^3383 ≤ 21893668050541^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304982131 10000000000 21893668050541 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1877406901/10000000000 : ℝ)^4407 ≤ (11315450861429/100000000000000 : ℝ)^3383 := by
    have hnat : (1877406901 : ℕ)^4407*100000000000000^3383 ≤ 11315450861429^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877406901 10000000000 11315450861429 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407902551/10000000000 : ℝ)^4407 ≤ (44897213025369/100000000000000 : ℝ)^3383 := by
    have hnat : (5407902551 : ℕ)^4407*100000000000000^3383 ≤ 44897213025369^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407902551 10000000000 44897213025369 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304982131/10000000000 : ℝ), (-1877406901/10000000000 : ℝ), (5407902551/10000000000 : ℝ)] ![(21893668050541/50000000000000 : ℝ), (11315450861429/100000000000000 : ℝ), (44897213025369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304982131/10000000000 : ℝ)|^4407 ≤ (21893668050541/50000000000000 : ℝ)^3383
        have hw : |(5304982131/10000000000 : ℝ)|=(5304982131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1877406901/10000000000 : ℝ)|^4407 ≤ (11315450861429/100000000000000 : ℝ)^3383
        have hw : |(-1877406901/10000000000 : ℝ)|=(1877406901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407902551/10000000000 : ℝ)|^4407 ≤ (44897213025369/100000000000000 : ℝ)^3383
        have hw : |(5407902551/10000000000 : ℝ)|=(5407902551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s4_6 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304982161/10000000000 : ℝ)*x 0 + (5407902549/10000000000 : ℝ)*x 1 + (-938703431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304982161/10000000000 : ℝ)^4407 ≤ (21893668211827/50000000000000 : ℝ)^3383 := by
    have hnat : (5304982161 : ℕ)^4407*50000000000000^3383 ≤ 21893668211827^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304982161 10000000000 21893668211827 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407902549/10000000000 : ℝ)^4407 ≤ (44897213003739/100000000000000 : ℝ)^3383 := by
    have hnat : (5407902549 : ℕ)^4407*100000000000000^3383 ≤ 44897213003739^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407902549 10000000000 44897213003739 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (938703431/5000000000 : ℝ)^4407 ≤ (11315450555219/100000000000000 : ℝ)^3383 := by
    have hnat : (938703431 : ℕ)^4407*100000000000000^3383 ≤ 11315450555219^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938703431 5000000000 11315450555219 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304982161/10000000000 : ℝ), (5407902549/10000000000 : ℝ), (-938703431/5000000000 : ℝ)] ![(21893668211827/50000000000000 : ℝ), (44897213003739/100000000000000 : ℝ), (11315450555219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304982161/10000000000 : ℝ)|^4407 ≤ (21893668211827/50000000000000 : ℝ)^3383
        have hw : |(5304982161/10000000000 : ℝ)|=(5304982161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407902549/10000000000 : ℝ)|^4407 ≤ (44897213003739/100000000000000 : ℝ)^3383
        have hw : |(5407902549/10000000000 : ℝ)|=(5407902549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-938703431/5000000000 : ℝ)|^4407 ≤ (11315450555219/100000000000000 : ℝ)^3383
        have hw : |(-938703431/5000000000 : ℝ)|=(938703431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s4_7 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074958951/2500000000 : ℝ)*x 0 + (4478497707/10000000000 : ℝ)*x 1 + (4127613543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074958951/2500000000 : ℝ)^4407 ≤ (4163048408751/12500000000000 : ℝ)^3383 := by
    have hnat : (1074958951 : ℕ)^4407*12500000000000^3383 ≤ 4163048408751^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074958951 2500000000 4163048408751 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478497707/10000000000 : ℝ)^4407 ≤ (2194894520379/6250000000000 : ℝ)^3383 := by
    have hnat : (4478497707 : ℕ)^4407*6250000000000^3383 ≤ 2194894520379^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478497707 10000000000 2194894520379 6250000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4127613543/10000000000 : ℝ)^4407 ≤ (31577300383219/100000000000000 : ℝ)^3383 := by
    have hnat : (4127613543 : ℕ)^4407*100000000000000^3383 ≤ 31577300383219^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127613543 10000000000 31577300383219 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074958951/2500000000 : ℝ), (4478497707/10000000000 : ℝ), (4127613543/10000000000 : ℝ)] ![(4163048408751/12500000000000 : ℝ), (2194894520379/6250000000000 : ℝ), (31577300383219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074958951/2500000000 : ℝ)|^4407 ≤ (4163048408751/12500000000000 : ℝ)^3383
        have hw : |(1074958951/2500000000 : ℝ)|=(1074958951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478497707/10000000000 : ℝ)|^4407 ≤ (2194894520379/6250000000000 : ℝ)^3383
        have hw : |(4478497707/10000000000 : ℝ)|=(4478497707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4127613543/10000000000 : ℝ)|^4407 ≤ (31577300383219/100000000000000 : ℝ)^3383
        have hw : |(4127613543/10000000000 : ℝ)|=(4127613543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1447_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7469/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1419/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14791/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7469/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7469/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7469/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7469/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7469/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7469/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5607/50000 : ℝ) ^ (2203/512 : ℝ) ≤ (8154025430614749/100000000000000000000 : ℝ) := by
    have hpowers : (5607/50000 : ℝ)^2203 ≤ (8154025430614749/100000000000000000000 : ℝ)^512 := by
      have hnat : (5607 : ℕ)^2203*100000000000000000000^512 ≤ 8154025430614749^512*50000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5607 50000 8154025430614749 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5607/50000 : ℝ)) (X := (8154025430614749/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7469/50000 : ℝ) ^ (2203/512 : ℝ) ≤ (14001345330263429/50000000000000000000 : ℝ) := by
    have hpowers : (7469/50000 : ℝ)^2203 ≤ (14001345330263429/50000000000000000000 : ℝ)^512 := by
      have hnat : (7469 : ℕ)^2203*50000000000000000000^512 ≤ 14001345330263429^512*50000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7469 50000 14001345330263429 50000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7469/50000 : ℝ)) (X := (14001345330263429/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008154025430614749/50000000000000000000 : ℝ) ≤ (5000189496129973/5000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50008154025430614749/50000000000000000000 : ℝ)^512 ≤ (5000189496129973/5000000000000000 : ℝ)^2203 := by
      have hnat : (50008154025430614749 : ℕ)^512*5000000000000000^2203 ≤ 5000189496129973^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008154025430614749 50000000000000000000 5000189496129973 5000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000189496129973/5000000000000000 : ℝ)) (X := (50008154025430614749/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036156716091141607/100000000000000000000 : ℝ) ≤ (10000840202918147/10000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (100036156716091141607/100000000000000000000 : ℝ)^512 ≤ (10000840202918147/10000000000000000 : ℝ)^2203 := by
      have hnat : (100036156716091141607 : ℕ)^512*10000000000000000^2203 ≤ 10000840202918147^2203*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036156716091141607 100000000000000000000 10000840202918147 10000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000840202918147/10000000000000000 : ℝ)) (X := (100036156716091141607/100000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014001345330263429/25000000000000000000 : ℝ) ≤ (2500325353394087/2500000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (25014001345330263429/25000000000000000000 : ℝ)^512 ≤ (2500325353394087/2500000000000000 : ℝ)^2203 := by
      have hnat : (25014001345330263429 : ℕ)^512*2500000000000000^2203 ≤ 2500325353394087^2203*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014001345330263429 25000000000000000000 2500325353394087 2500000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500325353394087/2500000000000000 : ℝ)) (X := (25014001345330263429/25000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8154025430614749/100000000000000000000 : ℝ) ≤ ((1329680976233353817/1330000000000000000 : ℝ)+2*(461210658201/372400000000000 : ℝ)*(5607/50000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (1329680976233353817/1330000000000000000 : ℝ)+2*(461210658201/372400000000000 : ℝ)*(5607/50000 : ℝ)=(5000189496129973/5000000000000000 : ℝ) by norm_num, show 1+2*(8154025430614749/100000000000000000000 : ℝ)=(50008154025430614749/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14001345330263429/50000000000000000000 : ℝ)+(8154025430614749/100000000000000000000 : ℝ) ≤ ((1329680976233353817/1330000000000000000 : ℝ)+(461210658201/372400000000000 : ℝ)*((7469/50000 : ℝ)+(5607/50000 : ℝ)))^(2203/512 : ℝ) := by
    rw [show (1329680976233353817/1330000000000000000 : ℝ)+(461210658201/372400000000000 : ℝ)*((7469/50000 : ℝ)+(5607/50000 : ℝ))=(10000840202918147/10000000000000000 : ℝ) by norm_num, show 1+(14001345330263429/50000000000000000000 : ℝ)+(8154025430614749/100000000000000000000 : ℝ)=(100036156716091141607/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14001345330263429/50000000000000000000 : ℝ) ≤ ((1329680976233353817/1330000000000000000 : ℝ)+2*(461210658201/372400000000000 : ℝ)*(7469/50000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (1329680976233353817/1330000000000000000 : ℝ)+2*(461210658201/372400000000000 : ℝ)*(7469/50000 : ℝ)=(2500325353394087/2500000000000000 : ℝ) by norm_num, show 1+2*(14001345330263429/50000000000000000000 : ℝ)=(25014001345330263429/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1329680976233353817/1330000000000000000 : ℝ)*(X 1 0+X 2 0)+(461210658201/372400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (7469/50000 : ℝ)) (c := (1329680976233353817/1330000000000000000 : ℝ)) (alpha := (461210658201/372400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1329680976233353817/1330000000000000000 : ℝ)*(X 0 1+X 2 1)+(461210658201/372400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (7469/50000 : ℝ)) (c := (1329680976233353817/1330000000000000000 : ℝ)) (alpha := (461210658201/372400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1329680976233353817/1330000000000000000 : ℝ)*(X 0 2+X 1 2)+(461210658201/372400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (7469/50000 : ℝ)) (c := (1329680976233353817/1330000000000000000 : ℝ)) (alpha := (461210658201/372400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-978241477/5000000000 : ℝ)*X 0 0+(5408500507/10000000000 : ℝ)*X 0 1+(1311543737/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069451109/2000000000 : ℝ)*X 1 0+(-509783623/2500000000 : ℝ)*X 1 1+(5246174863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347255499/10000000000 : ℝ)*X 2 0+(5246174893/10000000000 : ℝ)*X 2 1+(-407826903/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((33592269/78125000 : ℝ)*X 0 0+(4126311267/10000000000 : ℝ)*X 0 1+(111994829/250000000 : ℝ)*X 0 2+(33592269/78125000 : ℝ)*X 1 0+(4126311267/10000000000 : ℝ)*X 1 1+(111994829/250000000 : ℝ)*X 1 2+(33592269/78125000 : ℝ)*X 2 0+(4126311267/10000000000 : ℝ)*X 2 1+(111994829/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-978247293/5000000000 : ℝ)*X 0 0+(655846221/1250000000 : ℝ)*X 0 1+(5407902577/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304982131/10000000000 : ℝ)*X 1 0+(-1877406901/10000000000 : ℝ)*X 1 1+(5407902551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304982161/10000000000 : ℝ)*X 2 0+(5407902549/10000000000 : ℝ)*X 2 1+(-938703431/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1074958951/2500000000 : ℝ)*X 0 0+(4478497707/10000000000 : ℝ)*X 0 1+(4127613543/10000000000 : ℝ)*X 0 2+(1074958951/2500000000 : ℝ)*X 1 0+(4478497707/10000000000 : ℝ)*X 1 1+(4127613543/10000000000 : ℝ)*X 1 2+(1074958951/2500000000 : ℝ)*X 2 0+(4478497707/10000000000 : ℝ)*X 2 1+(4127613543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52783009456312544342307/4655000000000000000000000000 : ℝ) := by norm_num
    linear_combination (266890363/12500000000000 : ℝ)*(base19) + (478995633/25000000000000 : ℝ)*(base23) + (17768293/20000000000000 : ℝ)*(lower2) + (15664453/5000000000000 : ℝ)*(upper3) + (155067869/100000000000000 : ℝ)*(upper5) + (4494791895839281/100000000000000 : ℝ)*(major0) + (4494791895839281/100000000000000 : ℝ)*(major1) + (2247395947919641/50000000000000 : ℝ)*(major2) + (96257869160377/1562500000000 : ℝ)*(sp0) + (6160541641758269/100000000000000 : ℝ)*(sp1) + (6160541860898641/100000000000000 : ℝ)*(sp2) + (88406810742547/3125000000000 : ℝ)*(sp3) + (8030123409/20000000000000 : ℝ)*(sp4) + (2711633683/12500000000000 : ℝ)*(sp7) + (353629954603871/12500000000000 : ℝ)*(f.failure) + (6160543776881173/100000000000000 : ℝ)*(f.sum) + (287249617158683/37240000000000000000000000000 : ℝ)*base65 + (3407054661739249039/931000000000000000000000000000000 : ℝ)*base67 + (5115947548559350379/465500000000000000000000000000000 : ℝ)*base69 + (4911576800387750961/931000000000000000000000000000000 : ℝ)*base72 + (32615011064843/37240000000000000000000000000 : ℝ)*base73 + (940161757029649621/465500000000000000000000000000000 : ℝ)*base76 + (933790421683224039/931000000000000000000000000000000 : ℝ)*base77 + (20602501336682775961/931000000000000000000000000000000 : ℝ)*base80 + (79956548931741/18620000000000000000000000000 : ℝ)*base81 + (1028513/250000000000000000000 : ℝ)*base90 + (1028513/250000000000000000000 : ℝ)*base92 + (3528513/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34042383257177672321127/9310000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22711341/5000000000000 : ℝ)*(base19) + (37599497/6250000000000 : ℝ)*(base23) + (40947139/100000000000000 : ℝ)*(upper3) + (6352947/12500000000000 : ℝ)*(lower4) + (23686691/25000000000000 : ℝ)*(upper5) + (2264001131125449/50000000000000 : ℝ)*(major0) + (2264001131125449/50000000000000 : ℝ)*(major1) + (2264001131125449/50000000000000 : ℝ)*(major2) + (9367751751/100000000000000 : ℝ)*(sp1) + (5717062513/50000000000000 : ℝ)*(sp2) + (6206062030996797/100000000000000 : ℝ)*(sp4) + (248242088360729/4000000000000 : ℝ)*(sp5) + (3103024997639909/50000000000000 : ℝ)*(sp6) + (142497118581017/5000000000000 : ℝ)*(sp7) + (142497118581017/5000000000000 : ℝ)*(f.failure) + (6206062030996797/100000000000000 : ℝ)*(f.sum) + (8912908976669/9310000000000000000000000000 : ℝ)*base65 + (1016863916436853169/465500000000000000000000000000000 : ℝ)*base68 + (4250095185988353169/465500000000000000000000000000000 : ℝ)*base70 + (1267620786126146831/465500000000000000000000000000000 : ℝ)*base71 + (15707217000281/9310000000000000000000000000 : ℝ)*base74 + (4720843356567146831/465500000000000000000000000000000 : ℝ)*base75 + (3674815362745146831/465500000000000000000000000000000 : ℝ)*base77 + (4345279783898853169/465500000000000000000000000000000 : ℝ)*base80 + (19578193514091/9310000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (550649/100000000000000000000 : ℝ)*base89 + (550649/100000000000000000000 : ℝ)*base91 + (550649/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1447_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7469/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14791/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1447_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1447_s5_0 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-489150727/2500000000 : ℝ)*x 0 + (5407445413/10000000000 : ℝ)*x 1 + (5247150767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489150727/2500000000 : ℝ)^4407 ≤ (149264907053/1250000000000 : ℝ)^3383 := by
    have hnat : (489150727 : ℕ)^4407*1250000000000^3383 ≤ 149264907053^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489150727 2500000000 149264907053 1250000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407445413/10000000000 : ℝ)^4407 ≤ (8978453816721/20000000000000 : ℝ)^3383 := by
    have hnat : (5407445413 : ℕ)^4407*20000000000000^3383 ≤ 8978453816721^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407445413 10000000000 8978453816721 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247150767/10000000000 : ℝ)^4407 ≤ (43166538338259/100000000000000 : ℝ)^3383 := by
    have hnat : (5247150767 : ℕ)^4407*100000000000000^3383 ≤ 43166538338259^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247150767 10000000000 43166538338259 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489150727/2500000000 : ℝ), (5407445413/10000000000 : ℝ), (5247150767/10000000000 : ℝ)] ![(149264907053/1250000000000 : ℝ), (8978453816721/20000000000000 : ℝ), (43166538338259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489150727/2500000000 : ℝ)|^4407 ≤ (149264907053/1250000000000 : ℝ)^3383
        have hw : |(-489150727/2500000000 : ℝ)|=(489150727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407445413/10000000000 : ℝ)|^4407 ≤ (8978453816721/20000000000000 : ℝ)^3383
        have hw : |(5407445413/10000000000 : ℝ)|=(5407445413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247150767/10000000000 : ℝ)|^4407 ≤ (43166538338259/100000000000000 : ℝ)^3383
        have hw : |(5247150767/10000000000 : ℝ)|=(5247150767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s5_1 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346981711/10000000000 : ℝ)*x 0 + (-407640387/2000000000 : ℝ)*x 1 + (655893847/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346981711/10000000000 : ℝ)^4407 ≤ (884789454893/2000000000000 : ℝ)^3383 := by
    have hnat : (5346981711 : ℕ)^4407*2000000000000^3383 ≤ 884789454893^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346981711 10000000000 884789454893 2000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (407640387/2000000000 : ℝ)^4407 ≤ (2518797758879/20000000000000 : ℝ)^3383 := by
    have hnat : (407640387 : ℕ)^4407*20000000000000^3383 ≤ 2518797758879^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407640387 2000000000 2518797758879 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655893847/1250000000 : ℝ)^4407 ≤ (4316653843471/10000000000000 : ℝ)^3383 := by
    have hnat : (655893847 : ℕ)^4407*10000000000000^3383 ≤ 4316653843471^3383*1250000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655893847 1250000000 4316653843471 10000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346981711/10000000000 : ℝ), (-407640387/2000000000 : ℝ), (655893847/1250000000 : ℝ)] ![(884789454893/2000000000000 : ℝ), (2518797758879/20000000000000 : ℝ), (4316653843471/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346981711/10000000000 : ℝ)|^4407 ≤ (884789454893/2000000000000 : ℝ)^3383
        have hw : |(5346981711/10000000000 : ℝ)|=(5346981711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-407640387/2000000000 : ℝ)|^4407 ≤ (2518797758879/20000000000000 : ℝ)^3383
        have hw : |(-407640387/2000000000 : ℝ)|=(407640387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655893847/1250000000 : ℝ)|^4407 ≤ (4316653843471/10000000000000 : ℝ)^3383
        have hw : |(655893847/1250000000 : ℝ)|=(655893847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s5_2 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673490849/5000000000 : ℝ)*x 0 + (5247150791/10000000000 : ℝ)*x 1 + (-407640387/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673490849/5000000000 : ℝ)^4407 ≤ (8847894520907/20000000000000 : ℝ)^3383 := by
    have hnat : (2673490849 : ℕ)^4407*20000000000000^3383 ≤ 8847894520907^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673490849 5000000000 8847894520907 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247150791/10000000000 : ℝ)^4407 ≤ (43166538595461/100000000000000 : ℝ)^3383 := by
    have hnat : (5247150791 : ℕ)^4407*100000000000000^3383 ≤ 43166538595461^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247150791 10000000000 43166538595461 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407640387/2000000000 : ℝ)^4407 ≤ (2518797758879/20000000000000 : ℝ)^3383 := by
    have hnat : (407640387 : ℕ)^4407*20000000000000^3383 ≤ 2518797758879^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407640387 2000000000 2518797758879 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673490849/5000000000 : ℝ), (5247150791/10000000000 : ℝ), (-407640387/2000000000 : ℝ)] ![(8847894520907/20000000000000 : ℝ), (43166538595461/100000000000000 : ℝ), (2518797758879/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673490849/5000000000 : ℝ)|^4407 ≤ (8847894520907/20000000000000 : ℝ)^3383
        have hw : |(2673490849/5000000000 : ℝ)|=(2673490849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247150791/10000000000 : ℝ)|^4407 ≤ (43166538595461/100000000000000 : ℝ)^3383
        have hw : |(5247150791/10000000000 : ℝ)|=(5247150791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407640387/2000000000 : ℝ)|^4407 ≤ (2518797758879/20000000000000 : ℝ)^3383
        have hw : |(-407640387/2000000000 : ℝ)|=(407640387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s5_3 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149941149/5000000000 : ℝ)*x 0 + (2064257039/5000000000 : ℝ)*x 1 + (4477573157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149941149/5000000000 : ℝ)^4407 ≤ (6660971278931/20000000000000 : ℝ)^3383 := by
    have hnat : (2149941149 : ℕ)^4407*20000000000000^3383 ≤ 6660971278931^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149941149 5000000000 6660971278931 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064257039/5000000000 : ℝ)^4407 ≤ (3948284416447/12500000000000 : ℝ)^3383 := by
    have hnat : (2064257039 : ℕ)^4407*12500000000000^3383 ≤ 3948284416447^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064257039 5000000000 3948284416447 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477573157/10000000000 : ℝ)^4407 ≤ (17554434128369/50000000000000 : ℝ)^3383 := by
    have hnat : (4477573157 : ℕ)^4407*50000000000000^3383 ≤ 17554434128369^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477573157 10000000000 17554434128369 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149941149/5000000000 : ℝ), (2064257039/5000000000 : ℝ), (4477573157/10000000000 : ℝ)] ![(6660971278931/20000000000000 : ℝ), (3948284416447/12500000000000 : ℝ), (17554434128369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149941149/5000000000 : ℝ)|^4407 ≤ (6660971278931/20000000000000 : ℝ)^3383
        have hw : |(2149941149/5000000000 : ℝ)|=(2149941149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2064257039/5000000000 : ℝ)|^4407 ≤ (3948284416447/12500000000000 : ℝ)^3383
        have hw : |(2064257039/5000000000 : ℝ)|=(2064257039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477573157/10000000000 : ℝ)|^4407 ≤ (17554434128369/50000000000000 : ℝ)^3383
        have hw : |(4477573157/10000000000 : ℝ)|=(4477573157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s5_4 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-489153533/2500000000 : ℝ)*x 0 + (2623865463/5000000000 : ℝ)*x 1 + (1351715561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489153533/2500000000 : ℝ)^4407 ≤ (11941281799007/100000000000000 : ℝ)^3383 := by
    have hnat : (489153533 : ℕ)^4407*100000000000000^3383 ≤ 11941281799007^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489153533 2500000000 11941281799007 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623865463/5000000000 : ℝ)^4407 ≤ (21586377942317/50000000000000 : ℝ)^3383 := by
    have hnat : (2623865463 : ℕ)^4407*50000000000000^3383 ≤ 21586377942317^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623865463 5000000000 21586377942317 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351715561/2500000000 : ℝ)^4407 ≤ (5610745287723/12500000000000 : ℝ)^3383 := by
    have hnat : (1351715561 : ℕ)^4407*12500000000000^3383 ≤ 5610745287723^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351715561 2500000000 5610745287723 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489153533/2500000000 : ℝ), (2623865463/5000000000 : ℝ), (1351715561/2500000000 : ℝ)] ![(11941281799007/100000000000000 : ℝ), (21586377942317/50000000000000 : ℝ), (5610745287723/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489153533/2500000000 : ℝ)|^4407 ≤ (11941281799007/100000000000000 : ℝ)^3383
        have hw : |(-489153533/2500000000 : ℝ)|=(489153533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623865463/5000000000 : ℝ)|^4407 ≤ (21586377942317/50000000000000 : ℝ)^3383
        have hw : |(2623865463/5000000000 : ℝ)|=(2623865463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351715561/2500000000 : ℝ)|^4407 ≤ (5610745287723/12500000000000 : ℝ)^3383
        have hw : |(1351715561/2500000000 : ℝ)|=(1351715561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s5_5 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305237097/10000000000 : ℝ)*x 0 + (-1878490503/10000000000 : ℝ)*x 1 + (1351715573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305237097/10000000000 : ℝ)^4407 ≤ (10947519404739/25000000000000 : ℝ)^3383 := by
    have hnat : (5305237097 : ℕ)^4407*25000000000000^3383 ≤ 10947519404739^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305237097 10000000000 10947519404739 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1878490503/10000000000 : ℝ)^4407 ≤ (11323959542277/100000000000000 : ℝ)^3383 := by
    have hnat : (1878490503 : ℕ)^4407*100000000000000^3383 ≤ 11323959542277^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878490503 10000000000 11323959542277 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351715573/2500000000 : ℝ)^4407 ≤ (44885962820879/100000000000000 : ℝ)^3383 := by
    have hnat : (1351715573 : ℕ)^4407*100000000000000^3383 ≤ 44885962820879^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351715573 2500000000 44885962820879 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305237097/10000000000 : ℝ), (-1878490503/10000000000 : ℝ), (1351715573/2500000000 : ℝ)] ![(10947519404739/25000000000000 : ℝ), (11323959542277/100000000000000 : ℝ), (44885962820879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305237097/10000000000 : ℝ)|^4407 ≤ (10947519404739/25000000000000 : ℝ)^3383
        have hw : |(5305237097/10000000000 : ℝ)|=(5305237097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1878490503/10000000000 : ℝ)|^4407 ≤ (11323959542277/100000000000000 : ℝ)^3383
        have hw : |(-1878490503/10000000000 : ℝ)|=(1878490503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351715573/2500000000 : ℝ)|^4407 ≤ (44885962820879/100000000000000 : ℝ)^3383
        have hw : |(1351715573/2500000000 : ℝ)|=(1351715573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s5_6 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326309279/2500000000 : ℝ)*x 0 + (5406862297/10000000000 : ℝ)*x 1 + (-1878490471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326309279/2500000000 : ℝ)^4407 ≤ (21895038911627/50000000000000 : ℝ)^3383 := by
    have hnat : (1326309279 : ℕ)^4407*50000000000000^3383 ≤ 21895038911627^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326309279 2500000000 21895038911627 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406862297/10000000000 : ℝ)^4407 ≤ (5610745359369/12500000000000 : ℝ)^3383 := by
    have hnat : (5406862297 : ℕ)^4407*12500000000000^3383 ≤ 5610745359369^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406862297 10000000000 5610745359369 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1878490471/10000000000 : ℝ)^4407 ≤ (1415494911373/12500000000000 : ℝ)^3383 := by
    have hnat : (1878490471 : ℕ)^4407*12500000000000^3383 ≤ 1415494911373^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878490471 10000000000 1415494911373 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326309279/2500000000 : ℝ), (5406862297/10000000000 : ℝ), (-1878490471/10000000000 : ℝ)] ![(21895038911627/50000000000000 : ℝ), (5610745359369/12500000000000 : ℝ), (1415494911373/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326309279/2500000000 : ℝ)|^4407 ≤ (21895038911627/50000000000000 : ℝ)^3383
        have hw : |(1326309279/2500000000 : ℝ)|=(1326309279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406862297/10000000000 : ℝ)|^4407 ≤ (5610745359369/12500000000000 : ℝ)^3383
        have hw : |(5406862297/10000000000 : ℝ)|=(5406862297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1878490471/10000000000 : ℝ)|^4407 ≤ (1415494911373/12500000000000 : ℝ)^3383
        have hw : |(-1878490471/10000000000 : ℝ)|=(1878490471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s5_7 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (17199627/40000000 : ℝ)*x 0 + (895261969/2000000000 : ℝ)*x 1 + (2064891971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17199627/40000000 : ℝ)^4407 ≤ (666102062321/2000000000000 : ℝ)^3383 := by
    have hnat : (17199627 : ℕ)^4407*2000000000000^3383 ≤ 666102062321^3383*40000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17199627 40000000 666102062321 2000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895261969/2000000000 : ℝ)^4407 ≤ (35095964764419/100000000000000 : ℝ)^3383 := by
    have hnat : (895261969 : ℕ)^4407*100000000000000^3383 ≤ 35095964764419^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895261969 2000000000 35095964764419 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064891971/5000000000 : ℝ)^4407 ≤ (31598932108507/100000000000000 : ℝ)^3383 := by
    have hnat : (2064891971 : ℕ)^4407*100000000000000^3383 ≤ 31598932108507^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064891971 5000000000 31598932108507 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17199627/40000000 : ℝ), (895261969/2000000000 : ℝ), (2064891971/5000000000 : ℝ)] ![(666102062321/2000000000000 : ℝ), (35095964764419/100000000000000 : ℝ), (31598932108507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17199627/40000000 : ℝ)|^4407 ≤ (666102062321/2000000000000 : ℝ)^3383
        have hw : |(17199627/40000000 : ℝ)|=(17199627/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895261969/2000000000 : ℝ)|^4407 ≤ (35095964764419/100000000000000 : ℝ)^3383
        have hw : |(895261969/2000000000 : ℝ)|=(895261969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064891971/5000000000 : ℝ)|^4407 ≤ (31598932108507/100000000000000 : ℝ)^3383
        have hw : |(2064891971/5000000000 : ℝ)|=(2064891971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1447_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11373/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14769/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1419/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1419/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1419/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1419/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1419/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1419/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1419/12500 : ℝ) ^ (2203/512 : ℝ) ≤ (8594635404411521/100000000000000000000 : ℝ) := by
    have hpowers : (1419/12500 : ℝ)^2203 ≤ (8594635404411521/100000000000000000000 : ℝ)^512 := by
      have hnat : (1419 : ℕ)^2203*100000000000000000000^512 ≤ 8594635404411521^512*12500^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1419 12500 8594635404411521 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1419/12500 : ℝ)) (X := (8594635404411521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14791/100000 : ℝ) ^ (2203/512 : ℝ) ≤ (26836129034593351/100000000000000000000 : ℝ) := by
    have hpowers : (14791/100000 : ℝ)^2203 ≤ (26836129034593351/100000000000000000000 : ℝ)^512 := by
      have hnat : (14791 : ℕ)^2203*100000000000000000000^512 ≤ 26836129034593351^512*100000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14791 100000 26836129034593351 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14791/100000 : ℝ)) (X := (26836129034593351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008594635404411521/50000000000000000000 : ℝ) ≤ (200007989401819/200000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50008594635404411521/50000000000000000000 : ℝ)^512 ≤ (200007989401819/200000000000000 : ℝ)^2203 := by
      have hnat : (50008594635404411521 : ℕ)^512*200000000000000^2203 ≤ 200007989401819^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008594635404411521 50000000000000000000 200007989401819 200000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200007989401819/200000000000000 : ℝ)) (X := (50008594635404411521/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504428845554875609/12500000000000000000 : ℝ) ≤ (10000823335684489/10000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (12504428845554875609/12500000000000000000 : ℝ)^512 ≤ (10000823335684489/10000000000000000 : ℝ)^2203 := by
      have hnat : (12504428845554875609 : ℕ)^512*10000000000000000^2203 ≤ 10000823335684489^2203*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504428845554875609 12500000000000000000 10000823335684489 10000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000823335684489/10000000000000000 : ℝ)) (X := (12504428845554875609/12500000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026836129034593351/50000000000000000000 : ℝ) ≤ (2500311800319507/2500000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50026836129034593351/50000000000000000000 : ℝ)^512 ≤ (2500311800319507/2500000000000000 : ℝ)^2203 := by
      have hnat : (50026836129034593351 : ℕ)^512*2500000000000000^2203 ≤ 2500311800319507^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026836129034593351 50000000000000000000 2500311800319507 2500000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500311800319507/2500000000000000 : ℝ)) (X := (50026836129034593351/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8594635404411521/100000000000000000000 : ℝ) ≤ ((17190875166603533797/17195000000000000000 : ℝ)+2*(423865593539/343900000000000 : ℝ)*(1419/12500 : ℝ))^(2203/512 : ℝ) := by
    rw [show (17190875166603533797/17195000000000000000 : ℝ)+2*(423865593539/343900000000000 : ℝ)*(1419/12500 : ℝ)=(200007989401819/200000000000000 : ℝ) by norm_num, show 1+2*(8594635404411521/100000000000000000000 : ℝ)=(50008594635404411521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26836129034593351/100000000000000000000 : ℝ)+(8594635404411521/100000000000000000000 : ℝ) ≤ ((17190875166603533797/17195000000000000000 : ℝ)+(423865593539/343900000000000 : ℝ)*((14791/100000 : ℝ)+(1419/12500 : ℝ)))^(2203/512 : ℝ) := by
    rw [show (17190875166603533797/17195000000000000000 : ℝ)+(423865593539/343900000000000 : ℝ)*((14791/100000 : ℝ)+(1419/12500 : ℝ))=(10000823335684489/10000000000000000 : ℝ) by norm_num, show 1+(26836129034593351/100000000000000000000 : ℝ)+(8594635404411521/100000000000000000000 : ℝ)=(12504428845554875609/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26836129034593351/100000000000000000000 : ℝ) ≤ ((17190875166603533797/17195000000000000000 : ℝ)+2*(423865593539/343900000000000 : ℝ)*(14791/100000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (17190875166603533797/17195000000000000000 : ℝ)+2*(423865593539/343900000000000 : ℝ)*(14791/100000 : ℝ)=(2500311800319507/2500000000000000 : ℝ) by norm_num, show 1+2*(26836129034593351/100000000000000000000 : ℝ)=(50026836129034593351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17190875166603533797/17195000000000000000 : ℝ)*(X 1 0+X 2 0)+(423865593539/343900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (14791/100000 : ℝ)) (c := (17190875166603533797/17195000000000000000 : ℝ)) (alpha := (423865593539/343900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17190875166603533797/17195000000000000000 : ℝ)*(X 0 1+X 2 1)+(423865593539/343900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (14791/100000 : ℝ)) (c := (17190875166603533797/17195000000000000000 : ℝ)) (alpha := (423865593539/343900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17190875166603533797/17195000000000000000 : ℝ)*(X 0 2+X 1 2)+(423865593539/343900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (14791/100000 : ℝ)) (c := (17190875166603533797/17195000000000000000 : ℝ)) (alpha := (423865593539/343900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-489150727/2500000000 : ℝ)*X 0 0+(5407445413/10000000000 : ℝ)*X 0 1+(5247150767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346981711/10000000000 : ℝ)*X 1 0+(-407640387/2000000000 : ℝ)*X 1 1+(655893847/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673490849/5000000000 : ℝ)*X 2 0+(5247150791/10000000000 : ℝ)*X 2 1+(-407640387/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2149941149/5000000000 : ℝ)*X 0 0+(2064257039/5000000000 : ℝ)*X 0 1+(4477573157/10000000000 : ℝ)*X 0 2+(2149941149/5000000000 : ℝ)*X 1 0+(2064257039/5000000000 : ℝ)*X 1 1+(4477573157/10000000000 : ℝ)*X 1 2+(2149941149/5000000000 : ℝ)*X 2 0+(2064257039/5000000000 : ℝ)*X 2 1+(4477573157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-489153533/2500000000 : ℝ)*X 0 0+(2623865463/5000000000 : ℝ)*X 0 1+(1351715561/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305237097/10000000000 : ℝ)*X 1 0+(-1878490503/10000000000 : ℝ)*X 1 1+(1351715573/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326309279/2500000000 : ℝ)*X 2 0+(5406862297/10000000000 : ℝ)*X 2 1+(-1878490471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((17199627/40000000 : ℝ)*X 0 0+(895261969/2000000000 : ℝ)*X 0 1+(2064891971/5000000000 : ℝ)*X 0 2+(17199627/40000000 : ℝ)*X 1 0+(895261969/2000000000 : ℝ)*X 1 1+(2064891971/5000000000 : ℝ)*X 1 2+(17199627/40000000 : ℝ)*X 2 0+(895261969/2000000000 : ℝ)*X 2 1+(2064891971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1678708902291382345222363653/171950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1776729693/100000000000000 : ℝ)*(base19) + (829327949/50000000000000 : ℝ)*(base23) + (27511839/50000000000000 : ℝ)*(lower2) + (118970549/50000000000000 : ℝ)*(upper3) + (162150571/100000000000000 : ℝ)*(upper5) + (910346986743239/20000000000000 : ℝ)*(major0) + (910346986743239/20000000000000 : ℝ)*(major1) + (910346986743239/20000000000000 : ℝ)*(major2) + (6238551406926231/100000000000000 : ℝ)*(sp0) + (6238587957214759/100000000000000 : ℝ)*(sp1) + (3119294037644277/50000000000000 : ℝ)*(sp2) + (716215342767481/25000000000000 : ℝ)*(sp3) + (19163509111/50000000000000 : ℝ)*(sp4) + (9218496107/50000000000000 : ℝ)*(sp7) + (1432439904031069/50000000000000 : ℝ)*(f.failure) + (6238589733944453/100000000000000 : ℝ)*(f.sum) + (2827604002379/3439000000000000000000000000 : ℝ)*base66 + (5443047432538498483/343900000000000000000000000000000 : ℝ)*base67 + (1623543361694898483/343900000000000000000000000000000 : ℝ)*base69 + (2078287318244898483/343900000000000000000000000000000 : ℝ)*base71 + (10334644887889/1719500000000000000000000000 : ℝ)*base73 + (9963247792242798483/343900000000000000000000000000000 : ℝ)*base75 + (2960524236657198483/343900000000000000000000000000000 : ℝ)*base77 + (3906129362746398483/343900000000000000000000000000000 : ℝ)*base79 + (14087293347447/3439000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10442307/1000000000000000000000 : ℝ)*base90 + (10442307/1000000000000000000000 : ℝ)*base92 + (10442307/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31483326072982958485932081/6878000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (156153511/25000000000000 : ℝ)*(base19) + (711617731/100000000000000 : ℝ)*(base23) + (23628073/25000000000000 : ℝ)*(upper3) + (12086079/50000000000000 : ℝ)*(lower4) + (47224169/50000000000000 : ℝ)*(upper5) + (36679620329409/800000000000 : ℝ)*(major0) + (36679620329409/800000000000 : ℝ)*(major1) + (36679620329409/800000000000 : ℝ)*(major2) + (13934205371/100000000000000 : ℝ)*(sp1) + (16340645457/100000000000000 : ℝ)*(sp2) + (1256823565875339/20000000000000 : ℝ)*(sp4) + (6284103270557281/100000000000000 : ℝ)*(sp5) + (1571025194278377/25000000000000 : ℝ)*(sp6) + (28857871003957/1000000000000 : ℝ)*(sp7) + (28857871003957/1000000000000 : ℝ)*(f.failure) + (1256823565875339/20000000000000 : ℝ)*(f.sum) + (1028978319627/687800000000000000000000000 : ℝ)*base65 + (161698747248165973/13756000000000000000000000000000 : ℝ)*base67 + (36285062634205973/13756000000000000000000000000000 : ℝ)*base69 + (6022618416357973/13756000000000000000000000000000 : ℝ)*base71 + (555422893133/3439000000000000000000000000 : ℝ)*base74 + (96784468299997973/13756000000000000000000000000000 : ℝ)*base75 + (90170144093898027/13756000000000000000000000000000 : ℝ)*base78 + (91240318924342027/13756000000000000000000000000000 : ℝ)*base80 + (441715330021/429875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (15829/20000000000000000000 : ℝ)*base89 + (15829/20000000000000000000 : ℝ)*base91 + (15829/20000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1447_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1447_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1447_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7873/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1447_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1447_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1447_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7873/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1447_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
