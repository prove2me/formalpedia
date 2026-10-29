-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1420_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:51:28.026745+00:00
-- url     : https://prove2.me/submissions/99135dd0-191e-49e2-a37a-06ad42b27897

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
theorem support_rectangle_w1420_s6_0 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-123653441/625000000 : ℝ)*x 0 + (5408683613/10000000000 : ℝ)*x 1 + (5246701973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123653441/625000000 : ℝ)^1095 ≤ (12067508476277/100000000000000 : ℝ)^839 := by
    have hnat : (123653441 : ℕ)^1095*100000000000000^839 ≤ 12067508476277^839*625000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123653441 625000000 12067508476277 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408683613/10000000000 : ℝ)^1095 ≤ (44838503093657/100000000000000 : ℝ)^839 := by
    have hnat : (5408683613 : ℕ)^1095*100000000000000^839 ≤ 44838503093657^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408683613 10000000000 44838503093657 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246701973/10000000000 : ℝ)^1095 ≤ (21546994207289/50000000000000 : ℝ)^839 := by
    have hnat : (5246701973 : ℕ)^1095*50000000000000^839 ≤ 21546994207289^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246701973 10000000000 21546994207289 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-123653441/625000000 : ℝ), (5408683613/10000000000 : ℝ), (5246701973/10000000000 : ℝ)] ![(12067508476277/100000000000000 : ℝ), (44838503093657/100000000000000 : ℝ), (21546994207289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-123653441/625000000 : ℝ)|^1095 ≤ (12067508476277/100000000000000 : ℝ)^839
        have hw : |(-123653441/625000000 : ℝ)|=(123653441/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408683613/10000000000 : ℝ)|^1095 ≤ (44838503093657/100000000000000 : ℝ)^839
        have hw : |(5408683613/10000000000 : ℝ)|=(5408683613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246701973/10000000000 : ℝ)|^1095 ≤ (21546994207289/50000000000000 : ℝ)^839
        have hw : |(5246701973/10000000000 : ℝ)|=(5246701973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s6_1 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069503043/2000000000 : ℝ)*x 0 + (-1030464453/5000000000 : ℝ)*x 1 + (655837743/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069503043/2000000000 : ℝ)^1095 ≤ (22088914826097/50000000000000 : ℝ)^839 := by
    have hnat : (1069503043 : ℕ)^1095*50000000000000^839 ≤ 22088914826097^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069503043 2000000000 22088914826097 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030464453/5000000000 : ℝ)^1095 ≤ (6364091114727/50000000000000 : ℝ)^839 := by
    have hnat : (1030464453 : ℕ)^1095*50000000000000^839 ≤ 6364091114727^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030464453 5000000000 6364091114727 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655837743/1250000000 : ℝ)^1095 ≤ (43093988103707/100000000000000 : ℝ)^839 := by
    have hnat : (655837743 : ℕ)^1095*100000000000000^839 ≤ 43093988103707^839*1250000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655837743 1250000000 43093988103707 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069503043/2000000000 : ℝ), (-1030464453/5000000000 : ℝ), (655837743/1250000000 : ℝ)] ![(22088914826097/50000000000000 : ℝ), (6364091114727/50000000000000 : ℝ), (43093988103707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069503043/2000000000 : ℝ)|^1095 ≤ (22088914826097/50000000000000 : ℝ)^839
        have hw : |(1069503043/2000000000 : ℝ)|=(1069503043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030464453/5000000000 : ℝ)|^1095 ≤ (6364091114727/50000000000000 : ℝ)^839
        have hw : |(-1030464453/5000000000 : ℝ)|=(1030464453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655837743/1250000000 : ℝ)|^1095 ≤ (43093988103707/100000000000000 : ℝ)^839
        have hw : |(655837743/1250000000 : ℝ)|=(655837743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s6_2 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069503077/2000000000 : ℝ)*x 0 + (1049340359/2000000000 : ℝ)*x 1 + (-515232219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069503077/2000000000 : ℝ)^1095 ≤ (11044457871289/25000000000000 : ℝ)^839 := by
    have hnat : (1069503077 : ℕ)^1095*25000000000000^839 ≤ 11044457871289^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069503077 2000000000 11044457871289 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049340359/2000000000 : ℝ)^1095 ≤ (5386748313309/12500000000000 : ℝ)^839 := by
    have hnat : (1049340359 : ℕ)^1095*12500000000000^839 ≤ 5386748313309^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049340359 2000000000 5386748313309 12500000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515232219/2500000000 : ℝ)^1095 ≤ (6364090993821/50000000000000 : ℝ)^839 := by
    have hnat : (515232219 : ℕ)^1095*50000000000000^839 ≤ 6364090993821^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515232219 2500000000 6364090993821 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069503077/2000000000 : ℝ), (1049340359/2000000000 : ℝ), (-515232219/2500000000 : ℝ)] ![(11044457871289/25000000000000 : ℝ), (5386748313309/12500000000000 : ℝ), (6364090993821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069503077/2000000000 : ℝ)|^1095 ≤ (11044457871289/25000000000000 : ℝ)^839
        have hw : |(1069503077/2000000000 : ℝ)|=(1069503077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049340359/2000000000 : ℝ)|^1095 ≤ (5386748313309/12500000000000 : ℝ)^839
        have hw : |(1049340359/2000000000 : ℝ)|=(1049340359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-515232219/2500000000 : ℝ)|^1095 ≤ (6364090993821/50000000000000 : ℝ)^839
        have hw : |(-515232219/2500000000 : ℝ)|=(515232219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s6_3 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4306628881/10000000000 : ℝ)*x 0 + (4135193379/10000000000 : ℝ)*x 1 + (140139341/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306628881/10000000000 : ℝ)^1095 ≤ (6660910199529/20000000000000 : ℝ)^839 := by
    have hnat : (4306628881 : ℕ)^1095*20000000000000^839 ≤ 6660910199529^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306628881 10000000000 6660910199529 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4135193379/10000000000 : ℝ)^1095 ≤ (252678937409/800000000000 : ℝ)^839 := by
    have hnat : (4135193379 : ℕ)^1095*800000000000^839 ≤ 252678937409^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135193379 10000000000 252678937409 800000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140139341/312500000 : ℝ)^1095 ≤ (35110581808573/100000000000000 : ℝ)^839 := by
    have hnat : (140139341 : ℕ)^1095*100000000000000^839 ≤ 35110581808573^839*312500000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140139341 312500000 35110581808573 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306628881/10000000000 : ℝ), (4135193379/10000000000 : ℝ), (140139341/312500000 : ℝ)] ![(6660910199529/20000000000000 : ℝ), (252678937409/800000000000 : ℝ), (35110581808573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306628881/10000000000 : ℝ)|^1095 ≤ (6660910199529/20000000000000 : ℝ)^839
        have hw : |(4306628881/10000000000 : ℝ)|=(4306628881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4135193379/10000000000 : ℝ)|^1095 ≤ (252678937409/800000000000 : ℝ)^839
        have hw : |(4135193379/10000000000 : ℝ)|=(4135193379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140139341/312500000 : ℝ)|^1095 ≤ (35110581808573/100000000000000 : ℝ)^839
        have hw : |(140139341/312500000 : ℝ)|=(140139341/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s6_4 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1978466451/10000000000 : ℝ)*x 0 + (524728591/1000000000 : ℝ)*x 1 + (1081619333/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1978466451/10000000000 : ℝ)^1095 ≤ (12067599186929/100000000000000 : ℝ)^839 := by
    have hnat : (1978466451 : ℕ)^1095*100000000000000^839 ≤ 12067599186929^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978466451 10000000000 12067599186929 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524728591/1000000000 : ℝ)^1095 ≤ (172400992591/400000000000 : ℝ)^839 := by
    have hnat : (524728591 : ℕ)^1095*400000000000^839 ≤ 172400992591^839*1000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524728591 1000000000 172400992591 400000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081619333/2000000000 : ℝ)^1095 ≤ (22416076324593/50000000000000 : ℝ)^839 := by
    have hnat : (1081619333 : ℕ)^1095*50000000000000^839 ≤ 22416076324593^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081619333 2000000000 22416076324593 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1978466451/10000000000 : ℝ), (524728591/1000000000 : ℝ), (1081619333/2000000000 : ℝ)] ![(12067599186929/100000000000000 : ℝ), (172400992591/400000000000 : ℝ), (22416076324593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1978466451/10000000000 : ℝ)|^1095 ≤ (12067599186929/100000000000000 : ℝ)^839
        have hw : |(-1978466451/10000000000 : ℝ)|=(1978466451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524728591/1000000000 : ℝ)|^1095 ≤ (172400992591/400000000000 : ℝ)^839
        have hw : |(524728591/1000000000 : ℝ)|=(524728591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081619333/2000000000 : ℝ)|^1095 ≤ (22416076324593/50000000000000 : ℝ)^839
        have hw : |(1081619333/2000000000 : ℝ)|=(1081619333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s6_5 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305441633/10000000000 : ℝ)*x 0 + (-189953411/1000000000 : ℝ)*x 1 + (338006053/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305441633/10000000000 : ℝ)^1095 ≤ (43724732404951/100000000000000 : ℝ)^839 := by
    have hnat : (5305441633 : ℕ)^1095*100000000000000^839 ≤ 43724732404951^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305441633 10000000000 43724732404951 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189953411/1000000000 : ℝ)^1095 ≤ (1430389118049/12500000000000 : ℝ)^839 := by
    have hnat : (189953411 : ℕ)^1095*12500000000000^839 ≤ 1430389118049^839*1000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189953411 1000000000 1430389118049 12500000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338006053/625000000 : ℝ)^1095 ≤ (44832154629109/100000000000000 : ℝ)^839 := by
    have hnat : (338006053 : ℕ)^1095*100000000000000^839 ≤ 44832154629109^839*625000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338006053 625000000 44832154629109 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305441633/10000000000 : ℝ), (-189953411/1000000000 : ℝ), (338006053/625000000 : ℝ)] ![(43724732404951/100000000000000 : ℝ), (1430389118049/12500000000000 : ℝ), (44832154629109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305441633/10000000000 : ℝ)|^1095 ≤ (43724732404951/100000000000000 : ℝ)^839
        have hw : |(5305441633/10000000000 : ℝ)|=(5305441633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-189953411/1000000000 : ℝ)|^1095 ≤ (1430389118049/12500000000000 : ℝ)^839
        have hw : |(-189953411/1000000000 : ℝ)|=(189953411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338006053/625000000 : ℝ)|^1095 ≤ (44832154629109/100000000000000 : ℝ)^839
        have hw : |(338006053/625000000 : ℝ)|=(338006053/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s6_6 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652720581/5000000000 : ℝ)*x 0 + (1352024367/2500000000 : ℝ)*x 1 + (-1899533901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652720581/5000000000 : ℝ)^1095 ≤ (21862363669397/50000000000000 : ℝ)^839 := by
    have hnat : (2652720581 : ℕ)^1095*50000000000000^839 ≤ 21862363669397^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652720581 5000000000 21862363669397 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352024367/2500000000 : ℝ)^1095 ≤ (44832161337047/100000000000000 : ℝ)^839 := by
    have hnat : (1352024367 : ℕ)^1095*100000000000000^839 ≤ 44832161337047^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352024367 2500000000 44832161337047 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1899533901/10000000000 : ℝ)^1095 ≤ (11443111301173/100000000000000 : ℝ)^839 := by
    have hnat : (1899533901 : ℕ)^1095*100000000000000^839 ≤ 11443111301173^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899533901 10000000000 11443111301173 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652720581/5000000000 : ℝ), (1352024367/2500000000 : ℝ), (-1899533901/10000000000 : ℝ)] ![(21862363669397/50000000000000 : ℝ), (44832161337047/100000000000000 : ℝ), (11443111301173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652720581/5000000000 : ℝ)|^1095 ≤ (21862363669397/50000000000000 : ℝ)^839
        have hw : |(2652720581/5000000000 : ℝ)|=(2652720581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352024367/2500000000 : ℝ)|^1095 ≤ (44832161337047/100000000000000 : ℝ)^839
        have hw : |(1352024367/2500000000 : ℝ)|=(1352024367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1899533901/10000000000 : ℝ)|^1095 ≤ (11443111301173/100000000000000 : ℝ)^839
        have hw : |(-1899533901/10000000000 : ℝ)|=(1899533901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s6_7 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4306653271/10000000000 : ℝ)*x 0 + (179328017/400000000 : ℝ)*x 1 + (2068229291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306653271/10000000000 : ℝ)^1095 ≤ (6660959433001/20000000000000 : ℝ)^839 := by
    have hnat : (4306653271 : ℕ)^1095*20000000000000^839 ≤ 6660959433001^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306653271 10000000000 6660959433001 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179328017/400000000 : ℝ)^1095 ≤ (4387215339683/12500000000000 : ℝ)^839 := by
    have hnat : (179328017 : ℕ)^1095*12500000000000^839 ≤ 4387215339683^839*400000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179328017 400000000 4387215339683 12500000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068229291/5000000000 : ℝ)^1095 ≤ (15798740051423/50000000000000 : ℝ)^839 := by
    have hnat : (2068229291 : ℕ)^1095*50000000000000^839 ≤ 15798740051423^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068229291 5000000000 15798740051423 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306653271/10000000000 : ℝ), (179328017/400000000 : ℝ), (2068229291/5000000000 : ℝ)] ![(6660959433001/20000000000000 : ℝ), (4387215339683/12500000000000 : ℝ), (15798740051423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306653271/10000000000 : ℝ)|^1095 ≤ (6660959433001/20000000000000 : ℝ)^839
        have hw : |(4306653271/10000000000 : ℝ)|=(4306653271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179328017/400000000 : ℝ)|^1095 ≤ (4387215339683/12500000000000 : ℝ)^839
        have hw : |(179328017/400000000 : ℝ)|=(179328017/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2068229291/5000000000 : ℝ)|^1095 ≤ (15798740051423/50000000000000 : ℝ)^839
        have hw : |(2068229291/5000000000 : ℝ)|=(2068229291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1420_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11321/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (461/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (5659/50000 : ℝ) ^ (4379/1024 : ℝ) ≤ (8986110377545357/100000000000000000000 : ℝ) := by
    have hpowers : (5659/50000 : ℝ)^4379 ≤ (8986110377545357/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5659 : ℕ)^4379*100000000000000000000^1024 ≤ 8986110377545357^1024*50000^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5659 50000 8986110377545357 100000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5659/50000 : ℝ)) (X := (8986110377545357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3689/25000 : ℝ) ^ (4379/1024 : ℝ) ≤ (27938609550950069/100000000000000000000 : ℝ) := by
    have hpowers : (3689/25000 : ℝ)^4379 ≤ (27938609550950069/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3689 : ℕ)^4379*100000000000000000000^1024 ≤ 27938609550950069^1024*25000^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3689 25000 27938609550950069 100000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3689/25000 : ℝ)) (X := (27938609550950069/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008986110377545357/50000000000000000000 : ℝ) ≤ (10000420239487217/10000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (50008986110377545357/50000000000000000000 : ℝ)^1024 ≤ (10000420239487217/10000000000000000 : ℝ)^4379 := by
      have hnat : (50008986110377545357 : ℕ)^1024*10000000000000000^4379 ≤ 10000420239487217^4379*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008986110377545357 50000000000000000000 10000420239487217 10000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000420239487217/10000000000000000 : ℝ)) (X := (50008986110377545357/50000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018462359964247713/50000000000000000000 : ℝ) ≤ (10000863337885197/10000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (50018462359964247713/50000000000000000000 : ℝ)^1024 ≤ (10000863337885197/10000000000000000 : ℝ)^4379 := by
      have hnat : (50018462359964247713 : ℕ)^1024*10000000000000000^4379 ≤ 10000863337885197^4379*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018462359964247713 50000000000000000000 10000863337885197 10000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000863337885197/10000000000000000 : ℝ)) (X := (50018462359964247713/50000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027938609550950069/50000000000000000000 : ℝ) ≤ (10001306436283177/10000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (50027938609550950069/50000000000000000000 : ℝ)^1024 ≤ (10001306436283177/10000000000000000 : ℝ)^4379 := by
      have hnat : (50027938609550950069 : ℕ)^1024*10000000000000000^4379 ≤ 10001306436283177^4379*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027938609550950069 50000000000000000000 10001306436283177 10000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001306436283177/10000000000000000 : ℝ)) (X := (50027938609550950069/50000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8986110377545357/100000000000000000000 : ℝ) ≤ ((17185707404010188383/17190000000000000000 : ℝ)+2*(22154919899/17190000000000 : ℝ)*(5659/50000 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (17185707404010188383/17190000000000000000 : ℝ)+2*(22154919899/17190000000000 : ℝ)*(5659/50000 : ℝ)=(10000420239487217/10000000000000000 : ℝ) by norm_num, show 1+2*(8986110377545357/100000000000000000000 : ℝ)=(50008986110377545357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27938609550950069/100000000000000000000 : ℝ)+(8986110377545357/100000000000000000000 : ℝ) ≤ ((17185707404010188383/17190000000000000000 : ℝ)+(22154919899/17190000000000 : ℝ)*((3689/25000 : ℝ)+(5659/50000 : ℝ)))^(4379/1024 : ℝ) := by
    rw [show (17185707404010188383/17190000000000000000 : ℝ)+(22154919899/17190000000000 : ℝ)*((3689/25000 : ℝ)+(5659/50000 : ℝ))=(10000863337885197/10000000000000000 : ℝ) by norm_num, show 1+(27938609550950069/100000000000000000000 : ℝ)+(8986110377545357/100000000000000000000 : ℝ)=(50018462359964247713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27938609550950069/100000000000000000000 : ℝ) ≤ ((17185707404010188383/17190000000000000000 : ℝ)+2*(22154919899/17190000000000 : ℝ)*(3689/25000 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (17185707404010188383/17190000000000000000 : ℝ)+2*(22154919899/17190000000000 : ℝ)*(3689/25000 : ℝ)=(10001306436283177/10000000000000000 : ℝ) by norm_num, show 1+2*(27938609550950069/100000000000000000000 : ℝ)=(50027938609550950069/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17185707404010188383/17190000000000000000 : ℝ)*(X 1 0+X 2 0)+(22154919899/17190000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (17185707404010188383/17190000000000000000 : ℝ)) (alpha := (22154919899/17190000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17185707404010188383/17190000000000000000 : ℝ)*(X 0 1+X 2 1)+(22154919899/17190000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (17185707404010188383/17190000000000000000 : ℝ)) (alpha := (22154919899/17190000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17185707404010188383/17190000000000000000 : ℝ)*(X 0 2+X 1 2)+(22154919899/17190000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (17185707404010188383/17190000000000000000 : ℝ)) (alpha := (22154919899/17190000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-123653441/625000000 : ℝ)*X 0 0+(5408683613/10000000000 : ℝ)*X 0 1+(5246701973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069503043/2000000000 : ℝ)*X 1 0+(-1030464453/5000000000 : ℝ)*X 1 1+(655837743/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069503077/2000000000 : ℝ)*X 2 0+(1049340359/2000000000 : ℝ)*X 2 1+(-515232219/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4306628881/10000000000 : ℝ)*X 0 0+(4135193379/10000000000 : ℝ)*X 0 1+(140139341/312500000 : ℝ)*X 0 2+(4306628881/10000000000 : ℝ)*X 1 0+(4135193379/10000000000 : ℝ)*X 1 1+(140139341/312500000 : ℝ)*X 1 2+(4306628881/10000000000 : ℝ)*X 2 0+(4135193379/10000000000 : ℝ)*X 2 1+(140139341/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1978466451/10000000000 : ℝ)*X 0 0+(524728591/1000000000 : ℝ)*X 0 1+(1081619333/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305441633/10000000000 : ℝ)*X 1 0+(-189953411/1000000000 : ℝ)*X 1 1+(338006053/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652720581/5000000000 : ℝ)*X 2 0+(1352024367/2500000000 : ℝ)*X 2 1+(-1899533901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4306653271/10000000000 : ℝ)*X 0 0+(179328017/400000000 : ℝ)*X 0 1+(2068229291/5000000000 : ℝ)*X 0 2+(4306653271/10000000000 : ℝ)*X 1 0+(179328017/400000000 : ℝ)*X 1 1+(2068229291/5000000000 : ℝ)*X 1 2+(4306653271/10000000000 : ℝ)*X 2 0+(179328017/400000000 : ℝ)*X 2 1+(2068229291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (658331437507973031653324617/57300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57273483/3125000000000 : ℝ)*(base19) + (353145489/20000000000000 : ℝ)*(base23) + (14079257/10000000000000 : ℝ)*(lower2) + (52010387/20000000000000 : ℝ)*(upper3) + (34746119/25000000000000 : ℝ)*(upper5) + (903679976329667/20000000000000 : ℝ)*(major0) + (903679976329667/20000000000000 : ℝ)*(major1) + (903679976329667/20000000000000 : ℝ)*(major2) + (6173575491757957/100000000000000 : ℝ)*(sp0) + (6173610413993667/100000000000000 : ℝ)*(sp1) + (3086805240508839/50000000000000 : ℝ)*(sp2) + (715791812887181/25000000000000 : ℝ)*(sp3) + (18377493583/50000000000000 : ℝ)*(sp4) + (4970507329/25000000000000 : ℝ)*(sp7) + (71579678339451/2500000000000 : ℝ)*(f.failure) + (6173612246745123/100000000000000 : ℝ)*(f.sum) + (274658496859/53718750000000000000000000 : ℝ)*base66 + (272116559347339829/38200000000000000000000000000000 : ℝ)*base67 + (266397203624539829/38200000000000000000000000000000 : ℝ)*base69 + (460164215505739829/38200000000000000000000000000000 : ℝ)*base71 + (1366142799511/429750000000000000000000000 : ℝ)*base73 + (470391388319139829/38200000000000000000000000000000 : ℝ)*base75 + (446189409230739829/38200000000000000000000000000000 : ℝ)*base77 + (363092063143539829/38200000000000000000000000000000 : ℝ)*base79 + (1838560221619/859500000000000000000000000 : ℝ)*base82 + (2611801/250000000000000000000 : ℝ)*base90 + (2611801/250000000000000000000 : ℝ)*base92 + (2611801/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1262696660465223419015813237/286500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3502101/3125000000000 : ℝ)*(base21) + (65079477/50000000000000 : ℝ)*(base29) + (66808147/100000000000000 : ℝ)*(upper2) + (43574749/100000000000000 : ℝ)*(upper3) + (109460407/100000000000000 : ℝ)*(lower4) + (4551239194198231/100000000000000 : ℝ)*(major0) + (910247864871437/20000000000000 : ℝ)*(major1) + (910247864871437/20000000000000 : ℝ)*(major2) + (950868919/6250000000000 : ℝ)*(sp2) + (2012806841/50000000000000 : ℝ)*(sp3) + (1554620476600697/25000000000000 : ℝ)*(sp4) + (3109240888121917/50000000000000 : ℝ)*(sp5) + (3109233225136949/50000000000000 : ℝ)*(sp6) + (36049907122341/1250000000000 : ℝ)*(sp7) + (1441998297700481/50000000000000 : ℝ)*(f.failure) + (1554620476600697/25000000000000 : ℝ)*(f.sum) + (329577872129/429750000000000000000000000 : ℝ)*base66 + (80971608903498181/38200000000000000000000000000000 : ℝ)*base68 + (553247774412698181/38200000000000000000000000000000 : ℝ)*base70 + (351123218581594497/191000000000000000000000000000000 : ℝ)*base71 + (594473270681/859500000000000000000000000 : ℝ)*base73 + (267451672569898181/38200000000000000000000000000000 : ℝ)*base76 + (5528493446127594497/191000000000000000000000000000000 : ℝ)*base77 + (2982965264567098181/38200000000000000000000000000000 : ℝ)*base80 + (915106463557/859500000000000000000000000 : ℝ)*base82 + (13981669/5000000000000000000000 : ℝ)*base89 + (13981669/5000000000000000000000 : ℝ)*base91 + (13981669/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1420_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1420_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1420_s7_0 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-989229947/5000000000 : ℝ)*x 0 + (2704328399/5000000000 : ℝ)*x 1 + (1049345089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989229947/5000000000 : ℝ)^1095 ≤ (12067546989477/100000000000000 : ℝ)^839 := by
    have hnat : (989229947 : ℕ)^1095*100000000000000^839 ≤ 12067546989477^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989229947 5000000000 12067546989477 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704328399/5000000000 : ℝ)^1095 ≤ (44838212965981/100000000000000 : ℝ)^839 := by
    have hnat : (2704328399 : ℕ)^1095*100000000000000^839 ≤ 44838212965981^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704328399 5000000000 44838212965981 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049345089/2000000000 : ℝ)^1095 ≤ (8618848005489/20000000000000 : ℝ)^839 := by
    have hnat : (1049345089 : ℕ)^1095*20000000000000^839 ≤ 8618848005489^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049345089 2000000000 8618848005489 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989229947/5000000000 : ℝ), (2704328399/5000000000 : ℝ), (1049345089/2000000000 : ℝ)] ![(12067546989477/100000000000000 : ℝ), (44838212965981/100000000000000 : ℝ), (8618848005489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989229947/5000000000 : ℝ)|^1095 ≤ (12067546989477/100000000000000 : ℝ)^839
        have hw : |(-989229947/5000000000 : ℝ)|=(989229947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704328399/5000000000 : ℝ)|^1095 ≤ (44838212965981/100000000000000 : ℝ)^839
        have hw : |(2704328399/5000000000 : ℝ)|=(2704328399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049345089/2000000000 : ℝ)|^1095 ≤ (8618848005489/20000000000000 : ℝ)^839
        have hw : |(1049345089/2000000000 : ℝ)|=(1049345089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s7_1 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347507811/10000000000 : ℝ)*x 0 + (-515226909/2500000000 : ℝ)*x 1 + (1049345077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347507811/10000000000 : ℝ)^1095 ≤ (44177749821331/100000000000000 : ℝ)^839 := by
    have hnat : (5347507811 : ℕ)^1095*100000000000000^839 ≤ 44177749821331^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347507811 10000000000 44177749821331 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515226909/2500000000 : ℝ)^1095 ≤ (2545602157087/20000000000000 : ℝ)^839 := by
    have hnat : (515226909 : ℕ)^1095*20000000000000^839 ≤ 2545602157087^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515226909 2500000000 2545602157087 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049345077/2000000000 : ℝ)^1095 ≤ (21547119692131/50000000000000 : ℝ)^839 := by
    have hnat : (1049345077 : ℕ)^1095*50000000000000^839 ≤ 21547119692131^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049345077 2000000000 21547119692131 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347507811/10000000000 : ℝ), (-515226909/2500000000 : ℝ), (1049345077/2000000000 : ℝ)] ![(44177749821331/100000000000000 : ℝ), (2545602157087/20000000000000 : ℝ), (21547119692131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347507811/10000000000 : ℝ)|^1095 ≤ (44177749821331/100000000000000 : ℝ)^839
        have hw : |(5347507811/10000000000 : ℝ)|=(5347507811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-515226909/2500000000 : ℝ)|^1095 ≤ (2545602157087/20000000000000 : ℝ)^839
        have hw : |(-515226909/2500000000 : ℝ)|=(515226909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049345077/2000000000 : ℝ)|^1095 ≤ (21547119692131/50000000000000 : ℝ)^839
        have hw : |(1049345077/2000000000 : ℝ)|=(1049345077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s7_2 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336876979/2500000000 : ℝ)*x 0 + (5246725251/10000000000 : ℝ)*x 1 + (-2060907673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336876979/2500000000 : ℝ)^1095 ≤ (22088875476727/50000000000000 : ℝ)^839 := by
    have hnat : (1336876979 : ℕ)^1095*50000000000000^839 ≤ 22088875476727^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336876979 2500000000 22088875476727 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246725251/10000000000 : ℝ)^1095 ≤ (43094237947821/100000000000000 : ℝ)^839 := by
    have hnat : (5246725251 : ℕ)^1095*100000000000000^839 ≤ 43094237947821^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246725251 10000000000 43094237947821 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2060907673/10000000000 : ℝ)^1095 ≤ (3182002770917/25000000000000 : ℝ)^839 := by
    have hnat : (2060907673 : ℕ)^1095*25000000000000^839 ≤ 3182002770917^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060907673 10000000000 3182002770917 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336876979/2500000000 : ℝ), (5246725251/10000000000 : ℝ), (-2060907673/10000000000 : ℝ)] ![(22088875476727/50000000000000 : ℝ), (43094237947821/100000000000000 : ℝ), (3182002770917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336876979/2500000000 : ℝ)|^1095 ≤ (22088875476727/50000000000000 : ℝ)^839
        have hw : |(1336876979/2500000000 : ℝ)|=(1336876979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246725251/10000000000 : ℝ)|^1095 ≤ (43094237947821/100000000000000 : ℝ)^839
        have hw : |(5246725251/10000000000 : ℝ)|=(5246725251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2060907673/10000000000 : ℝ)|^1095 ≤ (3182002770917/25000000000000 : ℝ)^839
        have hw : |(-2060907673/10000000000 : ℝ)|=(2060907673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s7_3 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4306630729/10000000000 : ℝ)*x 0 + (1033811793/2500000000 : ℝ)*x 1 + (4484404609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306630729/10000000000 : ℝ)^1095 ≤ (1332182785977/4000000000000 : ℝ)^839 := by
    have hnat : (4306630729 : ℕ)^1095*4000000000000^839 ≤ 1332182785977^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306630729 10000000000 1332182785977 4000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033811793/2500000000 : ℝ)^1095 ≤ (6317080683919/20000000000000 : ℝ)^839 := by
    have hnat : (1033811793 : ℕ)^1095*20000000000000^839 ≤ 6317080683919^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033811793 2500000000 6317080683919 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484404609/10000000000 : ℝ)^1095 ≤ (7022005384671/20000000000000 : ℝ)^839 := by
    have hnat : (4484404609 : ℕ)^1095*20000000000000^839 ≤ 7022005384671^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484404609 10000000000 7022005384671 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306630729/10000000000 : ℝ), (1033811793/2500000000 : ℝ), (4484404609/10000000000 : ℝ)] ![(1332182785977/4000000000000 : ℝ), (6317080683919/20000000000000 : ℝ), (7022005384671/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306630729/10000000000 : ℝ)|^1095 ≤ (1332182785977/4000000000000 : ℝ)^839
        have hw : |(4306630729/10000000000 : ℝ)|=(4306630729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033811793/2500000000 : ℝ)|^1095 ≤ (6317080683919/20000000000000 : ℝ)^839
        have hw : |(1033811793/2500000000 : ℝ)|=(1033811793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484404609/10000000000 : ℝ)|^1095 ≤ (7022005384671/20000000000000 : ℝ)^839
        have hw : |(4484404609/10000000000 : ℝ)|=(4484404609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s7_4 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-989235793/5000000000 : ℝ)*x 0 + (1311827199/2500000000 : ℝ)*x 1 + (5408070211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989235793/5000000000 : ℝ)^1095 ≤ (12067640064489/100000000000000 : ℝ)^839 := by
    have hnat : (989235793 : ℕ)^1095*100000000000000^839 ≤ 12067640064489^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989235793 5000000000 12067640064489 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311827199/2500000000 : ℝ)^1095 ≤ (21550246743599/50000000000000 : ℝ)^839 := by
    have hnat : (1311827199 : ℕ)^1095*50000000000000^839 ≤ 21550246743599^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311827199 2500000000 21550246743599 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408070211/10000000000 : ℝ)^1095 ≤ (22415933218431/50000000000000 : ℝ)^839 := by
    have hnat : (5408070211 : ℕ)^1095*50000000000000^839 ≤ 22415933218431^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408070211 10000000000 22415933218431 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989235793/5000000000 : ℝ), (1311827199/2500000000 : ℝ), (5408070211/10000000000 : ℝ)] ![(12067640064489/100000000000000 : ℝ), (21550246743599/50000000000000 : ℝ), (22415933218431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989235793/5000000000 : ℝ)|^1095 ≤ (12067640064489/100000000000000 : ℝ)^839
        have hw : |(-989235793/5000000000 : ℝ)|=(989235793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311827199/2500000000 : ℝ)|^1095 ≤ (21550246743599/50000000000000 : ℝ)^839
        have hw : |(1311827199/2500000000 : ℝ)|=(1311827199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408070211/10000000000 : ℝ)|^1095 ≤ (22415933218431/50000000000000 : ℝ)^839
        have hw : |(5408070211/10000000000 : ℝ)|=(5408070211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s7_5 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4306656109/10000000000 : ℝ)*x 0 + (448314589/1000000000 : ℝ)*x 1 + (10341279/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306656109/10000000000 : ℝ)^1095 ≤ (33304825808861/100000000000000 : ℝ)^839 := by
    have hnat : (4306656109 : ℕ)^1095*100000000000000^839 ≤ 33304825808861^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306656109 10000000000 33304825808861 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448314589/1000000000 : ℝ)^1095 ≤ (17548582754661/50000000000000 : ℝ)^839 := by
    have hnat : (448314589 : ℕ)^1095*50000000000000^839 ≤ 17548582754661^839*1000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448314589 1000000000 17548582754661 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10341279/25000000 : ℝ)^1095 ≤ (31598008669933/100000000000000 : ℝ)^839 := by
    have hnat : (10341279 : ℕ)^1095*100000000000000^839 ≤ 31598008669933^839*25000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10341279 25000000 31598008669933 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306656109/10000000000 : ℝ), (448314589/1000000000 : ℝ), (10341279/25000000 : ℝ)] ![(33304825808861/100000000000000 : ℝ), (17548582754661/50000000000000 : ℝ), (31598008669933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306656109/10000000000 : ℝ)|^1095 ≤ (33304825808861/100000000000000 : ℝ)^839
        have hw : |(4306656109/10000000000 : ℝ)|=(4306656109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448314589/1000000000 : ℝ)|^1095 ≤ (17548582754661/50000000000000 : ℝ)^839
        have hw : |(448314589/1000000000 : ℝ)|=(448314589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10341279/25000000 : ℝ)|^1095 ≤ (31598008669933/100000000000000 : ℝ)^839
        have hw : |(10341279/25000000 : ℝ)|=(10341279/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1420_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5661/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (461/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11321/100000 : ℝ) ^ (4379/1024 : ℝ) ≤ (8996300675455751/100000000000000000000 : ℝ) := by
    have hpowers : (11321/100000 : ℝ)^4379 ≤ (8996300675455751/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11321 : ℕ)^4379*100000000000000000000^1024 ≤ 8996300675455751^1024*100000^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11321 100000 8996300675455751 100000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11321/100000 : ℝ)) (X := (8996300675455751/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (461/3125 : ℝ) ^ (4379/1024 : ℝ) ≤ (279062369003241/1000000000000000000 : ℝ) := by
    have hpowers : (461/3125 : ℝ)^4379 ≤ (279062369003241/1000000000000000000 : ℝ)^1024 := by
      have hnat : (461 : ℕ)^4379*1000000000000000000^1024 ≤ 279062369003241^1024*3125^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        461 3125 279062369003241 1000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (461/3125 : ℝ)) (X := (279062369003241/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008996300675455751/50000000000000000000 : ℝ) ≤ (10000420716008233/10000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (50008996300675455751/50000000000000000000 : ℝ)^1024 ≤ (10000420716008233/10000000000000000 : ℝ)^4379 := by
      have hnat : (50008996300675455751 : ℕ)^1024*10000000000000000^4379 ≤ 10000420716008233^4379*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008996300675455751 50000000000000000000 10000420716008233 10000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000420716008233/10000000000000000 : ℝ)) (X := (50008996300675455751/50000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036902537575779851/100000000000000000000 : ℝ) ≤ (100008628193123/100000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (100036902537575779851/100000000000000000000 : ℝ)^1024 ≤ (100008628193123/100000000000000 : ℝ)^4379 := by
      have hnat : (100036902537575779851 : ℕ)^1024*100000000000000^4379 ≤ 100008628193123^4379*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036902537575779851 100000000000000000000 100008628193123 100000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100008628193123/100000000000000 : ℝ)) (X := (100036902537575779851/100000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (500279062369003241/500000000000000000 : ℝ) ≤ (10001304922616367/10000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (500279062369003241/500000000000000000 : ℝ)^1024 ≤ (10001304922616367/10000000000000000 : ℝ)^4379 := by
      have hnat : (500279062369003241 : ℕ)^1024*10000000000000000^4379 ≤ 10001304922616367^4379*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500279062369003241 500000000000000000 10001304922616367 10000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001304922616367/10000000000000000 : ℝ)) (X := (500279062369003241/500000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8996300675455751/100000000000000000000 : ℝ) ≤ ((34301433373613562409/34310000000000000000 : ℝ)+2*(442103304067/343100000000000 : ℝ)*(11321/100000 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (34301433373613562409/34310000000000000000 : ℝ)+2*(442103304067/343100000000000 : ℝ)*(11321/100000 : ℝ)=(10000420716008233/10000000000000000 : ℝ) by norm_num, show 1+2*(8996300675455751/100000000000000000000 : ℝ)=(50008996300675455751/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(279062369003241/1000000000000000000 : ℝ)+(8996300675455751/100000000000000000000 : ℝ) ≤ ((34301433373613562409/34310000000000000000 : ℝ)+(442103304067/343100000000000 : ℝ)*((461/3125 : ℝ)+(11321/100000 : ℝ)))^(4379/1024 : ℝ) := by
    rw [show (34301433373613562409/34310000000000000000 : ℝ)+(442103304067/343100000000000 : ℝ)*((461/3125 : ℝ)+(11321/100000 : ℝ))=(100008628193123/100000000000000 : ℝ) by norm_num, show 1+(279062369003241/1000000000000000000 : ℝ)+(8996300675455751/100000000000000000000 : ℝ)=(100036902537575779851/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(279062369003241/1000000000000000000 : ℝ) ≤ ((34301433373613562409/34310000000000000000 : ℝ)+2*(442103304067/343100000000000 : ℝ)*(461/3125 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (34301433373613562409/34310000000000000000 : ℝ)+2*(442103304067/343100000000000 : ℝ)*(461/3125 : ℝ)=(10001304922616367/10000000000000000 : ℝ) by norm_num, show 1+2*(279062369003241/1000000000000000000 : ℝ)=(500279062369003241/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34301433373613562409/34310000000000000000 : ℝ)*(X 1 0+X 2 0)+(442103304067/343100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (11321/100000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (34301433373613562409/34310000000000000000 : ℝ)) (alpha := (442103304067/343100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34301433373613562409/34310000000000000000 : ℝ)*(X 0 1+X 2 1)+(442103304067/343100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (11321/100000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (34301433373613562409/34310000000000000000 : ℝ)) (alpha := (442103304067/343100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34301433373613562409/34310000000000000000 : ℝ)*(X 0 2+X 1 2)+(442103304067/343100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (11321/100000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (34301433373613562409/34310000000000000000 : ℝ)) (alpha := (442103304067/343100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-989229947/5000000000 : ℝ)*X 0 0+(2704328399/5000000000 : ℝ)*X 0 1+(1049345089/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347507811/10000000000 : ℝ)*X 1 0+(-515226909/2500000000 : ℝ)*X 1 1+(1049345077/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336876979/2500000000 : ℝ)*X 2 0+(5246725251/10000000000 : ℝ)*X 2 1+(-2060907673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4306630729/10000000000 : ℝ)*X 0 0+(1033811793/2500000000 : ℝ)*X 0 1+(4484404609/10000000000 : ℝ)*X 0 2+(4306630729/10000000000 : ℝ)*X 1 0+(1033811793/2500000000 : ℝ)*X 1 1+(4484404609/10000000000 : ℝ)*X 1 2+(4306630729/10000000000 : ℝ)*X 2 0+(1033811793/2500000000 : ℝ)*X 2 1+(4484404609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-989235793/5000000000 : ℝ)*X 0 0+(1311827199/2500000000 : ℝ)*X 0 1+(5408070211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4306656109/10000000000 : ℝ)*X 0 0+(448314589/1000000000 : ℝ)*X 0 1+(10341279/25000000 : ℝ)*X 0 2+(4306656109/10000000000 : ℝ)*X 1 0+(448314589/1000000000 : ℝ)*X 1 1+(10341279/25000000 : ℝ)*X 1 2+(4306656109/10000000000 : ℝ)*X 2 0+(448314589/1000000000 : ℝ)*X 2 1+(10341279/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6723484547499463803183/1072187500000000000000000000 : ℝ) := by norm_num
    linear_combination (1039860901/100000000000000 : ℝ)*(base19) + (49079823/5000000000000 : ℝ)*(base23) + (239999/250000000000 : ℝ)*(lower2) + (201070737/100000000000000 : ℝ)*(upper3) + (43371773/100000000000000 : ℝ)*(upper5) + (4519774714409569/100000000000000 : ℝ)*(major0) + (4519774714409569/100000000000000 : ℝ)*(major1) + (4519774714409569/100000000000000 : ℝ)*(major2) + (385967188505737/6250000000000 : ℝ)*(sp0) + (6175489852218993/100000000000000 : ℝ)*(sp1) + (3087744955241717/50000000000000 : ℝ)*(sp2) + (358005765086911/12500000000000 : ℝ)*(sp3) + (7937994051/50000000000000 : ℝ)*(sp4) + (2441403387/20000000000000 : ℝ)*(sp5) + (89501822741007/3125000000000 : ℝ)*(f.failure) + (3087745446039947/50000000000000 : ℝ)*(f.sum) + (66388755852919/8577500000000000000000000000 : ℝ)*base65 + (24857652155433408279/3431000000000000000000000000000000 : ℝ)*base68 + (20372927631306591721/3431000000000000000000000000000000 : ℝ)*base69 + (11314964366009408279/3431000000000000000000000000000000 : ℝ)*base72 + (27984631539733/17155000000000000000000000000 : ℝ)*base73 + (31069977905526408279/3431000000000000000000000000000000 : ℝ)*base76 + (9436378196739591721/3431000000000000000000000000000000 : ℝ)*base77 + (10220052189660591721/3431000000000000000000000000000000 : ℝ)*base79 + (146657823554073/17155000000000000000000000000 : ℝ)*base81 + (44957/312500000000000000000 : ℝ)*base90 + (44957/312500000000000000000 : ℝ)*base92 + (44957/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1420_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1420_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1420_box_0 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1817142463/10000000000 : ℝ)*x 0 + (5386641919/10000000000 : ℝ)*x 1 + (673330309/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1817142463/10000000000 : ℝ)^1095 ≤ (10799656154457/100000000000000 : ℝ)^839 := by
    have hnat : (1817142463 : ℕ)^1095*100000000000000^839 ≤ 10799656154457^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817142463 10000000000 10799656154457 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386641919/10000000000 : ℝ)^1095 ≤ (44600168928961/100000000000000 : ℝ)^839 := by
    have hnat : (5386641919 : ℕ)^1095*100000000000000^839 ≤ 44600168928961^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386641919 10000000000 44600168928961 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673330309/1250000000 : ℝ)^1095 ≤ (11150043726189/25000000000000 : ℝ)^839 := by
    have hnat : (673330309 : ℕ)^1095*25000000000000^839 ≤ 11150043726189^839*1250000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673330309 1250000000 11150043726189 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1817142463/10000000000 : ℝ), (5386641919/10000000000 : ℝ), (673330309/1250000000 : ℝ)] ![(10799656154457/100000000000000 : ℝ), (44600168928961/100000000000000 : ℝ), (11150043726189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1817142463/10000000000 : ℝ)|^1095 ≤ (10799656154457/100000000000000 : ℝ)^839
        have hw : |(-1817142463/10000000000 : ℝ)|=(1817142463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386641919/10000000000 : ℝ)|^1095 ≤ (44600168928961/100000000000000 : ℝ)^839
        have hw : |(5386641919/10000000000 : ℝ)|=(5386641919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673330309/1250000000 : ℝ)|^1095 ≤ (11150043726189/25000000000000 : ℝ)^839
        have hw : |(673330309/1250000000 : ℝ)|=(673330309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_1 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642998593/5000000000 : ℝ)*x 0 + (-1955377677/10000000000 : ℝ)*x 1 + (1077328421/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642998593/5000000000 : ℝ)^1095 ≤ (43515701612439/100000000000000 : ℝ)^839 := by
    have hnat : (2642998593 : ℕ)^1095*100000000000000^839 ≤ 43515701612439^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642998593 5000000000 43515701612439 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955377677/10000000000 : ℝ)^1095 ≤ (2971031859381/25000000000000 : ℝ)^839 := by
    have hnat : (1955377677 : ℕ)^1095*25000000000000^839 ≤ 2971031859381^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955377677 10000000000 2971031859381 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077328421/2000000000 : ℝ)^1095 ≤ (44600170938903/100000000000000 : ℝ)^839 := by
    have hnat : (1077328421 : ℕ)^1095*100000000000000^839 ≤ 44600170938903^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077328421 2000000000 44600170938903 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642998593/5000000000 : ℝ), (-1955377677/10000000000 : ℝ), (1077328421/2000000000 : ℝ)] ![(43515701612439/100000000000000 : ℝ), (2971031859381/25000000000000 : ℝ), (44600170938903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642998593/5000000000 : ℝ)|^1095 ≤ (43515701612439/100000000000000 : ℝ)^839
        have hw : |(2642998593/5000000000 : ℝ)|=(2642998593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1955377677/10000000000 : ℝ)|^1095 ≤ (2971031859381/25000000000000 : ℝ)^839
        have hw : |(-1955377677/10000000000 : ℝ)|=(1955377677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077328421/2000000000 : ℝ)|^1095 ≤ (44600170938903/100000000000000 : ℝ)^839
        have hw : |(1077328421/2000000000 : ℝ)|=(1077328421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_2 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5285997681/10000000000 : ℝ)*x 0 + (5386642069/10000000000 : ℝ)*x 1 + (-391075411/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285997681/10000000000 : ℝ)^1095 ≤ (43515706930783/100000000000000 : ℝ)^839 := by
    have hnat : (5285997681 : ℕ)^1095*100000000000000^839 ≤ 43515706930783^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285997681 10000000000 43515706930783 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386642069/10000000000 : ℝ)^1095 ≤ (22300085274941/50000000000000 : ℝ)^839 := by
    have hnat : (5386642069 : ℕ)^1095*50000000000000^839 ≤ 22300085274941^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386642069 10000000000 22300085274941 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391075411/2000000000 : ℝ)^1095 ≤ (11884122503751/100000000000000 : ℝ)^839 := by
    have hnat : (391075411 : ℕ)^1095*100000000000000^839 ≤ 11884122503751^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391075411 2000000000 11884122503751 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285997681/10000000000 : ℝ), (5386642069/10000000000 : ℝ), (-391075411/2000000000 : ℝ)] ![(43515706930783/100000000000000 : ℝ), (22300085274941/50000000000000 : ℝ), (11884122503751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285997681/10000000000 : ℝ)|^1095 ≤ (43515706930783/100000000000000 : ℝ)^839
        have hw : |(5285997681/10000000000 : ℝ)|=(5285997681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386642069/10000000000 : ℝ)|^1095 ≤ (22300085274941/50000000000000 : ℝ)^839
        have hw : |(5386642069/10000000000 : ℝ)|=(5386642069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-391075411/2000000000 : ℝ)|^1095 ≤ (11884122503751/100000000000000 : ℝ)^839
        have hw : |(-391075411/2000000000 : ℝ)|=(391075411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_3 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2226555141/5000000000 : ℝ)*x 0 + (2118558403/5000000000 : ℝ)*x 1 + (2118558447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2226555141/5000000000 : ℝ)^1095 ≤ (34790593190633/100000000000000 : ℝ)^839 := by
    have hnat : (2226555141 : ℕ)^1095*100000000000000^839 ≤ 34790593190633^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226555141 5000000000 34790593190633 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118558403/5000000000 : ℝ)^1095 ≤ (63681060453/195312500000 : ℝ)^839 := by
    have hnat : (2118558403 : ℕ)^1095*195312500000^839 ≤ 63681060453^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118558403 5000000000 63681060453 195312500000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118558447/5000000000 : ℝ)^1095 ≤ (32604703835717/100000000000000 : ℝ)^839 := by
    have hnat : (2118558447 : ℕ)^1095*100000000000000^839 ≤ 32604703835717^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118558447 5000000000 32604703835717 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2226555141/5000000000 : ℝ), (2118558403/5000000000 : ℝ), (2118558447/5000000000 : ℝ)] ![(34790593190633/100000000000000 : ℝ), (63681060453/195312500000 : ℝ), (32604703835717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2226555141/5000000000 : ℝ)|^1095 ≤ (34790593190633/100000000000000 : ℝ)^839
        have hw : |(2226555141/5000000000 : ℝ)|=(2226555141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2118558403/5000000000 : ℝ)|^1095 ≤ (63681060453/195312500000 : ℝ)^839
        have hw : |(2118558403/5000000000 : ℝ)|=(2118558403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118558447/5000000000 : ℝ)|^1095 ≤ (32604703835717/100000000000000 : ℝ)^839
        have hw : |(2118558447/5000000000 : ℝ)|=(2118558447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_4 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-428501817/2000000000 : ℝ)*x 0 + (2633194917/5000000000 : ℝ)*x 1 + (2633194973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428501817/2000000000 : ℝ)^1095 ≤ (13389684775421/100000000000000 : ℝ)^839 := by
    have hnat : (428501817 : ℕ)^1095*100000000000000^839 ≤ 13389684775421^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428501817 2000000000 13389684775421 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633194917/5000000000 : ℝ)^1095 ≤ (10826289251823/25000000000000 : ℝ)^839 := by
    have hnat : (2633194917 : ℕ)^1095*25000000000000^839 ≤ 10826289251823^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633194917 5000000000 10826289251823 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633194973/5000000000 : ℝ)^1095 ≤ (43305158209271/100000000000000 : ℝ)^839 := by
    have hnat : (2633194973 : ℕ)^1095*100000000000000^839 ≤ 43305158209271^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633194973 5000000000 43305158209271 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428501817/2000000000 : ℝ), (2633194917/5000000000 : ℝ), (2633194973/5000000000 : ℝ)] ![(13389684775421/100000000000000 : ℝ), (10826289251823/25000000000000 : ℝ), (43305158209271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428501817/2000000000 : ℝ)|^1095 ≤ (13389684775421/100000000000000 : ℝ)^839
        have hw : |(-428501817/2000000000 : ℝ)|=(428501817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633194917/5000000000 : ℝ)|^1095 ≤ (10826289251823/25000000000000 : ℝ)^839
        have hw : |(2633194917/5000000000 : ℝ)|=(2633194917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633194973/5000000000 : ℝ)|^1095 ≤ (43305158209271/100000000000000 : ℝ)^839
        have hw : |(2633194973/5000000000 : ℝ)|=(2633194973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_5 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1342546829/2500000000 : ℝ)*x 0 + (-1002071701/5000000000 : ℝ)*x 1 + (5266389453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342546829/2500000000 : ℝ)^1095 ≤ (11105610280953/25000000000000 : ℝ)^839 := by
    have hnat : (1342546829 : ℕ)^1095*25000000000000^839 ≤ 11105610280953^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342546829 2500000000 11105610280953 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002071701/5000000000 : ℝ)^1095 ≤ (3068101485867/25000000000000 : ℝ)^839 := by
    have hnat : (1002071701 : ℕ)^1095*25000000000000^839 ≤ 3068101485867^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002071701 5000000000 3068101485867 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266389453/10000000000 : ℝ)^1095 ≤ (21652576459209/50000000000000 : ℝ)^839 := by
    have hnat : (5266389453 : ℕ)^1095*50000000000000^839 ≤ 21652576459209^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266389453 10000000000 21652576459209 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342546829/2500000000 : ℝ), (-1002071701/5000000000 : ℝ), (5266389453/10000000000 : ℝ)] ![(11105610280953/25000000000000 : ℝ), (3068101485867/25000000000000 : ℝ), (21652576459209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342546829/2500000000 : ℝ)|^1095 ≤ (11105610280953/25000000000000 : ℝ)^839
        have hw : |(1342546829/2500000000 : ℝ)|=(1342546829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1002071701/5000000000 : ℝ)|^1095 ≤ (3068101485867/25000000000000 : ℝ)^839
        have hw : |(-1002071701/5000000000 : ℝ)|=(1002071701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266389453/10000000000 : ℝ)|^1095 ≤ (21652576459209/50000000000000 : ℝ)^839
        have hw : |(5266389453/10000000000 : ℝ)|=(5266389453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_6 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2685093361/5000000000 : ℝ)*x 0 + (5266390581/10000000000 : ℝ)*x 1 + (-200414269/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685093361/5000000000 : ℝ)^1095 ≤ (22211217355477/50000000000000 : ℝ)^839 := by
    have hnat : (2685093361 : ℕ)^1095*50000000000000^839 ≤ 22211217355477^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685093361 5000000000 22211217355477 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266390581/10000000000 : ℝ)^1095 ≤ (43305165024061/100000000000000 : ℝ)^839 := by
    have hnat : (5266390581 : ℕ)^1095*100000000000000^839 ≤ 43305165024061^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266390581 10000000000 43305165024061 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200414269/1000000000 : ℝ)^1095 ≤ (3068100063299/25000000000000 : ℝ)^839 := by
    have hnat : (200414269 : ℕ)^1095*25000000000000^839 ≤ 3068100063299^839*1000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200414269 1000000000 3068100063299 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685093361/5000000000 : ℝ), (5266390581/10000000000 : ℝ), (-200414269/1000000000 : ℝ)] ![(22211217355477/50000000000000 : ℝ), (43305165024061/100000000000000 : ℝ), (3068100063299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685093361/5000000000 : ℝ)|^1095 ≤ (22211217355477/50000000000000 : ℝ)^839
        have hw : |(2685093361/5000000000 : ℝ)|=(2685093361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266390581/10000000000 : ℝ)|^1095 ≤ (43305165024061/100000000000000 : ℝ)^839
        have hw : |(5266390581/10000000000 : ℝ)|=(5266390581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200414269/1000000000 : ℝ)|^1095 ≤ (3068100063299/25000000000000 : ℝ)^839
        have hw : |(-200414269/1000000000 : ℝ)|=(200414269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_7 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4159114309/10000000000 : ℝ)*x 0 + (876812669/2000000000 : ℝ)*x 1 + (4384064017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4159114309/10000000000 : ℝ)^1095 ≤ (6364707238949/20000000000000 : ℝ)^839 := by
    have hnat : (4159114309 : ℕ)^1095*20000000000000^839 ≤ 6364707238949^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159114309 10000000000 6364707238949 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876812669/2000000000 : ℝ)^1095 ≤ (8522057120693/25000000000000 : ℝ)^839 := by
    have hnat : (876812669 : ℕ)^1095*25000000000000^839 ≤ 8522057120693^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876812669 2000000000 8522057120693 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4384064017/10000000000 : ℝ)^1095 ≤ (34088235302217/100000000000000 : ℝ)^839 := by
    have hnat : (4384064017 : ℕ)^1095*100000000000000^839 ≤ 34088235302217^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384064017 10000000000 34088235302217 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4159114309/10000000000 : ℝ), (876812669/2000000000 : ℝ), (4384064017/10000000000 : ℝ)] ![(6364707238949/20000000000000 : ℝ), (8522057120693/25000000000000 : ℝ), (34088235302217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4159114309/10000000000 : ℝ)|^1095 ≤ (6364707238949/20000000000000 : ℝ)^839
        have hw : |(4159114309/10000000000 : ℝ)|=(4159114309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(876812669/2000000000 : ℝ)|^1095 ≤ (8522057120693/25000000000000 : ℝ)^839
        have hw : |(876812669/2000000000 : ℝ)|=(876812669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4384064017/10000000000 : ℝ)|^1095 ≤ (34088235302217/100000000000000 : ℝ)^839
        have hw : |(4384064017/10000000000 : ℝ)|=(4384064017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_8 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1036998199/5000000000 : ℝ)*x 0 + (5183252949/10000000000 : ℝ)*x 1 + (675077693/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036998199/5000000000 : ℝ)^1095 ≤ (1283361292361/10000000000000 : ℝ)^839 := by
    have hnat : (1036998199 : ℕ)^1095*10000000000000^839 ≤ 1283361292361^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036998199 5000000000 1283361292361 10000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183252949/10000000000 : ℝ)^1095 ≤ (2650943286281/6250000000000 : ℝ)^839 := by
    have hnat : (5183252949 : ℕ)^1095*6250000000000^839 ≤ 2650943286281^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183252949 10000000000 2650943286281 6250000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675077693/1250000000 : ℝ)^1095 ≤ (44751294478473/100000000000000 : ℝ)^839 := by
    have hnat : (675077693 : ℕ)^1095*100000000000000^839 ≤ 44751294478473^839*1250000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675077693 1250000000 44751294478473 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1036998199/5000000000 : ℝ), (5183252949/10000000000 : ℝ), (675077693/1250000000 : ℝ)] ![(1283361292361/10000000000000 : ℝ), (2650943286281/6250000000000 : ℝ), (44751294478473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1036998199/5000000000 : ℝ)|^1095 ≤ (1283361292361/10000000000000 : ℝ)^839
        have hw : |(-1036998199/5000000000 : ℝ)|=(1036998199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183252949/10000000000 : ℝ)|^1095 ≤ (2650943286281/6250000000000 : ℝ)^839
        have hw : |(5183252949/10000000000 : ℝ)|=(5183252949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675077693/1250000000 : ℝ)|^1095 ≤ (44751294478473/100000000000000 : ℝ)^839
        have hw : |(675077693/1250000000 : ℝ)|=(675077693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_9 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2638102861/5000000000 : ℝ)*x 0 + (-974790577/5000000000 : ℝ)*x 1 + (5400622037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638102861/5000000000 : ℝ)^1095 ≤ (21705265300369/50000000000000 : ℝ)^839 := by
    have hnat : (2638102861 : ℕ)^1095*50000000000000^839 ≤ 21705265300369^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638102861 5000000000 21705265300369 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974790577/5000000000 : ℝ)^1095 ≤ (11838169579719/100000000000000 : ℝ)^839 := by
    have hnat : (974790577 : ℕ)^1095*100000000000000^839 ≤ 11838169579719^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974790577 5000000000 11838169579719 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400622037/10000000000 : ℝ)^1095 ≤ (8950259962023/20000000000000 : ℝ)^839 := by
    have hnat : (5400622037 : ℕ)^1095*20000000000000^839 ≤ 8950259962023^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400622037 10000000000 8950259962023 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638102861/5000000000 : ℝ), (-974790577/5000000000 : ℝ), (5400622037/10000000000 : ℝ)] ![(21705265300369/50000000000000 : ℝ), (11838169579719/100000000000000 : ℝ), (8950259962023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638102861/5000000000 : ℝ)|^1095 ≤ (21705265300369/50000000000000 : ℝ)^839
        have hw : |(2638102861/5000000000 : ℝ)|=(2638102861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-974790577/5000000000 : ℝ)|^1095 ≤ (11838169579719/100000000000000 : ℝ)^839
        have hw : |(-974790577/5000000000 : ℝ)|=(974790577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400622037/10000000000 : ℝ)|^1095 ≤ (8950259962023/20000000000000 : ℝ)^839
        have hw : |(5400622037/10000000000 : ℝ)|=(5400622037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_10 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5276205609/10000000000 : ℝ)*x 0 + (2700311187/5000000000 : ℝ)*x 1 + (-974790423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276205609/10000000000 : ℝ)^1095 ≤ (21705264693669/50000000000000 : ℝ)^839 := by
    have hnat : (5276205609 : ℕ)^1095*50000000000000^839 ≤ 21705264693669^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276205609 10000000000 21705264693669 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700311187/5000000000 : ℝ)^1095 ≤ (8950260690933/20000000000000 : ℝ)^839 := by
    have hnat : (2700311187 : ℕ)^1095*20000000000000^839 ≤ 8950260690933^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700311187 5000000000 8950260690933 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974790423/5000000000 : ℝ)^1095 ≤ (11838167138841/100000000000000 : ℝ)^839 := by
    have hnat : (974790423 : ℕ)^1095*100000000000000^839 ≤ 11838167138841^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974790423 5000000000 11838167138841 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276205609/10000000000 : ℝ), (2700311187/5000000000 : ℝ), (-974790423/5000000000 : ℝ)] ![(21705264693669/50000000000000 : ℝ), (8950260690933/20000000000000 : ℝ), (11838167138841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276205609/10000000000 : ℝ)|^1095 ≤ (21705264693669/50000000000000 : ℝ)^839
        have hw : |(5276205609/10000000000 : ℝ)|=(5276205609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700311187/5000000000 : ℝ)|^1095 ≤ (8950260690933/20000000000000 : ℝ)^839
        have hw : |(2700311187/5000000000 : ℝ)|=(2700311187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-974790423/5000000000 : ℝ)|^1095 ≤ (11838167138841/100000000000000 : ℝ)^839
        have hw : |(-974790423/5000000000 : ℝ)|=(974790423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_11 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4486731387/10000000000 : ℝ)*x 0 + (2110010077/5000000000 : ℝ)*x 1 + (168800727/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4486731387/10000000000 : ℝ)^1095 ≤ (17566902257167/50000000000000 : ℝ)^839 := by
    have hnat : (4486731387 : ℕ)^1095*50000000000000^839 ≤ 17566902257167^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486731387 10000000000 17566902257167 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110010077/5000000000 : ℝ)^1095 ≤ (32433107661871/100000000000000 : ℝ)^839 := by
    have hnat : (2110010077 : ℕ)^1095*100000000000000^839 ≤ 32433107661871^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110010077 5000000000 32433107661871 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168800727/400000000 : ℝ)^1095 ≤ (8108271952837/25000000000000 : ℝ)^839 := by
    have hnat : (168800727 : ℕ)^1095*25000000000000^839 ≤ 8108271952837^839*400000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168800727 400000000 8108271952837 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4486731387/10000000000 : ℝ), (2110010077/5000000000 : ℝ), (168800727/400000000 : ℝ)] ![(17566902257167/50000000000000 : ℝ), (32433107661871/100000000000000 : ℝ), (8108271952837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4486731387/10000000000 : ℝ)|^1095 ≤ (17566902257167/50000000000000 : ℝ)^839
        have hw : |(4486731387/10000000000 : ℝ)|=(4486731387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2110010077/5000000000 : ℝ)|^1095 ≤ (32433107661871/100000000000000 : ℝ)^839
        have hw : |(2110010077/5000000000 : ℝ)|=(2110010077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168800727/400000000 : ℝ)|^1095 ≤ (8108271952837/25000000000000 : ℝ)^839
        have hw : |(168800727/400000000 : ℝ)|=(168800727/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_12 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885850263/10000000000 : ℝ)*x 0 + (5467738433/10000000000 : ℝ)*x 1 + (1313817083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885850263/10000000000 : ℝ)^1095 ≤ (11335644962993/100000000000000 : ℝ)^839 := by
    have hnat : (1885850263 : ℕ)^1095*100000000000000^839 ≤ 11335644962993^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885850263 10000000000 11335644962993 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467738433/10000000000 : ℝ)^1095 ≤ (9095702997721/20000000000000 : ℝ)^839 := by
    have hnat : (5467738433 : ℕ)^1095*20000000000000^839 ≤ 9095702997721^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467738433 10000000000 9095702997721 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313817083/2500000000 : ℝ)^1095 ≤ (43185840040517/100000000000000 : ℝ)^839 := by
    have hnat : (1313817083 : ℕ)^1095*100000000000000^839 ≤ 43185840040517^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313817083 2500000000 43185840040517 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885850263/10000000000 : ℝ), (5467738433/10000000000 : ℝ), (1313817083/2500000000 : ℝ)] ![(11335644962993/100000000000000 : ℝ), (9095702997721/20000000000000 : ℝ), (43185840040517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885850263/10000000000 : ℝ)|^1095 ≤ (11335644962993/100000000000000 : ℝ)^839
        have hw : |(-1885850263/10000000000 : ℝ)|=(1885850263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467738433/10000000000 : ℝ)|^1095 ≤ (9095702997721/20000000000000 : ℝ)^839
        have hw : |(5467738433/10000000000 : ℝ)|=(5467738433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313817083/2500000000 : ℝ)|^1095 ≤ (43185840040517/100000000000000 : ℝ)^839
        have hw : |(1313817083/2500000000 : ℝ)|=(1313817083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_13 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2688985727/5000000000 : ℝ)*x 0 + (-502138327/2500000000 : ℝ)*x 1 + (2627634199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688985727/5000000000 : ℝ)^1095 ≤ (44506497694613/100000000000000 : ℝ)^839 := by
    have hnat : (2688985727 : ℕ)^1095*100000000000000^839 ≤ 44506497694613^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688985727 5000000000 44506497694613 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502138327/2500000000 : ℝ)^1095 ≤ (12307661542867/100000000000000 : ℝ)^839 := by
    have hnat : (502138327 : ℕ)^1095*100000000000000^839 ≤ 12307661542867^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502138327 2500000000 12307661542867 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627634199/5000000000 : ℝ)^1095 ≤ (43185840748369/100000000000000 : ℝ)^839 := by
    have hnat : (2627634199 : ℕ)^1095*100000000000000^839 ≤ 43185840748369^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627634199 5000000000 43185840748369 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688985727/5000000000 : ℝ), (-502138327/2500000000 : ℝ), (2627634199/5000000000 : ℝ)] ![(44506497694613/100000000000000 : ℝ), (12307661542867/100000000000000 : ℝ), (43185840748369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688985727/5000000000 : ℝ)|^1095 ≤ (44506497694613/100000000000000 : ℝ)^839
        have hw : |(2688985727/5000000000 : ℝ)|=(2688985727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-502138327/2500000000 : ℝ)|^1095 ≤ (12307661542867/100000000000000 : ℝ)^839
        have hw : |(-502138327/2500000000 : ℝ)|=(502138327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627634199/5000000000 : ℝ)|^1095 ≤ (43185840748369/100000000000000 : ℝ)^839
        have hw : |(2627634199/5000000000 : ℝ)|=(2627634199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_14 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5377971473/10000000000 : ℝ)*x 0 + (328454273/625000000 : ℝ)*x 1 + (-1004276661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377971473/10000000000 : ℝ)^1095 ≤ (11126624474957/25000000000000 : ℝ)^839 := by
    have hnat : (5377971473 : ℕ)^1095*25000000000000^839 ≤ 11126624474957^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377971473 10000000000 11126624474957 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328454273/625000000 : ℝ)^1095 ≤ (21592920213309/50000000000000 : ℝ)^839 := by
    have hnat : (328454273 : ℕ)^1095*50000000000000^839 ≤ 21592920213309^839*625000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328454273 625000000 21592920213309 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004276661/5000000000 : ℝ)^1095 ≤ (12307661654829/100000000000000 : ℝ)^839 := by
    have hnat : (1004276661 : ℕ)^1095*100000000000000^839 ≤ 12307661654829^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004276661 5000000000 12307661654829 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377971473/10000000000 : ℝ), (328454273/625000000 : ℝ), (-1004276661/5000000000 : ℝ)] ![(11126624474957/25000000000000 : ℝ), (21592920213309/50000000000000 : ℝ), (12307661654829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377971473/10000000000 : ℝ)|^1095 ≤ (11126624474957/25000000000000 : ℝ)^839
        have hw : |(5377971473/10000000000 : ℝ)|=(5377971473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328454273/625000000 : ℝ)|^1095 ≤ (21592920213309/50000000000000 : ℝ)^839
        have hw : |(328454273/625000000 : ℝ)|=(328454273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1004276661/5000000000 : ℝ)|^1095 ≤ (12307661654829/100000000000000 : ℝ)^839
        have hw : |(-1004276661/5000000000 : ℝ)|=(1004276661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_box_15 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (165258981/400000000 : ℝ)*x 0 + (4397642999/10000000000 : ℝ)*x 1 + (175905721/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165258981/400000000 : ℝ)^1095 ≤ (31547800391439/100000000000000 : ℝ)^839 := by
    have hnat : (165258981 : ℕ)^1095*100000000000000^839 ≤ 31547800391439^839*400000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165258981 400000000 31547800391439 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4397642999/10000000000 : ℝ)^1095 ≤ (8556524917119/25000000000000 : ℝ)^839 := by
    have hnat : (4397642999 : ℕ)^1095*25000000000000^839 ≤ 8556524917119^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4397642999 10000000000 8556524917119 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175905721/400000000 : ℝ)^1095 ≤ (34226099932573/100000000000000 : ℝ)^839 := by
    have hnat : (175905721 : ℕ)^1095*100000000000000^839 ≤ 34226099932573^839*400000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175905721 400000000 34226099932573 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165258981/400000000 : ℝ), (4397642999/10000000000 : ℝ), (175905721/400000000 : ℝ)] ![(31547800391439/100000000000000 : ℝ), (8556524917119/25000000000000 : ℝ), (34226099932573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165258981/400000000 : ℝ)|^1095 ≤ (31547800391439/100000000000000 : ℝ)^839
        have hw : |(165258981/400000000 : ℝ)|=(165258981/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4397642999/10000000000 : ℝ)|^1095 ≤ (8556524917119/25000000000000 : ℝ)^839
        have hw : |(4397642999/10000000000 : ℝ)|=(4397642999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(175905721/400000000 : ℝ)|^1095 ≤ (34226099932573/100000000000000 : ℝ)^839
        have hw : |(175905721/400000000 : ℝ)|=(175905721/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1420_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31447/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11819/20000 : ℝ) ∧ (80399/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84651/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5661/50000 : ℝ) ^ (4379/1024 : ℝ) ≤ (4499849704052979/50000000000000000000 : ℝ) := by
    have hpowers : (5661/50000 : ℝ)^4379 ≤ (4499849704052979/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5661 : ℕ)^4379*50000000000000000000^1024 ≤ 4499849704052979^1024*50000^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5661 50000 4499849704052979 50000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5661/50000 : ℝ)) (X := (4499849704052979/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (461/3125 : ℝ) ^ (4379/1024 : ℝ) ≤ (279062369003241/1000000000000000000 : ℝ) := by
    have hpowers : (461/3125 : ℝ)^4379 ≤ (279062369003241/1000000000000000000 : ℝ)^1024 := by
      have hnat : (461 : ℕ)^4379*1000000000000000000^1024 ≤ 279062369003241^1024*3125^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        461 3125 279062369003241 1000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (461/3125 : ℝ)) (X := (279062369003241/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004499849704052979/25000000000000000000 : ℝ) ≤ (10000420874940521/10000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (25004499849704052979/25000000000000000000 : ℝ)^1024 ≤ (10000420874940521/10000000000000000 : ℝ)^4379 := by
      have hnat : (25004499849704052979 : ℕ)^1024*10000000000000000^4379 ≤ 10000420874940521^4379*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004499849704052979 25000000000000000000 10000420874940521 10000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000420874940521/10000000000000000 : ℝ)) (X := (25004499849704052979/25000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018452968154215029/50000000000000000000 : ℝ) ≤ (1250107862345867/1250000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (50018452968154215029/50000000000000000000 : ℝ)^1024 ≤ (1250107862345867/1250000000000000 : ℝ)^4379 := by
      have hnat : (50018452968154215029 : ℕ)^1024*1250000000000000^4379 ≤ 1250107862345867^4379*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018452968154215029 50000000000000000000 1250107862345867 1250000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250107862345867/1250000000000000 : ℝ)) (X := (50018452968154215029/50000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (500279062369003241/500000000000000000 : ℝ) ≤ (10001304922593351/10000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (500279062369003241/500000000000000000 : ℝ)^1024 ≤ (10001304922593351/10000000000000000 : ℝ)^4379 := by
      have hnat : (500279062369003241 : ℕ)^1024*10000000000000000^4379 ≤ 10001304922593351^4379*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500279062369003241 500000000000000000 10001304922593351 10000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001304922593351/10000000000000000 : ℝ)) (X := (500279062369003241/500000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4499849704052979/50000000000000000000 : ℝ) ≤ ((3429143441352064577/3430000000000000000 : ℝ)+2*(88404765283/68600000000000 : ℝ)*(5661/50000 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (3429143441352064577/3430000000000000000 : ℝ)+2*(88404765283/68600000000000 : ℝ)*(5661/50000 : ℝ)=(10000420874940521/10000000000000000 : ℝ) by norm_num, show 1+2*(4499849704052979/50000000000000000000 : ℝ)=(25004499849704052979/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(279062369003241/1000000000000000000 : ℝ)+(4499849704052979/50000000000000000000 : ℝ) ≤ ((3429143441352064577/3430000000000000000 : ℝ)+(88404765283/68600000000000 : ℝ)*((461/3125 : ℝ)+(5661/50000 : ℝ)))^(4379/1024 : ℝ) := by
    rw [show (3429143441352064577/3430000000000000000 : ℝ)+(88404765283/68600000000000 : ℝ)*((461/3125 : ℝ)+(5661/50000 : ℝ))=(1250107862345867/1250000000000000 : ℝ) by norm_num, show 1+(279062369003241/1000000000000000000 : ℝ)+(4499849704052979/50000000000000000000 : ℝ)=(50018452968154215029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(279062369003241/1000000000000000000 : ℝ) ≤ ((3429143441352064577/3430000000000000000 : ℝ)+2*(88404765283/68600000000000 : ℝ)*(461/3125 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (3429143441352064577/3430000000000000000 : ℝ)+2*(88404765283/68600000000000 : ℝ)*(461/3125 : ℝ)=(10001304922593351/10000000000000000 : ℝ) by norm_num, show 1+2*(279062369003241/1000000000000000000 : ℝ)=(500279062369003241/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3429143441352064577/3430000000000000000 : ℝ)*(X 1 0+X 2 0)+(88404765283/68600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (3429143441352064577/3430000000000000000 : ℝ)) (alpha := (88404765283/68600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3429143441352064577/3430000000000000000 : ℝ)*(X 0 1+X 2 1)+(88404765283/68600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (3429143441352064577/3430000000000000000 : ℝ)) (alpha := (88404765283/68600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3429143441352064577/3430000000000000000 : ℝ)*(X 0 2+X 1 2)+(88404765283/68600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (3429143441352064577/3430000000000000000 : ℝ)) (alpha := (88404765283/68600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1817142463/10000000000 : ℝ)*X 0 0+(5386641919/10000000000 : ℝ)*X 0 1+(673330309/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642998593/5000000000 : ℝ)*X 1 0+(-1955377677/10000000000 : ℝ)*X 1 1+(1077328421/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285997681/10000000000 : ℝ)*X 2 0+(5386642069/10000000000 : ℝ)*X 2 1+(-391075411/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2226555141/5000000000 : ℝ)*X 0 0+(2118558403/5000000000 : ℝ)*X 0 1+(2118558447/5000000000 : ℝ)*X 0 2+(2226555141/5000000000 : ℝ)*X 1 0+(2118558403/5000000000 : ℝ)*X 1 1+(2118558447/5000000000 : ℝ)*X 1 2+(2226555141/5000000000 : ℝ)*X 2 0+(2118558403/5000000000 : ℝ)*X 2 1+(2118558447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-428501817/2000000000 : ℝ)*X 0 0+(2633194917/5000000000 : ℝ)*X 0 1+(2633194973/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1342546829/2500000000 : ℝ)*X 1 0+(-1002071701/5000000000 : ℝ)*X 1 1+(5266389453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2685093361/5000000000 : ℝ)*X 2 0+(5266390581/10000000000 : ℝ)*X 2 1+(-200414269/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4159114309/10000000000 : ℝ)*X 0 0+(876812669/2000000000 : ℝ)*X 0 1+(4384064017/10000000000 : ℝ)*X 0 2+(4159114309/10000000000 : ℝ)*X 1 0+(876812669/2000000000 : ℝ)*X 1 1+(4384064017/10000000000 : ℝ)*X 1 2+(4159114309/10000000000 : ℝ)*X 2 0+(876812669/2000000000 : ℝ)*X 2 1+(4384064017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1036998199/5000000000 : ℝ)*X 0 0+(5183252949/10000000000 : ℝ)*X 0 1+(675077693/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638102861/5000000000 : ℝ)*X 1 0+(-974790577/5000000000 : ℝ)*X 1 1+(5400622037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276205609/10000000000 : ℝ)*X 2 0+(2700311187/5000000000 : ℝ)*X 2 1+(-974790423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4486731387/10000000000 : ℝ)*X 0 0+(2110010077/5000000000 : ℝ)*X 0 1+(168800727/400000000 : ℝ)*X 0 2+(4486731387/10000000000 : ℝ)*X 1 0+(2110010077/5000000000 : ℝ)*X 1 1+(168800727/400000000 : ℝ)*X 1 2+(4486731387/10000000000 : ℝ)*X 2 0+(2110010077/5000000000 : ℝ)*X 2 1+(168800727/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1885850263/10000000000 : ℝ)*X 0 0+(5467738433/10000000000 : ℝ)*X 0 1+(1313817083/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2688985727/5000000000 : ℝ)*X 1 0+(-502138327/2500000000 : ℝ)*X 1 1+(2627634199/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5377971473/10000000000 : ℝ)*X 2 0+(328454273/625000000 : ℝ)*X 2 1+(-1004276661/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((165258981/400000000 : ℝ)*X 0 0+(4397642999/10000000000 : ℝ)*X 0 1+(175905721/400000000 : ℝ)*X 0 2+(165258981/400000000 : ℝ)*X 1 0+(4397642999/10000000000 : ℝ)*X 1 1+(175905721/400000000 : ℝ)*X 1 2+(165258981/400000000 : ℝ)*X 2 0+(4397642999/10000000000 : ℝ)*X 2 1+(175905721/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31447/50000 : ℝ) ≤ (-53929453990203542973657804658269/85750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3656893/4000000000000 : ℝ)*(lower1) + (85508437/100000000000000 : ℝ)*(lower2) + (1491701/1000000000000 : ℝ)*(lower3) + (6395547/50000000000000 : ℝ)*(lower4) + (1503476724502667/50000000000000 : ℝ)*(major0) + (1503476724502667/50000000000000 : ℝ)*(major1) + (1503476724502667/50000000000000 : ℝ)*(major2) + (12127293203/100000000000000 : ℝ)*(sp1) + (2064723048842849/50000000000000 : ℝ)*(sp4) + (258089623149531/6250000000000 : ℝ)*(sp5) + (1032292188035073/25000000000000 : ℝ)*(sp6) + (952695793926329/50000000000000 : ℝ)*(sp7) + (277345545407/100000000000000 : ℝ)*(sp14) + (33042983559/100000000000000 : ℝ)*(sp15) + (1905424630836217/100000000000000 : ℝ)*(f.failure) + (2064723048842849/50000000000000 : ℝ)*(f.sum) + (503918672259/107187500000000000000000000 : ℝ)*base66 + (76696312503723141/171500000000000000000000000000000 : ℝ)*base68 + (1128121118452723141/171500000000000000000000000000000 : ℝ)*base70 + (3040500437925723141/171500000000000000000000000000000 : ℝ)*base72 + (1054100337741/1715000000000000000000000000 : ℝ)*base73 + (845088613645223141/171500000000000000000000000000000 : ℝ)*base76 + (1537486415657223141/171500000000000000000000000000000 : ℝ)*base78 + (1726488804767723141/171500000000000000000000000000000 : ℝ)*base80 + (629114925591/107187500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (633667/10000000000000000000000 : ℝ)*base90 + (633667/10000000000000000000000 : ℝ)*base92 + (633667/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11819/20000 : ℝ) ≤ (25338088989589958932711010361207/42875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33727677/50000000000000 : ℝ)*(upper0) + (78416651/100000000000000 : ℝ)*(lower3) + (69010117/25000000000000 : ℝ)*(upper4) + (22806529/25000000000000 : ℝ)*(upper5) + (769563768349603/25000000000000 : ℝ)*(major0) + (769563768349603/25000000000000 : ℝ)*(major1) + (769563768349603/25000000000000 : ℝ)*(major2) + (1046550917428447/25000000000000 : ℝ)*(sp0) + (523269709660033/12500000000000 : ℝ)*(sp1) + (2093100841283481/50000000000000 : ℝ)*(sp2) + (1950606531268411/100000000000000 : ℝ)*(sp3) + (1369205853/50000000000000 : ℝ)*(sp6) + (23371849203/50000000000000 : ℝ)*(sp9) + (375632441/50000000000000 : ℝ)*(sp12) + (1950606531268411/100000000000000 : ℝ)*(f.failure) + (4186204420978669/100000000000000 : ℝ)*(f.sum) + (4226725668759/857500000000000000000000000 : ℝ)*base65 + (151049466102762931/85750000000000000000000000000000 : ℝ)*base67 + (858060980034737069/85750000000000000000000000000000 : ℝ)*base70 + (556903033267262931/85750000000000000000000000000000 : ℝ)*base71 + (872929902661/214375000000000000000000000 : ℝ)*base73 + (37447884491237069/85750000000000000000000000000000 : ℝ)*base76 + (1125171145773762931/85750000000000000000000000000000 : ℝ)*base77 + (1270123282428262931/85750000000000000000000000000000 : ℝ)*base79 + (4964209114131/857500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (101096761/10000000000000000000000 : ℝ)*base90 + (101096761/10000000000000000000000 : ℝ)*base92 + (101096761/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80399/100000 : ℝ) ≤ (17236011676555742906722587524787/21437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4956233/2500000000000 : ℝ)*(upper1) + (13477301/20000000000000 : ℝ)*(upper3) + (21664489/10000000000000 : ℝ)*(upper4) + (176336473/100000000000000 : ℝ)*(lower5) + (423332843314141/12500000000000 : ℝ)*(major0) + (423332843314141/12500000000000 : ℝ)*(major1) + (423332843314141/12500000000000 : ℝ)*(major2) + (255843105841/100000000000000 : ℝ)*(sp1) + (132540455079/25000000000000 : ℝ)*(sp2) + (62919765077/50000000000000 : ℝ)*(sp3) + (1150122249781933/25000000000000 : ℝ)*(sp8) + (4600233156021891/100000000000000 : ℝ)*(sp9) + (4599958837307417/100000000000000 : ℝ)*(sp10) + (214591024748547/10000000000000 : ℝ)*(sp11) + (137346309569/6400000000 : ℝ)*(f.failure) + (1150122249781933/25000000000000 : ℝ)*(f.sum) + (306755841741/857500000000000000000000000 : ℝ)*base65 + (838174747799933357/42875000000000000000000000000000 : ℝ)*base67 + (383104430054183357/42875000000000000000000000000000 : ℝ)*base69 + (662580104952183357/42875000000000000000000000000000 : ℝ)*base71 + (10658959627517/1715000000000000000000000000 : ℝ)*base73 + (201143398935183357/42875000000000000000000000000000 : ℝ)*base75 + (488088912526808357/42875000000000000000000000000000 : ℝ)*base77 + (467985991269683357/42875000000000000000000000000000 : ℝ)*base79 + (2293456856581/214375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3419/640000000000000000 : ℝ)*base90 + (3419/640000000000000000 : ℝ)*base92 + (3419/640000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-84651/100000 : ℝ) ≤ (-2903442518679520548640147059/3430000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1006239/25000000000000 : ℝ)*(lower1) + (1329833/25000000000000 : ℝ)*(upper3) + (2105771/100000000000000 : ℝ)*(lower4) + (660637/10000000000000 : ℝ)*(upper5) + (3424019001538789/100000000000000 : ℝ)*(major0) + (3424019001538789/100000000000000 : ℝ)*(major1) + (3424019001538789/100000000000000 : ℝ)*(major2) + (826605559/50000000000000 : ℝ)*(sp0) + (14192115601/100000000000000 : ℝ)*(sp6) + (2313019567/50000000000000 : ℝ)*(sp7) + (4706544776535107/100000000000000 : ℝ)*(sp12) + (188261857189849/4000000000000 : ℝ)*(sp13) + (4706532237630623/100000000000000 : ℝ)*(sp14) + (542425775984081/25000000000000 : ℝ)*(sp15) + (1084853864987729/50000000000000 : ℝ)*(f.failure) + (188261857189849/4000000000000 : ℝ)*(f.sum) + (24145590944957/3430000000000000000000000000 : ℝ)*base65 + (700087837684272747/343000000000000000000000000000000 : ℝ)*base68 + (1550952474901272747/343000000000000000000000000000000 : ℝ)*base70 + (2892249268204727253/343000000000000000000000000000000 : ℝ)*base71 + (7430127696293/3430000000000000000000000000 : ℝ)*base74 + (6616354091272747/343000000000000000000000000000000 : ℝ)*base76 + (2662368455511727253/343000000000000000000000000000000 : ℝ)*base77 + (3554393379819727253/343000000000000000000000000000000 : ℝ)*base79 + (9523177068973/3430000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (53338379/5000000000000000000000 : ℝ)*base90 + (53338379/5000000000000000000000 : ℝ)*base92 + (53338379/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1420_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31447/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11819/20000 : ℝ) else (80399/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84651/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1420_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1420_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31447/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11819/20000 : ℝ) else (80399/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84651/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1420_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1420_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1420_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31447/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11819/20000 : ℝ) else (80399/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84651/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1420_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
