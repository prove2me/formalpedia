-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1552_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:10:09.570405+00:00
-- url     : https://prove2.me/submissions/ab9cb963-07d1-49ac-8718-51319c15c9e4

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
theorem support_rectangle_w1552_s0_0 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-328843881/2000000000 : ℝ)*x 0 + (5882688023/10000000000 : ℝ)*x 1 + (609007223/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328843881/2000000000 : ℝ)^4601 ≤ (392256264011/4000000000000 : ℝ)^3577 := by
    have hnat : (328843881 : ℕ)^4601*4000000000000^3577 ≤ 392256264011^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328843881 2000000000 392256264011 4000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5882688023/10000000000 : ℝ)^4601 ≤ (50537237626019/100000000000000 : ℝ)^3577 := by
    have hnat : (5882688023 : ℕ)^4601*100000000000000^3577 ≤ 50537237626019^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5882688023 10000000000 50537237626019 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (609007223/1250000000 : ℝ)^4601 ≤ (4957044470089/12500000000000 : ℝ)^3577 := by
    have hnat : (609007223 : ℕ)^4601*12500000000000^3577 ≤ 4957044470089^3577*1250000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609007223 1250000000 4957044470089 12500000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-328843881/2000000000 : ℝ), (5882688023/10000000000 : ℝ), (609007223/1250000000 : ℝ)] ![(392256264011/4000000000000 : ℝ), (50537237626019/100000000000000 : ℝ), (4957044470089/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-328843881/2000000000 : ℝ)|^4601 ≤ (392256264011/4000000000000 : ℝ)^3577
        have hw : |(-328843881/2000000000 : ℝ)|=(328843881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5882688023/10000000000 : ℝ)|^4601 ≤ (50537237626019/100000000000000 : ℝ)^3577
        have hw : |(5882688023/10000000000 : ℝ)|=(5882688023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(609007223/1250000000 : ℝ)|^4601 ≤ (4957044470089/12500000000000 : ℝ)^3577
        have hw : |(609007223/1250000000 : ℝ)|=(609007223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s0_1 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1367332803/2500000000 : ℝ)*x 0 + (-2207849989/10000000000 : ℝ)*x 1 + (2436028891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1367332803/2500000000 : ℝ)^4601 ≤ (179751198477/390625000000 : ℝ)^3577 := by
    have hnat : (1367332803 : ℕ)^4601*390625000000^3577 ≤ 179751198477^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367332803 2500000000 179751198477 390625000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207849989/10000000000 : ℝ)^4601 ≤ (14327337434181/100000000000000 : ℝ)^3577 := by
    have hnat : (2207849989 : ℕ)^4601*100000000000000^3577 ≤ 14327337434181^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207849989 10000000000 14327337434181 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2436028891/5000000000 : ℝ)^4601 ≤ (9914088934943/25000000000000 : ℝ)^3577 := by
    have hnat : (2436028891 : ℕ)^4601*25000000000000^3577 ≤ 9914088934943^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436028891 5000000000 9914088934943 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1367332803/2500000000 : ℝ), (-2207849989/10000000000 : ℝ), (2436028891/5000000000 : ℝ)] ![(179751198477/390625000000 : ℝ), (14327337434181/100000000000000 : ℝ), (9914088934943/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1367332803/2500000000 : ℝ)|^4601 ≤ (179751198477/390625000000 : ℝ)^3577
        have hw : |(1367332803/2500000000 : ℝ)|=(1367332803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2207849989/10000000000 : ℝ)|^4601 ≤ (14327337434181/100000000000000 : ℝ)^3577
        have hw : |(-2207849989/10000000000 : ℝ)|=(2207849989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2436028891/5000000000 : ℝ)|^4601 ≤ (9914088934943/25000000000000 : ℝ)^3577
        have hw : |(2436028891/5000000000 : ℝ)|=(2436028891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s0_2 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (341833203/625000000 : ℝ)*x 0 + (243602887/500000000 : ℝ)*x 1 + (-441569999/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341833203/625000000 : ℝ)^4601 ≤ (46016307199707/100000000000000 : ℝ)^3577 := by
    have hnat : (341833203 : ℕ)^4601*100000000000000^3577 ≤ 46016307199707^3577*625000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341833203 625000000 46016307199707 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243602887/500000000 : ℝ)^4601 ≤ (19828177650023/50000000000000 : ℝ)^3577 := by
    have hnat : (243602887 : ℕ)^4601*50000000000000^3577 ≤ 19828177650023^3577*500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243602887 500000000 19828177650023 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441569999/2000000000 : ℝ)^4601 ≤ (14327337484263/100000000000000 : ℝ)^3577 := by
    have hnat : (441569999 : ℕ)^4601*100000000000000^3577 ≤ 14327337484263^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441569999 2000000000 14327337484263 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341833203/625000000 : ℝ), (243602887/500000000 : ℝ), (-441569999/2000000000 : ℝ)] ![(46016307199707/100000000000000 : ℝ), (19828177650023/50000000000000 : ℝ), (14327337484263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341833203/625000000 : ℝ)|^4601 ≤ (46016307199707/100000000000000 : ℝ)^3577
        have hw : |(341833203/625000000 : ℝ)|=(341833203/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(243602887/500000000 : ℝ)|^4601 ≤ (19828177650023/50000000000000 : ℝ)^3577
        have hw : |(243602887/500000000 : ℝ)|=(243602887/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441569999/2000000000 : ℝ)|^4601 ≤ (14327337484263/100000000000000 : ℝ)^3577
        have hw : |(-441569999/2000000000 : ℝ)|=(441569999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s0_3 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2067262781/5000000000 : ℝ)*x 0 + (38653519/125000000 : ℝ)*x 1 + (1089742279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067262781/5000000000 : ℝ)^4601 ≤ (4013548956741/12500000000000 : ℝ)^3577 := by
    have hnat : (2067262781 : ℕ)^4601*12500000000000^3577 ≤ 4013548956741^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067262781 5000000000 4013548956741 12500000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38653519/125000000 : ℝ)^4601 ≤ (1104916517531/5000000000000 : ℝ)^3577 := by
    have hnat : (38653519 : ℕ)^4601*5000000000000^3577 ≤ 1104916517531^3577*125000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38653519 125000000 1104916517531 5000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089742279/2000000000 : ℝ)^4601 ≤ (11448319495771/25000000000000 : ℝ)^3577 := by
    have hnat : (1089742279 : ℕ)^4601*25000000000000^3577 ≤ 11448319495771^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089742279 2000000000 11448319495771 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2067262781/5000000000 : ℝ), (38653519/125000000 : ℝ), (1089742279/2000000000 : ℝ)] ![(4013548956741/12500000000000 : ℝ), (1104916517531/5000000000000 : ℝ), (11448319495771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2067262781/5000000000 : ℝ)|^4601 ≤ (4013548956741/12500000000000 : ℝ)^3577
        have hw : |(2067262781/5000000000 : ℝ)|=(2067262781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38653519/125000000 : ℝ)|^4601 ≤ (1104916517531/5000000000000 : ℝ)^3577
        have hw : |(38653519/125000000 : ℝ)|=(38653519/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1089742279/2000000000 : ℝ)|^4601 ≤ (11448319495771/25000000000000 : ℝ)^3577
        have hw : |(1089742279/2000000000 : ℝ)|=(1089742279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s0_4 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8237063/50000000 : ℝ)*x 0 + (2448814023/5000000000 : ℝ)*x 1 + (5856208269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8237063/50000000 : ℝ)^4601 ≤ (9830910178821/100000000000000 : ℝ)^3577 := by
    have hnat : (8237063 : ℕ)^4601*100000000000000^3577 ≤ 9830910178821^3577*50000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8237063 50000000 9830910178821 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2448814023/5000000000 : ℝ)^4601 ≤ (9981067310799/25000000000000 : ℝ)^3577 := by
    have hnat : (2448814023 : ℕ)^4601*25000000000000^3577 ≤ 9981067310799^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2448814023 5000000000 9981067310799 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5856208269/10000000000 : ℝ)^4601 ≤ (50244820560427/100000000000000 : ℝ)^3577 := by
    have hnat : (5856208269 : ℕ)^4601*100000000000000^3577 ≤ 50244820560427^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5856208269 10000000000 50244820560427 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8237063/50000000 : ℝ), (2448814023/5000000000 : ℝ), (5856208269/10000000000 : ℝ)] ![(9830910178821/100000000000000 : ℝ), (9981067310799/25000000000000 : ℝ), (50244820560427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8237063/50000000 : ℝ)|^4601 ≤ (9830910178821/100000000000000 : ℝ)^3577
        have hw : |(-8237063/50000000 : ℝ)|=(8237063/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2448814023/5000000000 : ℝ)|^4601 ≤ (9981067310799/25000000000000 : ℝ)^3577
        have hw : |(2448814023/5000000000 : ℝ)|=(2448814023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5856208269/10000000000 : ℝ)|^4601 ≤ (50244820560427/100000000000000 : ℝ)^3577
        have hw : |(5856208269/10000000000 : ℝ)|=(5856208269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s0_5 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596541811/5000000000 : ℝ)*x 0 + (-1223699927/10000000000 : ℝ)*x 1 + (5856207981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596541811/5000000000 : ℝ)^4601 ≤ (43048611651307/100000000000000 : ℝ)^3577 := by
    have hnat : (2596541811 : ℕ)^4601*100000000000000^3577 ≤ 43048611651307^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596541811 5000000000 43048611651307 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1223699927/10000000000 : ℝ)^4601 ≤ (670657094841/10000000000000 : ℝ)^3577 := by
    have hnat : (1223699927 : ℕ)^4601*10000000000000^3577 ≤ 670657094841^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223699927 10000000000 670657094841 10000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5856207981/10000000000 : ℝ)^4601 ≤ (10048963476417/20000000000000 : ℝ)^3577 := by
    have hnat : (5856207981 : ℕ)^4601*20000000000000^3577 ≤ 10048963476417^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5856207981 10000000000 10048963476417 20000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596541811/5000000000 : ℝ), (-1223699927/10000000000 : ℝ), (5856207981/10000000000 : ℝ)] ![(43048611651307/100000000000000 : ℝ), (670657094841/10000000000000 : ℝ), (10048963476417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596541811/5000000000 : ℝ)|^4601 ≤ (43048611651307/100000000000000 : ℝ)^3577
        have hw : |(2596541811/5000000000 : ℝ)|=(2596541811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1223699927/10000000000 : ℝ)|^4601 ≤ (670657094841/10000000000000 : ℝ)^3577
        have hw : |(-1223699927/10000000000 : ℝ)|=(1223699927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5856207981/10000000000 : ℝ)|^4601 ≤ (10048963476417/20000000000000 : ℝ)^3577
        have hw : |(5856207981/10000000000 : ℝ)|=(5856207981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s0_6 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5193083187/10000000000 : ℝ)*x 0 + (292810439/500000000 : ℝ)*x 1 + (-611849667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5193083187/10000000000 : ℝ)^4601 ≤ (43048607013033/100000000000000 : ℝ)^3577 := by
    have hnat : (5193083187 : ℕ)^4601*100000000000000^3577 ≤ 43048607013033^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193083187 10000000000 43048607013033 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292810439/500000000 : ℝ)^4601 ≤ (1570150818743/3125000000000 : ℝ)^3577 := by
    have hnat : (292810439 : ℕ)^4601*3125000000000^3577 ≤ 1570150818743^3577*500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292810439 500000000 1570150818743 3125000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (611849667/5000000000 : ℝ)^4601 ≤ (6706566768051/100000000000000 : ℝ)^3577 := by
    have hnat : (611849667 : ℕ)^4601*100000000000000^3577 ≤ 6706566768051^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611849667 5000000000 6706566768051 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5193083187/10000000000 : ℝ), (292810439/500000000 : ℝ), (-611849667/5000000000 : ℝ)] ![(43048607013033/100000000000000 : ℝ), (1570150818743/3125000000000 : ℝ), (6706566768051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5193083187/10000000000 : ℝ)|^4601 ≤ (43048607013033/100000000000000 : ℝ)^3577
        have hw : |(5193083187/10000000000 : ℝ)|=(5193083187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(292810439/500000000 : ℝ)|^4601 ≤ (1570150818743/3125000000000 : ℝ)^3577
        have hw : |(292810439/500000000 : ℝ)|=(292810439/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-611849667/5000000000 : ℝ)|^4601 ≤ (6706566768051/100000000000000 : ℝ)^3577
        have hw : |(-611849667/5000000000 : ℝ)|=(611849667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s0_7 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4141969431/10000000000 : ℝ)*x 0 + (5389089923/10000000000 : ℝ)*x 1 + (3154022511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4141969431/10000000000 : ℝ)^4601 ≤ (32182768326141/100000000000000 : ℝ)^3577 := by
    have hnat : (4141969431 : ℕ)^4601*100000000000000^3577 ≤ 32182768326141^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141969431 10000000000 32182768326141 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389089923/10000000000 : ℝ)^4601 ≤ (45149758962967/100000000000000 : ℝ)^3577 := by
    have hnat : (5389089923 : ℕ)^4601*100000000000000^3577 ≤ 45149758962967^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389089923 10000000000 45149758962967 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154022511/10000000000 : ℝ)^4601 ≤ (22667472687113/100000000000000 : ℝ)^3577 := by
    have hnat : (3154022511 : ℕ)^4601*100000000000000^3577 ≤ 22667472687113^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154022511 10000000000 22667472687113 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4141969431/10000000000 : ℝ), (5389089923/10000000000 : ℝ), (3154022511/10000000000 : ℝ)] ![(32182768326141/100000000000000 : ℝ), (45149758962967/100000000000000 : ℝ), (22667472687113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4141969431/10000000000 : ℝ)|^4601 ≤ (32182768326141/100000000000000 : ℝ)^3577
        have hw : |(4141969431/10000000000 : ℝ)|=(4141969431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389089923/10000000000 : ℝ)|^4601 ≤ (45149758962967/100000000000000 : ℝ)^3577
        have hw : |(5389089923/10000000000 : ℝ)|=(5389089923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154022511/10000000000 : ℝ)|^4601 ≤ (22667472687113/100000000000000 : ℝ)^3577
        have hw : |(3154022511/10000000000 : ℝ)|=(3154022511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1552_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (104/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1561/6250 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4599/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4599 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4599*1^1024 ≤ 0^1024*1^4599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4599/1024 : ℝ) ≤ (816088926424022653/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4599 ≤ (816088926424022653/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4599*50000000000000000000^1024 ≤ 816088926424022653^1024*5^4599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 816088926424022653 50000000000000000000 4599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (816088926424022653/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4599 := by
      have hnat : (1 : ℕ)^1024*1^4599 ≤ 1^4599*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50816088926424022653/50000000000000000000 : ℝ) ≤ (10036113258823407/10000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (50816088926424022653/50000000000000000000 : ℝ)^1024 ≤ (10036113258823407/10000000000000000 : ℝ)^4599 := by
      have hnat : (50816088926424022653 : ℕ)^1024*10000000000000000^4599 ≤ 10036113258823407^4599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50816088926424022653 50000000000000000000 10036113258823407 10000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10036113258823407/10000000000000000 : ℝ)) (X := (50816088926424022653/50000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25816088926424022653/25000000000000000000 : ℝ) ≤ (5036113258823407/5000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (25816088926424022653/25000000000000000000 : ℝ)^1024 ≤ (5036113258823407/5000000000000000 : ℝ)^4599 := by
      have hnat : (25816088926424022653 : ℕ)^1024*5000000000000000^4599 ≤ 5036113258823407^4599*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25816088926424022653 25000000000000000000 5036113258823407 5000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5036113258823407/5000000000000000 : ℝ)) (X := (25816088926424022653/25000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(36113258823407/4000000000000000 : ℝ)*(0 : ℝ))^(4599/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(36113258823407/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(816088926424022653/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(36113258823407/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4599/1024 : ℝ) := by
    rw [show (1 : ℝ)+(36113258823407/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10036113258823407/10000000000000000 : ℝ) by norm_num, show 1+(816088926424022653/50000000000000000000 : ℝ)+(0 : ℝ)=(50816088926424022653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(816088926424022653/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(36113258823407/4000000000000000 : ℝ)*(2/5 : ℝ))^(4599/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(36113258823407/4000000000000000 : ℝ)*(2/5 : ℝ)=(5036113258823407/5000000000000000 : ℝ) by norm_num, show 1+2*(816088926424022653/50000000000000000000 : ℝ)=(25816088926424022653/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(36113258823407/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36113258823407/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(36113258823407/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36113258823407/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(36113258823407/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36113258823407/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-328843881/2000000000 : ℝ)*X 0 0+(5882688023/10000000000 : ℝ)*X 0 1+(609007223/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1367332803/2500000000 : ℝ)*X 1 0+(-2207849989/10000000000 : ℝ)*X 1 1+(2436028891/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((341833203/625000000 : ℝ)*X 2 0+(243602887/500000000 : ℝ)*X 2 1+(-441569999/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2067262781/5000000000 : ℝ)*X 0 0+(38653519/125000000 : ℝ)*X 0 1+(1089742279/2000000000 : ℝ)*X 0 2+(2067262781/5000000000 : ℝ)*X 1 0+(38653519/125000000 : ℝ)*X 1 1+(1089742279/2000000000 : ℝ)*X 1 2+(2067262781/5000000000 : ℝ)*X 2 0+(38653519/125000000 : ℝ)*X 2 1+(1089742279/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-8237063/50000000 : ℝ)*X 0 0+(2448814023/5000000000 : ℝ)*X 0 1+(5856208269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2596541811/5000000000 : ℝ)*X 1 0+(-1223699927/10000000000 : ℝ)*X 1 1+(5856207981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5193083187/10000000000 : ℝ)*X 2 0+(292810439/500000000 : ℝ)*X 2 1+(-611849667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4141969431/10000000000 : ℝ)*X 0 0+(5389089923/10000000000 : ℝ)*X 0 1+(3154022511/10000000000 : ℝ)*X 0 2+(4141969431/10000000000 : ℝ)*X 1 0+(5389089923/10000000000 : ℝ)*X 1 1+(3154022511/10000000000 : ℝ)*X 1 2+(4141969431/10000000000 : ℝ)*X 2 0+(5389089923/10000000000 : ℝ)*X 2 1+(3154022511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (677691144092331046122033/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65436071/100000000000000 : ℝ)*(base1) + (1437543717/100000000000000 : ℝ)*(base19) + (722028349/50000000000000 : ℝ)*(base23) + (186270977/100000000000000 : ℝ)*(upper3) + (93159017/50000000000000 : ℝ)*(upper5) + (706933626185991/100000000000000 : ℝ)*(major0) + (706933626185991/100000000000000 : ℝ)*(major1) + (706933626185991/100000000000000 : ℝ)*(major2) + (197897313206037/20000000000000 : ℝ)*(sp0) + (989490334748293/100000000000000 : ℝ)*(sp1) + (61843145514707/6250000000000 : ℝ)*(sp2) + (212186463920397/50000000000000 : ℝ)*(sp3) + (658962237/12500000000000 : ℝ)*(sp4) + (1130453027/50000000000000 : ℝ)*(sp7) + (212187627091459/50000000000000 : ℝ)*(f.failure) + (98949177229201/10000000000000 : ℝ)*(f.sum) + (661410789108663/200000000000000000000000000000 : ℝ)*base66 + (3132368870908663/400000000000000000000000000000 : ℝ)*base68 + (1102350908908663/400000000000000000000000000000 : ℝ)*base70 + (998227440908663/400000000000000000000000000000 : ℝ)*base72 + (1301014782708663/200000000000000000000000000000 : ℝ)*base74 + (2257772533708663/400000000000000000000000000000 : ℝ)*base76 + (1618230744908663/400000000000000000000000000000 : ℝ)*base78 + (2702828634508663/400000000000000000000000000000 : ℝ)*base80 + (580255550508663/200000000000000000000000000000 : ℝ)*base82 + (18623441/2500000000000000000000 : ℝ)*base89 + (18623441/2500000000000000000000 : ℝ)*base91 + (18623441/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (178334226120217078025457/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (301900039/100000000000000 : ℝ)*(base19) + (262401699/50000000000000 : ℝ)*(base23) + (40644641/12500000000000 : ℝ)*(base39) + (243891/20000000000000 : ℝ)*(upper2) + (108080741/50000000000000 : ℝ)*(upper5) + (149062126696339/20000000000000 : ℝ)*(major0) + (149062126696339/20000000000000 : ℝ)*(major1) + (372655154162283/50000000000000 : ℝ)*(major2) + (193175217/20000000000000 : ℝ)*(sp1) + (374238829/50000000000000 : ℝ)*(sp2) + (208641549585401/20000000000000 : ℝ)*(sp4) + (521603240075441/50000000000000 : ℝ)*(sp5) + (1043206799803077/100000000000000 : ℝ)*(sp6) + (223706567217253/50000000000000 : ℝ)*(sp7) + (223706567217253/50000000000000 : ℝ)*(f.failure) + (521604036542067/50000000000000 : ℝ)*(f.sum) + (2044808971551227/400000000000000000000000000000 : ℝ)*base65 + (1434998263358181/200000000000000000000000000000 : ℝ)*base67 + (220966398473027/80000000000000000000000000000 : ℝ)*base70 + (705929825041819/200000000000000000000000000000 : ℝ)*base72 + (1930104462351227/400000000000000000000000000000 : ℝ)*base73 + (647776667833027/80000000000000000000000000000 : ℝ)*base76 + (797926340886973/80000000000000000000000000000 : ℝ)*base77 + (435521352966973/80000000000000000000000000000 : ℝ)*base79 + (65488971113027/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (868953/2500000000000000000000 : ℝ)*base90 + (868953/2500000000000000000000 : ℝ)*base92 + (24131047/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1552_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (104/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1561/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1552_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1552_s1_0 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-446854231/2500000000 : ℝ)*x 0 + (5545303353/10000000000 : ℝ)*x 1 + (1279307681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446854231/2500000000 : ℝ)^4601 ≤ (10918375134691/100000000000000 : ℝ)^3577 := by
    have hnat : (446854231 : ℕ)^4601*100000000000000^3577 ≤ 10918375134691^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446854231 2500000000 10918375134691 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5545303353/10000000000 : ℝ)^4601 ≤ (46840112889379/100000000000000 : ℝ)^3577 := by
    have hnat : (5545303353 : ℕ)^4601*100000000000000^3577 ≤ 46840112889379^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5545303353 10000000000 46840112889379 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1279307681/2500000000 : ℝ)^4601 ≤ (42241511962099/100000000000000 : ℝ)^3577 := by
    have hnat : (1279307681 : ℕ)^4601*100000000000000^3577 ≤ 42241511962099^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279307681 2500000000 42241511962099 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-446854231/2500000000 : ℝ), (5545303353/10000000000 : ℝ), (1279307681/2500000000 : ℝ)] ![(10918375134691/100000000000000 : ℝ), (46840112889379/100000000000000 : ℝ), (42241511962099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-446854231/2500000000 : ℝ)|^4601 ≤ (10918375134691/100000000000000 : ℝ)^3577
        have hw : |(-446854231/2500000000 : ℝ)|=(446854231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5545303353/10000000000 : ℝ)|^4601 ≤ (46840112889379/100000000000000 : ℝ)^3577
        have hw : |(5545303353/10000000000 : ℝ)|=(5545303353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1279307681/2500000000 : ℝ)|^4601 ≤ (42241511962099/100000000000000 : ℝ)^3577
        have hw : |(1279307681/2500000000 : ℝ)|=(1279307681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s1_1 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075903053/2000000000 : ℝ)*x 0 + (-125735349/625000000 : ℝ)*x 1 + (1023446033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075903053/2000000000 : ℝ)^4601 ≤ (11261651241287/25000000000000 : ℝ)^3577 := by
    have hnat : (1075903053 : ℕ)^4601*25000000000000^3577 ≤ 11261651241287^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075903053 2000000000 11261651241287 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125735349/625000000 : ℝ)^4601 ≤ (1271188899951/10000000000000 : ℝ)^3577 := by
    have hnat : (125735349 : ℕ)^4601*10000000000000^3577 ≤ 1271188899951^3577*625000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125735349 625000000 1271188899951 10000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023446033/2000000000 : ℝ)^4601 ≤ (8448301205341/20000000000000 : ℝ)^3577 := by
    have hnat : (1023446033 : ℕ)^4601*20000000000000^3577 ≤ 8448301205341^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023446033 2000000000 8448301205341 20000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075903053/2000000000 : ℝ), (-125735349/625000000 : ℝ), (1023446033/2000000000 : ℝ)] ![(11261651241287/25000000000000 : ℝ), (1271188899951/10000000000000 : ℝ), (8448301205341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075903053/2000000000 : ℝ)|^4601 ≤ (11261651241287/25000000000000 : ℝ)^3577
        have hw : |(1075903053/2000000000 : ℝ)|=(1075903053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125735349/625000000 : ℝ)|^4601 ≤ (1271188899951/10000000000000 : ℝ)^3577
        have hw : |(-125735349/625000000 : ℝ)|=(125735349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1023446033/2000000000 : ℝ)|^4601 ≤ (8448301205341/20000000000000 : ℝ)^3577
        have hw : |(1023446033/2000000000 : ℝ)|=(1023446033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s1_2 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689757581/5000000000 : ℝ)*x 0 + (1023446021/2000000000 : ℝ)*x 1 + (-2011765799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689757581/5000000000 : ℝ)^4601 ≤ (351926592623/781250000000 : ℝ)^3577 := by
    have hnat : (2689757581 : ℕ)^4601*781250000000^3577 ≤ 351926592623^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689757581 5000000000 351926592623 781250000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023446021/2000000000 : ℝ)^4601 ≤ (42241505389633/100000000000000 : ℝ)^3577 := by
    have hnat : (1023446021 : ℕ)^4601*100000000000000^3577 ≤ 42241505389633^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023446021 2000000000 42241505389633 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011765799/10000000000 : ℝ)^4601 ≤ (12711890746959/100000000000000 : ℝ)^3577 := by
    have hnat : (2011765799 : ℕ)^4601*100000000000000^3577 ≤ 12711890746959^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011765799 10000000000 12711890746959 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689757581/5000000000 : ℝ), (1023446021/2000000000 : ℝ), (-2011765799/10000000000 : ℝ)] ![(351926592623/781250000000 : ℝ), (42241505389633/100000000000000 : ℝ), (12711890746959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689757581/5000000000 : ℝ)|^4601 ≤ (351926592623/781250000000 : ℝ)^3577
        have hw : |(2689757581/5000000000 : ℝ)|=(2689757581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1023446021/2000000000 : ℝ)|^4601 ≤ (42241505389633/100000000000000 : ℝ)^3577
        have hw : |(1023446021/2000000000 : ℝ)|=(1023446021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011765799/10000000000 : ℝ)|^4601 ≤ (12711890746959/100000000000000 : ℝ)^3577
        have hw : |(-2011765799/10000000000 : ℝ)|=(2011765799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s1_3 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2117508703/5000000000 : ℝ)*x 0 + (940001133/2500000000 : ℝ)*x 1 + (4758117561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117508703/5000000000 : ℝ)^4601 ≤ (8278921650739/25000000000000 : ℝ)^3577 := by
    have hnat : (2117508703 : ℕ)^4601*25000000000000^3577 ≤ 8278921650739^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117508703 5000000000 8278921650739 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (940001133/2500000000 : ℝ)^4601 ≤ (28416860318037/100000000000000 : ℝ)^3577 := by
    have hnat : (940001133 : ℕ)^4601*100000000000000^3577 ≤ 28416860318037^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940001133 2500000000 28416860318037 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4758117561/10000000000 : ℝ)^4601 ≤ (38467453073913/100000000000000 : ℝ)^3577 := by
    have hnat : (4758117561 : ℕ)^4601*100000000000000^3577 ≤ 38467453073913^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4758117561 10000000000 38467453073913 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117508703/5000000000 : ℝ), (940001133/2500000000 : ℝ), (4758117561/10000000000 : ℝ)] ![(8278921650739/25000000000000 : ℝ), (28416860318037/100000000000000 : ℝ), (38467453073913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117508703/5000000000 : ℝ)|^4601 ≤ (8278921650739/25000000000000 : ℝ)^3577
        have hw : |(2117508703/5000000000 : ℝ)|=(2117508703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(940001133/2500000000 : ℝ)|^4601 ≤ (28416860318037/100000000000000 : ℝ)^3577
        have hw : |(940001133/2500000000 : ℝ)|=(940001133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4758117561/10000000000 : ℝ)|^4601 ≤ (38467453073913/100000000000000 : ℝ)^3577
        have hw : |(4758117561/10000000000 : ℝ)|=(4758117561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s1_4 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-357530549/2000000000 : ℝ)*x 0 + (5121756541/10000000000 : ℝ)*x 1 + (5540708789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (357530549/2000000000 : ℝ)^4601 ≤ (682514253271/6250000000000 : ℝ)^3577 := by
    have hnat : (357530549 : ℕ)^4601*6250000000000^3577 ≤ 682514253271^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357530549 2000000000 682514253271 6250000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5121756541/10000000000 : ℝ)^4601 ≤ (42289572618991/100000000000000 : ℝ)^3577 := by
    have hnat : (5121756541 : ℕ)^4601*100000000000000^3577 ≤ 42289572618991^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121756541 10000000000 42289572618991 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5540708789/10000000000 : ℝ)^4601 ≤ (46790199311273/100000000000000 : ℝ)^3577 := by
    have hnat : (5540708789 : ℕ)^4601*100000000000000^3577 ≤ 46790199311273^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5540708789 10000000000 46790199311273 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-357530549/2000000000 : ℝ), (5121756541/10000000000 : ℝ), (5540708789/10000000000 : ℝ)] ![(682514253271/6250000000000 : ℝ), (42289572618991/100000000000000 : ℝ), (46790199311273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-357530549/2000000000 : ℝ)|^4601 ≤ (682514253271/6250000000000 : ℝ)^3577
        have hw : |(-357530549/2000000000 : ℝ)|=(357530549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5121756541/10000000000 : ℝ)|^4601 ≤ (42289572618991/100000000000000 : ℝ)^3577
        have hw : |(5121756541/10000000000 : ℝ)|=(5121756541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5540708789/10000000000 : ℝ)|^4601 ≤ (46790199311273/100000000000000 : ℝ)^3577
        have hw : |(5540708789/10000000000 : ℝ)|=(5540708789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s1_5 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053250721/2000000000 : ℝ)*x 0 + (-49634031/312500000 : ℝ)*x 1 + (2770354011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053250721/2000000000 : ℝ)^4601 ≤ (43830369343303/100000000000000 : ℝ)^3577 := by
    have hnat : (1053250721 : ℕ)^4601*100000000000000^3577 ≤ 43830369343303^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053250721 2000000000 43830369343303 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49634031/312500000 : ℝ)^4601 ≤ (586214978589/6250000000000 : ℝ)^3577 := by
    have hnat : (49634031 : ℕ)^4601*6250000000000^3577 ≤ 586214978589^3577*312500000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49634031 312500000 586214978589 6250000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2770354011/5000000000 : ℝ)^4601 ≤ (11697547744967/25000000000000 : ℝ)^3577 := by
    have hnat : (2770354011 : ℕ)^4601*25000000000000^3577 ≤ 11697547744967^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2770354011 5000000000 11697547744967 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053250721/2000000000 : ℝ), (-49634031/312500000 : ℝ), (2770354011/5000000000 : ℝ)] ![(43830369343303/100000000000000 : ℝ), (586214978589/6250000000000 : ℝ), (11697547744967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053250721/2000000000 : ℝ)|^4601 ≤ (43830369343303/100000000000000 : ℝ)^3577
        have hw : |(1053250721/2000000000 : ℝ)|=(1053250721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49634031/312500000 : ℝ)|^4601 ≤ (586214978589/6250000000000 : ℝ)^3577
        have hw : |(-49634031/312500000 : ℝ)|=(49634031/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2770354011/5000000000 : ℝ)|^4601 ≤ (11697547744967/25000000000000 : ℝ)^3577
        have hw : |(2770354011/5000000000 : ℝ)|=(2770354011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s1_6 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266255249/10000000000 : ℝ)*x 0 + (2770353789/5000000000 : ℝ)*x 1 + (-1588287311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266255249/10000000000 : ℝ)^4601 ≤ (21915193471567/50000000000000 : ℝ)^3577 := by
    have hnat : (5266255249 : ℕ)^4601*50000000000000^3577 ≤ 21915193471567^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266255249 10000000000 21915193471567 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2770353789/5000000000 : ℝ)^4601 ≤ (9358037231399/20000000000000 : ℝ)^3577 := by
    have hnat : (2770353789 : ℕ)^4601*20000000000000^3577 ≤ 9358037231399^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2770353789 5000000000 9358037231399 20000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1588287311/10000000000 : ℝ)^4601 ≤ (2344856722169/25000000000000 : ℝ)^3577 := by
    have hnat : (1588287311 : ℕ)^4601*25000000000000^3577 ≤ 2344856722169^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588287311 10000000000 2344856722169 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266255249/10000000000 : ℝ), (2770353789/5000000000 : ℝ), (-1588287311/10000000000 : ℝ)] ![(21915193471567/50000000000000 : ℝ), (9358037231399/20000000000000 : ℝ), (2344856722169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266255249/10000000000 : ℝ)|^4601 ≤ (21915193471567/50000000000000 : ℝ)^3577
        have hw : |(5266255249/10000000000 : ℝ)|=(5266255249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2770353789/5000000000 : ℝ)|^4601 ≤ (9358037231399/20000000000000 : ℝ)^3577
        have hw : |(2770353789/5000000000 : ℝ)|=(2770353789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1588287311/10000000000 : ℝ)|^4601 ≤ (2344856722169/25000000000000 : ℝ)^3577
        have hw : |(-1588287311/10000000000 : ℝ)|=(1588287311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s1_7 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105889189/250000000 : ℝ)*x 0 + (474756297/1000000000 : ℝ)*x 1 + (1885358911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105889189/250000000 : ℝ)^4601 ≤ (33121220157657/100000000000000 : ℝ)^3577 := by
    have hnat : (105889189 : ℕ)^4601*100000000000000^3577 ≤ 33121220157657^3577*250000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105889189 250000000 33121220157657 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474756297/1000000000 : ℝ)^4601 ≤ (2397358172169/6250000000000 : ℝ)^3577 := by
    have hnat : (474756297 : ℕ)^4601*6250000000000^3577 ≤ 2397358172169^3577*1000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474756297 1000000000 2397358172169 6250000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1885358911/5000000000 : ℝ)^4601 ≤ (28521049071783/100000000000000 : ℝ)^3577 := by
    have hnat : (1885358911 : ℕ)^4601*100000000000000^3577 ≤ 28521049071783^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885358911 5000000000 28521049071783 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105889189/250000000 : ℝ), (474756297/1000000000 : ℝ), (1885358911/5000000000 : ℝ)] ![(33121220157657/100000000000000 : ℝ), (2397358172169/6250000000000 : ℝ), (28521049071783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105889189/250000000 : ℝ)|^4601 ≤ (33121220157657/100000000000000 : ℝ)^3577
        have hw : |(105889189/250000000 : ℝ)|=(105889189/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(474756297/1000000000 : ℝ)|^4601 ≤ (2397358172169/6250000000000 : ℝ)^3577
        have hw : |(474756297/1000000000 : ℝ)|=(474756297/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1885358911/5000000000 : ℝ)|^4601 ≤ (28521049071783/100000000000000 : ℝ)^3577
        have hw : |(1885358911/5000000000 : ℝ)|=(1885358911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1552_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1561/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (104/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (8861/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4481/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1561/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (104/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1561/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (104/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1561/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (104/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1561/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (104/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1561/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (104/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1561/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (104/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (104/3125 : ℝ) ^ (4599/1024 : ℝ) ≤ (23057570886193/100000000000000000000 : ℝ) := by
    have hpowers : (104/3125 : ℝ)^4599 ≤ (23057570886193/100000000000000000000 : ℝ)^1024 := by
      have hnat : (104 : ℕ)^4599*100000000000000000000^1024 ≤ 23057570886193^1024*3125^4599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104 3125 23057570886193 100000000000000000000 4599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (104/3125 : ℝ)) (X := (23057570886193/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1561/6250 : ℝ) ^ (4599/1024 : ℝ) ≤ (196855790811542507/100000000000000000000 : ℝ) := by
    have hpowers : (1561/6250 : ℝ)^4599 ≤ (196855790811542507/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1561 : ℕ)^4599*100000000000000000000^1024 ≤ 196855790811542507^1024*6250^4599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1561 6250 196855790811542507 100000000000000000000 4599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1561/6250 : ℝ)) (X := (196855790811542507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000023057570886193/50000000000000000000 : ℝ) ≤ (10000001026786187/10000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (50000023057570886193/50000000000000000000 : ℝ)^1024 ≤ (10000001026786187/10000000000000000 : ℝ)^4599 := by
      have hnat : (50000023057570886193 : ℕ)^1024*10000000000000000^4599 ≤ 10000001026786187^4599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000023057570886193 50000000000000000000 10000001026786187 10000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001026786187/10000000000000000 : ℝ)) (X := (50000023057570886193/50000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1001968788483824287/1000000000000000000 : ℝ) ≤ (400175211872763/400000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (1001968788483824287/1000000000000000000 : ℝ)^1024 ≤ (400175211872763/400000000000000 : ℝ)^4599 := by
      have hnat : (1001968788483824287 : ℕ)^1024*400000000000000^4599 ≤ 400175211872763^4599*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1001968788483824287 1000000000000000000 400175211872763 400000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400175211872763/400000000000000 : ℝ)) (X := (1001968788483824287/1000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50196855790811542507/50000000000000000000 : ℝ) ≤ (10008759566851963/10000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (50196855790811542507/50000000000000000000 : ℝ)^1024 ≤ (10008759566851963/10000000000000000 : ℝ)^4599 := by
      have hnat : (50196855790811542507 : ℕ)^1024*10000000000000000^4599 ≤ 10008759566851963^4599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50196855790811542507 50000000000000000000 10008759566851963 10000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008759566851963/10000000000000000 : ℝ)) (X := (50196855790811542507/50000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23057570886193/100000000000000000000 : ℝ) ≤ ((13528179612908029603/13530000000000000000 : ℝ)+2*(547408754111/270600000000000 : ℝ)*(104/3125 : ℝ))^(4599/1024 : ℝ) := by
    rw [show (13528179612908029603/13530000000000000000 : ℝ)+2*(547408754111/270600000000000 : ℝ)*(104/3125 : ℝ)=(10000001026786187/10000000000000000 : ℝ) by norm_num, show 1+2*(23057570886193/100000000000000000000 : ℝ)=(50000023057570886193/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(196855790811542507/100000000000000000000 : ℝ)+(23057570886193/100000000000000000000 : ℝ) ≤ ((13528179612908029603/13530000000000000000 : ℝ)+(547408754111/270600000000000 : ℝ)*((1561/6250 : ℝ)+(104/3125 : ℝ)))^(4599/1024 : ℝ) := by
    rw [show (13528179612908029603/13530000000000000000 : ℝ)+(547408754111/270600000000000 : ℝ)*((1561/6250 : ℝ)+(104/3125 : ℝ))=(400175211872763/400000000000000 : ℝ) by norm_num, show 1+(196855790811542507/100000000000000000000 : ℝ)+(23057570886193/100000000000000000000 : ℝ)=(1001968788483824287/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(196855790811542507/100000000000000000000 : ℝ) ≤ ((13528179612908029603/13530000000000000000 : ℝ)+2*(547408754111/270600000000000 : ℝ)*(1561/6250 : ℝ))^(4599/1024 : ℝ) := by
    rw [show (13528179612908029603/13530000000000000000 : ℝ)+2*(547408754111/270600000000000 : ℝ)*(1561/6250 : ℝ)=(10008759566851963/10000000000000000 : ℝ) by norm_num, show 1+2*(196855790811542507/100000000000000000000 : ℝ)=(50196855790811542507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13528179612908029603/13530000000000000000 : ℝ)*(X 1 0+X 2 0)+(547408754111/270600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (104/3125 : ℝ)) (hi := (1561/6250 : ℝ)) (c := (13528179612908029603/13530000000000000000 : ℝ)) (alpha := (547408754111/270600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13528179612908029603/13530000000000000000 : ℝ)*(X 0 1+X 2 1)+(547408754111/270600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (104/3125 : ℝ)) (hi := (1561/6250 : ℝ)) (c := (13528179612908029603/13530000000000000000 : ℝ)) (alpha := (547408754111/270600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13528179612908029603/13530000000000000000 : ℝ)*(X 0 2+X 1 2)+(547408754111/270600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (104/3125 : ℝ)) (hi := (1561/6250 : ℝ)) (c := (13528179612908029603/13530000000000000000 : ℝ)) (alpha := (547408754111/270600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-446854231/2500000000 : ℝ)*X 0 0+(5545303353/10000000000 : ℝ)*X 0 1+(1279307681/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075903053/2000000000 : ℝ)*X 1 0+(-125735349/625000000 : ℝ)*X 1 1+(1023446033/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2689757581/5000000000 : ℝ)*X 2 0+(1023446021/2000000000 : ℝ)*X 2 1+(-2011765799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2117508703/5000000000 : ℝ)*X 0 0+(940001133/2500000000 : ℝ)*X 0 1+(4758117561/10000000000 : ℝ)*X 0 2+(2117508703/5000000000 : ℝ)*X 1 0+(940001133/2500000000 : ℝ)*X 1 1+(4758117561/10000000000 : ℝ)*X 1 2+(2117508703/5000000000 : ℝ)*X 2 0+(940001133/2500000000 : ℝ)*X 2 1+(4758117561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-357530549/2000000000 : ℝ)*X 0 0+(5121756541/10000000000 : ℝ)*X 0 1+(5540708789/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1053250721/2000000000 : ℝ)*X 1 0+(-49634031/312500000 : ℝ)*X 1 1+(2770354011/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266255249/10000000000 : ℝ)*X 2 0+(2770353789/5000000000 : ℝ)*X 2 1+(-1588287311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((105889189/250000000 : ℝ)*X 0 0+(474756297/1000000000 : ℝ)*X 0 1+(1885358911/5000000000 : ℝ)*X 0 2+(105889189/250000000 : ℝ)*X 1 0+(474756297/1000000000 : ℝ)*X 1 1+(1885358911/5000000000 : ℝ)*X 1 2+(105889189/250000000 : ℝ)*X 2 0+(474756297/1000000000 : ℝ)*X 2 1+(1885358911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2690195325088165483607562043/225500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19468253/12500000000000 : ℝ)*(base1) + (1814021853/100000000000000 : ℝ)*(base19) + (70771751/4000000000000 : ℝ)*(base23) + (131433337/50000000000000 : ℝ)*(upper3) + (17016753/12500000000000 : ℝ)*(upper5) + (1668986858813827/100000000000000 : ℝ)*(major0) + (1668986858813827/100000000000000 : ℝ)*(major1) + (1668986858813827/100000000000000 : ℝ)*(major2) + (116803192128581/5000000000000 : ℝ)*(sp0) + (1168035807883301/50000000000000 : ℝ)*(sp1) + (58401791512367/2500000000000 : ℝ)*(sp2) + (1001894745070939/100000000000000 : ℝ)*(sp3) + (9742962859/100000000000000 : ℝ)*(sp4) + (4989358473/100000000000000 : ℝ)*(sp7) + (250474972543859/25000000000000 : ℝ)*(f.failure) + (467214685957691/20000000000000 : ℝ)*(f.sum) + (31589657532073/13530000000000000000000000000 : ℝ)*base66 + (4392730688739429319/1353000000000000000000000000000000 : ℝ)*base68 + (10977501995226429319/1353000000000000000000000000000000 : ℝ)*base70 + (6874520603310429319/1353000000000000000000000000000000 : ℝ)*base72 + (24335115784097/13530000000000000000000000000 : ℝ)*base73 + (9025973624973429319/1353000000000000000000000000000000 : ℝ)*base76 + (3281167229700429319/1353000000000000000000000000000000 : ℝ)*base78 + (11639924763552429319/1353000000000000000000000000000000 : ℝ)*base80 + (67631020172653/13530000000000000000000000000 : ℝ)*base82 + (4311041/1250000000000000000000 : ℝ)*base89 + (4311041/1250000000000000000000 : ℝ)*base91 + (4311041/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2177094623483727707038265709/225500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (611094003/50000000000000 : ℝ)*(base19) + (149967119/6250000000000 : ℝ)*(base23) + (181307951/100000000000000 : ℝ)*(upper3) + (22350899/20000000000000 : ℝ)*(lower4) + (364397989/100000000000000 : ℝ)*(upper5) + (1705307661055899/100000000000000 : ℝ)*(major0) + (1705307661055899/100000000000000 : ℝ)*(major1) + (1705307661055899/100000000000000 : ℝ)*(major2) + (4265282017/100000000000000 : ℝ)*(sp1) + (14491935821/100000000000000 : ℝ)*(sp2) + (2386911578482251/100000000000000 : ℝ)*(sp4) + (596726522753057/25000000000000 : ℝ)*(sp5) + (1193447343536263/50000000000000 : ℝ)*(sp6) + (204740684362431/20000000000000 : ℝ)*(sp7) + (204740684362431/20000000000000 : ℝ)*(f.failure) + (2386911578482251/100000000000000 : ℝ)*(f.sum) + (14653137900287/4510000000000000000000000000 : ℝ)*base66 + (2856522178098742699/451000000000000000000000000000000 : ℝ)*base67 + (1263330263190742699/451000000000000000000000000000000 : ℝ)*base69 + (2383283772194742699/451000000000000000000000000000000 : ℝ)*base71 + (1349963710803/4510000000000000000000000000 : ℝ)*base73 + (4867753029508742699/451000000000000000000000000000000 : ℝ)*base75 + (351061747713742699/451000000000000000000000000000000 : ℝ)*base77 + (6247483189756742699/451000000000000000000000000000000 : ℝ)*base79 + (16563844680687/4510000000000000000000000000 : ℝ)*base82 + (2301669/1000000000000000000000 : ℝ)*base89 + (2301669/1000000000000000000000 : ℝ)*base91 + (2301669/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1552_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1561/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (104/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8861/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4481/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1552_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1552_s2_0 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-225962127/1250000000 : ℝ)*x 0 + (1089230021/2000000000 : ℝ)*x 1 + (325199543/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225962127/1250000000 : ℝ)^4601 ≤ (2769494272279/25000000000000 : ℝ)^3577 := by
    have hnat : (225962127 : ℕ)^4601*25000000000000^3577 ≤ 2769494272279^3577*1250000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225962127 1250000000 2769494272279 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089230021/2000000000 : ℝ)^4601 ≤ (11441397827881/25000000000000 : ℝ)^3577 := by
    have hnat : (1089230021 : ℕ)^4601*25000000000000^3577 ≤ 11441397827881^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089230021 2000000000 11441397827881 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325199543/625000000 : ℝ)^4601 ≤ (43156431593833/100000000000000 : ℝ)^3577 := by
    have hnat : (325199543 : ℕ)^4601*100000000000000^3577 ≤ 43156431593833^3577*625000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325199543 625000000 43156431593833 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-225962127/1250000000 : ℝ), (1089230021/2000000000 : ℝ), (325199543/625000000 : ℝ)] ![(2769494272279/25000000000000 : ℝ), (11441397827881/25000000000000 : ℝ), (43156431593833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-225962127/1250000000 : ℝ)|^4601 ≤ (2769494272279/25000000000000 : ℝ)^3577
        have hw : |(-225962127/1250000000 : ℝ)|=(225962127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1089230021/2000000000 : ℝ)|^4601 ≤ (11441397827881/25000000000000 : ℝ)^3577
        have hw : |(1089230021/2000000000 : ℝ)|=(1089230021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325199543/625000000 : ℝ)|^4601 ≤ (43156431593833/100000000000000 : ℝ)^3577
        have hw : |(325199543/625000000 : ℝ)|=(325199543/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s2_1 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354027223/10000000000 : ℝ)*x 0 + (-30195299/156250000 : ℝ)*x 1 + (5203192753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354027223/10000000000 : ℝ)^4601 ≤ (44772262064729/100000000000000 : ℝ)^3577 := by
    have hnat : (5354027223 : ℕ)^4601*100000000000000^3577 ≤ 44772262064729^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354027223 10000000000 44772262064729 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30195299/156250000 : ℝ)^4601 ≤ (1508913204403/12500000000000 : ℝ)^3577 := by
    have hnat : (30195299 : ℕ)^4601*12500000000000^3577 ≤ 1508913204403^3577*156250000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30195299 156250000 1508913204403 12500000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5203192753/10000000000 : ℝ)^4601 ≤ (21578216143647/50000000000000 : ℝ)^3577 := by
    have hnat : (5203192753 : ℕ)^4601*50000000000000^3577 ≤ 21578216143647^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203192753 10000000000 21578216143647 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354027223/10000000000 : ℝ), (-30195299/156250000 : ℝ), (5203192753/10000000000 : ℝ)] ![(44772262064729/100000000000000 : ℝ), (1508913204403/12500000000000 : ℝ), (21578216143647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354027223/10000000000 : ℝ)|^4601 ≤ (44772262064729/100000000000000 : ℝ)^3577
        have hw : |(5354027223/10000000000 : ℝ)|=(5354027223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30195299/156250000 : ℝ)|^4601 ≤ (1508913204403/12500000000000 : ℝ)^3577
        have hw : |(-30195299/156250000 : ℝ)|=(30195299/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5203192753/10000000000 : ℝ)|^4601 ≤ (21578216143647/50000000000000 : ℝ)^3577
        have hw : |(5203192753/10000000000 : ℝ)|=(5203192753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s2_2 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354027867/10000000000 : ℝ)*x 0 + (65039901/125000000 : ℝ)*x 1 + (-966249583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354027867/10000000000 : ℝ)^4601 ≤ (5596533623971/12500000000000 : ℝ)^3577 := by
    have hnat : (5354027867 : ℕ)^4601*12500000000000^3577 ≤ 5596533623971^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354027867 10000000000 5596533623971 12500000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65039901/125000000 : ℝ)^4601 ≤ (21578212553651/50000000000000 : ℝ)^3577 := by
    have hnat : (65039901 : ℕ)^4601*50000000000000^3577 ≤ 21578212553651^3577*125000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65039901 125000000 21578212553651 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966249583/5000000000 : ℝ)^4601 ≤ (1508913234533/12500000000000 : ℝ)^3577 := by
    have hnat : (966249583 : ℕ)^4601*12500000000000^3577 ≤ 1508913234533^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966249583 5000000000 1508913234533 12500000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354027867/10000000000 : ℝ), (65039901/125000000 : ℝ), (-966249583/5000000000 : ℝ)] ![(5596533623971/12500000000000 : ℝ), (21578212553651/50000000000000 : ℝ), (1508913234533/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354027867/10000000000 : ℝ)|^4601 ≤ (5596533623971/12500000000000 : ℝ)^3577
        have hw : |(5354027867/10000000000 : ℝ)|=(5354027867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65039901/125000000 : ℝ)|^4601 ≤ (21578212553651/50000000000000 : ℝ)^3577
        have hw : |(65039901/125000000 : ℝ)|=(65039901/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-966249583/5000000000 : ℝ)|^4601 ≤ (1508913234533/12500000000000 : ℝ)^3577
        have hw : |(-966249583/5000000000 : ℝ)|=(966249583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s2_3 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249674509/10000000000 : ℝ)*x 0 + (124193059/312500000 : ℝ)*x 1 + (4540670887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249674509/10000000000 : ℝ)^4601 ≤ (16631590396043/50000000000000 : ℝ)^3577 := by
    have hnat : (4249674509 : ℕ)^4601*50000000000000^3577 ≤ 16631590396043^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249674509 10000000000 16631590396043 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124193059/312500000 : ℝ)^4601 ≤ (476806850003/1562500000000 : ℝ)^3577 := by
    have hnat : (124193059 : ℕ)^4601*1562500000000^3577 ≤ 476806850003^3577*312500000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124193059 312500000 476806850003 1562500000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4540670887/10000000000 : ℝ)^4601 ≤ (9055295198137/25000000000000 : ℝ)^3577 := by
    have hnat : (4540670887 : ℕ)^4601*25000000000000^3577 ≤ 9055295198137^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540670887 10000000000 9055295198137 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249674509/10000000000 : ℝ), (124193059/312500000 : ℝ), (4540670887/10000000000 : ℝ)] ![(16631590396043/50000000000000 : ℝ), (476806850003/1562500000000 : ℝ), (9055295198137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249674509/10000000000 : ℝ)|^4601 ≤ (16631590396043/50000000000000 : ℝ)^3577
        have hw : |(4249674509/10000000000 : ℝ)|=(4249674509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124193059/312500000 : ℝ)|^4601 ≤ (476806850003/1562500000000 : ℝ)^3577
        have hw : |(124193059/312500000 : ℝ)|=(124193059/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4540670887/10000000000 : ℝ)|^4601 ≤ (9055295198137/25000000000000 : ℝ)^3577
        have hw : |(4540670887/10000000000 : ℝ)|=(4540670887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s2_4 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1807739409/10000000000 : ℝ)*x 0 + (5204658331/10000000000 : ℝ)*x 1 + (5444672453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1807739409/10000000000 : ℝ)^4601 ≤ (5539155628121/50000000000000 : ℝ)^3577 := by
    have hnat : (1807739409 : ℕ)^4601*50000000000000^3577 ≤ 5539155628121^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1807739409 10000000000 5539155628121 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204658331/10000000000 : ℝ)^4601 ≤ (21586034318201/50000000000000 : ℝ)^3577 := by
    have hnat : (5204658331 : ℕ)^4601*50000000000000^3577 ≤ 21586034318201^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204658331 10000000000 21586034318201 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444672453/10000000000 : ℝ)^4601 ≤ (22874810046307/50000000000000 : ℝ)^3577 := by
    have hnat : (5444672453 : ℕ)^4601*50000000000000^3577 ≤ 22874810046307^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444672453 10000000000 22874810046307 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1807739409/10000000000 : ℝ), (5204658331/10000000000 : ℝ), (5444672453/10000000000 : ℝ)] ![(5539155628121/50000000000000 : ℝ), (21586034318201/50000000000000 : ℝ), (22874810046307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1807739409/10000000000 : ℝ)|^4601 ≤ (5539155628121/50000000000000 : ℝ)^3577
        have hw : |(-1807739409/10000000000 : ℝ)|=(1807739409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204658331/10000000000 : ℝ)|^4601 ≤ (21586034318201/50000000000000 : ℝ)^3577
        have hw : |(5204658331/10000000000 : ℝ)|=(5204658331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444672453/10000000000 : ℝ)|^4601 ≤ (22874810046307/50000000000000 : ℝ)^3577
        have hw : |(5444672453/10000000000 : ℝ)|=(5444672453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s2_5 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644941101/5000000000 : ℝ)*x 0 + (-845509883/5000000000 : ℝ)*x 1 + (5444672579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644941101/5000000000 : ℝ)^4601 ≤ (4408348739413/10000000000000 : ℝ)^3577 := by
    have hnat : (2644941101 : ℕ)^4601*10000000000000^3577 ≤ 4408348739413^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644941101 5000000000 4408348739413 10000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845509883/5000000000 : ℝ)^4601 ≤ (10166891131311/100000000000000 : ℝ)^3577 := by
    have hnat : (845509883 : ℕ)^4601*100000000000000^3577 ≤ 10166891131311^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845509883 5000000000 10166891131311 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444672579/10000000000 : ℝ)^4601 ≤ (22874810727217/50000000000000 : ℝ)^3577 := by
    have hnat : (5444672579 : ℕ)^4601*50000000000000^3577 ≤ 22874810727217^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444672579 10000000000 22874810727217 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644941101/5000000000 : ℝ), (-845509883/5000000000 : ℝ), (5444672579/10000000000 : ℝ)] ![(4408348739413/10000000000000 : ℝ), (10166891131311/100000000000000 : ℝ), (22874810727217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644941101/5000000000 : ℝ)|^4601 ≤ (4408348739413/10000000000000 : ℝ)^3577
        have hw : |(2644941101/5000000000 : ℝ)|=(2644941101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-845509883/5000000000 : ℝ)|^4601 ≤ (10166891131311/100000000000000 : ℝ)^3577
        have hw : |(-845509883/5000000000 : ℝ)|=(845509883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444672579/10000000000 : ℝ)|^4601 ≤ (22874810727217/50000000000000 : ℝ)^3577
        have hw : |(5444672579/10000000000 : ℝ)|=(5444672579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s2_6 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644941003/5000000000 : ℝ)*x 0 + (5444672757/10000000000 : ℝ)*x 1 + (-1691019789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644941003/5000000000 : ℝ)^4601 ≤ (22041742646581/50000000000000 : ℝ)^3577 := by
    have hnat : (2644941003 : ℕ)^4601*50000000000000^3577 ≤ 22041742646581^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644941003 5000000000 22041742646581 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444672757/10000000000 : ℝ)^4601 ≤ (22874811689137/50000000000000 : ℝ)^3577 := by
    have hnat : (5444672757 : ℕ)^4601*50000000000000^3577 ≤ 22874811689137^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444672757 10000000000 22874811689137 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1691019789/10000000000 : ℝ)^4601 ≤ (10166891309181/100000000000000 : ℝ)^3577 := by
    have hnat : (1691019789 : ℕ)^4601*100000000000000^3577 ≤ 10166891309181^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691019789 10000000000 10166891309181 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644941003/5000000000 : ℝ), (5444672757/10000000000 : ℝ), (-1691019789/10000000000 : ℝ)] ![(22041742646581/50000000000000 : ℝ), (22874811689137/50000000000000 : ℝ), (10166891309181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644941003/5000000000 : ℝ)|^4601 ≤ (22041742646581/50000000000000 : ℝ)^3577
        have hw : |(2644941003/5000000000 : ℝ)|=(2644941003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444672757/10000000000 : ℝ)|^4601 ≤ (22874811689137/50000000000000 : ℝ)^3577
        have hw : |(5444672757/10000000000 : ℝ)|=(5444672757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1691019789/10000000000 : ℝ)|^4601 ≤ (10166891309181/100000000000000 : ℝ)^3577
        have hw : |(-1691019789/10000000000 : ℝ)|=(1691019789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s2_7 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249773757/10000000000 : ℝ)*x 0 + (4537252073/10000000000 : ℝ)*x 1 + (198881383/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249773757/10000000000 : ℝ)^4601 ≤ (33264180020137/100000000000000 : ℝ)^3577 := by
    have hnat : (4249773757 : ℕ)^4601*100000000000000^3577 ≤ 33264180020137^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249773757 10000000000 33264180020137 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4537252073/10000000000 : ℝ)^4601 ≤ (9046526309819/25000000000000 : ℝ)^3577 := by
    have hnat : (4537252073 : ℕ)^4601*25000000000000^3577 ≤ 9046526309819^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537252073 10000000000 9046526309819 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198881383/500000000 : ℝ)^4601 ≤ (30549714728181/100000000000000 : ℝ)^3577 := by
    have hnat : (198881383 : ℕ)^4601*100000000000000^3577 ≤ 30549714728181^3577*500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198881383 500000000 30549714728181 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249773757/10000000000 : ℝ), (4537252073/10000000000 : ℝ), (198881383/500000000 : ℝ)] ![(33264180020137/100000000000000 : ℝ), (9046526309819/25000000000000 : ℝ), (30549714728181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249773757/10000000000 : ℝ)|^4601 ≤ (33264180020137/100000000000000 : ℝ)^3577
        have hw : |(4249773757/10000000000 : ℝ)|=(4249773757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4537252073/10000000000 : ℝ)|^4601 ≤ (9046526309819/25000000000000 : ℝ)^3577
        have hw : |(4537252073/10000000000 : ℝ)|=(4537252073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198881383/500000000 : ℝ)|^4601 ≤ (30549714728181/100000000000000 : ℝ)^3577
        have hw : |(198881383/500000000 : ℝ)|=(198881383/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1552_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4481/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5357/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7931/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4481/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4481/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4481/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4481/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4481/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4481/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8861/100000 : ℝ) ^ (4599/1024 : ℝ) ≤ (1874661906455689/100000000000000000000 : ℝ) := by
    have hpowers : (8861/100000 : ℝ)^4599 ≤ (1874661906455689/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8861 : ℕ)^4599*100000000000000000000^1024 ≤ 1874661906455689^1024*100000^4599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8861 100000 1874661906455689 100000000000000000000 4599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8861/100000 : ℝ)) (X := (1874661906455689/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4481/25000 : ℝ) ^ (4599/1024 : ℝ) ≤ (8872557269567111/20000000000000000000 : ℝ) := by
    have hpowers : (4481/25000 : ℝ)^4599 ≤ (8872557269567111/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4481 : ℕ)^4599*20000000000000000000^1024 ≤ 8872557269567111^1024*25000^4599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4481 25000 8872557269567111 20000000000000000000 4599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4481/25000 : ℝ)) (X := (8872557269567111/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001874661906455689/50000000000000000000 : ℝ) ≤ (10000083480139969/10000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (50001874661906455689/50000000000000000000 : ℝ)^1024 ≤ (10000083480139969/10000000000000000 : ℝ)^4599 := by
      have hnat : (50001874661906455689 : ℕ)^1024*10000000000000000^4599 ≤ 10000083480139969^4599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001874661906455689 50000000000000000000 10000083480139969 10000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000083480139969/10000000000000000 : ℝ)) (X := (50001874661906455689/50000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011559362063572811/25000000000000000000 : ℝ) ≤ (2000205864929347/2000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (25011559362063572811/25000000000000000000 : ℝ)^1024 ≤ (2000205864929347/2000000000000000 : ℝ)^4599 := by
      have hnat : (25011559362063572811 : ℕ)^1024*2000000000000000^4599 ≤ 2000205864929347^4599*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011559362063572811 25000000000000000000 2000205864929347 2000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000205864929347/2000000000000000 : ℝ)) (X := (25011559362063572811/25000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008872557269567111/10000000000000000000 : ℝ) ≤ (10001975169153501/10000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (10008872557269567111/10000000000000000000 : ℝ)^1024 ≤ (10001975169153501/10000000000000000 : ℝ)^4599 := by
      have hnat : (10008872557269567111 : ℕ)^1024*10000000000000000^4599 ≤ 10001975169153501^4599*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008872557269567111 10000000000000000000 10001975169153501 10000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001975169153501/10000000000000000 : ℝ)) (X := (10008872557269567111/10000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1874661906455689/100000000000000000000 : ℝ) ≤ ((18122798864831926399/18126000000000000000 : ℝ)+2*(472922253383/453150000000000 : ℝ)*(8861/100000 : ℝ))^(4599/1024 : ℝ) := by
    rw [show (18122798864831926399/18126000000000000000 : ℝ)+2*(472922253383/453150000000000 : ℝ)*(8861/100000 : ℝ)=(10000083480139969/10000000000000000 : ℝ) by norm_num, show 1+2*(1874661906455689/100000000000000000000 : ℝ)=(50001874661906455689/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8872557269567111/20000000000000000000 : ℝ)+(1874661906455689/100000000000000000000 : ℝ) ≤ ((18122798864831926399/18126000000000000000 : ℝ)+(472922253383/453150000000000 : ℝ)*((4481/25000 : ℝ)+(8861/100000 : ℝ)))^(4599/1024 : ℝ) := by
    rw [show (18122798864831926399/18126000000000000000 : ℝ)+(472922253383/453150000000000 : ℝ)*((4481/25000 : ℝ)+(8861/100000 : ℝ))=(2000205864929347/2000000000000000 : ℝ) by norm_num, show 1+(8872557269567111/20000000000000000000 : ℝ)+(1874661906455689/100000000000000000000 : ℝ)=(25011559362063572811/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8872557269567111/20000000000000000000 : ℝ) ≤ ((18122798864831926399/18126000000000000000 : ℝ)+2*(472922253383/453150000000000 : ℝ)*(4481/25000 : ℝ))^(4599/1024 : ℝ) := by
    rw [show (18122798864831926399/18126000000000000000 : ℝ)+2*(472922253383/453150000000000 : ℝ)*(4481/25000 : ℝ)=(10001975169153501/10000000000000000 : ℝ) by norm_num, show 1+2*(8872557269567111/20000000000000000000 : ℝ)=(10008872557269567111/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18122798864831926399/18126000000000000000 : ℝ)*(X 1 0+X 2 0)+(472922253383/453150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (8861/100000 : ℝ)) (hi := (4481/25000 : ℝ)) (c := (18122798864831926399/18126000000000000000 : ℝ)) (alpha := (472922253383/453150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18122798864831926399/18126000000000000000 : ℝ)*(X 0 1+X 2 1)+(472922253383/453150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (8861/100000 : ℝ)) (hi := (4481/25000 : ℝ)) (c := (18122798864831926399/18126000000000000000 : ℝ)) (alpha := (472922253383/453150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18122798864831926399/18126000000000000000 : ℝ)*(X 0 2+X 1 2)+(472922253383/453150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (8861/100000 : ℝ)) (hi := (4481/25000 : ℝ)) (c := (18122798864831926399/18126000000000000000 : ℝ)) (alpha := (472922253383/453150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-225962127/1250000000 : ℝ)*X 0 0+(1089230021/2000000000 : ℝ)*X 0 1+(325199543/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354027223/10000000000 : ℝ)*X 1 0+(-30195299/156250000 : ℝ)*X 1 1+(5203192753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354027867/10000000000 : ℝ)*X 2 0+(65039901/125000000 : ℝ)*X 2 1+(-966249583/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4249674509/10000000000 : ℝ)*X 0 0+(124193059/312500000 : ℝ)*X 0 1+(4540670887/10000000000 : ℝ)*X 0 2+(4249674509/10000000000 : ℝ)*X 1 0+(124193059/312500000 : ℝ)*X 1 1+(4540670887/10000000000 : ℝ)*X 1 2+(4249674509/10000000000 : ℝ)*X 2 0+(124193059/312500000 : ℝ)*X 2 1+(4540670887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1807739409/10000000000 : ℝ)*X 0 0+(5204658331/10000000000 : ℝ)*X 0 1+(5444672453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644941101/5000000000 : ℝ)*X 1 0+(-845509883/5000000000 : ℝ)*X 1 1+(5444672579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644941003/5000000000 : ℝ)*X 2 0+(5444672757/10000000000 : ℝ)*X 2 1+(-1691019789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4249773757/10000000000 : ℝ)*X 0 0+(4537252073/10000000000 : ℝ)*X 0 1+(198881383/500000000 : ℝ)*X 0 2+(4249773757/10000000000 : ℝ)*X 1 0+(4537252073/10000000000 : ℝ)*X 1 1+(198881383/500000000 : ℝ)*X 1 2+(4249773757/10000000000 : ℝ)*X 2 0+(4537252073/10000000000 : ℝ)*X 2 1+(198881383/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (113588570227686940690864117/50350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1550482011/100000000000000 : ℝ)*(base19) + (796058201/50000000000000 : ℝ)*(base23) + (87474157/25000000000000 : ℝ)*(upper3) + (242778009/100000000000000 : ℝ)*(upper4) + (42253693/50000000000000 : ℝ)*(upper5) + (2940626652718751/100000000000000 : ℝ)*(major0) + (2940626652718751/100000000000000 : ℝ)*(major1) + (2940626652718751/100000000000000 : ℝ)*(major2) + (4115965160914139/100000000000000 : ℝ)*(sp0) + (4115981027775243/100000000000000 : ℝ)*(sp1) + (1028995246535213/25000000000000 : ℝ)*(sp2) + (1765256375886259/100000000000000 : ℝ)*(sp3) + (3483468623/20000000000000 : ℝ)*(sp4) + (14276094663/100000000000000 : ℝ)*(sp7) + (882635325990461/50000000000000 : ℝ)*(f.failure) + (2057991289128627/50000000000000 : ℝ)*(f.sum) + (308358132958421/45315000000000000000000000000 : ℝ)*base65 + (1712789504357991961/201400000000000000000000000000000 : ℝ)*base67 + (1066608884973391961/201400000000000000000000000000000 : ℝ)*base69 + (453522337353991961/201400000000000000000000000000000 : ℝ)*base71 + (244729760871221/45315000000000000000000000000 : ℝ)*base73 + (1342152687579408039/201400000000000000000000000000000 : ℝ)*base76 + (839082860991961/201400000000000000000000000000000 : ℝ)*base77 + (1005920517257991961/201400000000000000000000000000000 : ℝ)*base79 + (358871288296751/45315000000000000000000000000 : ℝ)*base81 + (14793361/2500000000000000000000 : ℝ)*base90 + (14793361/2500000000000000000000 : ℝ)*base92 + (14793361/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5596258349669153146999/629375000000000000000000000 : ℝ) := by norm_num
    linear_combination (15989269/20000000000000 : ℝ)*(base23) + (62952069/50000000000000 : ℝ)*(upper2) + (811163/10000000000000 : ℝ)*(upper4) + (57298681/100000000000000 : ℝ)*(upper5) + (93021133132083/3125000000000 : ℝ)*(major0) + (93021133132083/3125000000000 : ℝ)*(major1) + (93021133132083/3125000000000 : ℝ)*(major2) + (10230345661/100000000000000 : ℝ)*(sp0) + (3101079973/25000000000000 : ℝ)*(sp1) + (167056657/1250000000000 : ℝ)*(sp2) + (4166430609446801/100000000000000 : ℝ)*(sp4) + (416642843547257/10000000000000 : ℝ)*(sp5) + (1041606848828389/25000000000000 : ℝ)*(sp6) + (893455692134239/50000000000000 : ℝ)*(sp7) + (893455692134239/50000000000000 : ℝ)*(f.failure) + (2083220419896231/50000000000000 : ℝ)*(f.sum) + (27670900885427/15105000000000000000000000000 : ℝ)*base65 + (10305608818478513/6293750000000000000000000000000 : ℝ)*base67 + (9290942679627737/6293750000000000000000000000000 : ℝ)*base70 + (148094032635328513/6293750000000000000000000000000 : ℝ)*base71 + (57640044828089/7552500000000000000000000000 : ℝ)*base74 + (26487992008346487/6293750000000000000000000000000 : ℝ)*base76 + (16868325655921487/6293750000000000000000000000000 : ℝ)*base78 + (4309394867903513/6293750000000000000000000000000 : ℝ)*base79 + (12610370630737/3776250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (21838661/2500000000000000000000 : ℝ)*base89 + (21838661/2500000000000000000000 : ℝ)*base91 + (21838661/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1552_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4481/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7931/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1552_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1552_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7931/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1552_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1552_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1552_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7931/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1552_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
