-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1096_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:58:52.847983+00:00
-- url     : https://prove2.me/submissions/e34abf4b-1a8a-416e-bda8-63476399179c

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
theorem support_rectangle_w1096_box_0 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-128790569/625000000 : ℝ)*x 0 + (672119523/1250000000 : ℝ)*x 1 + (215078271/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128790569/625000000 : ℝ)^8289 ≤ (12271360921131/100000000000000 : ℝ)^6241 := by
    have hnat : (128790569 : ℕ)^8289*100000000000000^6241 ≤ 12271360921131^6241*625000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128790569 625000000 12271360921131 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672119523/1250000000 : ℝ)^8289 ≤ (43864316327249/100000000000000 : ℝ)^6241 := by
    have hnat : (672119523 : ℕ)^8289*100000000000000^6241 ≤ 43864316327249^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672119523 1250000000 43864316327249 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215078271/400000000 : ℝ)^8289 ≤ (10966080682661/25000000000000 : ℝ)^6241 := by
    have hnat : (215078271 : ℕ)^8289*25000000000000^6241 ≤ 10966080682661^6241*400000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215078271 400000000 10966080682661 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128790569/625000000 : ℝ), (672119523/1250000000 : ℝ), (215078271/400000000 : ℝ)] ![(12271360921131/100000000000000 : ℝ), (43864316327249/100000000000000 : ℝ), (10966080682661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128790569/625000000 : ℝ)|^8289 ≤ (12271360921131/100000000000000 : ℝ)^6241
        have hw : |(-128790569/625000000 : ℝ)|=(128790569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672119523/1250000000 : ℝ)|^8289 ≤ (43864316327249/100000000000000 : ℝ)^6241
        have hw : |(672119523/1250000000 : ℝ)|=(672119523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215078271/400000000 : ℝ)|^8289 ≤ (10966080682661/25000000000000 : ℝ)^6241
        have hw : |(215078271/400000000 : ℝ)|=(215078271/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_1 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (264776479/500000000 : ℝ)*x 0 + (-2170959189/10000000000 : ℝ)*x 1 + (1075391341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264776479/500000000 : ℝ)^8289 ≤ (859685421021/2000000000000 : ℝ)^6241 := by
    have hnat : (264776479 : ℕ)^8289*2000000000000^6241 ≤ 859685421021^6241*500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264776479 500000000 859685421021 2000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170959189/10000000000 : ℝ)^8289 ≤ (13151406956353/100000000000000 : ℝ)^6241 := by
    have hnat : (2170959189 : ℕ)^8289*100000000000000^6241 ≤ 13151406956353^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170959189 10000000000 13151406956353 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075391341/2000000000 : ℝ)^8289 ≤ (8772864394441/20000000000000 : ℝ)^6241 := by
    have hnat : (1075391341 : ℕ)^8289*20000000000000^6241 ≤ 8772864394441^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075391341 2000000000 8772864394441 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264776479/500000000 : ℝ), (-2170959189/10000000000 : ℝ), (1075391341/2000000000 : ℝ)] ![(859685421021/2000000000000 : ℝ), (13151406956353/100000000000000 : ℝ), (8772864394441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264776479/500000000 : ℝ)|^8289 ≤ (859685421021/2000000000000 : ℝ)^6241
        have hw : |(264776479/500000000 : ℝ)|=(264776479/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2170959189/10000000000 : ℝ)|^8289 ≤ (13151406956353/100000000000000 : ℝ)^6241
        have hw : |(-2170959189/10000000000 : ℝ)|=(2170959189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075391341/2000000000 : ℝ)|^8289 ≤ (8772864394441/20000000000000 : ℝ)^6241
        have hw : |(1075391341/2000000000 : ℝ)|=(1075391341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_2 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295530251/10000000000 : ℝ)*x 0 + (5376956353/10000000000 : ℝ)*x 1 + (-434191753/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295530251/10000000000 : ℝ)^8289 ≤ (42984278284919/100000000000000 : ℝ)^6241 := by
    have hnat : (5295530251 : ℕ)^8289*100000000000000^6241 ≤ 42984278284919^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295530251 10000000000 42984278284919 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376956353/10000000000 : ℝ)^8289 ≤ (21932159079169/50000000000000 : ℝ)^6241 := by
    have hnat : (5376956353 : ℕ)^8289*50000000000000^6241 ≤ 21932159079169^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376956353 10000000000 21932159079169 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434191753/2000000000 : ℝ)^8289 ≤ (13151403544939/100000000000000 : ℝ)^6241 := by
    have hnat : (434191753 : ℕ)^8289*100000000000000^6241 ≤ 13151403544939^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434191753 2000000000 13151403544939 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295530251/10000000000 : ℝ), (5376956353/10000000000 : ℝ), (-434191753/2000000000 : ℝ)] ![(42984278284919/100000000000000 : ℝ), (21932159079169/50000000000000 : ℝ), (13151403544939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295530251/10000000000 : ℝ)|^8289 ≤ (42984278284919/100000000000000 : ℝ)^6241
        have hw : |(5295530251/10000000000 : ℝ)|=(5295530251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376956353/10000000000 : ℝ)|^8289 ≤ (21932159079169/50000000000000 : ℝ)^6241
        have hw : |(5376956353/10000000000 : ℝ)|=(5376956353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434191753/2000000000 : ℝ)|^8289 ≤ (13151403544939/100000000000000 : ℝ)^6241
        have hw : |(-434191753/2000000000 : ℝ)|=(434191753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_3 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4479243423/10000000000 : ℝ)*x 0 + (33744637/78125000 : ℝ)*x 1 + (2159656771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4479243423/10000000000 : ℝ)^8289 ≤ (17207453075207/50000000000000 : ℝ)^6241 := by
    have hnat : (4479243423 : ℕ)^8289*50000000000000^6241 ≤ 17207453075207^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479243423 10000000000 17207453075207 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33744637/78125000 : ℝ)^8289 ≤ (32792546886423/100000000000000 : ℝ)^6241 := by
    have hnat : (33744637 : ℕ)^8289*100000000000000^6241 ≤ 32792546886423^6241*78125000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33744637 78125000 32792546886423 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2159656771/5000000000 : ℝ)^8289 ≤ (32792546946923/100000000000000 : ℝ)^6241 := by
    have hnat : (2159656771 : ℕ)^8289*100000000000000^6241 ≤ 32792546946923^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159656771 5000000000 32792546946923 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4479243423/10000000000 : ℝ), (33744637/78125000 : ℝ), (2159656771/5000000000 : ℝ)] ![(17207453075207/50000000000000 : ℝ), (32792546886423/100000000000000 : ℝ), (32792546946923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4479243423/10000000000 : ℝ)|^8289 ≤ (17207453075207/50000000000000 : ℝ)^6241
        have hw : |(4479243423/10000000000 : ℝ)|=(4479243423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33744637/78125000 : ℝ)|^8289 ≤ (32792546886423/100000000000000 : ℝ)^6241
        have hw : |(33744637/78125000 : ℝ)|=(33744637/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2159656771/5000000000 : ℝ)|^8289 ≤ (32792546946923/100000000000000 : ℝ)^6241
        have hw : |(2159656771/5000000000 : ℝ)|=(2159656771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_4 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-579725547/2500000000 : ℝ)*x 0 + (2640262289/5000000000 : ℝ)*x 1 + (33003279/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (579725547/2500000000 : ℝ)^8289 ≤ (3588709105259/25000000000000 : ℝ)^6241 := by
    have hnat : (579725547 : ℕ)^8289*25000000000000^6241 ≤ 3588709105259^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579725547 2500000000 3588709105259 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640262289/5000000000 : ℝ)^8289 ≤ (21411290723451/50000000000000 : ℝ)^6241 := by
    have hnat : (2640262289 : ℕ)^8289*50000000000000^6241 ≤ 21411290723451^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640262289 5000000000 21411290723451 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33003279/62500000 : ℝ)^8289 ≤ (8564516422937/20000000000000 : ℝ)^6241 := by
    have hnat : (33003279 : ℕ)^8289*20000000000000^6241 ≤ 8564516422937^6241*62500000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33003279 62500000 8564516422937 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-579725547/2500000000 : ℝ), (2640262289/5000000000 : ℝ), (33003279/62500000 : ℝ)] ![(3588709105259/25000000000000 : ℝ), (21411290723451/50000000000000 : ℝ), (8564516422937/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-579725547/2500000000 : ℝ)|^8289 ≤ (3588709105259/25000000000000 : ℝ)^6241
        have hw : |(-579725547/2500000000 : ℝ)|=(579725547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640262289/5000000000 : ℝ)|^8289 ≤ (21411290723451/50000000000000 : ℝ)^6241
        have hw : |(2640262289/5000000000 : ℝ)|=(2640262289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33003279/62500000 : ℝ)|^8289 ≤ (8564516422937/20000000000000 : ℝ)^6241
        have hw : |(33003279/62500000 : ℝ)|=(33003279/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_5 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536372963/1000000000 : ℝ)*x 0 + (-441750577/2000000000 : ℝ)*x 1 + (1056104913/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536372963/1000000000 : ℝ)^8289 ≤ (8744213299239/20000000000000 : ℝ)^6241 := by
    have hnat : (536372963 : ℕ)^8289*20000000000000^6241 ≤ 8744213299239^6241*1000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536372963 1000000000 8744213299239 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441750577/2000000000 : ℝ)^8289 ≤ (6728176086931/50000000000000 : ℝ)^6241 := by
    have hnat : (441750577 : ℕ)^8289*50000000000000^6241 ≤ 6728176086931^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441750577 2000000000 6728176086931 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056104913/2000000000 : ℝ)^8289 ≤ (42822581306883/100000000000000 : ℝ)^6241 := by
    have hnat : (1056104913 : ℕ)^8289*100000000000000^6241 ≤ 42822581306883^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056104913 2000000000 42822581306883 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536372963/1000000000 : ℝ), (-441750577/2000000000 : ℝ), (1056104913/2000000000 : ℝ)] ![(8744213299239/20000000000000 : ℝ), (6728176086931/50000000000000 : ℝ), (42822581306883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536372963/1000000000 : ℝ)|^8289 ≤ (8744213299239/20000000000000 : ℝ)^6241
        have hw : |(536372963/1000000000 : ℝ)|=(536372963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441750577/2000000000 : ℝ)|^8289 ≤ (6728176086931/50000000000000 : ℝ)^6241
        have hw : |(-441750577/2000000000 : ℝ)|=(441750577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056104913/2000000000 : ℝ)|^8289 ≤ (42822581306883/100000000000000 : ℝ)^6241
        have hw : |(1056104913/2000000000 : ℝ)|=(1056104913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_6 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (268186479/500000000 : ℝ)*x 0 + (660065621/1250000000 : ℝ)*x 1 + (-69023513/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268186479/500000000 : ℝ)^8289 ≤ (4372106595489/10000000000000 : ℝ)^6241 := by
    have hnat : (268186479 : ℕ)^8289*10000000000000^6241 ≤ 4372106595489^6241*500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268186479 500000000 4372106595489 10000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660065621/1250000000 : ℝ)^8289 ≤ (42822585647473/100000000000000 : ℝ)^6241 := by
    have hnat : (660065621 : ℕ)^8289*100000000000000^6241 ≤ 42822585647473^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660065621 1250000000 42822585647473 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69023513/312500000 : ℝ)^8289 ≤ (3364087094739/25000000000000 : ℝ)^6241 := by
    have hnat : (69023513 : ℕ)^8289*25000000000000^6241 ≤ 3364087094739^6241*312500000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69023513 312500000 3364087094739 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268186479/500000000 : ℝ), (660065621/1250000000 : ℝ), (-69023513/312500000 : ℝ)] ![(4372106595489/10000000000000 : ℝ), (42822585647473/100000000000000 : ℝ), (3364087094739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268186479/500000000 : ℝ)|^8289 ≤ (4372106595489/10000000000000 : ℝ)^6241
        have hw : |(268186479/500000000 : ℝ)|=(268186479/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660065621/1250000000 : ℝ)|^8289 ≤ (42822585647473/100000000000000 : ℝ)^6241
        have hw : |(660065621/1250000000 : ℝ)|=(660065621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69023513/312500000 : ℝ)|^8289 ≤ (3364087094739/25000000000000 : ℝ)^6241
        have hw : |(-69023513/312500000 : ℝ)|=(69023513/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_7 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4262807583/10000000000 : ℝ)*x 0 + (1106877633/2500000000 : ℝ)*x 1 + (4427509967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4262807583/10000000000 : ℝ)^8289 ≤ (6444799911417/20000000000000 : ℝ)^6241 := by
    have hnat : (4262807583 : ℕ)^8289*20000000000000^6241 ≤ 6444799911417^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4262807583 10000000000 6444799911417 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106877633/2500000000 : ℝ)^8289 ≤ (33888003089489/100000000000000 : ℝ)^6241 := by
    have hnat : (1106877633 : ℕ)^8289*100000000000000^6241 ≤ 33888003089489^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106877633 2500000000 33888003089489 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4427509967/10000000000 : ℝ)^8289 ≤ (8471999336477/25000000000000 : ℝ)^6241 := by
    have hnat : (4427509967 : ℕ)^8289*25000000000000^6241 ≤ 8471999336477^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427509967 10000000000 8471999336477 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4262807583/10000000000 : ℝ), (1106877633/2500000000 : ℝ), (4427509967/10000000000 : ℝ)] ![(6444799911417/20000000000000 : ℝ), (33888003089489/100000000000000 : ℝ), (8471999336477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4262807583/10000000000 : ℝ)|^8289 ≤ (6444799911417/20000000000000 : ℝ)^6241
        have hw : |(4262807583/10000000000 : ℝ)|=(4262807583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1106877633/2500000000 : ℝ)|^8289 ≤ (33888003089489/100000000000000 : ℝ)^6241
        have hw : |(1106877633/2500000000 : ℝ)|=(1106877633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4427509967/10000000000 : ℝ)|^8289 ≤ (8471999336477/25000000000000 : ℝ)^6241
        have hw : |(4427509967/10000000000 : ℝ)|=(4427509967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_8 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2264952107/10000000000 : ℝ)*x 0 + (1303757791/2500000000 : ℝ)*x 1 + (538656101/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2264952107/10000000000 : ℝ)^8289 ≤ (13912974966329/100000000000000 : ℝ)^6241 := by
    have hnat : (2264952107 : ℕ)^8289*100000000000000^6241 ≤ 13912974966329^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264952107 10000000000 13912974966329 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303757791/2500000000 : ℝ)^8289 ≤ (2632413210957/6250000000000 : ℝ)^6241 := by
    have hnat : (1303757791 : ℕ)^8289*6250000000000^6241 ≤ 2632413210957^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303757791 2500000000 2632413210957 6250000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538656101/1000000000 : ℝ)^8289 ≤ (8793682729187/20000000000000 : ℝ)^6241 := by
    have hnat : (538656101 : ℕ)^8289*20000000000000^6241 ≤ 8793682729187^6241*1000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538656101 1000000000 8793682729187 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2264952107/10000000000 : ℝ), (1303757791/2500000000 : ℝ), (538656101/1000000000 : ℝ)] ![(13912974966329/100000000000000 : ℝ), (2632413210957/6250000000000 : ℝ), (8793682729187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2264952107/10000000000 : ℝ)|^8289 ≤ (13912974966329/100000000000000 : ℝ)^6241
        have hw : |(-2264952107/10000000000 : ℝ)|=(2264952107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303757791/2500000000 : ℝ)|^8289 ≤ (2632413210957/6250000000000 : ℝ)^6241
        have hw : |(1303757791/2500000000 : ℝ)|=(1303757791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538656101/1000000000 : ℝ)|^8289 ≤ (8793682729187/20000000000000 : ℝ)^6241
        have hw : |(538656101/1000000000 : ℝ)|=(538656101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_9 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322183489/2500000000 : ℝ)*x 0 + (-433424833/2000000000 : ℝ)*x 1 + (5386561151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322183489/2500000000 : ℝ)^8289 ≤ (2681939043819/6250000000000 : ℝ)^6241 := by
    have hnat : (1322183489 : ℕ)^8289*6250000000000^6241 ≤ 2681939043819^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322183489 2500000000 2681939043819 6250000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433424833/2000000000 : ℝ)^8289 ≤ (3280140029539/25000000000000 : ℝ)^6241 := by
    have hnat : (433424833 : ℕ)^8289*25000000000000^6241 ≤ 3280140029539^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433424833 2000000000 3280140029539 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386561151/10000000000 : ℝ)^8289 ≤ (2748025948409/6250000000000 : ℝ)^6241 := by
    have hnat : (5386561151 : ℕ)^8289*6250000000000^6241 ≤ 2748025948409^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386561151 10000000000 2748025948409 6250000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322183489/2500000000 : ℝ), (-433424833/2000000000 : ℝ), (5386561151/10000000000 : ℝ)] ![(2681939043819/6250000000000 : ℝ), (3280140029539/25000000000000 : ℝ), (2748025948409/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322183489/2500000000 : ℝ)|^8289 ≤ (2681939043819/6250000000000 : ℝ)^6241
        have hw : |(1322183489/2500000000 : ℝ)|=(1322183489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433424833/2000000000 : ℝ)|^8289 ≤ (3280140029539/25000000000000 : ℝ)^6241
        have hw : |(-433424833/2000000000 : ℝ)|=(433424833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386561151/10000000000 : ℝ)|^8289 ≤ (2748025948409/6250000000000 : ℝ)^6241
        have hw : |(5386561151/10000000000 : ℝ)|=(5386561151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_10 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288733783/10000000000 : ℝ)*x 0 + (1077312079/2000000000 : ℝ)*x 1 + (-1083562707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288733783/10000000000 : ℝ)^8289 ≤ (42911022836823/100000000000000 : ℝ)^6241 := by
    have hnat : (5288733783 : ℕ)^8289*100000000000000^6241 ≤ 42911022836823^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288733783 10000000000 42911022836823 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077312079/2000000000 : ℝ)^8289 ≤ (219842034893/500000000000 : ℝ)^6241 := by
    have hnat : (1077312079 : ℕ)^8289*500000000000^6241 ≤ 219842034893^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077312079 2000000000 219842034893 500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083562707/5000000000 : ℝ)^8289 ≤ (2624114032303/20000000000000 : ℝ)^6241 := by
    have hnat : (1083562707 : ℕ)^8289*20000000000000^6241 ≤ 2624114032303^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083562707 5000000000 2624114032303 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288733783/10000000000 : ℝ), (1077312079/2000000000 : ℝ), (-1083562707/5000000000 : ℝ)] ![(42911022836823/100000000000000 : ℝ), (219842034893/500000000000 : ℝ), (2624114032303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288733783/10000000000 : ℝ)|^8289 ≤ (42911022836823/100000000000000 : ℝ)^6241
        have hw : |(5288733783/10000000000 : ℝ)|=(5288733783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077312079/2000000000 : ℝ)|^8289 ≤ (219842034893/500000000000 : ℝ)^6241
        have hw : |(1077312079/2000000000 : ℝ)|=(1077312079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1083562707/5000000000 : ℝ)|^8289 ≤ (2624114032303/20000000000000 : ℝ)^6241
        have hw : |(-1083562707/5000000000 : ℝ)|=(1083562707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_11 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (900105457/2000000000 : ℝ)*x 0 + (4308530699/10000000000 : ℝ)*x 1 + (538566431/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (900105457/2000000000 : ℝ)^8289 ≤ (34632265545343/100000000000000 : ℝ)^6241 := by
    have hnat : (900105457 : ℕ)^8289*100000000000000^6241 ≤ 34632265545343^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900105457 2000000000 34632265545343 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4308530699/10000000000 : ℝ)^8289 ≤ (32683863442851/100000000000000 : ℝ)^6241 := by
    have hnat : (4308530699 : ℕ)^8289*100000000000000^6241 ≤ 32683863442851^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308530699 10000000000 32683863442851 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538566431/1250000000 : ℝ)^8289 ≤ (32683870989149/100000000000000 : ℝ)^6241 := by
    have hnat : (538566431 : ℕ)^8289*100000000000000^6241 ≤ 32683870989149^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538566431 1250000000 32683870989149 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(900105457/2000000000 : ℝ), (4308530699/10000000000 : ℝ), (538566431/1250000000 : ℝ)] ![(34632265545343/100000000000000 : ℝ), (32683863442851/100000000000000 : ℝ), (32683870989149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(900105457/2000000000 : ℝ)|^8289 ≤ (34632265545343/100000000000000 : ℝ)^6241
        have hw : |(900105457/2000000000 : ℝ)|=(900105457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4308530699/10000000000 : ℝ)|^8289 ≤ (32683863442851/100000000000000 : ℝ)^6241
        have hw : |(4308530699/10000000000 : ℝ)|=(4308530699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538566431/1250000000 : ℝ)|^8289 ≤ (32683870989149/100000000000000 : ℝ)^6241
        have hw : |(538566431/1250000000 : ℝ)|=(538566431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_12 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-84597901/400000000 : ℝ)*x 0 + (272056899/500000000 : ℝ)*x 1 + (1054501573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84597901/400000000 : ℝ)^8289 ≤ (12702667940769/100000000000000 : ℝ)^6241 := by
    have hnat : (84597901 : ℕ)^8289*100000000000000^6241 ≤ 12702667940769^6241*400000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84597901 400000000 12702667940769 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272056899/500000000 : ℝ)^8289 ≤ (22280537322009/50000000000000 : ℝ)^6241 := by
    have hnat : (272056899 : ℕ)^8289*50000000000000^6241 ≤ 22280537322009^6241*500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272056899 500000000 22280537322009 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054501573/2000000000 : ℝ)^8289 ≤ (42736257390883/100000000000000 : ℝ)^6241 := by
    have hnat : (1054501573 : ℕ)^8289*100000000000000^6241 ≤ 42736257390883^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054501573 2000000000 42736257390883 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84597901/400000000 : ℝ), (272056899/500000000 : ℝ), (1054501573/2000000000 : ℝ)] ![(12702667940769/100000000000000 : ℝ), (22280537322009/50000000000000 : ℝ), (42736257390883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84597901/400000000 : ℝ)|^8289 ≤ (12702667940769/100000000000000 : ℝ)^6241
        have hw : |(-84597901/400000000 : ℝ)|=(84597901/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272056899/500000000 : ℝ)|^8289 ≤ (22280537322009/50000000000000 : ℝ)^6241
        have hw : |(272056899/500000000 : ℝ)|=(272056899/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054501573/2000000000 : ℝ)|^8289 ≤ (42736257390883/100000000000000 : ℝ)^6241
        have hw : |(1054501573/2000000000 : ℝ)|=(1054501573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_13 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684698353/5000000000 : ℝ)*x 0 + (-552959197/2500000000 : ℝ)*x 1 + (1318127011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684698353/5000000000 : ℝ)^8289 ≤ (43782429431511/100000000000000 : ℝ)^6241 := by
    have hnat : (2684698353 : ℕ)^8289*100000000000000^6241 ≤ 43782429431511^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684698353 5000000000 43782429431511 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552959197/2500000000 : ℝ)^8289 ≤ (13481311239893/100000000000000 : ℝ)^6241 := by
    have hnat : (552959197 : ℕ)^8289*100000000000000^6241 ≤ 13481311239893^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552959197 2500000000 13481311239893 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318127011/2500000000 : ℝ)^8289 ≤ (10684064829469/25000000000000 : ℝ)^6241 := by
    have hnat : (1318127011 : ℕ)^8289*25000000000000^6241 ≤ 10684064829469^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318127011 2500000000 10684064829469 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684698353/5000000000 : ℝ), (-552959197/2500000000 : ℝ), (1318127011/2500000000 : ℝ)] ![(43782429431511/100000000000000 : ℝ), (13481311239893/100000000000000 : ℝ), (10684064829469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684698353/5000000000 : ℝ)|^8289 ≤ (43782429431511/100000000000000 : ℝ)^6241
        have hw : |(2684698353/5000000000 : ℝ)|=(2684698353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-552959197/2500000000 : ℝ)|^8289 ≤ (13481311239893/100000000000000 : ℝ)^6241
        have hw : |(-552959197/2500000000 : ℝ)|=(552959197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318127011/2500000000 : ℝ)|^8289 ≤ (10684064829469/25000000000000 : ℝ)^6241
        have hw : |(1318127011/2500000000 : ℝ)|=(1318127011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_14 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1073879333/2000000000 : ℝ)*x 0 + (329531767/625000000 : ℝ)*x 1 + (-110591827/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073879333/2000000000 : ℝ)^8289 ≤ (43782428987487/100000000000000 : ℝ)^6241 := by
    have hnat : (1073879333 : ℕ)^8289*100000000000000^6241 ≤ 43782428987487^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073879333 2000000000 43782428987487 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329531767/625000000 : ℝ)^8289 ≤ (42736261772371/100000000000000 : ℝ)^6241 := by
    have hnat : (329531767 : ℕ)^8289*100000000000000^6241 ≤ 42736261772371^6241*625000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329531767 625000000 42736261772371 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110591827/500000000 : ℝ)^8289 ≤ (6740654616143/50000000000000 : ℝ)^6241 := by
    have hnat : (110591827 : ℕ)^8289*50000000000000^6241 ≤ 6740654616143^6241*500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110591827 500000000 6740654616143 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073879333/2000000000 : ℝ), (329531767/625000000 : ℝ), (-110591827/500000000 : ℝ)] ![(43782428987487/100000000000000 : ℝ), (42736261772371/100000000000000 : ℝ), (6740654616143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073879333/2000000000 : ℝ)|^8289 ≤ (43782428987487/100000000000000 : ℝ)^6241
        have hw : |(1073879333/2000000000 : ℝ)|=(1073879333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329531767/625000000 : ℝ)|^8289 ≤ (42736261772371/100000000000000 : ℝ)^6241
        have hw : |(329531767/625000000 : ℝ)|=(329531767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110591827/500000000 : ℝ)|^8289 ≤ (6740654616143/50000000000000 : ℝ)^6241
        have hw : |(-110591827/500000000 : ℝ)|=(110591827/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_box_15 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4244584323/10000000000 : ℝ)*x 0 + (4436499757/10000000000 : ℝ)*x 1 + (4436500083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244584323/10000000000 : ℝ)^8289 ≤ (6408233468383/20000000000000 : ℝ)^6241 := by
    have hnat : (4244584323 : ℕ)^8289*20000000000000^6241 ≤ 6408233468383^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244584323 10000000000 6408233468383 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4436499757/10000000000 : ℝ)^8289 ≤ (8494853664871/25000000000000 : ℝ)^6241 := by
    have hnat : (4436499757 : ℕ)^8289*25000000000000^6241 ≤ 8494853664871^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4436499757 10000000000 8494853664871 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4436500083/10000000000 : ℝ)^8289 ≤ (33979417975687/100000000000000 : ℝ)^6241 := by
    have hnat : (4436500083 : ℕ)^8289*100000000000000^6241 ≤ 33979417975687^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4436500083 10000000000 33979417975687 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244584323/10000000000 : ℝ), (4436499757/10000000000 : ℝ), (4436500083/10000000000 : ℝ)] ![(6408233468383/20000000000000 : ℝ), (8494853664871/25000000000000 : ℝ), (33979417975687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244584323/10000000000 : ℝ)|^8289 ≤ (6408233468383/20000000000000 : ℝ)^6241
        have hw : |(4244584323/10000000000 : ℝ)|=(4244584323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4436499757/10000000000 : ℝ)|^8289 ≤ (8494853664871/25000000000000 : ℝ)^6241
        have hw : |(4436499757/10000000000 : ℝ)|=(4436499757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4436500083/10000000000 : ℝ)|^8289 ≤ (33979417975687/100000000000000 : ℝ)^6241
        have hw : |(4436500083/10000000000 : ℝ)|=(4436500083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1096_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62227/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59263/100000 : ℝ) ∧ (39833/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83021/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11293/100000 : ℝ) ^ (259/64 : ℝ) ≤ (14683775968522709/100000000000000000000 : ℝ) := by
    have hpowers : (11293/100000 : ℝ)^259 ≤ (14683775968522709/100000000000000000000 : ℝ)^64 := by
      have hnat : (11293 : ℕ)^259*100000000000000000000^64 ≤ 14683775968522709^64*100000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11293 100000 14683775968522709 100000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11293/100000 : ℝ)) (X := (14683775968522709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14021/100000 : ℝ) ^ (259/64 : ℝ) ≤ (8811731005377977/25000000000000000000 : ℝ) := by
    have hpowers : (14021/100000 : ℝ)^259 ≤ (8811731005377977/25000000000000000000 : ℝ)^64 := by
      have hnat : (14021 : ℕ)^259*25000000000000000000^64 ≤ 8811731005377977^64*100000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14021 100000 8811731005377977 25000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14021/100000 : ℝ)) (X := (8811731005377977/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014683775968522709/50000000000000000000 : ℝ) ≤ (5000362802233917/5000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (50014683775968522709/50000000000000000000 : ℝ)^64 ≤ (5000362802233917/5000000000000000 : ℝ)^259 := by
      have hnat : (50014683775968522709 : ℕ)^64*5000000000000000^259 ≤ 5000362802233917^259*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014683775968522709 50000000000000000000 5000362802233917 5000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000362802233917/5000000000000000 : ℝ)) (X := (50014683775968522709/50000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049930699990034617/100000000000000000000 : ℝ) ≤ (10001233576960001/10000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (100049930699990034617/100000000000000000000 : ℝ)^64 ≤ (10001233576960001/10000000000000000 : ℝ)^259 := by
      have hnat : (100049930699990034617 : ℕ)^64*10000000000000000^259 ≤ 10001233576960001^259*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049930699990034617 100000000000000000000 10001233576960001 10000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001233576960001/10000000000000000 : ℝ)) (X := (100049930699990034617/100000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508811731005377977/12500000000000000000 : ℝ) ≤ (1250217693681521/1250000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (12508811731005377977/12500000000000000000 : ℝ)^64 ≤ (1250217693681521/1250000000000000 : ℝ)^259 := by
      have hnat : (12508811731005377977 : ℕ)^64*1250000000000000^259 ≤ 1250217693681521^259*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508811731005377977 12500000000000000000 1250217693681521 1250000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250217693681521/1250000000000000 : ℝ)) (X := (12508811731005377977/12500000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14683775968522709/100000000000000000000 : ℝ) ≤ ((2727050638228016729/2728000000000000000 : ℝ)+2*(507972492167/272800000000000 : ℝ)*(11293/100000 : ℝ))^(259/64 : ℝ) := by
    rw [show (2727050638228016729/2728000000000000000 : ℝ)+2*(507972492167/272800000000000 : ℝ)*(11293/100000 : ℝ)=(5000362802233917/5000000000000000 : ℝ) by norm_num, show 1+2*(14683775968522709/100000000000000000000 : ℝ)=(50014683775968522709/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8811731005377977/25000000000000000000 : ℝ)+(14683775968522709/100000000000000000000 : ℝ) ≤ ((2727050638228016729/2728000000000000000 : ℝ)+(507972492167/272800000000000 : ℝ)*((14021/100000 : ℝ)+(11293/100000 : ℝ)))^(259/64 : ℝ) := by
    rw [show (2727050638228016729/2728000000000000000 : ℝ)+(507972492167/272800000000000 : ℝ)*((14021/100000 : ℝ)+(11293/100000 : ℝ))=(10001233576960001/10000000000000000 : ℝ) by norm_num, show 1+(8811731005377977/25000000000000000000 : ℝ)+(14683775968522709/100000000000000000000 : ℝ)=(100049930699990034617/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8811731005377977/25000000000000000000 : ℝ) ≤ ((2727050638228016729/2728000000000000000 : ℝ)+2*(507972492167/272800000000000 : ℝ)*(14021/100000 : ℝ))^(259/64 : ℝ) := by
    rw [show (2727050638228016729/2728000000000000000 : ℝ)+2*(507972492167/272800000000000 : ℝ)*(14021/100000 : ℝ)=(1250217693681521/1250000000000000 : ℝ) by norm_num, show 1+2*(8811731005377977/25000000000000000000 : ℝ)=(12508811731005377977/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2727050638228016729/2728000000000000000 : ℝ)*(X 1 0+X 2 0)+(507972492167/272800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (11293/100000 : ℝ)) (hi := (14021/100000 : ℝ)) (c := (2727050638228016729/2728000000000000000 : ℝ)) (alpha := (507972492167/272800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2727050638228016729/2728000000000000000 : ℝ)*(X 0 1+X 2 1)+(507972492167/272800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (11293/100000 : ℝ)) (hi := (14021/100000 : ℝ)) (c := (2727050638228016729/2728000000000000000 : ℝ)) (alpha := (507972492167/272800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2727050638228016729/2728000000000000000 : ℝ)*(X 0 2+X 1 2)+(507972492167/272800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (11293/100000 : ℝ)) (hi := (14021/100000 : ℝ)) (c := (2727050638228016729/2728000000000000000 : ℝ)) (alpha := (507972492167/272800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-128790569/625000000 : ℝ)*X 0 0+(672119523/1250000000 : ℝ)*X 0 1+(215078271/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((264776479/500000000 : ℝ)*X 1 0+(-2170959189/10000000000 : ℝ)*X 1 1+(1075391341/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295530251/10000000000 : ℝ)*X 2 0+(5376956353/10000000000 : ℝ)*X 2 1+(-434191753/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4479243423/10000000000 : ℝ)*X 0 0+(33744637/78125000 : ℝ)*X 0 1+(2159656771/5000000000 : ℝ)*X 0 2+(4479243423/10000000000 : ℝ)*X 1 0+(33744637/78125000 : ℝ)*X 1 1+(2159656771/5000000000 : ℝ)*X 1 2+(4479243423/10000000000 : ℝ)*X 2 0+(33744637/78125000 : ℝ)*X 2 1+(2159656771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-579725547/2500000000 : ℝ)*X 0 0+(2640262289/5000000000 : ℝ)*X 0 1+(33003279/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((536372963/1000000000 : ℝ)*X 1 0+(-441750577/2000000000 : ℝ)*X 1 1+(1056104913/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((268186479/500000000 : ℝ)*X 2 0+(660065621/1250000000 : ℝ)*X 2 1+(-69023513/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4262807583/10000000000 : ℝ)*X 0 0+(1106877633/2500000000 : ℝ)*X 0 1+(4427509967/10000000000 : ℝ)*X 0 2+(4262807583/10000000000 : ℝ)*X 1 0+(1106877633/2500000000 : ℝ)*X 1 1+(4427509967/10000000000 : ℝ)*X 1 2+(4262807583/10000000000 : ℝ)*X 2 0+(1106877633/2500000000 : ℝ)*X 2 1+(4427509967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2264952107/10000000000 : ℝ)*X 0 0+(1303757791/2500000000 : ℝ)*X 0 1+(538656101/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322183489/2500000000 : ℝ)*X 1 0+(-433424833/2000000000 : ℝ)*X 1 1+(5386561151/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288733783/10000000000 : ℝ)*X 2 0+(1077312079/2000000000 : ℝ)*X 2 1+(-1083562707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((900105457/2000000000 : ℝ)*X 0 0+(4308530699/10000000000 : ℝ)*X 0 1+(538566431/1250000000 : ℝ)*X 0 2+(900105457/2000000000 : ℝ)*X 1 0+(4308530699/10000000000 : ℝ)*X 1 1+(538566431/1250000000 : ℝ)*X 1 2+(900105457/2000000000 : ℝ)*X 2 0+(4308530699/10000000000 : ℝ)*X 2 1+(538566431/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-84597901/400000000 : ℝ)*X 0 0+(272056899/500000000 : ℝ)*X 0 1+(1054501573/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684698353/5000000000 : ℝ)*X 1 0+(-552959197/2500000000 : ℝ)*X 1 1+(1318127011/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1073879333/2000000000 : ℝ)*X 2 0+(329531767/625000000 : ℝ)*X 2 1+(-110591827/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4244584323/10000000000 : ℝ)*X 0 0+(4436499757/10000000000 : ℝ)*X 0 1+(4436500083/10000000000 : ℝ)*X 0 2+(4244584323/10000000000 : ℝ)*X 1 0+(4436499757/10000000000 : ℝ)*X 1 1+(4436500083/10000000000 : ℝ)*X 1 2+(4244584323/10000000000 : ℝ)*X 2 0+(4436499757/10000000000 : ℝ)*X 2 1+(4436500083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62227/100000 : ℝ) ≤ (-84873607178648531132092639706901/136400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38172161/100000000000000 : ℝ)*(upper1) + (73912341/50000000000000 : ℝ)*(lower2) + (69768189/100000000000000 : ℝ)*(upper4) + (3881918144549941/100000000000000 : ℝ)*(major0) + (3881918144549941/100000000000000 : ℝ)*(major1) + (3881918144549941/100000000000000 : ℝ)*(major2) + (2292201721/25000000000000 : ℝ)*(sp1) + (1616429617/100000000000000 : ℝ)*(sp3) + (5171837605684399/100000000000000 : ℝ)*(sp4) + (5171836717063197/100000000000000 : ℝ)*(sp5) + (5171526637450891/100000000000000 : ℝ)*(sp6) + (81647816797753/3125000000000 : ℝ)*(sp7) + (4140092841/50000000000000 : ℝ)*(sp8) + (319248419191/100000000000000 : ℝ)*(sp14) + (2612731753957713/100000000000000 : ℝ)*(f.failure) + (5171845885870081/100000000000000 : ℝ)*(f.sum) + (48663439779573/13640000000000000000000000000 : ℝ)*base66 + (2371431659554232989/272800000000000000000000000000000 : ℝ)*base67 + (3120812939832632989/272800000000000000000000000000000 : ℝ)*base69 + (5158953472806232989/272800000000000000000000000000000 : ℝ)*base71 + (8902019780827/13640000000000000000000000000 : ℝ)*base73 + (1760811820916632989/272800000000000000000000000000000 : ℝ)*base75 + (611268907954232989/272800000000000000000000000000000 : ℝ)*base77 + (1142974530138232989/272800000000000000000000000000000 : ℝ)*base79 + (27808531714147/13640000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5772889/2500000000000000000000 : ℝ)*base90 + (5772889/2500000000000000000000 : ℝ)*base92 + (5772889/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59263/100000 : ℝ) ≤ (252620346686799942054504633/426250000000000000000000000 : ℝ) := by norm_num
    linear_combination (3993553/25000000000000 : ℝ)*(lower1) + (54945199/25000000000000 : ℝ)*(lower2) + (124689301/50000000000000 : ℝ)*(lower3) + (53264467/100000000000000 : ℝ)*(upper4) + (493166665634263/12500000000000 : ℝ)*(major0) + (493166665634263/12500000000000 : ℝ)*(major1) + (493166665634263/12500000000000 : ℝ)*(major2) + (40746077671057/781250000000 : ℝ)*(sp0) + (651934690477059/12500000000000 : ℝ)*(sp1) + (5215488801518957/100000000000000 : ℝ)*(sp2) + (5186347773101/195312500000 : ℝ)*(sp3) + (816723153/4000000000000 : ℝ)*(sp5) + (9140376339/100000000000000 : ℝ)*(sp6) + (1695798643/50000000000000 : ℝ)*(sp7) + (1327706725712499/50000000000000 : ℝ)*(f.failure) + (40746077671057/781250000000 : ℝ)*(f.sum) + (2420488718729/1705000000000000000000000000 : ℝ)*base66 + (202054557518004273/34100000000000000000000000000000 : ℝ)*base68 + (124469323508195727/34100000000000000000000000000000 : ℝ)*base69 + (1413165319680395727/34100000000000000000000000000000 : ℝ)*base71 + (3687315864483/852500000000000000000000000 : ℝ)*base73 + (341365678030304273/34100000000000000000000000000000 : ℝ)*base76 + (728623187970695727/34100000000000000000000000000000 : ℝ)*base77 + (283529875374904273/34100000000000000000000000000000 : ℝ)*base80 + (7026585417/213125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (13843253/1250000000000000000000 : ℝ)*base89 + (13843253/1250000000000000000000 : ℝ)*base91 + (13843253/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39833/50000 : ℝ) ≤ (6791752677748432865830809907389/8525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3230709/1250000000000 : ℝ)*(upper0) + (119687307/25000000000000 : ℝ)*(upper2) + (1310509/781250000000 : ℝ)*(lower3) + (718623839/100000000000000 : ℝ)*(lower5) + (275840615634051/6250000000000 : ℝ)*(major0) + (275840615634051/6250000000000 : ℝ)*(major1) + (275840615634051/6250000000000 : ℝ)*(major2) + (278041127229/50000000000000 : ℝ)*(sp1) + (213927713/80000000000 : ℝ)*(sp3) + (669911593/2500000000000 : ℝ)*(sp4) + (2914918296956191/50000000000000 : ℝ)*(sp8) + (1457326827030411/25000000000000 : ℝ)*(sp9) + (2914931695188051/50000000000000 : ℝ)*(sp10) + (185638292660529/6250000000000 : ℝ)*(sp11) + (1485240046104857/50000000000000 : ℝ)*(f.failure) + (2914931695188051/50000000000000 : ℝ)*(f.sum) + (2601125759027/852500000000000000000000000 : ℝ)*base65 + (31913303950009179/17050000000000000000000000000000 : ℝ)*base67 + (299389767991609179/17050000000000000000000000000000 : ℝ)*base69 + (86440377842509179/17050000000000000000000000000000 : ℝ)*base71 + (1146226711167/213125000000000000000000000 : ℝ)*base74 + (39404436927909179/17050000000000000000000000000000 : ℝ)*base75 + (101852852160409179/17050000000000000000000000000000 : ℝ)*base77 + (655484701881909179/17050000000000000000000000000000 : ℝ)*base79 + (3136686388257/852500000000000000000000000 : ℝ)*base81 + (3692321/1250000000000000000000 : ℝ)*base90 + (3692321/1250000000000000000000 : ℝ)*base92 + (3692321/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-83021/100000 : ℝ) ≤ (-56618465192643017953527439003797/68200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8296697/20000000000000 : ℝ)*(lower0) + (61482187/50000000000000 : ℝ)*(upper3) + (395879833/100000000000000 : ℝ)*(upper5) + (2224072884364031/50000000000000 : ℝ)*(major0) + (2224072884364031/50000000000000 : ℝ)*(major1) + (2224072884364031/50000000000000 : ℝ)*(major2) + (159675099/5000000000000 : ℝ)*(sp4) + (1716126021/4000000000000 : ℝ)*(sp5) + (3727993651/10000000000000 : ℝ)*(sp7) + (658387499/50000000000000 : ℝ)*(sp8) + (1186025509160337/20000000000000 : ℝ)*(sp12) + (2965044576464069/50000000000000 : ℝ)*(sp13) + (5930132056078663/100000000000000 : ℝ)*(sp14) + (2993794960577117/100000000000000 : ℝ)*(sp15) + (2993832240513627/100000000000000 : ℝ)*(f.failure) + (5930132056078663/100000000000000 : ℝ)*(f.sum) + (1686047540223/6820000000000000000000000000 : ℝ)*base66 + (6990644845810755401/136400000000000000000000000000000 : ℝ)*base68 + (697939266915244599/136400000000000000000000000000000 : ℝ)*base69 + (39154858862044599/136400000000000000000000000000000 : ℝ)*base71 + (367227606461223/6820000000000000000000000000 : ℝ)*base74 + (2256592843606444599/136400000000000000000000000000000 : ℝ)*base75 + (10684298536755401/136400000000000000000000000000000 : ℝ)*base78 + (12798130491755644599/136400000000000000000000000000000 : ℝ)*base79 + (21303712006843/6820000000000000000000000000 : ℝ)*base82 + (18153869/2500000000000000000000 : ℝ)*base89 + (18153869/2500000000000000000000 : ℝ)*base91 + (18153869/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1096_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59263/100000 : ℝ) else (39833/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83021/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1096_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1096_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59263/100000 : ℝ) else (39833/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83021/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1096_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59263/100000 : ℝ) else (39833/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83021/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1096_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
