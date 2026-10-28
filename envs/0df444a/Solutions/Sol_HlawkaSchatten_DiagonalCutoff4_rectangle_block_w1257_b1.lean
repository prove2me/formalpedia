-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1257_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:52:19.46701+00:00
-- url     : https://prove2.me/submissions/3d7220f1-8362-429a-a9a6-909dc8b1f205

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
theorem support_rectangle_w1257_s3_0 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110352207/10000000000 : ℝ)*x 0 + (677294427/1250000000 : ℝ)*x 1 + (1310440027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110352207/10000000000 : ℝ)^4225 ≤ (6414843600073/50000000000000 : ℝ)^3201 := by
    have hnat : (2110352207 : ℕ)^4225*50000000000000^3201 ≤ 6414843600073^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110352207 10000000000 6414843600073 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677294427/1250000000 : ℝ)^4225 ≤ (44538100461341/100000000000000 : ℝ)^3201 := by
    have hnat : (677294427 : ℕ)^4225*100000000000000^3201 ≤ 44538100461341^3201*1250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677294427 1250000000 44538100461341 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310440027/2500000000 : ℝ)^4225 ≤ (42632212315237/100000000000000 : ℝ)^3201 := by
    have hnat : (1310440027 : ℕ)^4225*100000000000000^3201 ≤ 42632212315237^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310440027 2500000000 42632212315237 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110352207/10000000000 : ℝ), (677294427/1250000000 : ℝ), (1310440027/2500000000 : ℝ)] ![(6414843600073/50000000000000 : ℝ), (44538100461341/100000000000000 : ℝ), (42632212315237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110352207/10000000000 : ℝ)|^4225 ≤ (6414843600073/50000000000000 : ℝ)^3201
        have hw : |(-2110352207/10000000000 : ℝ)|=(2110352207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677294427/1250000000 : ℝ)|^4225 ≤ (44538100461341/100000000000000 : ℝ)^3201
        have hw : |(677294427/1250000000 : ℝ)|=(677294427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310440027/2500000000 : ℝ)|^4225 ≤ (42632212315237/100000000000000 : ℝ)^3201
        have hw : |(1310440027/2500000000 : ℝ)|=(1310440027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s3_1 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334447511/625000000 : ℝ)*x 0 + (-440083177/2000000000 : ℝ)*x 1 + (5241760207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334447511/625000000 : ℝ)^4225 ≤ (21905261710323/50000000000000 : ℝ)^3201 := by
    have hnat : (334447511 : ℕ)^4225*50000000000000^3201 ≤ 21905261710323^3201*625000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334447511 625000000 21905261710323 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440083177/2000000000 : ℝ)^4225 ≤ (1355726319561/10000000000000 : ℝ)^3201 := by
    have hnat : (440083177 : ℕ)^4225*10000000000000^3201 ≤ 1355726319561^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440083177 2000000000 1355726319561 10000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241760207/10000000000 : ℝ)^4225 ≤ (42632213378001/100000000000000 : ℝ)^3201 := by
    have hnat : (5241760207 : ℕ)^4225*100000000000000^3201 ≤ 42632213378001^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241760207 10000000000 42632213378001 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334447511/625000000 : ℝ), (-440083177/2000000000 : ℝ), (5241760207/10000000000 : ℝ)] ![(21905261710323/50000000000000 : ℝ), (1355726319561/10000000000000 : ℝ), (42632213378001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334447511/625000000 : ℝ)|^4225 ≤ (21905261710323/50000000000000 : ℝ)^3201
        have hw : |(334447511/625000000 : ℝ)|=(334447511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440083177/2000000000 : ℝ)|^4225 ≤ (1355726319561/10000000000000 : ℝ)^3201
        have hw : |(-440083177/2000000000 : ℝ)|=(440083177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241760207/10000000000 : ℝ)|^4225 ≤ (42632213378001/100000000000000 : ℝ)^3201
        have hw : |(5241760207/10000000000 : ℝ)|=(5241760207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s3_2 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334447509/625000000 : ℝ)*x 0 + (5241760681/10000000000 : ℝ)*x 1 + (-2200415301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334447509/625000000 : ℝ)^4225 ≤ (43810523074849/100000000000000 : ℝ)^3201 := by
    have hnat : (334447509 : ℕ)^4225*100000000000000^3201 ≤ 43810523074849^3201*625000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334447509 625000000 43810523074849 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241760681/10000000000 : ℝ)^4225 ≤ (10658054616597/25000000000000 : ℝ)^3201 := by
    have hnat : (5241760681 : ℕ)^4225*25000000000000^3201 ≤ 10658054616597^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241760681 10000000000 10658054616597 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200415301/10000000000 : ℝ)^4225 ≤ (13557258446403/100000000000000 : ℝ)^3201 := by
    have hnat : (2200415301 : ℕ)^4225*100000000000000^3201 ≤ 13557258446403^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200415301 10000000000 13557258446403 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334447509/625000000 : ℝ), (5241760681/10000000000 : ℝ), (-2200415301/10000000000 : ℝ)] ![(43810523074849/100000000000000 : ℝ), (10658054616597/25000000000000 : ℝ), (13557258446403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334447509/625000000 : ℝ)|^4225 ≤ (43810523074849/100000000000000 : ℝ)^3201
        have hw : |(334447509/625000000 : ℝ)|=(334447509/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241760681/10000000000 : ℝ)|^4225 ≤ (10658054616597/25000000000000 : ℝ)^3201
        have hw : |(5241760681/10000000000 : ℝ)|=(5241760681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2200415301/10000000000 : ℝ)|^4225 ≤ (13557258446403/100000000000000 : ℝ)^3201
        have hw : |(-2200415301/10000000000 : ℝ)|=(2200415301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s3_3 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (54338661/125000000 : ℝ)*x 0 + (1042762363/2500000000 : ℝ)*x 1 + (4530321621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54338661/125000000 : ℝ)^4225 ≤ (2081319531719/6250000000000 : ℝ)^3201 := by
    have hnat : (54338661 : ℕ)^4225*6250000000000^3201 ≤ 2081319531719^3201*125000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54338661 125000000 2081319531719 6250000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042762363/2500000000 : ℝ)^4225 ≤ (31532747335283/100000000000000 : ℝ)^3201 := by
    have hnat : (1042762363 : ℕ)^4225*100000000000000^3201 ≤ 31532747335283^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042762363 2500000000 31532747335283 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530321621/10000000000 : ℝ)^4225 ≤ (35166140143039/100000000000000 : ℝ)^3201 := by
    have hnat : (4530321621 : ℕ)^4225*100000000000000^3201 ≤ 35166140143039^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530321621 10000000000 35166140143039 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54338661/125000000 : ℝ), (1042762363/2500000000 : ℝ), (4530321621/10000000000 : ℝ)] ![(2081319531719/6250000000000 : ℝ), (31532747335283/100000000000000 : ℝ), (35166140143039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54338661/125000000 : ℝ)|^4225 ≤ (2081319531719/6250000000000 : ℝ)^3201
        have hw : |(54338661/125000000 : ℝ)|=(54338661/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042762363/2500000000 : ℝ)|^4225 ≤ (31532747335283/100000000000000 : ℝ)^3201
        have hw : |(1042762363/2500000000 : ℝ)|=(1042762363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530321621/10000000000 : ℝ)|^4225 ≤ (35166140143039/100000000000000 : ℝ)^3201
        have hw : |(4530321621/10000000000 : ℝ)|=(4530321621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s3_4 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110366307/10000000000 : ℝ)*x 0 + (2621197987/5000000000 : ℝ)*x 1 + (5417715803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110366307/10000000000 : ℝ)^4225 ≤ (3207450085399/25000000000000 : ℝ)^3201 := by
    have hnat : (2110366307 : ℕ)^4225*25000000000000^3201 ≤ 3207450085399^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110366307 10000000000 3207450085399 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621197987/5000000000 : ℝ)^4225 ≤ (1705561538591/4000000000000 : ℝ)^3201 := by
    have hnat : (2621197987 : ℕ)^4225*4000000000000^3201 ≤ 1705561538591^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621197987 5000000000 1705561538591 4000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417715803/10000000000 : ℝ)^4225 ≤ (2783197573923/6250000000000 : ℝ)^3201 := by
    have hnat : (5417715803 : ℕ)^4225*6250000000000^3201 ≤ 2783197573923^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417715803 10000000000 2783197573923 6250000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110366307/10000000000 : ℝ), (2621197987/5000000000 : ℝ), (5417715803/10000000000 : ℝ)] ![(3207450085399/25000000000000 : ℝ), (1705561538591/4000000000000 : ℝ), (2783197573923/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110366307/10000000000 : ℝ)|^4225 ≤ (3207450085399/25000000000000 : ℝ)^3201
        have hw : |(-2110366307/10000000000 : ℝ)|=(2110366307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621197987/5000000000 : ℝ)|^4225 ≤ (1705561538591/4000000000000 : ℝ)^3201
        have hw : |(2621197987/5000000000 : ℝ)|=(2621197987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417715803/10000000000 : ℝ)|^4225 ≤ (2783197573923/6250000000000 : ℝ)^3201
        have hw : |(5417715803/10000000000 : ℝ)|=(5417715803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s3_5 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061212411/2000000000 : ℝ)*x 0 + (-2024459667/10000000000 : ℝ)*x 1 + (2708857821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061212411/2000000000 : ℝ)^4225 ≤ (5415480494291/12500000000000 : ℝ)^3201 := by
    have hnat : (1061212411 : ℕ)^4225*12500000000000^3201 ≤ 5415480494291^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061212411 2000000000 5415480494291 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2024459667/10000000000 : ℝ)^4225 ≤ (151812457459/1250000000000 : ℝ)^3201 := by
    have hnat : (2024459667 : ℕ)^4225*1250000000000^3201 ≤ 151812457459^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024459667 10000000000 151812457459 1250000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708857821/5000000000 : ℝ)^4225 ≤ (44531159436083/100000000000000 : ℝ)^3201 := by
    have hnat : (2708857821 : ℕ)^4225*100000000000000^3201 ≤ 44531159436083^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708857821 5000000000 44531159436083 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061212411/2000000000 : ℝ), (-2024459667/10000000000 : ℝ), (2708857821/5000000000 : ℝ)] ![(5415480494291/12500000000000 : ℝ), (151812457459/1250000000000 : ℝ), (44531159436083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061212411/2000000000 : ℝ)|^4225 ≤ (5415480494291/12500000000000 : ℝ)^3201
        have hw : |(1061212411/2000000000 : ℝ)|=(1061212411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2024459667/10000000000 : ℝ)|^4225 ≤ (151812457459/1250000000000 : ℝ)^3201
        have hw : |(-2024459667/10000000000 : ℝ)|=(2024459667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708857821/5000000000 : ℝ)|^4225 ≤ (44531159436083/100000000000000 : ℝ)^3201
        have hw : |(2708857821/5000000000 : ℝ)|=(2708857821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s3_6 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2653030703/5000000000 : ℝ)*x 0 + (42325907/78125000 : ℝ)*x 1 + (-253057491/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2653030703/5000000000 : ℝ)^4225 ≤ (4332383696009/10000000000000 : ℝ)^3201 := by
    have hnat : (2653030703 : ℕ)^4225*10000000000000^3201 ≤ 4332383696009^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653030703 5000000000 4332383696009 10000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42325907/78125000 : ℝ)^4225 ≤ (44531164361519/100000000000000 : ℝ)^3201 := by
    have hnat : (42325907 : ℕ)^4225*100000000000000^3201 ≤ 44531164361519^3201*78125000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42325907 78125000 44531164361519 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253057491/1250000000 : ℝ)^4225 ≤ (12144998663383/100000000000000 : ℝ)^3201 := by
    have hnat : (253057491 : ℕ)^4225*100000000000000^3201 ≤ 12144998663383^3201*1250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253057491 1250000000 12144998663383 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2653030703/5000000000 : ℝ), (42325907/78125000 : ℝ), (-253057491/1250000000 : ℝ)] ![(4332383696009/10000000000000 : ℝ), (44531164361519/100000000000000 : ℝ), (12144998663383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2653030703/5000000000 : ℝ)|^4225 ≤ (4332383696009/10000000000000 : ℝ)^3201
        have hw : |(2653030703/5000000000 : ℝ)|=(2653030703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42325907/78125000 : ℝ)|^4225 ≤ (44531164361519/100000000000000 : ℝ)^3201
        have hw : |(42325907/78125000 : ℝ)|=(42325907/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253057491/1250000000 : ℝ)|^4225 ≤ (12144998663383/100000000000000 : ℝ)^3201
        have hw : |(-253057491/1250000000 : ℝ)|=(253057491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s3_7 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4347121047/10000000000 : ℝ)*x 0 + (4529027211/10000000000 : ℝ)*x 1 + (521543733/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347121047/10000000000 : ℝ)^4225 ≤ (33301397308763/100000000000000 : ℝ)^3201 := by
    have hnat : (4347121047 : ℕ)^4225*100000000000000^3201 ≤ 33301397308763^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347121047 10000000000 33301397308763 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4529027211/10000000000 : ℝ)^4225 ≤ (274631865337/781250000000 : ℝ)^3201 := by
    have hnat : (4529027211 : ℕ)^4225*781250000000^3201 ≤ 274631865337^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529027211 10000000000 274631865337 781250000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521543733/1250000000 : ℝ)^4225 ≤ (1971607744493/6250000000000 : ℝ)^3201 := by
    have hnat : (521543733 : ℕ)^4225*6250000000000^3201 ≤ 1971607744493^3201*1250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521543733 1250000000 1971607744493 6250000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347121047/10000000000 : ℝ), (4529027211/10000000000 : ℝ), (521543733/1250000000 : ℝ)] ![(33301397308763/100000000000000 : ℝ), (274631865337/781250000000 : ℝ), (1971607744493/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347121047/10000000000 : ℝ)|^4225 ≤ (33301397308763/100000000000000 : ℝ)^3201
        have hw : |(4347121047/10000000000 : ℝ)|=(4347121047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4529027211/10000000000 : ℝ)|^4225 ≤ (274631865337/781250000000 : ℝ)^3201
        have hw : |(4529027211/10000000000 : ℝ)|=(4529027211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521543733/1250000000 : ℝ)|^4225 ≤ (1971607744493/6250000000000 : ℝ)^3201
        have hw : |(521543733/1250000000 : ℝ)|=(521543733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1257_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2023/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (239/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (10949/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14687/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2023/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (239/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2023/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (239/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2023/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (239/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2023/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (239/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2023/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (239/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2023/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (239/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (239/2500 : ℝ) ^ (8449/2048 : ℝ) ≤ (3110720467222311/50000000000000000000 : ℝ) := by
    have hpowers : (239/2500 : ℝ)^8449 ≤ (3110720467222311/50000000000000000000 : ℝ)^2048 := by
      have hnat : (239 : ℕ)^8449*50000000000000000000^2048 ≤ 3110720467222311^2048*2500^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        239 2500 3110720467222311 50000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (239/2500 : ℝ)) (X := (3110720467222311/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2023/12500 : ℝ) ^ (8449/2048 : ℝ) ≤ (54587477287618979/100000000000000000000 : ℝ) := by
    have hpowers : (2023/12500 : ℝ)^8449 ≤ (54587477287618979/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2023 : ℕ)^8449*100000000000000000000^2048 ≤ 54587477287618979^2048*12500^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2023 12500 54587477287618979 100000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2023/12500 : ℝ)) (X := (54587477287618979/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003110720467222311/25000000000000000000 : ℝ) ≤ (10000301595704113/10000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (25003110720467222311/25000000000000000000 : ℝ)^2048 ≤ (10000301595704113/10000000000000000 : ℝ)^8449 := by
      have hnat : (25003110720467222311 : ℕ)^2048*10000000000000000^8449 ≤ 10000301595704113^8449*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003110720467222311 25000000000000000000 10000301595704113 10000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000301595704113/10000000000000000 : ℝ)) (X := (25003110720467222311/25000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100060808918222063601/100000000000000000000 : ℝ) ≤ (10001473641712271/10000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (100060808918222063601/100000000000000000000 : ℝ)^2048 ≤ (10001473641712271/10000000000000000 : ℝ)^8449 := by
      have hnat : (100060808918222063601 : ℕ)^2048*10000000000000000^8449 ≤ 10001473641712271^8449*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100060808918222063601 100000000000000000000 10001473641712271 10000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001473641712271/10000000000000000 : ℝ)) (X := (100060808918222063601/100000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50054587477287618979/50000000000000000000 : ℝ) ≤ (10002645687720429/10000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (50054587477287618979/50000000000000000000 : ℝ)^2048 ≤ (10002645687720429/10000000000000000 : ℝ)^8449 := by
      have hnat : (50054587477287618979 : ℕ)^2048*10000000000000000^8449 ≤ 10002645687720429^8449*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054587477287618979 50000000000000000000 10002645687720429 10000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002645687720429/10000000000000000 : ℝ)) (X := (50054587477287618979/50000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3110720467222311/50000000000000000000 : ℝ) ≤ ((1034681066410438493/1035000000000000000 : ℝ)+2*(586023004079/331200000000000 : ℝ)*(239/2500 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (1034681066410438493/1035000000000000000 : ℝ)+2*(586023004079/331200000000000 : ℝ)*(239/2500 : ℝ)=(10000301595704113/10000000000000000 : ℝ) by norm_num, show 1+2*(3110720467222311/50000000000000000000 : ℝ)=(25003110720467222311/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54587477287618979/100000000000000000000 : ℝ)+(3110720467222311/50000000000000000000 : ℝ) ≤ ((1034681066410438493/1035000000000000000 : ℝ)+(586023004079/331200000000000 : ℝ)*((2023/12500 : ℝ)+(239/2500 : ℝ)))^(8449/2048 : ℝ) := by
    rw [show (1034681066410438493/1035000000000000000 : ℝ)+(586023004079/331200000000000 : ℝ)*((2023/12500 : ℝ)+(239/2500 : ℝ))=(10001473641712271/10000000000000000 : ℝ) by norm_num, show 1+(54587477287618979/100000000000000000000 : ℝ)+(3110720467222311/50000000000000000000 : ℝ)=(100060808918222063601/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54587477287618979/100000000000000000000 : ℝ) ≤ ((1034681066410438493/1035000000000000000 : ℝ)+2*(586023004079/331200000000000 : ℝ)*(2023/12500 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (1034681066410438493/1035000000000000000 : ℝ)+2*(586023004079/331200000000000 : ℝ)*(2023/12500 : ℝ)=(10002645687720429/10000000000000000 : ℝ) by norm_num, show 1+2*(54587477287618979/100000000000000000000 : ℝ)=(50054587477287618979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1034681066410438493/1035000000000000000 : ℝ)*(X 1 0+X 2 0)+(586023004079/331200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (239/2500 : ℝ)) (hi := (2023/12500 : ℝ)) (c := (1034681066410438493/1035000000000000000 : ℝ)) (alpha := (586023004079/331200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1034681066410438493/1035000000000000000 : ℝ)*(X 0 1+X 2 1)+(586023004079/331200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (239/2500 : ℝ)) (hi := (2023/12500 : ℝ)) (c := (1034681066410438493/1035000000000000000 : ℝ)) (alpha := (586023004079/331200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1034681066410438493/1035000000000000000 : ℝ)*(X 0 2+X 1 2)+(586023004079/331200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (239/2500 : ℝ)) (hi := (2023/12500 : ℝ)) (c := (1034681066410438493/1035000000000000000 : ℝ)) (alpha := (586023004079/331200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2110352207/10000000000 : ℝ)*X 0 0+(677294427/1250000000 : ℝ)*X 0 1+(1310440027/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334447511/625000000 : ℝ)*X 1 0+(-440083177/2000000000 : ℝ)*X 1 1+(5241760207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334447509/625000000 : ℝ)*X 2 0+(5241760681/10000000000 : ℝ)*X 2 1+(-2200415301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((54338661/125000000 : ℝ)*X 0 0+(1042762363/2500000000 : ℝ)*X 0 1+(4530321621/10000000000 : ℝ)*X 0 2+(54338661/125000000 : ℝ)*X 1 0+(1042762363/2500000000 : ℝ)*X 1 1+(4530321621/10000000000 : ℝ)*X 1 2+(54338661/125000000 : ℝ)*X 2 0+(1042762363/2500000000 : ℝ)*X 2 1+(4530321621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2110366307/10000000000 : ℝ)*X 0 0+(2621197987/5000000000 : ℝ)*X 0 1+(5417715803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061212411/2000000000 : ℝ)*X 1 0+(-2024459667/10000000000 : ℝ)*X 1 1+(2708857821/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2653030703/5000000000 : ℝ)*X 2 0+(42325907/78125000 : ℝ)*X 2 1+(-253057491/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347121047/10000000000 : ℝ)*X 0 0+(4529027211/10000000000 : ℝ)*X 0 1+(521543733/1250000000 : ℝ)*X 0 2+(4347121047/10000000000 : ℝ)*X 1 0+(4529027211/10000000000 : ℝ)*X 1 1+(521543733/1250000000 : ℝ)*X 1 2+(4347121047/10000000000 : ℝ)*X 2 0+(4529027211/10000000000 : ℝ)*X 2 1+(521543733/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26568271638069940494338161/2875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (254259647/20000000000000 : ℝ)*(base19) + (818042471/100000000000000 : ℝ)*(base23) + (126448339/50000000000000 : ℝ)*(lower2) + (3195539/3125000000000 : ℝ)*(upper5) + (4223086847075637/100000000000000 : ℝ)*(major0) + (4223086847075637/100000000000000 : ℝ)*(major1) + (2111543423537819/50000000000000 : ℝ)*(major2) + (2831349535969233/50000000000000 : ℝ)*(sp0) + (707841920688039/12500000000000 : ℝ)*(sp1) + (2831371066167029/50000000000000 : ℝ)*(sp2) + (695854373331439/25000000000000 : ℝ)*(sp3) + (43878438063/100000000000000 : ℝ)*(sp4) + (6313573983/100000000000000 : ℝ)*(sp5) + (12942411047/100000000000000 : ℝ)*(sp7) + (1391715217868401/50000000000000 : ℝ)*(f.failure) + (566274295037653/10000000000000 : ℝ)*(f.sum) + (16277417173919/6624000000000000000000000000 : ℝ)*base66 + (1211774263734073709/103500000000000000000000000000000 : ℝ)*base68 + (1119486483849617909/103500000000000000000000000000000 : ℝ)*base69 + (795781021300573709/103500000000000000000000000000000 : ℝ)*base72 + (58220983687007/6624000000000000000000000000 : ℝ)*base74 + (1163936550914117909/103500000000000000000000000000000 : ℝ)*base75 + (12351589624988603/1437500000000000000000000000000 : ℝ)*base77 + (2935603401363603/1437500000000000000000000000000 : ℝ)*base79 + (8205561733693/1840000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (20388789/2500000000000000000000 : ℝ)*base89 + (20388789/2500000000000000000000 : ℝ)*base91 + (4611211/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1050938940511723382219/920000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100137041/5000000000000 : ℝ)*(base19) + (1241602649/100000000000000 : ℝ)*(base23) + (25945709/50000000000000 : ℝ)*(lower4) + (322180227/100000000000000 : ℝ)*(upper5) + (2126879340477657/50000000000000 : ℝ)*(major0) + (2126879340477657/50000000000000 : ℝ)*(major1) + (2126879340477657/50000000000000 : ℝ)*(major2) + (2641134053/100000000000000 : ℝ)*(sp0) + (3098628087/6250000000000 : ℝ)*(sp1) + (30602361521/100000000000000 : ℝ)*(sp2) + (2851934242796693/50000000000000 : ℝ)*(sp4) + (5703819545937227/100000000000000 : ℝ)*(sp5) + (5703839282763269/100000000000000 : ℝ)*(sp6) + (1401823098552843/50000000000000 : ℝ)*(sp7) + (1401823098552843/50000000000000 : ℝ)*(f.failure) + (5703871126727439/100000000000000 : ℝ)*(f.sum) + (18076007611861/2760000000000000000000000000 : ℝ)*base65 + (5189203448308017/718750000000000000000000000000 : ℝ)*base68 + (1345432475316983/718750000000000000000000000000 : ℝ)*base69 + (7487263110973233/718750000000000000000000000000 : ℝ)*base71 + (5229387256619/2760000000000000000000000000 : ℝ)*base74 + (7188941915558017/718750000000000000000000000000 : ℝ)*base76 + (2957930064004483/718750000000000000000000000000 : ℝ)*base77 + (5276908638901767/718750000000000000000000000000 : ℝ)*base80 + (2104476921541/2760000000000000000000000000 : ℝ)*base81 + (689673/2500000000000000000000 : ℝ)*base90 + (689673/2500000000000000000000 : ℝ)*base92 + (689673/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1257_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2023/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (239/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10949/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1257_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1257_s4_0 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056277121/5000000000 : ℝ)*x 0 + (5396893573/10000000000 : ℝ)*x 1 + (1315444607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056277121/5000000000 : ℝ)^4225 ≤ (6423679867399/50000000000000 : ℝ)^3201 := by
    have hnat : (1056277121 : ℕ)^4225*50000000000000^3201 ≤ 6423679867399^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056277121 5000000000 6423679867399 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396893573/10000000000 : ℝ)^4225 ≤ (22152700127019/50000000000000 : ℝ)^3201 := by
    have hnat : (5396893573 : ℕ)^4225*50000000000000^3201 ≤ 22152700127019^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396893573 10000000000 22152700127019 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315444607/2500000000 : ℝ)^4225 ≤ (10711809999397/25000000000000 : ℝ)^3201 := by
    have hnat : (1315444607 : ℕ)^4225*25000000000000^3201 ≤ 10711809999397^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315444607 2500000000 10711809999397 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056277121/5000000000 : ℝ), (5396893573/10000000000 : ℝ), (1315444607/2500000000 : ℝ)] ![(6423679867399/50000000000000 : ℝ), (22152700127019/50000000000000 : ℝ), (10711809999397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056277121/5000000000 : ℝ)|^4225 ≤ (6423679867399/50000000000000 : ℝ)^3201
        have hw : |(-1056277121/5000000000 : ℝ)|=(1056277121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396893573/10000000000 : ℝ)|^4225 ≤ (22152700127019/50000000000000 : ℝ)^3201
        have hw : |(5396893573/10000000000 : ℝ)|=(5396893573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315444607/2500000000 : ℝ)|^4225 ≤ (10711809999397/25000000000000 : ℝ)^3201
        have hw : |(1315444607/2500000000 : ℝ)|=(1315444607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s4_1 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345742013/10000000000 : ℝ)*x 0 + (-2181145973/10000000000 : ℝ)*x 1 + (2630889231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345742013/10000000000 : ℝ)^4225 ≤ (43751983350391/100000000000000 : ℝ)^3201 := by
    have hnat : (5345742013 : ℕ)^4225*100000000000000^3201 ≤ 43751983350391^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345742013 10000000000 43751983350391 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181145973/10000000000 : ℝ)^4225 ≤ (536031050921/4000000000000 : ℝ)^3201 := by
    have hnat : (2181145973 : ℕ)^4225*4000000000000^3201 ≤ 536031050921^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181145973 10000000000 536031050921 4000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630889231/5000000000 : ℝ)^4225 ≤ (42847240363023/100000000000000 : ℝ)^3201 := by
    have hnat : (2630889231 : ℕ)^4225*100000000000000^3201 ≤ 42847240363023^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630889231 5000000000 42847240363023 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345742013/10000000000 : ℝ), (-2181145973/10000000000 : ℝ), (2630889231/5000000000 : ℝ)] ![(43751983350391/100000000000000 : ℝ), (536031050921/4000000000000 : ℝ), (42847240363023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345742013/10000000000 : ℝ)|^4225 ≤ (43751983350391/100000000000000 : ℝ)^3201
        have hw : |(5345742013/10000000000 : ℝ)|=(5345742013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2181145973/10000000000 : ℝ)|^4225 ≤ (536031050921/4000000000000 : ℝ)^3201
        have hw : |(-2181145973/10000000000 : ℝ)|=(2181145973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630889231/5000000000 : ℝ)|^4225 ≤ (42847240363023/100000000000000 : ℝ)^3201
        have hw : |(2630889231/5000000000 : ℝ)|=(2630889231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s4_2 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345742129/10000000000 : ℝ)*x 0 + (2630889187/5000000000 : ℝ)*x 1 + (-436229187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345742129/10000000000 : ℝ)^4225 ≤ (43751984603499/100000000000000 : ℝ)^3201 := by
    have hnat : (5345742129 : ℕ)^4225*100000000000000^3201 ≤ 43751984603499^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345742129 10000000000 43751984603499 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630889187/5000000000 : ℝ)^4225 ≤ (42847239417191/100000000000000 : ℝ)^3201 := by
    have hnat : (2630889187 : ℕ)^4225*100000000000000^3201 ≤ 42847239417191^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630889187 5000000000 42847239417191 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436229187/2000000000 : ℝ)^4225 ≤ (13400775964869/100000000000000 : ℝ)^3201 := by
    have hnat : (436229187 : ℕ)^4225*100000000000000^3201 ≤ 13400775964869^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436229187 2000000000 13400775964869 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345742129/10000000000 : ℝ), (2630889187/5000000000 : ℝ), (-436229187/2000000000 : ℝ)] ![(43751984603499/100000000000000 : ℝ), (42847239417191/100000000000000 : ℝ), (13400775964869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345742129/10000000000 : ℝ)|^4225 ≤ (43751984603499/100000000000000 : ℝ)^3201
        have hw : |(5345742129/10000000000 : ℝ)|=(5345742129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630889187/5000000000 : ℝ)|^4225 ≤ (42847239417191/100000000000000 : ℝ)^3201
        have hw : |(2630889187/5000000000 : ℝ)|=(2630889187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-436229187/2000000000 : ℝ)|^4225 ≤ (13400775964869/100000000000000 : ℝ)^3201
        have hw : |(-436229187/2000000000 : ℝ)|=(436229187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s4_3 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4348413389/10000000000 : ℝ)*x 0 + (2106537531/5000000000 : ℝ)*x 1 + (4487959721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348413389/10000000000 : ℝ)^4225 ≤ (33314465030269/100000000000000 : ℝ)^3201 := by
    have hnat : (4348413389 : ℕ)^4225*100000000000000^3201 ≤ 33314465030269^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348413389 10000000000 33314465030269 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106537531/5000000000 : ℝ)^4225 ≤ (15976383336809/50000000000000 : ℝ)^3201 := by
    have hnat : (2106537531 : ℕ)^4225*50000000000000^3201 ≤ 15976383336809^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106537531 5000000000 15976383336809 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487959721/10000000000 : ℝ)^4225 ≤ (542699504343/1562500000000 : ℝ)^3201 := by
    have hnat : (4487959721 : ℕ)^4225*1562500000000^3201 ≤ 542699504343^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487959721 10000000000 542699504343 1562500000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348413389/10000000000 : ℝ), (2106537531/5000000000 : ℝ), (4487959721/10000000000 : ℝ)] ![(33314465030269/100000000000000 : ℝ), (15976383336809/50000000000000 : ℝ), (542699504343/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348413389/10000000000 : ℝ)|^4225 ≤ (33314465030269/100000000000000 : ℝ)^3201
        have hw : |(4348413389/10000000000 : ℝ)|=(4348413389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2106537531/5000000000 : ℝ)|^4225 ≤ (15976383336809/50000000000000 : ℝ)^3201
        have hw : |(2106537531/5000000000 : ℝ)|=(2106537531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487959721/10000000000 : ℝ)|^4225 ≤ (542699504343/1562500000000 : ℝ)^3201
        have hw : |(4487959721/10000000000 : ℝ)|=(4487959721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s4_4 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-52814001/250000000 : ℝ)*x 0 + (2631075663/5000000000 : ℝ)*x 1 + (674564923/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52814001/250000000 : ℝ)^4225 ≤ (12847406274699/100000000000000 : ℝ)^3201 := by
    have hnat : (52814001 : ℕ)^4225*100000000000000^3201 ≤ 12847406274699^3201*250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52814001 250000000 12847406274699 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631075663/5000000000 : ℝ)^4225 ≤ (2142562399233/5000000000000 : ℝ)^3201 := by
    have hnat : (2631075663 : ℕ)^4225*5000000000000^3201 ≤ 2142562399233^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631075663 5000000000 2142562399233 5000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674564923/1250000000 : ℝ)^4225 ≤ (11075336432103/25000000000000 : ℝ)^3201 := by
    have hnat : (674564923 : ℕ)^4225*25000000000000^3201 ≤ 11075336432103^3201*1250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674564923 1250000000 11075336432103 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52814001/250000000 : ℝ), (2631075663/5000000000 : ℝ), (674564923/1250000000 : ℝ)] ![(12847406274699/100000000000000 : ℝ), (2142562399233/5000000000000 : ℝ), (11075336432103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52814001/250000000 : ℝ)|^4225 ≤ (12847406274699/100000000000000 : ℝ)^3201
        have hw : |(-52814001/250000000 : ℝ)|=(52814001/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631075663/5000000000 : ℝ)|^4225 ≤ (2142562399233/5000000000000 : ℝ)^3201
        have hw : |(2631075663/5000000000 : ℝ)|=(2631075663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674564923/1250000000 : ℝ)|^4225 ≤ (11075336432103/25000000000000 : ℝ)^3201
        have hw : |(674564923/1250000000 : ℝ)|=(674564923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s4_5 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311233893/10000000000 : ℝ)*x 0 + (-2046404929/10000000000 : ℝ)*x 1 + (5396519359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311233893/10000000000 : ℝ)^4225 ≤ (4337958925959/10000000000000 : ℝ)^3201 := by
    have hnat : (5311233893 : ℕ)^4225*10000000000000^3201 ≤ 4337958925959^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311233893 10000000000 4337958925959 10000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2046404929/10000000000 : ℝ)^4225 ≤ (12319065260733/100000000000000 : ℝ)^3201 := by
    have hnat : (2046404929 : ℕ)^4225*100000000000000^3201 ≤ 12319065260733^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046404929 10000000000 12319065260733 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396519359/10000000000 : ℝ)^4225 ≤ (44301345457527/100000000000000 : ℝ)^3201 := by
    have hnat : (5396519359 : ℕ)^4225*100000000000000^3201 ≤ 44301345457527^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396519359 10000000000 44301345457527 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311233893/10000000000 : ℝ), (-2046404929/10000000000 : ℝ), (5396519359/10000000000 : ℝ)] ![(4337958925959/10000000000000 : ℝ), (12319065260733/100000000000000 : ℝ), (44301345457527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311233893/10000000000 : ℝ)|^4225 ≤ (4337958925959/10000000000000 : ℝ)^3201
        have hw : |(5311233893/10000000000 : ℝ)|=(5311233893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2046404929/10000000000 : ℝ)|^4225 ≤ (12319065260733/100000000000000 : ℝ)^3201
        have hw : |(-2046404929/10000000000 : ℝ)|=(2046404929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396519359/10000000000 : ℝ)|^4225 ≤ (44301345457527/100000000000000 : ℝ)^3201
        have hw : |(5396519359/10000000000 : ℝ)|=(5396519359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s4_6 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663904211/1250000000 : ℝ)*x 0 + (5396519537/10000000000 : ℝ)*x 1 + (-1023202483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663904211/1250000000 : ℝ)^4225 ≤ (10844896762407/25000000000000 : ℝ)^3201 := by
    have hnat : (663904211 : ℕ)^4225*25000000000000^3201 ≤ 10844896762407^3201*1250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663904211 1250000000 10844896762407 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396519537/10000000000 : ℝ)^4225 ≤ (1772053895449/4000000000000 : ℝ)^3201 := by
    have hnat : (5396519537 : ℕ)^4225*4000000000000^3201 ≤ 1772053895449^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396519537 10000000000 1772053895449 4000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023202483/5000000000 : ℝ)^4225 ≤ (76994159717/625000000000 : ℝ)^3201 := by
    have hnat : (1023202483 : ℕ)^4225*625000000000^3201 ≤ 76994159717^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023202483 5000000000 76994159717 625000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663904211/1250000000 : ℝ), (5396519537/10000000000 : ℝ), (-1023202483/5000000000 : ℝ)] ![(10844896762407/25000000000000 : ℝ), (1772053895449/4000000000000 : ℝ), (76994159717/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663904211/1250000000 : ℝ)|^4225 ≤ (10844896762407/25000000000000 : ℝ)^3201
        have hw : |(663904211/1250000000 : ℝ)|=(663904211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396519537/10000000000 : ℝ)|^4225 ≤ (1772053895449/4000000000000 : ℝ)^3201
        have hw : |(5396519537/10000000000 : ℝ)|=(5396519537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1023202483/5000000000 : ℝ)|^4225 ≤ (76994159717/625000000000 : ℝ)^3201
        have hw : |(-1023202483/5000000000 : ℝ)|=(1023202483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s4_7 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (869685097/2000000000 : ℝ)*x 0 + (17528131/39062500 : ℝ)*x 1 + (526729559/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869685097/2000000000 : ℝ)^4225 ≤ (6662917469353/20000000000000 : ℝ)^3201 := by
    have hnat : (869685097 : ℕ)^4225*20000000000000^3201 ≤ 6662917469353^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869685097 2000000000 6662917469353 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17528131/39062500 : ℝ)^4225 ≤ (8681255937553/25000000000000 : ℝ)^3201 := by
    have hnat : (17528131 : ℕ)^4225*25000000000000^3201 ≤ 8681255937553^3201*39062500^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17528131 39062500 8681255937553 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526729559/1250000000 : ℝ)^4225 ≤ (31960388892927/100000000000000 : ℝ)^3201 := by
    have hnat : (526729559 : ℕ)^4225*100000000000000^3201 ≤ 31960388892927^3201*1250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526729559 1250000000 31960388892927 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869685097/2000000000 : ℝ), (17528131/39062500 : ℝ), (526729559/1250000000 : ℝ)] ![(6662917469353/20000000000000 : ℝ), (8681255937553/25000000000000 : ℝ), (31960388892927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869685097/2000000000 : ℝ)|^4225 ≤ (6662917469353/20000000000000 : ℝ)^3201
        have hw : |(869685097/2000000000 : ℝ)|=(869685097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17528131/39062500 : ℝ)|^4225 ≤ (8681255937553/25000000000000 : ℝ)^3201
        have hw : |(17528131/39062500 : ℝ)|=(17528131/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526729559/1250000000 : ℝ)|^4225 ≤ (31960388892927/100000000000000 : ℝ)^3201
        have hw : |(526729559/1250000000 : ℝ)|=(526729559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1257_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10949/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (711/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14687/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10949/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14687/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10949/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14687/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10949/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14687/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10949/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14687/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10949/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14687/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10949/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10949/100000 : ℝ) ^ (8449/2048 : ℝ) ≤ (10888061734093237/100000000000000000000 : ℝ) := by
    have hpowers : (10949/100000 : ℝ)^8449 ≤ (10888061734093237/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10949 : ℕ)^8449*100000000000000000000^2048 ≤ 10888061734093237^2048*100000^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10949 100000 10888061734093237 100000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10949/100000 : ℝ)) (X := (10888061734093237/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14687/100000 : ℝ) ^ (8449/2048 : ℝ) ≤ (36575666213157507/100000000000000000000 : ℝ) := by
    have hpowers : (14687/100000 : ℝ)^8449 ≤ (36575666213157507/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14687 : ℕ)^8449*100000000000000000000^2048 ≤ 36575666213157507^2048*100000^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14687 100000 36575666213157507 100000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14687/100000 : ℝ)) (X := (36575666213157507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010888061734093237/50000000000000000000 : ℝ) ≤ (2000105560001311/2000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (50010888061734093237/50000000000000000000 : ℝ)^2048 ≤ (2000105560001311/2000000000000000 : ℝ)^8449 := by
      have hnat : (50010888061734093237 : ℕ)^2048*2000000000000000^8449 ≤ 2000105560001311^8449*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010888061734093237 50000000000000000000 2000105560001311 2000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000105560001311/2000000000000000 : ℝ)) (X := (50010888061734093237/50000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505932965993406343/12500000000000000000 : ℝ) ≤ (200023005856959/200000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (12505932965993406343/12500000000000000000 : ℝ)^2048 ≤ (200023005856959/200000000000000 : ℝ)^8449 := by
      have hnat : (12505932965993406343 : ℕ)^2048*200000000000000^8449 ≤ 200023005856959^8449*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505932965993406343 12500000000000000000 200023005856959 200000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200023005856959/200000000000000 : ℝ)) (X := (12505932965993406343/12500000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036575666213157507/50000000000000000000 : ℝ) ≤ (2000354557137869/2000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (50036575666213157507/50000000000000000000 : ℝ)^2048 ≤ (2000354557137869/2000000000000000 : ℝ)^8449 := by
      have hnat : (50036575666213157507 : ℕ)^2048*2000000000000000^8449 ≤ 2000354557137869^8449*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036575666213157507 50000000000000000000 2000354557137869 2000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000354557137869/2000000000000000 : ℝ)) (X := (50036575666213157507/50000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10888061734093237/100000000000000000000 : ℝ) ≤ ((116776067400573859/116812500000000000 : ℝ)+2*(124498568279/74760000000000 : ℝ)*(10949/100000 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (116776067400573859/116812500000000000 : ℝ)+2*(124498568279/74760000000000 : ℝ)*(10949/100000 : ℝ)=(2000105560001311/2000000000000000 : ℝ) by norm_num, show 1+2*(10888061734093237/100000000000000000000 : ℝ)=(50010888061734093237/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36575666213157507/100000000000000000000 : ℝ)+(10888061734093237/100000000000000000000 : ℝ) ≤ ((116776067400573859/116812500000000000 : ℝ)+(124498568279/74760000000000 : ℝ)*((14687/100000 : ℝ)+(10949/100000 : ℝ)))^(8449/2048 : ℝ) := by
    rw [show (116776067400573859/116812500000000000 : ℝ)+(124498568279/74760000000000 : ℝ)*((14687/100000 : ℝ)+(10949/100000 : ℝ))=(200023005856959/200000000000000 : ℝ) by norm_num, show 1+(36575666213157507/100000000000000000000 : ℝ)+(10888061734093237/100000000000000000000 : ℝ)=(12505932965993406343/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36575666213157507/100000000000000000000 : ℝ) ≤ ((116776067400573859/116812500000000000 : ℝ)+2*(124498568279/74760000000000 : ℝ)*(14687/100000 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (116776067400573859/116812500000000000 : ℝ)+2*(124498568279/74760000000000 : ℝ)*(14687/100000 : ℝ)=(2000354557137869/2000000000000000 : ℝ) by norm_num, show 1+2*(36575666213157507/100000000000000000000 : ℝ)=(50036575666213157507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (116776067400573859/116812500000000000 : ℝ)*(X 1 0+X 2 0)+(124498568279/74760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (10949/100000 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (116776067400573859/116812500000000000 : ℝ)) (alpha := (124498568279/74760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (116776067400573859/116812500000000000 : ℝ)*(X 0 1+X 2 1)+(124498568279/74760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (10949/100000 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (116776067400573859/116812500000000000 : ℝ)) (alpha := (124498568279/74760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (116776067400573859/116812500000000000 : ℝ)*(X 0 2+X 1 2)+(124498568279/74760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (10949/100000 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (116776067400573859/116812500000000000 : ℝ)) (alpha := (124498568279/74760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056277121/5000000000 : ℝ)*X 0 0+(5396893573/10000000000 : ℝ)*X 0 1+(1315444607/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345742013/10000000000 : ℝ)*X 1 0+(-2181145973/10000000000 : ℝ)*X 1 1+(2630889231/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345742129/10000000000 : ℝ)*X 2 0+(2630889187/5000000000 : ℝ)*X 2 1+(-436229187/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348413389/10000000000 : ℝ)*X 0 0+(2106537531/5000000000 : ℝ)*X 0 1+(4487959721/10000000000 : ℝ)*X 0 2+(4348413389/10000000000 : ℝ)*X 1 0+(2106537531/5000000000 : ℝ)*X 1 1+(4487959721/10000000000 : ℝ)*X 1 2+(4348413389/10000000000 : ℝ)*X 2 0+(2106537531/5000000000 : ℝ)*X 2 1+(4487959721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-52814001/250000000 : ℝ)*X 0 0+(2631075663/5000000000 : ℝ)*X 0 1+(674564923/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311233893/10000000000 : ℝ)*X 1 0+(-2046404929/10000000000 : ℝ)*X 1 1+(5396519359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663904211/1250000000 : ℝ)*X 2 0+(5396519537/10000000000 : ℝ)*X 2 1+(-1023202483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((869685097/2000000000 : ℝ)*X 0 0+(17528131/39062500 : ℝ)*X 0 1+(526729559/1250000000 : ℝ)*X 0 2+(869685097/2000000000 : ℝ)*X 1 0+(17528131/39062500 : ℝ)*X 1 1+(526729559/1250000000 : ℝ)*X 1 2+(869685097/2000000000 : ℝ)*X 2 0+(17528131/39062500 : ℝ)*X 2 1+(526729559/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25405385342831570684826913/3893750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64146177/4000000000000 : ℝ)*(base19) + (15850087/1000000000000 : ℝ)*(base23) + (12543367/5000000000000 : ℝ)*(upper3) + (19164219/20000000000000 : ℝ)*(upper4) + (13054003/6250000000000 : ℝ)*(upper5) + (5519549377010241/100000000000000 : ℝ)*(major0) + (5519549377010241/100000000000000 : ℝ)*(major1) + (2759774688505121/50000000000000 : ℝ)*(major2) + (7401131879303593/100000000000000 : ℝ)*(sp0) + (1850292479477963/25000000000000 : ℝ)*(sp1) + (3700584968278789/50000000000000 : ℝ)*(sp2) + (363790697376253/10000000000000 : ℝ)*(sp3) + (7928452537/20000000000000 : ℝ)*(sp4) + (20041203081/100000000000000 : ℝ)*(sp7) + (909481753741403/25000000000000 : ℝ)*(f.failure) + (3700585760783139/50000000000000 : ℝ)*(f.sum) + (1537013029567/7476000000000000000000000000 : ℝ)*base66 + (14048814614307107/1460156250000000000000000000000 : ℝ)*base68 + (204391104167875369/23362500000000000000000000000000 : ℝ)*base70 + (2269681310985509/730078125000000000000000000000 : ℝ)*base71 + (12885975246523/7476000000000000000000000000 : ℝ)*base74 + (21396856896874631/23362500000000000000000000000000 : ℝ)*base75 + (3034000747003529/7787500000000000000000000000000 : ℝ)*base78 + (150094244353416029/7787500000000000000000000000000 : ℝ)*base80 + (1597858500859/1246000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (17608167/1250000000000000000000 : ℝ)*base89 + (17608167/1250000000000000000000 : ℝ)*base91 + (5108167/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20239833914744899146891/2781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (57264309/5000000000000 : ℝ)*(base19) + (897706481/100000000000000 : ℝ)*(base23) + (78019887/50000000000000 : ℝ)*(upper3) + (1853403/10000000000000 : ℝ)*(lower4) + (30235327/50000000000000 : ℝ)*(upper5) + (111003496284537/2000000000000 : ℝ)*(major0) + (111003496284537/2000000000000 : ℝ)*(major1) + (111003496284537/2000000000000 : ℝ)*(major2) + (2616762359/10000000000000 : ℝ)*(sp1) + (6725600431/25000000000000 : ℝ)*(sp2) + (3721118594758979/50000000000000 : ℝ)*(sp4) + (7442209876608187/100000000000000 : ℝ)*(sp5) + (7442209389409753/100000000000000 : ℝ)*(sp6) + (1829056098180471/50000000000000 : ℝ)*(sp7) + (1829056098180471/50000000000000 : ℝ)*(f.failure) + (3721118594758979/50000000000000 : ℝ)*(f.sum) + (125586597/39872000000000000000000 : ℝ)*base66 + (2894821351203853/155750000000000000000000000000 : ℝ)*base68 + (1724617910440853/155750000000000000000000000000 : ℝ)*base70 + (1039909921642103/155750000000000000000000000000 : ℝ)*base72 + (653758393903/155750000000000000000000000 : ℝ)*base74 + (2974575960426603/155750000000000000000000000000 : ℝ)*base76 + (1309329511086353/155750000000000000000000000000 : ℝ)*base78 + (3981309806320603/155750000000000000000000000000 : ℝ)*base80 + (1046772797347/623000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (16640019/2500000000000000000000 : ℝ)*base89 + (16640019/2500000000000000000000 : ℝ)*base91 + (16640019/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1257_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10949/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1257_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1257_s5_0 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2112979109/10000000000 : ℝ)*x 0 + (2696025293/5000000000 : ℝ)*x 1 + (5266342213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112979109/10000000000 : ℝ)^4225 ≤ (12850770203161/100000000000000 : ℝ)^3201 := by
    have hnat : (2112979109 : ℕ)^4225*100000000000000^3201 ≤ 12850770203161^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112979109 10000000000 12850770203161 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696025293/5000000000 : ℝ)^4225 ≤ (44252931010869/100000000000000 : ℝ)^3201 := by
    have hnat : (2696025293 : ℕ)^4225*100000000000000^3201 ≤ 44252931010869^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696025293 5000000000 44252931010869 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266342213/10000000000 : ℝ)^4225 ≤ (42896298777857/100000000000000 : ℝ)^3201 := by
    have hnat : (5266342213 : ℕ)^4225*100000000000000^3201 ≤ 42896298777857^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266342213 10000000000 42896298777857 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2112979109/10000000000 : ℝ), (2696025293/5000000000 : ℝ), (5266342213/10000000000 : ℝ)] ![(12850770203161/100000000000000 : ℝ), (44252931010869/100000000000000 : ℝ), (42896298777857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2112979109/10000000000 : ℝ)|^4225 ≤ (12850770203161/100000000000000 : ℝ)^3201
        have hw : |(-2112979109/10000000000 : ℝ)|=(2112979109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696025293/5000000000 : ℝ)|^4225 ≤ (44252931010869/100000000000000 : ℝ)^3201
        have hw : |(2696025293/5000000000 : ℝ)|=(2696025293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266342213/10000000000 : ℝ)|^4225 ≤ (42896298777857/100000000000000 : ℝ)^3201
        have hw : |(5266342213/10000000000 : ℝ)|=(5266342213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s5_1 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344515557/10000000000 : ℝ)*x 0 + (-544182163/2500000000 : ℝ)*x 1 + (5266342223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344515557/10000000000 : ℝ)^4225 ≤ (21869367423483/50000000000000 : ℝ)^3201 := by
    have hnat : (5344515557 : ℕ)^4225*50000000000000^3201 ≤ 21869367423483^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344515557 10000000000 21869367423483 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544182163/2500000000 : ℝ)^4225 ≤ (13364966262123/100000000000000 : ℝ)^3201 := by
    have hnat : (544182163 : ℕ)^4225*100000000000000^3201 ≤ 13364966262123^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544182163 2500000000 13364966262123 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266342223/10000000000 : ℝ)^4225 ≤ (5362037360671/12500000000000 : ℝ)^3201 := by
    have hnat : (5266342223 : ℕ)^4225*12500000000000^3201 ≤ 5362037360671^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266342223 10000000000 5362037360671 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344515557/10000000000 : ℝ), (-544182163/2500000000 : ℝ), (5266342223/10000000000 : ℝ)] ![(21869367423483/50000000000000 : ℝ), (13364966262123/100000000000000 : ℝ), (5362037360671/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344515557/10000000000 : ℝ)|^4225 ≤ (21869367423483/50000000000000 : ℝ)^3201
        have hw : |(5344515557/10000000000 : ℝ)|=(5344515557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544182163/2500000000 : ℝ)|^4225 ≤ (13364966262123/100000000000000 : ℝ)^3201
        have hw : |(-544182163/2500000000 : ℝ)|=(544182163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266342223/10000000000 : ℝ)|^4225 ≤ (5362037360671/12500000000000 : ℝ)^3201
        have hw : |(5266342223/10000000000 : ℝ)|=(5266342223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s5_2 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068903117/2000000000 : ℝ)*x 0 + (210653689/400000000 : ℝ)*x 1 + (-2176728611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068903117/2000000000 : ℝ)^4225 ≤ (21869367574709/50000000000000 : ℝ)^3201 := by
    have hnat : (1068903117 : ℕ)^4225*50000000000000^3201 ≤ 21869367574709^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068903117 2000000000 21869367574709 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210653689/400000000 : ℝ)^4225 ≤ (4289629890687/10000000000000 : ℝ)^3201 := by
    have hnat : (210653689 : ℕ)^4225*10000000000000^3201 ≤ 4289629890687^3201*400000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210653689 400000000 4289629890687 10000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2176728611/10000000000 : ℝ)^4225 ≤ (2672993185971/20000000000000 : ℝ)^3201 := by
    have hnat : (2176728611 : ℕ)^4225*20000000000000^3201 ≤ 2672993185971^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176728611 10000000000 2672993185971 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068903117/2000000000 : ℝ), (210653689/400000000 : ℝ), (-2176728611/10000000000 : ℝ)] ![(21869367574709/50000000000000 : ℝ), (4289629890687/10000000000000 : ℝ), (2672993185971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068903117/2000000000 : ℝ)|^4225 ≤ (21869367574709/50000000000000 : ℝ)^3201
        have hw : |(1068903117/2000000000 : ℝ)|=(1068903117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210653689/400000000 : ℝ)|^4225 ≤ (4289629890687/10000000000000 : ℝ)^3201
        have hw : |(210653689/400000000 : ℝ)|=(210653689/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2176728611/10000000000 : ℝ)|^4225 ≤ (2672993185971/20000000000000 : ℝ)^3201
        have hw : |(-2176728611/10000000000 : ℝ)|=(2176728611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s5_3 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4348663899/10000000000 : ℝ)*x 0 + (1055653013/2500000000 : ℝ)*x 1 + (895671793/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348663899/10000000000 : ℝ)^4225 ≤ (16658499122857/50000000000000 : ℝ)^3201 := by
    have hnat : (4348663899 : ℕ)^4225*50000000000000^3201 ≤ 16658499122857^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348663899 10000000000 16658499122857 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055653013/2500000000 : ℝ)^4225 ≤ (16024135030429/50000000000000 : ℝ)^3201 := by
    have hnat : (1055653013 : ℕ)^4225*50000000000000^3201 ≤ 16024135030429^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055653013 2500000000 16024135030429 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895671793/2000000000 : ℝ)^4225 ≤ (2164670730167/6250000000000 : ℝ)^3201 := by
    have hnat : (895671793 : ℕ)^4225*6250000000000^3201 ≤ 2164670730167^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895671793 2000000000 2164670730167 6250000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348663899/10000000000 : ℝ), (1055653013/2500000000 : ℝ), (895671793/2000000000 : ℝ)] ![(16658499122857/50000000000000 : ℝ), (16024135030429/50000000000000 : ℝ), (2164670730167/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348663899/10000000000 : ℝ)|^4225 ≤ (16658499122857/50000000000000 : ℝ)^3201
        have hw : |(4348663899/10000000000 : ℝ)|=(4348663899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055653013/2500000000 : ℝ)|^4225 ≤ (16024135030429/50000000000000 : ℝ)^3201
        have hw : |(1055653013/2500000000 : ℝ)|=(1055653013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895671793/2000000000 : ℝ)|^4225 ≤ (2164670730167/6250000000000 : ℝ)^3201
        have hw : |(895671793/2000000000 : ℝ)|=(895671793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s5_4 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-528245993/2500000000 : ℝ)*x 0 + (2633332531/5000000000 : ℝ)*x 1 + (5391726553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528245993/2500000000 : ℝ)^4225 ≤ (12850809240429/100000000000000 : ℝ)^3201 := by
    have hnat : (528245993 : ℕ)^4225*100000000000000^3201 ≤ 12850809240429^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528245993 2500000000 12850809240429 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633332531/5000000000 : ℝ)^4225 ≤ (8579953956969/20000000000000 : ℝ)^3201 := by
    have hnat : (2633332531 : ℕ)^4225*20000000000000^3201 ≤ 8579953956969^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633332531 5000000000 8579953956969 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391726553/10000000000 : ℝ)^4225 ≤ (11062355238427/25000000000000 : ℝ)^3201 := by
    have hnat : (5391726553 : ℕ)^4225*25000000000000^3201 ≤ 11062355238427^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391726553 10000000000 11062355238427 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528245993/2500000000 : ℝ), (2633332531/5000000000 : ℝ), (5391726553/10000000000 : ℝ)] ![(12850809240429/100000000000000 : ℝ), (8579953956969/20000000000000 : ℝ), (11062355238427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528245993/2500000000 : ℝ)|^4225 ≤ (12850809240429/100000000000000 : ℝ)^3201
        have hw : |(-528245993/2500000000 : ℝ)|=(528245993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633332531/5000000000 : ℝ)|^4225 ≤ (8579953956969/20000000000000 : ℝ)^3201
        have hw : |(2633332531/5000000000 : ℝ)|=(2633332531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391726553/10000000000 : ℝ)|^4225 ≤ (11062355238427/25000000000000 : ℝ)^3201
        have hw : |(5391726553/10000000000 : ℝ)|=(5391726553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s5_5 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10624817/20000000 : ℝ)*x 0 + (-410268859/2000000000 : ℝ)*x 1 + (1078345311/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10624817/20000000 : ℝ)^4225 ≤ (5424031541149/12500000000000 : ℝ)^3201 := by
    have hnat : (10624817 : ℕ)^4225*12500000000000^3201 ≤ 5424031541149^3201*20000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10624817 20000000 5424031541149 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410268859/2000000000 : ℝ)^4225 ≤ (3089581669507/25000000000000 : ℝ)^3201 := by
    have hnat : (410268859 : ℕ)^4225*25000000000000^3201 ≤ 3089581669507^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410268859 2000000000 3089581669507 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078345311/2000000000 : ℝ)^4225 ≤ (11062355243843/25000000000000 : ℝ)^3201 := by
    have hnat : (1078345311 : ℕ)^4225*25000000000000^3201 ≤ 11062355243843^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078345311 2000000000 11062355243843 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10624817/20000000 : ℝ), (-410268859/2000000000 : ℝ), (1078345311/2000000000 : ℝ)] ![(5424031541149/12500000000000 : ℝ), (3089581669507/25000000000000 : ℝ), (11062355243843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10624817/20000000 : ℝ)|^4225 ≤ (5424031541149/12500000000000 : ℝ)^3201
        have hw : |(10624817/20000000 : ℝ)|=(10624817/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410268859/2000000000 : ℝ)|^4225 ≤ (3089581669507/25000000000000 : ℝ)^3201
        have hw : |(-410268859/2000000000 : ℝ)|=(410268859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078345311/2000000000 : ℝ)|^4225 ≤ (11062355243843/25000000000000 : ℝ)^3201
        have hw : |(1078345311/2000000000 : ℝ)|=(1078345311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s5_6 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656204247/5000000000 : ℝ)*x 0 + (33698291/62500000 : ℝ)*x 1 + (-256418037/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656204247/5000000000 : ℝ)^4225 ≤ (8678450452901/20000000000000 : ℝ)^3201 := by
    have hnat : (2656204247 : ℕ)^4225*20000000000000^3201 ≤ 8678450452901^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656204247 5000000000 8678450452901 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33698291/62500000 : ℝ)^4225 ≤ (22124710514767/50000000000000 : ℝ)^3201 := by
    have hnat : (33698291 : ℕ)^4225*50000000000000^3201 ≤ 22124710514767^3201*62500000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33698291 62500000 22124710514767 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256418037/1250000000 : ℝ)^4225 ≤ (12358326685979/100000000000000 : ℝ)^3201 := by
    have hnat : (256418037 : ℕ)^4225*100000000000000^3201 ≤ 12358326685979^3201*1250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256418037 1250000000 12358326685979 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656204247/5000000000 : ℝ), (33698291/62500000 : ℝ), (-256418037/1250000000 : ℝ)] ![(8678450452901/20000000000000 : ℝ), (22124710514767/50000000000000 : ℝ), (12358326685979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656204247/5000000000 : ℝ)|^4225 ≤ (8678450452901/20000000000000 : ℝ)^3201
        have hw : |(2656204247/5000000000 : ℝ)|=(2656204247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33698291/62500000 : ℝ)|^4225 ≤ (22124710514767/50000000000000 : ℝ)^3201
        have hw : |(33698291/62500000 : ℝ)|=(33698291/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256418037/1250000000 : ℝ)|^4225 ≤ (12358326685979/100000000000000 : ℝ)^3201
        have hw : |(-256418037/1250000000 : ℝ)|=(256418037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s5_7 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4348673853/10000000000 : ℝ)*x 0 + (4477702231/10000000000 : ℝ)*x 1 + (527908897/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348673853/10000000000 : ℝ)^4225 ≤ (8329274725961/25000000000000 : ℝ)^3201 := by
    have hnat : (4348673853 : ℕ)^4225*25000000000000^3201 ≤ 8329274725961^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348673853 10000000000 8329274725961 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477702231/10000000000 : ℝ)^4225 ≤ (1731401400131/5000000000000 : ℝ)^3201 := by
    have hnat : (4477702231 : ℕ)^4225*5000000000000^3201 ≤ 1731401400131^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477702231 10000000000 1731401400131 5000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527908897/1250000000 : ℝ)^4225 ≤ (6410974615573/20000000000000 : ℝ)^3201 := by
    have hnat : (527908897 : ℕ)^4225*20000000000000^3201 ≤ 6410974615573^3201*1250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527908897 1250000000 6410974615573 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348673853/10000000000 : ℝ), (4477702231/10000000000 : ℝ), (527908897/1250000000 : ℝ)] ![(8329274725961/25000000000000 : ℝ), (1731401400131/5000000000000 : ℝ), (6410974615573/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348673853/10000000000 : ℝ)|^4225 ≤ (8329274725961/25000000000000 : ℝ)^3201
        have hw : |(4348673853/10000000000 : ℝ)|=(4348673853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477702231/10000000000 : ℝ)|^4225 ≤ (1731401400131/5000000000000 : ℝ)^3201
        have hw : |(4477702231/10000000000 : ℝ)|=(4477702231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527908897/1250000000 : ℝ)|^4225 ≤ (6410974615573/20000000000000 : ℝ)^3201
        have hw : |(527908897/1250000000 : ℝ)|=(527908897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1257_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11473/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1767/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (711/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (711/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (711/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (711/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (711/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (711/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (711/6250 : ℝ) ^ (8449/2048 : ℝ) ≤ (6225383877019/48828125000000000 : ℝ) := by
    have hpowers : (711/6250 : ℝ)^8449 ≤ (6225383877019/48828125000000000 : ℝ)^2048 := by
      have hnat : (711 : ℕ)^8449*48828125000000000^2048 ≤ 6225383877019^2048*6250^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        711 6250 6225383877019 48828125000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (711/6250 : ℝ)) (X := (6225383877019/48828125000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (8449/2048 : ℝ) ≤ (32178346432577503/100000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^8449 ≤ (32178346432577503/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7119 : ℕ)^8449*100000000000000000000^2048 ≤ 32178346432577503^2048*50000^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 32178346432577503 100000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (32178346432577503/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (24420287883877019/24414062500000000 : ℝ) ≤ (2500154507224287/2500000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (24420287883877019/24414062500000000 : ℝ)^2048 ≤ (2500154507224287/2500000000000000 : ℝ)^8449 := by
      have hnat : (24420287883877019 : ℕ)^2048*2500000000000000^8449 ≤ 2500154507224287^8449*24414062500000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24420287883877019 24414062500000000 2500154507224287 2500000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500154507224287/2500000000000000 : ℝ)) (X := (24420287883877019/24414062500000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008985586522542483/20000000000000000000 : ℝ) ≤ (5000544423900481/5000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (20008985586522542483/20000000000000000000 : ℝ)^2048 ≤ (5000544423900481/5000000000000000 : ℝ)^8449 := by
      have hnat : (20008985586522542483 : ℕ)^2048*5000000000000000^8449 ≤ 5000544423900481^8449*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008985586522542483 20000000000000000000 5000544423900481 5000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000544423900481/5000000000000000 : ℝ)) (X := (20008985586522542483/20000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032178346432577503/50000000000000000000 : ℝ) ≤ (1250194958338097/1250000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (50032178346432577503/50000000000000000000 : ℝ)^2048 ≤ (1250194958338097/1250000000000000 : ℝ)^8449 := by
      have hnat : (50032178346432577503 : ℕ)^2048*1250000000000000^8449 ≤ 1250194958338097^8449*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032178346432577503 50000000000000000000 1250194958338097 1250000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250194958338097/1250000000000000 : ℝ)) (X := (50032178346432577503/50000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6225383877019/48828125000000000 : ℝ) ≤ ((397375787875056409/397500000000000000 : ℝ)+2*(235409451907/143100000000000 : ℝ)*(711/6250 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (397375787875056409/397500000000000000 : ℝ)+2*(235409451907/143100000000000 : ℝ)*(711/6250 : ℝ)=(2500154507224287/2500000000000000 : ℝ) by norm_num, show 1+2*(6225383877019/48828125000000000 : ℝ)=(24420287883877019/24414062500000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32178346432577503/100000000000000000000 : ℝ)+(6225383877019/48828125000000000 : ℝ) ≤ ((397375787875056409/397500000000000000 : ℝ)+(235409451907/143100000000000 : ℝ)*((7119/50000 : ℝ)+(711/6250 : ℝ)))^(8449/2048 : ℝ) := by
    rw [show (397375787875056409/397500000000000000 : ℝ)+(235409451907/143100000000000 : ℝ)*((7119/50000 : ℝ)+(711/6250 : ℝ))=(5000544423900481/5000000000000000 : ℝ) by norm_num, show 1+(32178346432577503/100000000000000000000 : ℝ)+(6225383877019/48828125000000000 : ℝ)=(20008985586522542483/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32178346432577503/100000000000000000000 : ℝ) ≤ ((397375787875056409/397500000000000000 : ℝ)+2*(235409451907/143100000000000 : ℝ)*(7119/50000 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (397375787875056409/397500000000000000 : ℝ)+2*(235409451907/143100000000000 : ℝ)*(7119/50000 : ℝ)=(1250194958338097/1250000000000000 : ℝ) by norm_num, show 1+2*(32178346432577503/100000000000000000000 : ℝ)=(50032178346432577503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (397375787875056409/397500000000000000 : ℝ)*(X 1 0+X 2 0)+(235409451907/143100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (711/6250 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (397375787875056409/397500000000000000 : ℝ)) (alpha := (235409451907/143100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (397375787875056409/397500000000000000 : ℝ)*(X 0 1+X 2 1)+(235409451907/143100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (711/6250 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (397375787875056409/397500000000000000 : ℝ)) (alpha := (235409451907/143100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (397375787875056409/397500000000000000 : ℝ)*(X 0 2+X 1 2)+(235409451907/143100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (711/6250 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (397375787875056409/397500000000000000 : ℝ)) (alpha := (235409451907/143100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2112979109/10000000000 : ℝ)*X 0 0+(2696025293/5000000000 : ℝ)*X 0 1+(5266342213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344515557/10000000000 : ℝ)*X 1 0+(-544182163/2500000000 : ℝ)*X 1 1+(5266342223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068903117/2000000000 : ℝ)*X 2 0+(210653689/400000000 : ℝ)*X 2 1+(-2176728611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348663899/10000000000 : ℝ)*X 0 0+(1055653013/2500000000 : ℝ)*X 0 1+(895671793/2000000000 : ℝ)*X 0 2+(4348663899/10000000000 : ℝ)*X 1 0+(1055653013/2500000000 : ℝ)*X 1 1+(895671793/2000000000 : ℝ)*X 1 2+(4348663899/10000000000 : ℝ)*X 2 0+(1055653013/2500000000 : ℝ)*X 2 1+(895671793/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528245993/2500000000 : ℝ)*X 0 0+(2633332531/5000000000 : ℝ)*X 0 1+(5391726553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10624817/20000000 : ℝ)*X 1 0+(-410268859/2000000000 : ℝ)*X 1 1+(1078345311/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656204247/5000000000 : ℝ)*X 2 0+(33698291/62500000 : ℝ)*X 2 1+(-256418037/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348673853/10000000000 : ℝ)*X 0 0+(4477702231/10000000000 : ℝ)*X 0 1+(527908897/1250000000 : ℝ)*X 0 2+(4348673853/10000000000 : ℝ)*X 1 0+(4477702231/10000000000 : ℝ)*X 1 1+(527908897/1250000000 : ℝ)*X 1 2+(4348673853/10000000000 : ℝ)*X 2 0+(4477702231/10000000000 : ℝ)*X 2 1+(527908897/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (580427635205511805109032681/59625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1833561927/100000000000000 : ℝ)*(base19) + (448866539/25000000000000 : ℝ)*(base23) + (10658603/25000000000000 : ℝ)*(lower2) + (94478097/50000000000000 : ℝ)*(upper3) + (10190041/5000000000000 : ℝ)*(upper5) + (1483149032228591/25000000000000 : ℝ)*(major0) + (1483149032228591/25000000000000 : ℝ)*(major1) + (1186519225782873/20000000000000 : ℝ)*(major2) + (7954971614233631/100000000000000 : ℝ)*(sp0) + (1988756141940187/25000000000000 : ℝ)*(sp1) + (7955024605856519/100000000000000 : ℝ)*(sp2) + (1955070163624191/50000000000000 : ℝ)*(sp3) + (10957417809/20000000000000 : ℝ)*(sp4) + (12602384909/50000000000000 : ℝ)*(sp7) + (19550827660091/500000000000 : ℝ)*(f.failure) + (318201056052907/4000000000000 : ℝ)*(f.sum) + (10982948588227/14310000000000000000000000000 : ℝ)*base66 + (193707177417074593/29812500000000000000000000000000 : ℝ)*base68 + (622807792232812487/71550000000000000000000000000000 : ℝ)*base70 + (467950868326050407/29812500000000000000000000000000 : ℝ)*base71 + (51315447086857/14310000000000000000000000000 : ℝ)*base74 + (170109905902612487/71550000000000000000000000000000 : ℝ)*base76 + (532208800781919971/89437500000000000000000000000000 : ℝ)*base77 + (281166699025044971/89437500000000000000000000000000 : ℝ)*base79 + (27487142981647/7155000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (108199/25000000000000000000 : ℝ)*base89 + (108199/25000000000000000000 : ℝ)*base91 + (141801/25000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45288379369681020398380819/19875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216207769/50000000000000 : ℝ)*(base19) + (453674951/100000000000000 : ℝ)*(base23) + (12390719/25000000000000 : ℝ)*(upper3) + (13759127/100000000000000 : ℝ)*(lower4) + (11683743/25000000000000 : ℝ)*(upper5) + (5963201853441501/100000000000000 : ℝ)*(major0) + (5963201853441501/100000000000000 : ℝ)*(major1) + (5963201853441501/100000000000000 : ℝ)*(major2) + (6033658237/50000000000000 : ℝ)*(sp1) + (2558748271/20000000000000 : ℝ)*(sp2) + (1599213182023849/20000000000000 : ℝ)*(sp4) + (7996053410387233/100000000000000 : ℝ)*(sp5) + (3998026331351469/50000000000000 : ℝ)*(sp6) + (1965168860404199/50000000000000 : ℝ)*(sp7) + (1965168860404199/50000000000000 : ℝ)*(f.failure) + (1599213182023849/20000000000000 : ℝ)*(f.sum) + (3036017693179/2385000000000000000000000000 : ℝ)*base65 + (182049493642614727/119250000000000000000000000000000 : ℝ)*base67 + (38723585846364727/119250000000000000000000000000000 : ℝ)*base69 + (190775029975614727/119250000000000000000000000000000 : ℝ)*base71 + (5486331658603/1192500000000000000000000000 : ℝ)*base74 + (317060058155364727/119250000000000000000000000000000 : ℝ)*base75 + (1899579051392364727/119250000000000000000000000000000 : ℝ)*base77 + (674011795316364727/119250000000000000000000000000000 : ℝ)*base79 + (1593593496553/1192500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (31732611/2500000000000000000000 : ℝ)*base89 + (31732611/2500000000000000000000 : ℝ)*base91 + (31732611/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1257_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1257_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1257_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2023/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (239/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1257_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1257_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1257_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2023/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (239/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1257_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
