-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1070_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:10:01.248666+00:00
-- url     : https://prove2.me/submissions/73f3d38b-2673-469f-9c20-d163909ae2a6

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
theorem support_rectangle_w1070_s0_0 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-239351169/1250000000 : ℝ)*x 0 + (6071121383/10000000000 : ℝ)*x 1 + (2385649649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239351169/1250000000 : ℝ)^8263 ≤ (11106256850219/100000000000000 : ℝ)^6215 := by
    have hnat : (239351169 : ℕ)^8263*100000000000000^6215 ≤ 11106256850219^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239351169 1250000000 11106256850219 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6071121383/10000000000 : ℝ)^8263 ≤ (51505135194817/100000000000000 : ℝ)^6215 := by
    have hnat : (6071121383 : ℕ)^8263*100000000000000^6215 ≤ 51505135194817^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6071121383 10000000000 51505135194817 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2385649649/5000000000 : ℝ)^8263 ≤ (934715198609/2500000000000 : ℝ)^6215 := by
    have hnat : (2385649649 : ℕ)^8263*2500000000000^6215 ≤ 934715198609^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385649649 5000000000 934715198609 2500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239351169/1250000000 : ℝ), (6071121383/10000000000 : ℝ), (2385649649/5000000000 : ℝ)] ![(11106256850219/100000000000000 : ℝ), (51505135194817/100000000000000 : ℝ), (934715198609/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239351169/1250000000 : ℝ)|^8263 ≤ (11106256850219/100000000000000 : ℝ)^6215
        have hw : |(-239351169/1250000000 : ℝ)|=(239351169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6071121383/10000000000 : ℝ)|^8263 ≤ (51505135194817/100000000000000 : ℝ)^6215
        have hw : |(6071121383/10000000000 : ℝ)|=(6071121383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2385649649/5000000000 : ℝ)|^8263 ≤ (934715198609/2500000000000 : ℝ)^6215
        have hw : |(2385649649/5000000000 : ℝ)|=(2385649649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s0_1 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (690105997/1250000000 : ℝ)*x 0 + (-16642967/62500000 : ℝ)*x 1 + (47712993/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (690105997/1250000000 : ℝ)^8263 ≤ (22696566457169/50000000000000 : ℝ)^6215 := by
    have hnat : (690105997 : ℕ)^8263*50000000000000^6215 ≤ 22696566457169^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690105997 1250000000 22696566457169 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16642967/62500000 : ℝ)^8263 ≤ (17218259111889/100000000000000 : ℝ)^6215 := by
    have hnat : (16642967 : ℕ)^8263*100000000000000^6215 ≤ 17218259111889^6215*62500000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16642967 62500000 17218259111889 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47712993/100000000 : ℝ)^8263 ≤ (9347151991299/25000000000000 : ℝ)^6215 := by
    have hnat : (47712993 : ℕ)^8263*25000000000000^6215 ≤ 9347151991299^6215*100000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47712993 100000000 9347151991299 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(690105997/1250000000 : ℝ), (-16642967/62500000 : ℝ), (47712993/100000000 : ℝ)] ![(22696566457169/50000000000000 : ℝ), (17218259111889/100000000000000 : ℝ), (9347151991299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(690105997/1250000000 : ℝ)|^8263 ≤ (22696566457169/50000000000000 : ℝ)^6215
        have hw : |(690105997/1250000000 : ℝ)|=(690105997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16642967/62500000 : ℝ)|^8263 ≤ (17218259111889/100000000000000 : ℝ)^6215
        have hw : |(-16642967/62500000 : ℝ)|=(16642967/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(47712993/100000000 : ℝ)|^8263 ≤ (9347151991299/25000000000000 : ℝ)^6215
        have hw : |(47712993/100000000 : ℝ)|=(47712993/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s0_2 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5520847991/10000000000 : ℝ)*x 0 + (477129929/1000000000 : ℝ)*x 1 + (-332859339/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520847991/10000000000 : ℝ)^8263 ≤ (45393133078311/100000000000000 : ℝ)^6215 := by
    have hnat : (5520847991 : ℕ)^8263*100000000000000^6215 ≤ 45393133078311^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520847991 10000000000 45393133078311 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (477129929/1000000000 : ℝ)^8263 ≤ (37388607861013/100000000000000 : ℝ)^6215 := by
    have hnat : (477129929 : ℕ)^8263*100000000000000^6215 ≤ 37388607861013^6215*1000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477129929 1000000000 37388607861013 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (332859339/1250000000 : ℝ)^8263 ≤ (3443651808623/20000000000000 : ℝ)^6215 := by
    have hnat : (332859339 : ℕ)^8263*20000000000000^6215 ≤ 3443651808623^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332859339 1250000000 3443651808623 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520847991/10000000000 : ℝ), (477129929/1000000000 : ℝ), (-332859339/1250000000 : ℝ)] ![(45393133078311/100000000000000 : ℝ), (37388607861013/100000000000000 : ℝ), (3443651808623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520847991/10000000000 : ℝ)|^8263 ≤ (45393133078311/100000000000000 : ℝ)^6215
        have hw : |(5520847991/10000000000 : ℝ)|=(5520847991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(477129929/1000000000 : ℝ)|^8263 ≤ (37388607861013/100000000000000 : ℝ)^6215
        have hw : |(477129929/1000000000 : ℝ)|=(477129929/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-332859339/1250000000 : ℝ)|^8263 ≤ (3443651808623/20000000000000 : ℝ)^6215
        have hw : |(-332859339/1250000000 : ℝ)|=(332859339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s0_3 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4206878563/10000000000 : ℝ)*x 0 + (62493069/200000000 : ℝ)*x 1 + (1418536701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206878563/10000000000 : ℝ)^8263 ≤ (15813036103281/50000000000000 : ℝ)^6215 := by
    have hnat : (4206878563 : ℕ)^8263*50000000000000^6215 ≤ 15813036103281^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206878563 10000000000 15813036103281 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62493069/200000000 : ℝ)^8263 ≤ (10648692131973/50000000000000 : ℝ)^6215 := by
    have hnat : (62493069 : ℕ)^8263*50000000000000^6215 ≤ 10648692131973^6215*200000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62493069 200000000 10648692131973 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1418536701/2500000000 : ℝ)^8263 ≤ (23538271760457/50000000000000 : ℝ)^6215 := by
    have hnat : (1418536701 : ℕ)^8263*50000000000000^6215 ≤ 23538271760457^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1418536701 2500000000 23538271760457 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206878563/10000000000 : ℝ), (62493069/200000000 : ℝ), (1418536701/2500000000 : ℝ)] ![(15813036103281/50000000000000 : ℝ), (10648692131973/50000000000000 : ℝ), (23538271760457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206878563/10000000000 : ℝ)|^8263 ≤ (15813036103281/50000000000000 : ℝ)^6215
        have hw : |(4206878563/10000000000 : ℝ)|=(4206878563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(62493069/200000000 : ℝ)|^8263 ≤ (10648692131973/50000000000000 : ℝ)^6215
        have hw : |(62493069/200000000 : ℝ)|=(62493069/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1418536701/2500000000 : ℝ)|^8263 ≤ (23538271760457/50000000000000 : ℝ)^6215
        have hw : |(1418536701/2500000000 : ℝ)|=(1418536701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s0_4 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1920170551/10000000000 : ℝ)*x 0 + (300303749/625000000 : ℝ)*x 1 + (6036386331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1920170551/10000000000 : ℝ)^8263 ≤ (2229523757941/20000000000000 : ℝ)^6215 := by
    have hnat : (1920170551 : ℕ)^8263*20000000000000^6215 ≤ 2229523757941^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920170551 10000000000 2229523757941 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300303749/625000000 : ℝ)^8263 ≤ (9434664936547/25000000000000 : ℝ)^6215 := by
    have hnat : (300303749 : ℕ)^8263*25000000000000^6215 ≤ 9434664936547^6215*625000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300303749 625000000 9434664936547 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6036386331/10000000000 : ℝ)^8263 ≤ (99831487201/195312500000 : ℝ)^6215 := by
    have hnat : (6036386331 : ℕ)^8263*195312500000^6215 ≤ 99831487201^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6036386331 10000000000 99831487201 195312500000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1920170551/10000000000 : ℝ), (300303749/625000000 : ℝ), (6036386331/10000000000 : ℝ)] ![(2229523757941/20000000000000 : ℝ), (9434664936547/25000000000000 : ℝ), (99831487201/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1920170551/10000000000 : ℝ)|^8263 ≤ (2229523757941/20000000000000 : ℝ)^6215
        have hw : |(-1920170551/10000000000 : ℝ)|=(1920170551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(300303749/625000000 : ℝ)|^8263 ≤ (9434664936547/25000000000000 : ℝ)^6215
        have hw : |(300303749/625000000 : ℝ)|=(300303749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6036386331/10000000000 : ℝ)|^8263 ≤ (99831487201/195312500000 : ℝ)^6215
        have hw : |(6036386331/10000000000 : ℝ)|=(6036386331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s0_5 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (258401687/500000000 : ℝ)*x 0 + (-698895691/5000000000 : ℝ)*x 1 + (1207276833/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258401687/500000000 : ℝ)^8263 ≤ (41577538567561/100000000000000 : ℝ)^6215 := by
    have hnat : (258401687 : ℕ)^8263*100000000000000^6215 ≤ 41577538567561^6215*500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258401687 500000000 41577538567561 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698895691/5000000000 : ℝ)^8263 ≤ (7308764349989/100000000000000 : ℝ)^6215 := by
    have hnat : (698895691 : ℕ)^8263*100000000000000^6215 ≤ 7308764349989^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698895691 5000000000 7308764349989 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207276833/2000000000 : ℝ)^8263 ≤ (25556848531159/50000000000000 : ℝ)^6215 := by
    have hnat : (1207276833 : ℕ)^8263*50000000000000^6215 ≤ 25556848531159^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207276833 2000000000 25556848531159 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258401687/500000000 : ℝ), (-698895691/5000000000 : ℝ), (1207276833/2000000000 : ℝ)] ![(41577538567561/100000000000000 : ℝ), (7308764349989/100000000000000 : ℝ), (25556848531159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258401687/500000000 : ℝ)|^8263 ≤ (41577538567561/100000000000000 : ℝ)^6215
        have hw : |(258401687/500000000 : ℝ)|=(258401687/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-698895691/5000000000 : ℝ)|^8263 ≤ (7308764349989/100000000000000 : ℝ)^6215
        have hw : |(-698895691/5000000000 : ℝ)|=(698895691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207276833/2000000000 : ℝ)|^8263 ≤ (25556848531159/50000000000000 : ℝ)^6215
        have hw : |(1207276833/2000000000 : ℝ)|=(1207276833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s0_6 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2584016867/5000000000 : ℝ)*x 0 + (6036385571/10000000000 : ℝ)*x 1 + (-349447279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584016867/5000000000 : ℝ)^8263 ≤ (5197192312923/12500000000000 : ℝ)^6215 := by
    have hnat : (2584016867 : ℕ)^8263*12500000000000^6215 ≤ 5197192312923^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584016867 5000000000 5197192312923 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6036385571/10000000000 : ℝ)^8263 ≤ (51113712890913/100000000000000 : ℝ)^6215 := by
    have hnat : (6036385571 : ℕ)^8263*100000000000000^6215 ≤ 51113712890913^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6036385571 10000000000 51113712890913 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349447279/2500000000 : ℝ)^8263 ≤ (365437429859/5000000000000 : ℝ)^6215 := by
    have hnat : (349447279 : ℕ)^8263*5000000000000^6215 ≤ 365437429859^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349447279 2500000000 365437429859 5000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584016867/5000000000 : ℝ), (6036385571/10000000000 : ℝ), (-349447279/2500000000 : ℝ)] ![(5197192312923/12500000000000 : ℝ), (51113712890913/100000000000000 : ℝ), (365437429859/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584016867/5000000000 : ℝ)|^8263 ≤ (5197192312923/12500000000000 : ℝ)^6215
        have hw : |(2584016867/5000000000 : ℝ)|=(2584016867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6036385571/10000000000 : ℝ)|^8263 ≤ (51113712890913/100000000000000 : ℝ)^6215
        have hw : |(6036385571/10000000000 : ℝ)|=(6036385571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-349447279/2500000000 : ℝ)|^8263 ≤ (365437429859/5000000000000 : ℝ)^6215
        have hw : |(-349447279/2500000000 : ℝ)|=(349447279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s0_7 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4217392753/10000000000 : ℝ)*x 0 + (5608317463/10000000000 : ℝ)*x 1 + (1596392743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4217392753/10000000000 : ℝ)^8263 ≤ (31731204569127/100000000000000 : ℝ)^6215 := by
    have hnat : (4217392753 : ℕ)^8263*100000000000000^6215 ≤ 31731204569127^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217392753 10000000000 31731204569127 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5608317463/10000000000 : ℝ)^8263 ≤ (4635179555411/10000000000000 : ℝ)^6215 := by
    have hnat : (5608317463 : ℕ)^8263*10000000000000^6215 ≤ 4635179555411^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608317463 10000000000 4635179555411 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1596392743/5000000000 : ℝ)^8263 ≤ (42806640341/195312500000 : ℝ)^6215 := by
    have hnat : (1596392743 : ℕ)^8263*195312500000^6215 ≤ 42806640341^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596392743 5000000000 42806640341 195312500000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4217392753/10000000000 : ℝ), (5608317463/10000000000 : ℝ), (1596392743/5000000000 : ℝ)] ![(31731204569127/100000000000000 : ℝ), (4635179555411/10000000000000 : ℝ), (42806640341/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4217392753/10000000000 : ℝ)|^8263 ≤ (31731204569127/100000000000000 : ℝ)^6215
        have hw : |(4217392753/10000000000 : ℝ)|=(4217392753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5608317463/10000000000 : ℝ)|^8263 ≤ (4635179555411/10000000000000 : ℝ)^6215
        have hw : |(5608317463/10000000000 : ℝ)|=(5608317463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1596392743/5000000000 : ℝ)|^8263 ≤ (42806640341/195312500000 : ℝ)^6215
        have hw : |(1596392743/5000000000 : ℝ)|=(1596392743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1070_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (113/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14047/50000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (4131/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4131 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4131*1^1024 ≤ 0^1024*1^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4131/1024 : ℝ) ≤ (2481067044738636563/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4131 ≤ (2481067044738636563/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4131*100000000000000000000^1024 ≤ 2481067044738636563^1024*5^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2481067044738636563 100000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2481067044738636563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4131 := by
      have hnat : (1 : ℕ)^1024*1^4131 ≤ 1^4131*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102481067044738636563/100000000000000000000 : ℝ) ≤ (2012187101262641/2000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (102481067044738636563/100000000000000000000 : ℝ)^1024 ≤ (2012187101262641/2000000000000000 : ℝ)^4131 := by
      have hnat : (102481067044738636563 : ℕ)^1024*2000000000000000^4131 ≤ 2012187101262641^4131*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102481067044738636563 100000000000000000000 2012187101262641 2000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2012187101262641/2000000000000000 : ℝ)) (X := (102481067044738636563/100000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52481067044738636563/50000000000000000000 : ℝ) ≤ (1012187101262641/1000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (52481067044738636563/50000000000000000000 : ℝ)^1024 ≤ (1012187101262641/1000000000000000 : ℝ)^4131 := by
      have hnat : (52481067044738636563 : ℕ)^1024*1000000000000000^4131 ≤ 1012187101262641^4131*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52481067044738636563 50000000000000000000 1012187101262641 1000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1012187101262641/1000000000000000 : ℝ)) (X := (52481067044738636563/50000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12187101262641/800000000000000 : ℝ)*(0 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12187101262641/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2481067044738636563/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12187101262641/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4131/1024 : ℝ) := by
    rw [show (1 : ℝ)+(12187101262641/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2012187101262641/2000000000000000 : ℝ) by norm_num, show 1+(2481067044738636563/100000000000000000000 : ℝ)+(0 : ℝ)=(102481067044738636563/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2481067044738636563/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12187101262641/800000000000000 : ℝ)*(2/5 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12187101262641/800000000000000 : ℝ)*(2/5 : ℝ)=(1012187101262641/1000000000000000 : ℝ) by norm_num, show 1+2*(2481067044738636563/100000000000000000000 : ℝ)=(52481067044738636563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12187101262641/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12187101262641/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12187101262641/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12187101262641/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12187101262641/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12187101262641/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-239351169/1250000000 : ℝ)*X 0 0+(6071121383/10000000000 : ℝ)*X 0 1+(2385649649/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((690105997/1250000000 : ℝ)*X 1 0+(-16642967/62500000 : ℝ)*X 1 1+(47712993/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5520847991/10000000000 : ℝ)*X 2 0+(477129929/1000000000 : ℝ)*X 2 1+(-332859339/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4206878563/10000000000 : ℝ)*X 0 0+(62493069/200000000 : ℝ)*X 0 1+(1418536701/2500000000 : ℝ)*X 0 2+(4206878563/10000000000 : ℝ)*X 1 0+(62493069/200000000 : ℝ)*X 1 1+(1418536701/2500000000 : ℝ)*X 1 2+(4206878563/10000000000 : ℝ)*X 2 0+(62493069/200000000 : ℝ)*X 2 1+(1418536701/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1920170551/10000000000 : ℝ)*X 0 0+(300303749/625000000 : ℝ)*X 0 1+(6036386331/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((258401687/500000000 : ℝ)*X 1 0+(-698895691/5000000000 : ℝ)*X 1 1+(1207276833/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2584016867/5000000000 : ℝ)*X 2 0+(6036385571/10000000000 : ℝ)*X 2 1+(-349447279/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4217392753/10000000000 : ℝ)*X 0 0+(5608317463/10000000000 : ℝ)*X 0 1+(1596392743/5000000000 : ℝ)*X 0 2+(4217392753/10000000000 : ℝ)*X 1 0+(5608317463/10000000000 : ℝ)*X 1 1+(1596392743/5000000000 : ℝ)*X 1 2+(4217392753/10000000000 : ℝ)*X 2 0+(5608317463/10000000000 : ℝ)*X 2 1+(1596392743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (138995209082610727491/20000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37400221/50000000000000 : ℝ)*(base1) + (1742871101/100000000000000 : ℝ)*(base19) + (813184351/50000000000000 : ℝ)*(base23) + (59296343/50000000000000 : ℝ)*(base24) + (196408063/50000000000000 : ℝ)*(upper3) + (1161585504917/200000000000 : ℝ)*(major0) + (1161585504917/200000000000 : ℝ)*(major1) + (1161585504917/200000000000 : ℝ)*(major2) + (384670893935061/50000000000000 : ℝ)*(sp0) + (769343787669913/100000000000000 : ℝ)*(sp1) + (384671892789813/50000000000000 : ℝ)*(sp2) + (392236610433059/100000000000000 : ℝ)*(sp3) + (1908735667/50000000000000 : ℝ)*(sp4) + (15287419/500000000000 : ℝ)*(sp7) + (392239742717301/100000000000000 : ℝ)*(f.failure) + (384672765270507/50000000000000 : ℝ)*(f.sum) + (64830065323/80000000000000000000000000 : ℝ)*base66 + (335021347323/160000000000000000000000000 : ℝ)*base68 + (970846917563/160000000000000000000000000 : ℝ)*base70 + (790691967003/160000000000000000000000000 : ℝ)*base72 + (2557618597/80000000000000000000000000 : ℝ)*base73 + (486407075963/160000000000000000000000000 : ℝ)*base76 + (795569611483/160000000000000000000000000 : ℝ)*base78 + (537829052603/160000000000000000000000000 : ℝ)*base80 + (446834296123/80000000000000000000000000 : ℝ)*base82 + (5257129/5000000000000000000000 : ℝ)*base89 + (5257129/5000000000000000000000 : ℝ)*base91 + (5257129/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91580408669187321633141/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1094903/25000000000000 : ℝ)*(base1) + (2138260307/100000000000000 : ℝ)*(base19) + (44169443/2000000000000 : ℝ)*(base23) + (428916643/100000000000000 : ℝ)*(base45) + (240085151/100000000000000 : ℝ)*(upper3) + (180121737/50000000000000 : ℝ)*(upper5) + (153247959139833/25000000000000 : ℝ)*(major0) + (153247959139833/25000000000000 : ℝ)*(major1) + (153247959139833/25000000000000 : ℝ)*(major2) + (1042274059/100000000000000 : ℝ)*(sp2) + (101499737851803/12500000000000 : ℝ)*(sp4) + (162399152034901/20000000000000 : ℝ)*(sp5) + (811994647688603/100000000000000 : ℝ)*(sp6) + (25874091564763/6250000000000 : ℝ)*(sp7) + (20699273470791/5000000000000 : ℝ)*(f.failure) + (202999474608703/25000000000000 : ℝ)*(f.sum) + (59152121047/10000000000000000000000000000 : ℝ)*base66 + (132944387478953/20000000000000000000000000000 : ℝ)*base67 + (81471730761047/20000000000000000000000000000 : ℝ)*base70 + (42538591398953/20000000000000000000000000000 : ℝ)*base71 + (21644733938953/10000000000000000000000000000 : ℝ)*base73 + (35418769618953/20000000000000000000000000000 : ℝ)*base75 + (42436583978953/20000000000000000000000000000 : ℝ)*base77 + (83207263338953/20000000000000000000000000000 : ℝ)*base79 + (53384783441047/10000000000000000000000000000 : ℝ)*base82 + (654339/250000000000000000000 : ℝ)*base89 + (654339/250000000000000000000 : ℝ)*base91 + (654339/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1070_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (113/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1070_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1070_s1_0 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1062325257/5000000000 : ℝ)*x 0 + (5721214291/10000000000 : ℝ)*x 1 + (4986825543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062325257/5000000000 : ℝ)^8263 ≤ (12752980247331/100000000000000 : ℝ)^6215 := by
    have hnat : (1062325257 : ℕ)^8263*100000000000000^6215 ≤ 12752980247331^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062325257 5000000000 12752980247331 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5721214291/10000000000 : ℝ)^8263 ≤ (9519287237101/20000000000000 : ℝ)^6215 := by
    have hnat : (5721214291 : ℕ)^8263*20000000000000^6215 ≤ 9519287237101^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5721214291 10000000000 9519287237101 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4986825543/10000000000 : ℝ)^8263 ≤ (1239080735971/3125000000000 : ℝ)^6215 := by
    have hnat : (4986825543 : ℕ)^8263*3125000000000^6215 ≤ 1239080735971^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986825543 10000000000 1239080735971 3125000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1062325257/5000000000 : ℝ), (5721214291/10000000000 : ℝ), (4986825543/10000000000 : ℝ)] ![(12752980247331/100000000000000 : ℝ), (9519287237101/20000000000000 : ℝ), (1239080735971/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1062325257/5000000000 : ℝ)|^8263 ≤ (12752980247331/100000000000000 : ℝ)^6215
        have hw : |(-1062325257/5000000000 : ℝ)|=(1062325257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5721214291/10000000000 : ℝ)|^8263 ≤ (9519287237101/20000000000000 : ℝ)^6215
        have hw : |(5721214291/10000000000 : ℝ)|=(5721214291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4986825543/10000000000 : ℝ)|^8263 ≤ (1239080735971/3125000000000 : ℝ)^6215
        have hw : |(4986825543/10000000000 : ℝ)|=(4986825543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s1_1 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (338943393/625000000 : ℝ)*x 0 + (-2522458513/10000000000 : ℝ)*x 1 + (4986825853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338943393/625000000 : ℝ)^8263 ≤ (44327665332267/100000000000000 : ℝ)^6215 := by
    have hnat : (338943393 : ℕ)^8263*100000000000000^6215 ≤ 44327665332267^6215*625000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338943393 625000000 44327665332267 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2522458513/10000000000 : ℝ)^8263 ≤ (128173982571/800000000000 : ℝ)^6215 := by
    have hnat : (2522458513 : ℕ)^8263*800000000000^6215 ≤ 128173982571^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2522458513 10000000000 128173982571 800000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4986825853/10000000000 : ℝ)^8263 ≤ (39650586828127/100000000000000 : ℝ)^6215 := by
    have hnat : (4986825853 : ℕ)^8263*100000000000000^6215 ≤ 39650586828127^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986825853 10000000000 39650586828127 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338943393/625000000 : ℝ), (-2522458513/10000000000 : ℝ), (4986825853/10000000000 : ℝ)] ![(44327665332267/100000000000000 : ℝ), (128173982571/800000000000 : ℝ), (39650586828127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338943393/625000000 : ℝ)|^8263 ≤ (44327665332267/100000000000000 : ℝ)^6215
        have hw : |(338943393/625000000 : ℝ)|=(338943393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2522458513/10000000000 : ℝ)|^8263 ≤ (128173982571/800000000000 : ℝ)^6215
        have hw : |(-2522458513/10000000000 : ℝ)|=(2522458513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4986825853/10000000000 : ℝ)|^8263 ≤ (39650586828127/100000000000000 : ℝ)^6215
        have hw : |(4986825853/10000000000 : ℝ)|=(4986825853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s1_2 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2711547453/5000000000 : ℝ)*x 0 + (4986825163/10000000000 : ℝ)*x 1 + (-2522458581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711547453/5000000000 : ℝ)^8263 ≤ (443276720483/1000000000000 : ℝ)^6215 := by
    have hnat : (2711547453 : ℕ)^8263*1000000000000^6215 ≤ 443276720483^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711547453 5000000000 443276720483 1000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4986825163/10000000000 : ℝ)^8263 ≤ (39650579534037/100000000000000 : ℝ)^6215 := by
    have hnat : (4986825163 : ℕ)^8263*100000000000000^6215 ≤ 39650579534037^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986825163 10000000000 39650579534037 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2522458581/10000000000 : ℝ)^8263 ≤ (4005437098903/25000000000000 : ℝ)^6215 := by
    have hnat : (2522458581 : ℕ)^8263*25000000000000^6215 ≤ 4005437098903^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2522458581 10000000000 4005437098903 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711547453/5000000000 : ℝ), (4986825163/10000000000 : ℝ), (-2522458581/10000000000 : ℝ)] ![(443276720483/1000000000000 : ℝ), (39650579534037/100000000000000 : ℝ), (4005437098903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711547453/5000000000 : ℝ)|^8263 ≤ (443276720483/1000000000000 : ℝ)^6215
        have hw : |(2711547453/5000000000 : ℝ)|=(2711547453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4986825163/10000000000 : ℝ)|^8263 ≤ (39650579534037/100000000000000 : ℝ)^6215
        have hw : |(4986825163/10000000000 : ℝ)|=(4986825163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2522458581/10000000000 : ℝ)|^8263 ≤ (4005437098903/25000000000000 : ℝ)^6215
        have hw : |(-2522458581/10000000000 : ℝ)|=(2522458581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s1_3 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2161733809/5000000000 : ℝ)*x 0 + (3663292689/10000000000 : ℝ)*x 1 + (2551866989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161733809/5000000000 : ℝ)^8263 ≤ (4099583232777/12500000000000 : ℝ)^6215 := by
    have hnat : (2161733809 : ℕ)^8263*12500000000000^6215 ≤ 4099583232777^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161733809 5000000000 4099583232777 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3663292689/10000000000 : ℝ)^8263 ≤ (1644509106619/6250000000000 : ℝ)^6215 := by
    have hnat : (3663292689 : ℕ)^8263*6250000000000^6215 ≤ 1644509106619^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3663292689 10000000000 1644509106619 6250000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2551866989/5000000000 : ℝ)^8263 ≤ (4089118841989/10000000000000 : ℝ)^6215 := by
    have hnat : (2551866989 : ℕ)^8263*10000000000000^6215 ≤ 4089118841989^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2551866989 5000000000 4089118841989 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161733809/5000000000 : ℝ), (3663292689/10000000000 : ℝ), (2551866989/5000000000 : ℝ)] ![(4099583232777/12500000000000 : ℝ), (1644509106619/6250000000000 : ℝ), (4089118841989/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161733809/5000000000 : ℝ)|^8263 ≤ (4099583232777/12500000000000 : ℝ)^6215
        have hw : |(2161733809/5000000000 : ℝ)|=(2161733809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3663292689/10000000000 : ℝ)|^8263 ≤ (1644509106619/6250000000000 : ℝ)^6215
        have hw : |(3663292689/10000000000 : ℝ)|=(3663292689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2551866989/5000000000 : ℝ)|^8263 ≤ (4089118841989/10000000000000 : ℝ)^6215
        have hw : |(2551866989/5000000000 : ℝ)|=(2551866989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s1_4 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125566507/10000000000 : ℝ)*x 0 + (2498565533/5000000000 : ℝ)*x 1 + (2855348713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125566507/10000000000 : ℝ)^8263 ≤ (12760290692167/100000000000000 : ℝ)^6215 := by
    have hnat : (2125566507 : ℕ)^8263*100000000000000^6215 ≤ 12760290692167^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125566507 10000000000 12760290692167 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2498565533/5000000000 : ℝ)^8263 ≤ (39759561804777/100000000000000 : ℝ)^6215 := by
    have hnat : (2498565533 : ℕ)^8263*100000000000000^6215 ≤ 39759561804777^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498565533 5000000000 39759561804777 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2855348713/5000000000 : ℝ)^8263 ≤ (4748014748137/10000000000000 : ℝ)^6215 := by
    have hnat : (2855348713 : ℕ)^8263*10000000000000^6215 ≤ 4748014748137^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2855348713 5000000000 4748014748137 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125566507/10000000000 : ℝ), (2498565533/5000000000 : ℝ), (2855348713/5000000000 : ℝ)] ![(12760290692167/100000000000000 : ℝ), (39759561804777/100000000000000 : ℝ), (4748014748137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125566507/10000000000 : ℝ)|^8263 ≤ (12760290692167/100000000000000 : ℝ)^6215
        have hw : |(-2125566507/10000000000 : ℝ)|=(2125566507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2498565533/5000000000 : ℝ)|^8263 ≤ (39759561804777/100000000000000 : ℝ)^6215
        have hw : |(2498565533/5000000000 : ℝ)|=(2498565533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2855348713/5000000000 : ℝ)|^8263 ≤ (4748014748137/10000000000000 : ℝ)^6215
        have hw : |(2855348713/5000000000 : ℝ)|=(2855348713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s1_5 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2617751609/5000000000 : ℝ)*x 0 + (-1798584611/10000000000 : ℝ)*x 1 + (5710699253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617751609/5000000000 : ℝ)^8263 ≤ (21150377149727/50000000000000 : ℝ)^6215 := by
    have hnat : (2617751609 : ℕ)^8263*50000000000000^6215 ≤ 21150377149727^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617751609 5000000000 21150377149727 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1798584611/10000000000 : ℝ)^8263 ≤ (5109539004641/50000000000000 : ℝ)^6215 := by
    have hnat : (1798584611 : ℕ)^8263*50000000000000^6215 ≤ 5109539004641^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798584611 10000000000 5109539004641 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5710699253/10000000000 : ℝ)^8263 ≤ (47480167677033/100000000000000 : ℝ)^6215 := by
    have hnat : (5710699253 : ℕ)^8263*100000000000000^6215 ≤ 47480167677033^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5710699253 10000000000 47480167677033 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617751609/5000000000 : ℝ), (-1798584611/10000000000 : ℝ), (5710699253/10000000000 : ℝ)] ![(21150377149727/50000000000000 : ℝ), (5109539004641/50000000000000 : ℝ), (47480167677033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617751609/5000000000 : ℝ)|^8263 ≤ (21150377149727/50000000000000 : ℝ)^6215
        have hw : |(2617751609/5000000000 : ℝ)|=(2617751609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1798584611/10000000000 : ℝ)|^8263 ≤ (5109539004641/50000000000000 : ℝ)^6215
        have hw : |(-1798584611/10000000000 : ℝ)|=(1798584611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5710699253/10000000000 : ℝ)|^8263 ≤ (47480167677033/100000000000000 : ℝ)^6215
        have hw : |(5710699253/10000000000 : ℝ)|=(5710699253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s1_6 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2617750583/5000000000 : ℝ)*x 0 + (1427675381/2500000000 : ℝ)*x 1 + (-359716841/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617750583/5000000000 : ℝ)^8263 ≤ (42300732256813/100000000000000 : ℝ)^6215 := by
    have hnat : (2617750583 : ℕ)^8263*100000000000000^6215 ≤ 42300732256813^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617750583 5000000000 42300732256813 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1427675381/2500000000 : ℝ)^8263 ≤ (1899207711227/4000000000000 : ℝ)^6215 := by
    have hnat : (1427675381 : ℕ)^8263*4000000000000^6215 ≤ 1899207711227^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427675381 2500000000 1899207711227 4000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359716841/2000000000 : ℝ)^8263 ≤ (2043814988471/20000000000000 : ℝ)^6215 := by
    have hnat : (359716841 : ℕ)^8263*20000000000000^6215 ≤ 2043814988471^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359716841 2000000000 2043814988471 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617750583/5000000000 : ℝ), (1427675381/2500000000 : ℝ), (-359716841/2000000000 : ℝ)] ![(42300732256813/100000000000000 : ℝ), (1899207711227/4000000000000 : ℝ), (2043814988471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617750583/5000000000 : ℝ)|^8263 ≤ (42300732256813/100000000000000 : ℝ)^6215
        have hw : |(2617750583/5000000000 : ℝ)|=(2617750583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1427675381/2500000000 : ℝ)|^8263 ≤ (1899207711227/4000000000000 : ℝ)^6215
        have hw : |(1427675381/2500000000 : ℝ)|=(1427675381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-359716841/2000000000 : ℝ)|^8263 ≤ (2043814988471/20000000000000 : ℝ)^6215
        have hw : |(-359716841/2000000000 : ℝ)|=(359716841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s1_7 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4325260067/10000000000 : ℝ)*x 0 + (635439639/1250000000 : ℝ)*x 1 + (1841958473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325260067/10000000000 : ℝ)^8263 ≤ (32814744702759/100000000000000 : ℝ)^6215 := by
    have hnat : (4325260067 : ℕ)^8263*100000000000000^6215 ≤ 32814744702759^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325260067 10000000000 32814744702759 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635439639/1250000000 : ℝ)^8263 ≤ (40675975486897/100000000000000 : ℝ)^6215 := by
    have hnat : (635439639 : ℕ)^8263*100000000000000^6215 ≤ 40675975486897^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635439639 1250000000 40675975486897 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1841958473/5000000000 : ℝ)^8263 ≤ (165682998751/625000000000 : ℝ)^6215 := by
    have hnat : (1841958473 : ℕ)^8263*625000000000^6215 ≤ 165682998751^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841958473 5000000000 165682998751 625000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325260067/10000000000 : ℝ), (635439639/1250000000 : ℝ), (1841958473/5000000000 : ℝ)] ![(32814744702759/100000000000000 : ℝ), (40675975486897/100000000000000 : ℝ), (165682998751/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325260067/10000000000 : ℝ)|^8263 ≤ (32814744702759/100000000000000 : ℝ)^6215
        have hw : |(4325260067/10000000000 : ℝ)|=(4325260067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635439639/1250000000 : ℝ)|^8263 ≤ (40675975486897/100000000000000 : ℝ)^6215
        have hw : |(635439639/1250000000 : ℝ)|=(635439639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1841958473/5000000000 : ℝ)|^8263 ≤ (165682998751/625000000000 : ℝ)^6215
        have hw : |(1841958473/5000000000 : ℝ)|=(1841958473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1070_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1309/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5193/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14047/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (113/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14047/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (113/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14047/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (113/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14047/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (113/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14047/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (113/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14047/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (113/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (113/100000 : ℝ) ^ (4131/1024 : ℝ) ≤ (6464857/5000000000000000000 : ℝ) := by
    have hpowers : (113/100000 : ℝ)^4131 ≤ (6464857/5000000000000000000 : ℝ)^1024 := by
      have hnat : (113 : ℕ)^4131*5000000000000000000^1024 ≤ 6464857^1024*100000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 100000 6464857 5000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/100000 : ℝ)) (X := (6464857/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14047/50000 : ℝ) ^ (4131/1024 : ℝ) ≤ (596496770576522901/100000000000000000000 : ℝ) := by
    have hpowers : (14047/50000 : ℝ)^4131 ≤ (596496770576522901/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14047 : ℕ)^4131*100000000000000000000^1024 ≤ 596496770576522901^1024*50000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14047 50000 596496770576522901 100000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14047/50000 : ℝ)) (X := (596496770576522901/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500000000006464857/2500000000000000000 : ℝ) ≤ (10000000000006411/10000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (2500000000006464857/2500000000000000000 : ℝ)^1024 ≤ (10000000000006411/10000000000000000 : ℝ)^4131 := by
      have hnat : (2500000000006464857 : ℕ)^1024*10000000000000000^4131 ≤ 10000000000006411^4131*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500000000006464857 2500000000000000000 10000000000006411 10000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000006411/10000000000000000 : ℝ)) (X := (2500000000006464857/2500000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100596496770705820041/100000000000000000000 : ℝ) ≤ (10014753020675677/10000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (100596496770705820041/100000000000000000000 : ℝ)^1024 ≤ (10014753020675677/10000000000000000 : ℝ)^4131 := by
      have hnat : (100596496770705820041 : ℕ)^1024*10000000000000000^4131 ≤ 10014753020675677^4131*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100596496770705820041 100000000000000000000 10014753020675677 10000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014753020675677/10000000000000000 : ℝ)) (X := (100596496770705820041/100000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50596496770576522901/50000000000000000000 : ℝ) ≤ (10029506041344943/10000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (50596496770576522901/50000000000000000000 : ℝ)^1024 ≤ (10029506041344943/10000000000000000 : ℝ)^4131 := by
      have hnat : (50596496770576522901 : ℕ)^1024*10000000000000000^4131 ≤ 10029506041344943^4131*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50596496770576522901 50000000000000000000 10029506041344943 10000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029506041344943/10000000000000000 : ℝ)) (X := (50596496770576522901/50000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6464857/5000000000000000000 : ℝ) ≤ ((3730755544233441761/3730800000000000000 : ℝ)+2*(2458836778211/466350000000000 : ℝ)*(113/100000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (3730755544233441761/3730800000000000000 : ℝ)+2*(2458836778211/466350000000000 : ℝ)*(113/100000 : ℝ)=(10000000000006411/10000000000000000 : ℝ) by norm_num, show 1+2*(6464857/5000000000000000000 : ℝ)=(2500000000006464857/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(596496770576522901/100000000000000000000 : ℝ)+(6464857/5000000000000000000 : ℝ) ≤ ((3730755544233441761/3730800000000000000 : ℝ)+(2458836778211/466350000000000 : ℝ)*((14047/50000 : ℝ)+(113/100000 : ℝ)))^(4131/1024 : ℝ) := by
    rw [show (3730755544233441761/3730800000000000000 : ℝ)+(2458836778211/466350000000000 : ℝ)*((14047/50000 : ℝ)+(113/100000 : ℝ))=(10014753020675677/10000000000000000 : ℝ) by norm_num, show 1+(596496770576522901/100000000000000000000 : ℝ)+(6464857/5000000000000000000 : ℝ)=(100596496770705820041/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(596496770576522901/100000000000000000000 : ℝ) ≤ ((3730755544233441761/3730800000000000000 : ℝ)+2*(2458836778211/466350000000000 : ℝ)*(14047/50000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (3730755544233441761/3730800000000000000 : ℝ)+2*(2458836778211/466350000000000 : ℝ)*(14047/50000 : ℝ)=(10029506041344943/10000000000000000 : ℝ) by norm_num, show 1+2*(596496770576522901/100000000000000000000 : ℝ)=(50596496770576522901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3730755544233441761/3730800000000000000 : ℝ)*(X 1 0+X 2 0)+(2458836778211/466350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (113/100000 : ℝ)) (hi := (14047/50000 : ℝ)) (c := (3730755544233441761/3730800000000000000 : ℝ)) (alpha := (2458836778211/466350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3730755544233441761/3730800000000000000 : ℝ)*(X 0 1+X 2 1)+(2458836778211/466350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (113/100000 : ℝ)) (hi := (14047/50000 : ℝ)) (c := (3730755544233441761/3730800000000000000 : ℝ)) (alpha := (2458836778211/466350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3730755544233441761/3730800000000000000 : ℝ)*(X 0 2+X 1 2)+(2458836778211/466350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (113/100000 : ℝ)) (hi := (14047/50000 : ℝ)) (c := (3730755544233441761/3730800000000000000 : ℝ)) (alpha := (2458836778211/466350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1062325257/5000000000 : ℝ)*X 0 0+(5721214291/10000000000 : ℝ)*X 0 1+(4986825543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((338943393/625000000 : ℝ)*X 1 0+(-2522458513/10000000000 : ℝ)*X 1 1+(4986825853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2711547453/5000000000 : ℝ)*X 2 0+(4986825163/10000000000 : ℝ)*X 2 1+(-2522458581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2161733809/5000000000 : ℝ)*X 0 0+(3663292689/10000000000 : ℝ)*X 0 1+(2551866989/5000000000 : ℝ)*X 0 2+(2161733809/5000000000 : ℝ)*X 1 0+(3663292689/10000000000 : ℝ)*X 1 1+(2551866989/5000000000 : ℝ)*X 1 2+(2161733809/5000000000 : ℝ)*X 2 0+(3663292689/10000000000 : ℝ)*X 2 1+(2551866989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2125566507/10000000000 : ℝ)*X 0 0+(2498565533/5000000000 : ℝ)*X 0 1+(2855348713/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2617751609/5000000000 : ℝ)*X 1 0+(-1798584611/10000000000 : ℝ)*X 1 1+(5710699253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2617750583/5000000000 : ℝ)*X 2 0+(1427675381/2500000000 : ℝ)*X 2 1+(-359716841/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325260067/10000000000 : ℝ)*X 0 0+(635439639/1250000000 : ℝ)*X 0 1+(1841958473/5000000000 : ℝ)*X 0 2+(4325260067/10000000000 : ℝ)*X 1 0+(635439639/1250000000 : ℝ)*X 1 1+(1841958473/5000000000 : ℝ)*X 1 2+(4325260067/10000000000 : ℝ)*X 2 0+(635439639/1250000000 : ℝ)*X 2 1+(1841958473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (262254007641518374031402421/31090000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (147903569/100000000000000 : ℝ)*(base1) + (455696081/25000000000000 : ℝ)*(base19) + (1977958889/100000000000000 : ℝ)*(base23) + (92353393/50000000000000 : ℝ)*(upper3) + (203783803/100000000000000 : ℝ)*(upper5) + (513983954730939/50000000000000 : ℝ)*(major0) + (513983954730939/50000000000000 : ℝ)*(major1) + (513983954730939/50000000000000 : ℝ)*(major2) + (1361685519309617/100000000000000 : ℝ)*(sp0) + (680846592444919/50000000000000 : ℝ)*(sp1) + (680846514857637/50000000000000 : ℝ)*(sp2) + (86779492364453/12500000000000 : ℝ)*(sp3) + (4818134057/50000000000000 : ℝ)*(sp4) + (4443253157/100000000000000 : ℝ)*(sp7) + (694240530072351/100000000000000 : ℝ)*(f.failure) + (1361695007674163/100000000000000 : ℝ)*(f.sum) + (9753187287997/15545000000000000000000000000 : ℝ)*base65 + (170904334114254807/62180000000000000000000000000000 : ℝ)*base68 + (347811746866105193/62180000000000000000000000000000 : ℝ)*base69 + (180777730635025193/62180000000000000000000000000000 : ℝ)*base71 + (26578017525499/7772500000000000000000000000 : ℝ)*base74 + (319920272448685193/62180000000000000000000000000000 : ℝ)*base75 + (137702604033025193/62180000000000000000000000000000 : ℝ)*base77 + (488014474002634807/62180000000000000000000000000000 : ℝ)*base80 + (8000646088293/3886250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (7323579/5000000000000000000000 : ℝ)*base89 + (7323579/5000000000000000000000 : ℝ)*base91 + (7323579/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1460336083075631668599/15545000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119854897/6250000000000 : ℝ)*(base19) + (120216451/6250000000000 : ℝ)*(base23) + (262332551/100000000000000 : ℝ)*(upper2) + (352823921/100000000000000 : ℝ)*(upper3) + (473622113/100000000000000 : ℝ)*(upper5) + (132243664151751/12500000000000 : ℝ)*(major0) + (132243664151751/12500000000000 : ℝ)*(major1) + (132243664151751/12500000000000 : ℝ)*(major2) + (10026112571/100000000000000 : ℝ)*(sp1) + (5766343499/50000000000000 : ℝ)*(sp2) + (1401410082132061/100000000000000 : ℝ)*(sp4) + (700699069170569/50000000000000 : ℝ)*(sp5) + (175174578247731/12500000000000 : ℝ)*(sp6) + (357244270582267/50000000000000 : ℝ)*(sp7) + (357244270582267/50000000000000 : ℝ)*(f.failure) + (1401410082132061/100000000000000 : ℝ)*(f.sum) + (50441401500997/15545000000000000000000000000 : ℝ)*base65 + (24818549396923837/15545000000000000000000000000000 : ℝ)*base67 + (42988045990296163/15545000000000000000000000000000 : ℝ)*base70 + (20072233782503837/15545000000000000000000000000000 : ℝ)*base71 + (26629124110777/15545000000000000000000000000 : ℝ)*base73 + (77841381535391163/15545000000000000000000000000000 : ℝ)*base76 + (10291468641423837/15545000000000000000000000000000 : ℝ)*base77 + (168896400803076163/15545000000000000000000000000000 : ℝ)*base80 + (8050803987539/7772500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (17137543/2500000000000000000000 : ℝ)*base89 + (17137543/2500000000000000000000 : ℝ)*base91 + (17137543/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1070_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1309/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5193/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1070_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1070_s2_0 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090925597/5000000000 : ℝ)*x 0 + (552508681/1000000000 : ℝ)*x 1 + (321666101/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090925597/5000000000 : ℝ)^8263 ≤ (13211473310479/100000000000000 : ℝ)^6215 := by
    have hnat : (1090925597 : ℕ)^8263*100000000000000^6215 ≤ 13211473310479^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090925597 5000000000 13211473310479 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552508681/1000000000 : ℝ)^8263 ≤ (45439475720169/100000000000000 : ℝ)^6215 := by
    have hnat : (552508681 : ℕ)^8263*100000000000000^6215 ≤ 45439475720169^6215*1000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552508681 1000000000 45439475720169 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321666101/625000000 : ℝ)^8263 ≤ (2067452547479/5000000000000 : ℝ)^6215 := by
    have hnat : (321666101 : ℕ)^8263*5000000000000^6215 ≤ 2067452547479^6215*625000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321666101 625000000 2067452547479 5000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090925597/5000000000 : ℝ), (552508681/1000000000 : ℝ), (321666101/625000000 : ℝ)] ![(13211473310479/100000000000000 : ℝ), (45439475720169/100000000000000 : ℝ), (2067452547479/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090925597/5000000000 : ℝ)|^8263 ≤ (13211473310479/100000000000000 : ℝ)^6215
        have hw : |(-1090925597/5000000000 : ℝ)|=(1090925597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552508681/1000000000 : ℝ)|^8263 ≤ (45439475720169/100000000000000 : ℝ)^6215
        have hw : |(552508681/1000000000 : ℝ)|=(552508681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(321666101/625000000 : ℝ)|^8263 ≤ (2067452547479/5000000000000 : ℝ)^6215
        have hw : |(321666101/625000000 : ℝ)|=(321666101/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s2_1 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5377026341/10000000000 : ℝ)*x 0 + (-594792827/2500000000 : ℝ)*x 1 + (5146658701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377026341/10000000000 : ℝ)^8263 ≤ (43827730095589/100000000000000 : ℝ)^6215 := by
    have hnat : (5377026341 : ℕ)^8263*100000000000000^6215 ≤ 43827730095589^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377026341 10000000000 43827730095589 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (594792827/2500000000 : ℝ)^8263 ≤ (14823207358001/100000000000000 : ℝ)^6215 := by
    have hnat : (594792827 : ℕ)^8263*100000000000000^6215 ≤ 14823207358001^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594792827 2500000000 14823207358001 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5146658701/10000000000 : ℝ)^8263 ≤ (10337265634783/25000000000000 : ℝ)^6215 := by
    have hnat : (5146658701 : ℕ)^8263*25000000000000^6215 ≤ 10337265634783^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146658701 10000000000 10337265634783 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377026341/10000000000 : ℝ), (-594792827/2500000000 : ℝ), (5146658701/10000000000 : ℝ)] ![(43827730095589/100000000000000 : ℝ), (14823207358001/100000000000000 : ℝ), (10337265634783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377026341/10000000000 : ℝ)|^8263 ≤ (43827730095589/100000000000000 : ℝ)^6215
        have hw : |(5377026341/10000000000 : ℝ)|=(5377026341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-594792827/2500000000 : ℝ)|^8263 ≤ (14823207358001/100000000000000 : ℝ)^6215
        have hw : |(-594792827/2500000000 : ℝ)|=(594792827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5146658701/10000000000 : ℝ)|^8263 ≤ (10337265634783/25000000000000 : ℝ)^6215
        have hw : |(5146658701/10000000000 : ℝ)|=(5146658701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s2_2 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1344256519/2500000000 : ℝ)*x 0 + (5146659001/10000000000 : ℝ)*x 1 + (-2379171267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344256519/2500000000 : ℝ)^8263 ≤ (43827727223821/100000000000000 : ℝ)^6215 := by
    have hnat : (1344256519 : ℕ)^8263*100000000000000^6215 ≤ 43827727223821^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344256519 2500000000 43827727223821 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5146659001/10000000000 : ℝ)^8263 ≤ (161519788061/390625000000 : ℝ)^6215 := by
    have hnat : (5146659001 : ℕ)^8263*390625000000^6215 ≤ 161519788061^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146659001 10000000000 161519788061 390625000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2379171267/10000000000 : ℝ)^8263 ≤ (7411603509189/50000000000000 : ℝ)^6215 := by
    have hnat : (2379171267 : ℕ)^8263*50000000000000^6215 ≤ 7411603509189^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2379171267 10000000000 7411603509189 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344256519/2500000000 : ℝ), (5146659001/10000000000 : ℝ), (-2379171267/10000000000 : ℝ)] ![(43827727223821/100000000000000 : ℝ), (161519788061/390625000000 : ℝ), (7411603509189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344256519/2500000000 : ℝ)|^8263 ≤ (43827727223821/100000000000000 : ℝ)^6215
        have hw : |(1344256519/2500000000 : ℝ)|=(1344256519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5146659001/10000000000 : ℝ)|^8263 ≤ (161519788061/390625000000 : ℝ)^6215
        have hw : |(5146659001/10000000000 : ℝ)|=(5146659001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2379171267/10000000000 : ℝ)|^8263 ≤ (7411603509189/50000000000000 : ℝ)^6215
        have hw : |(-2379171267/10000000000 : ℝ)|=(2379171267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s2_3 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362512011/10000000000 : ℝ)*x 0 + (4007288631/10000000000 : ℝ)*x 1 + (4749535211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362512011/10000000000 : ℝ)^8263 ≤ (8297757452661/25000000000000 : ℝ)^6215 := by
    have hnat : (4362512011 : ℕ)^8263*25000000000000^6215 ≤ 8297757452661^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362512011 10000000000 8297757452661 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4007288631/10000000000 : ℝ)^8263 ≤ (29646937679481/100000000000000 : ℝ)^6215 := by
    have hnat : (4007288631 : ℕ)^8263*100000000000000^6215 ≤ 29646937679481^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007288631 10000000000 29646937679481 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4749535211/10000000000 : ℝ)^8263 ≤ (37162032492533/100000000000000 : ℝ)^6215 := by
    have hnat : (4749535211 : ℕ)^8263*100000000000000^6215 ≤ 37162032492533^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4749535211 10000000000 37162032492533 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362512011/10000000000 : ℝ), (4007288631/10000000000 : ℝ), (4749535211/10000000000 : ℝ)] ![(8297757452661/25000000000000 : ℝ), (29646937679481/100000000000000 : ℝ), (37162032492533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362512011/10000000000 : ℝ)|^8263 ≤ (8297757452661/25000000000000 : ℝ)^6215
        have hw : |(4362512011/10000000000 : ℝ)|=(4362512011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4007288631/10000000000 : ℝ)|^8263 ≤ (29646937679481/100000000000000 : ℝ)^6215
        have hw : |(4007288631/10000000000 : ℝ)|=(4007288631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4749535211/10000000000 : ℝ)|^8263 ≤ (37162032492533/100000000000000 : ℝ)^6215
        have hw : |(4749535211/10000000000 : ℝ)|=(4749535211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s2_4 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090987721/5000000000 : ℝ)*x 0 + (5149404639/10000000000 : ℝ)*x 1 + (5522311323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090987721/5000000000 : ℝ)^8263 ≤ (13212473578133/100000000000000 : ℝ)^6215 := by
    have hnat : (1090987721 : ℕ)^8263*100000000000000^6215 ≤ 13212473578133^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090987721 5000000000 13212473578133 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149404639/10000000000 : ℝ)^8263 ≤ (41378396169619/100000000000000 : ℝ)^6215 := by
    have hnat : (5149404639 : ℕ)^8263*100000000000000^6215 ≤ 41378396169619^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149404639 10000000000 41378396169619 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5522311323/10000000000 : ℝ)^8263 ≤ (5676141279491/12500000000000 : ℝ)^6215 := by
    have hnat : (5522311323 : ℕ)^8263*12500000000000^6215 ≤ 5676141279491^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522311323 10000000000 5676141279491 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090987721/5000000000 : ℝ), (5149404639/10000000000 : ℝ), (5522311323/10000000000 : ℝ)] ![(13212473578133/100000000000000 : ℝ), (41378396169619/100000000000000 : ℝ), (5676141279491/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090987721/5000000000 : ℝ)|^8263 ≤ (13212473578133/100000000000000 : ℝ)^6215
        have hw : |(-1090987721/5000000000 : ℝ)|=(1090987721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149404639/10000000000 : ℝ)|^8263 ≤ (41378396169619/100000000000000 : ℝ)^6215
        have hw : |(5149404639/10000000000 : ℝ)|=(5149404639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5522311323/10000000000 : ℝ)|^8263 ≤ (5676141279491/12500000000000 : ℝ)^6215
        have hw : |(5522311323/10000000000 : ℝ)|=(5522311323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s2_5 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5281479559/10000000000 : ℝ)*x 0 + (-1001760283/5000000000 : ℝ)*x 1 + (5522311411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281479559/10000000000 : ℝ)^8263 ≤ (10698836663871/25000000000000 : ℝ)^6215 := by
    have hnat : (5281479559 : ℕ)^8263*25000000000000^6215 ≤ 10698836663871^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281479559 10000000000 10698836663871 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001760283/5000000000 : ℝ)^8263 ≤ (11795522126071/100000000000000 : ℝ)^6215 := by
    have hnat : (1001760283 : ℕ)^8263*100000000000000^6215 ≤ 11795522126071^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001760283 5000000000 11795522126071 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5522311411/10000000000 : ℝ)^8263 ≤ (45409131197987/100000000000000 : ℝ)^6215 := by
    have hnat : (5522311411 : ℕ)^8263*100000000000000^6215 ≤ 45409131197987^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522311411 10000000000 45409131197987 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281479559/10000000000 : ℝ), (-1001760283/5000000000 : ℝ), (5522311411/10000000000 : ℝ)] ![(10698836663871/25000000000000 : ℝ), (11795522126071/100000000000000 : ℝ), (45409131197987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281479559/10000000000 : ℝ)|^8263 ≤ (10698836663871/25000000000000 : ℝ)^6215
        have hw : |(5281479559/10000000000 : ℝ)|=(5281479559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1001760283/5000000000 : ℝ)|^8263 ≤ (11795522126071/100000000000000 : ℝ)^6215
        have hw : |(-1001760283/5000000000 : ℝ)|=(1001760283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5522311411/10000000000 : ℝ)|^8263 ≤ (45409131197987/100000000000000 : ℝ)^6215
        have hw : |(5522311411/10000000000 : ℝ)|=(5522311411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s2_6 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5281479803/10000000000 : ℝ)*x 0 + (5522311249/10000000000 : ℝ)*x 1 + (-2003520457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281479803/10000000000 : ℝ)^8263 ≤ (42795349284101/100000000000000 : ℝ)^6215 := by
    have hnat : (5281479803 : ℕ)^8263*100000000000000^6215 ≤ 42795349284101^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281479803 10000000000 42795349284101 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5522311249/10000000000 : ℝ)^8263 ≤ (11352282356731/25000000000000 : ℝ)^6215 := by
    have hnat : (5522311249 : ℕ)^8263*25000000000000^6215 ≤ 11352282356731^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522311249 10000000000 11352282356731 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2003520457/10000000000 : ℝ)^8263 ≤ (11795521272879/100000000000000 : ℝ)^6215 := by
    have hnat : (2003520457 : ℕ)^8263*100000000000000^6215 ≤ 11795521272879^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003520457 10000000000 11795521272879 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281479803/10000000000 : ℝ), (5522311249/10000000000 : ℝ), (-2003520457/10000000000 : ℝ)] ![(42795349284101/100000000000000 : ℝ), (11352282356731/25000000000000 : ℝ), (11795521272879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281479803/10000000000 : ℝ)|^8263 ≤ (42795349284101/100000000000000 : ℝ)^6215
        have hw : |(5281479803/10000000000 : ℝ)|=(5281479803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5522311249/10000000000 : ℝ)|^8263 ≤ (11352282356731/25000000000000 : ℝ)^6215
        have hw : |(5522311249/10000000000 : ℝ)|=(5522311249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2003520457/10000000000 : ℝ)|^8263 ≤ (11795521272879/100000000000000 : ℝ)^6215
        have hw : |(-2003520457/10000000000 : ℝ)|=(2003520457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s2_7 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362753407/10000000000 : ℝ)*x 0 + (14825483/31250000 : ℝ)*x 1 + (4012728649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362753407/10000000000 : ℝ)^8263 ≤ (16596735818397/50000000000000 : ℝ)^6215 := by
    have hnat : (4362753407 : ℕ)^8263*50000000000000^6215 ≤ 16596735818397^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362753407 10000000000 16596735818397 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14825483/31250000 : ℝ)^8263 ≤ (7421213957497/20000000000000 : ℝ)^6215 := by
    have hnat : (14825483 : ℕ)^8263*20000000000000^6215 ≤ 7421213957497^6215*31250000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14825483 31250000 7421213957497 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4012728649/10000000000 : ℝ)^8263 ≤ (7425114640659/25000000000000 : ℝ)^6215 := by
    have hnat : (4012728649 : ℕ)^8263*25000000000000^6215 ≤ 7425114640659^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4012728649 10000000000 7425114640659 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362753407/10000000000 : ℝ), (14825483/31250000 : ℝ), (4012728649/10000000000 : ℝ)] ![(16596735818397/50000000000000 : ℝ), (7421213957497/20000000000000 : ℝ), (7425114640659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362753407/10000000000 : ℝ)|^8263 ≤ (16596735818397/50000000000000 : ℝ)^6215
        have hw : |(4362753407/10000000000 : ℝ)|=(4362753407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14825483/31250000 : ℝ)|^8263 ≤ (7421213957497/20000000000000 : ℝ)^6215
        have hw : |(14825483/31250000 : ℝ)|=(14825483/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4012728649/10000000000 : ℝ)|^8263 ≤ (7425114640659/25000000000000 : ℝ)^6215
        have hw : |(4012728649/10000000000 : ℝ)|=(4012728649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1070_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5193/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1309/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (8731/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2091/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5193/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1309/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5193/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1309/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5193/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1309/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5193/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1309/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5193/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1309/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5193/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1309/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1309/25000 : ℝ) ^ (4131/1024 : ℝ) ≤ (679538957288269/100000000000000000000 : ℝ) := by
    have hpowers : (1309/25000 : ℝ)^4131 ≤ (679538957288269/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1309 : ℕ)^4131*100000000000000000000^1024 ≤ 679538957288269^1024*25000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1309 25000 679538957288269 100000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1309/25000 : ℝ)) (X := (679538957288269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5193/25000 : ℝ) ^ (4131/1024 : ℝ) ≤ (176435055235291587/100000000000000000000 : ℝ) := by
    have hpowers : (5193/25000 : ℝ)^4131 ≤ (176435055235291587/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5193 : ℕ)^4131*100000000000000000000^1024 ≤ 176435055235291587^1024*25000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5193 25000 176435055235291587 100000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5193/25000 : ℝ)) (X := (176435055235291587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000679538957288269/50000000000000000000 : ℝ) ≤ (200000673778103/200000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (50000679538957288269/50000000000000000000 : ℝ)^1024 ≤ (200000673778103/200000000000000 : ℝ)^4131 := by
      have hnat : (50000679538957288269 : ℕ)^1024*200000000000000^4131 ≤ 200000673778103^4131*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000679538957288269 50000000000000000000 200000673778103 200000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200000673778103/200000000000000 : ℝ)) (X := (50000679538957288269/50000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6261069662137036241/6250000000000000000 : ℝ) ≤ (2000877485692933/2000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (6261069662137036241/6250000000000000000 : ℝ)^1024 ≤ (2000877485692933/2000000000000000 : ℝ)^4131 := by
      have hnat : (6261069662137036241 : ℕ)^1024*2000000000000000^4131 ≤ 2000877485692933^4131*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6261069662137036241 6250000000000000000 2000877485692933 2000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000877485692933/2000000000000000 : ℝ)) (X := (6261069662137036241/6250000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50176435055235291587/50000000000000000000 : ℝ) ≤ (500437058401209/500000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (50176435055235291587/50000000000000000000 : ℝ)^1024 ≤ (500437058401209/500000000000000 : ℝ)^4131 := by
      have hnat : (50176435055235291587 : ℕ)^1024*500000000000000^4131 ≤ 500437058401209^4131*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50176435055235291587 50000000000000000000 500437058401209 500000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500437058401209/500000000000000 : ℝ)) (X := (50176435055235291587/50000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(679538957288269/100000000000000000000 : ℝ) ≤ ((3882873275754079233/3884000000000000000 : ℝ)+2*(870747911903/310720000000000 : ℝ)*(1309/25000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (3882873275754079233/3884000000000000000 : ℝ)+2*(870747911903/310720000000000 : ℝ)*(1309/25000 : ℝ)=(200000673778103/200000000000000 : ℝ) by norm_num, show 1+2*(679538957288269/100000000000000000000 : ℝ)=(50000679538957288269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(176435055235291587/100000000000000000000 : ℝ)+(679538957288269/100000000000000000000 : ℝ) ≤ ((3882873275754079233/3884000000000000000 : ℝ)+(870747911903/310720000000000 : ℝ)*((5193/25000 : ℝ)+(1309/25000 : ℝ)))^(4131/1024 : ℝ) := by
    rw [show (3882873275754079233/3884000000000000000 : ℝ)+(870747911903/310720000000000 : ℝ)*((5193/25000 : ℝ)+(1309/25000 : ℝ))=(2000877485692933/2000000000000000 : ℝ) by norm_num, show 1+(176435055235291587/100000000000000000000 : ℝ)+(679538957288269/100000000000000000000 : ℝ)=(6261069662137036241/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(176435055235291587/100000000000000000000 : ℝ) ≤ ((3882873275754079233/3884000000000000000 : ℝ)+2*(870747911903/310720000000000 : ℝ)*(5193/25000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (3882873275754079233/3884000000000000000 : ℝ)+2*(870747911903/310720000000000 : ℝ)*(5193/25000 : ℝ)=(500437058401209/500000000000000 : ℝ) by norm_num, show 1+2*(176435055235291587/100000000000000000000 : ℝ)=(50176435055235291587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3882873275754079233/3884000000000000000 : ℝ)*(X 1 0+X 2 0)+(870747911903/310720000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (1309/25000 : ℝ)) (hi := (5193/25000 : ℝ)) (c := (3882873275754079233/3884000000000000000 : ℝ)) (alpha := (870747911903/310720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3882873275754079233/3884000000000000000 : ℝ)*(X 0 1+X 2 1)+(870747911903/310720000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (1309/25000 : ℝ)) (hi := (5193/25000 : ℝ)) (c := (3882873275754079233/3884000000000000000 : ℝ)) (alpha := (870747911903/310720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3882873275754079233/3884000000000000000 : ℝ)*(X 0 2+X 1 2)+(870747911903/310720000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (1309/25000 : ℝ)) (hi := (5193/25000 : ℝ)) (c := (3882873275754079233/3884000000000000000 : ℝ)) (alpha := (870747911903/310720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1090925597/5000000000 : ℝ)*X 0 0+(552508681/1000000000 : ℝ)*X 0 1+(321666101/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377026341/10000000000 : ℝ)*X 1 0+(-594792827/2500000000 : ℝ)*X 1 1+(5146658701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1344256519/2500000000 : ℝ)*X 2 0+(5146659001/10000000000 : ℝ)*X 2 1+(-2379171267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362512011/10000000000 : ℝ)*X 0 0+(4007288631/10000000000 : ℝ)*X 0 1+(4749535211/10000000000 : ℝ)*X 0 2+(4362512011/10000000000 : ℝ)*X 1 0+(4007288631/10000000000 : ℝ)*X 1 1+(4749535211/10000000000 : ℝ)*X 1 2+(4362512011/10000000000 : ℝ)*X 2 0+(4007288631/10000000000 : ℝ)*X 2 1+(4749535211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1090987721/5000000000 : ℝ)*X 0 0+(5149404639/10000000000 : ℝ)*X 0 1+(5522311323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5281479559/10000000000 : ℝ)*X 1 0+(-1001760283/5000000000 : ℝ)*X 1 1+(5522311411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5281479803/10000000000 : ℝ)*X 2 0+(5522311249/10000000000 : ℝ)*X 2 1+(-2003520457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362753407/10000000000 : ℝ)*X 0 0+(14825483/31250000 : ℝ)*X 0 1+(4012728649/10000000000 : ℝ)*X 0 2+(4362753407/10000000000 : ℝ)*X 1 0+(14825483/31250000 : ℝ)*X 1 1+(4012728649/10000000000 : ℝ)*X 1 2+(4362753407/10000000000 : ℝ)*X 2 0+(14825483/31250000 : ℝ)*X 2 1+(4012728649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59745525074979647901/1553600000000000000000000000 : ℝ) := by norm_num
    linear_combination (90623939/20000000000000 : ℝ)*(base1) + (620510437/20000000000000 : ℝ)*(base19) + (743079133/25000000000000 : ℝ)*(base23) + (260281343/100000000000000 : ℝ)*(upper3) + (127564859/50000000000000 : ℝ)*(upper5) + (39898474092017/2000000000000 : ℝ)*(major0) + (39898474092017/2000000000000 : ℝ)*(major1) + (39898474092017/2000000000000 : ℝ)*(major2) + (1321268447494097/50000000000000 : ℝ)*(sp0) + (2642567919219559/100000000000000 : ℝ)*(sp1) + (660642012363803/25000000000000 : ℝ)*(sp2) + (84204287621591/6250000000000 : ℝ)*(sp3) + (6915980649/20000000000000 : ℝ)*(sp4) + (1832770731/25000000000000 : ℝ)*(sp7) + (1347276386148077/100000000000000 : ℝ)*(f.failure) + (82580344430367/3125000000000 : ℝ)*(f.sum) + (11456883823431/7768000000000000000000000000 : ℝ)*base65 + (45136287290242461/7768000000000000000000000000000 : ℝ)*base67 + (26119052963362461/7768000000000000000000000000000 : ℝ)*base69 + (26963215723266461/7768000000000000000000000000000 : ℝ)*base71 + (50359417419703/7768000000000000000000000000 : ℝ)*base73 + (47433064617597539/7768000000000000000000000000000 : ℝ)*base76 + (1100272778357539/7768000000000000000000000000000 : ℝ)*base78 + (18847862709813539/7768000000000000000000000000000 : ℝ)*base80 + (43440333325591/7768000000000000000000000000 : ℝ)*base81 + (38220033/5000000000000000000000 : ℝ)*base89 + (38220033/5000000000000000000000 : ℝ)*base91 + (38220033/5000000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (354834594406608393856896729/48550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1421607373/100000000000000 : ℝ)*(base19) + (51899717/3125000000000 : ℝ)*(base23) + (49010407/25000000000000 : ℝ)*(upper3) + (19377687/50000000000000 : ℝ)*(lower4) + (75746139/50000000000000 : ℝ)*(upper5) + (506103581713343/25000000000000 : ℝ)*(major0) + (506103581713343/25000000000000 : ℝ)*(major1) + (506103581713343/25000000000000 : ℝ)*(major2) + (12354716527/100000000000000 : ℝ)*(sp1) + (3667919521/25000000000000 : ℝ)*(sp2) + (1340817731638903/50000000000000 : ℝ)*(sp4) + (1340810843476953/50000000000000 : ℝ)*(sp5) + (1340809565404389/50000000000000 : ℝ)*(sp6) + (341798236701879/25000000000000 : ℝ)*(sp7) + (341798236701879/25000000000000 : ℝ)*(f.failure) + (1340817731638903/50000000000000 : ℝ)*(f.sum) + (12050261674111/3884000000000000000000000000 : ℝ)*base66 + (437455544869518419/97100000000000000000000000000000 : ℝ)*base67 + (1202534775930718419/97100000000000000000000000000000 : ℝ)*base69 + (454036614788618419/97100000000000000000000000000000 : ℝ)*base71 + (4611057072097/3884000000000000000000000000 : ℝ)*base73 + (402481709250218419/97100000000000000000000000000000 : ℝ)*base75 + (490295312563918419/97100000000000000000000000000000 : ℝ)*base77 + (471611851408318419/97100000000000000000000000000000 : ℝ)*base79 + (3289304443289/3884000000000000000000000000 : ℝ)*base81 + (6871091/1250000000000000000000 : ℝ)*base89 + (6871091/1250000000000000000000 : ℝ)*base91 + (6871091/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1070_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5193/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1309/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8731/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2091/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1070_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1070_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8731/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2091/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1070_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1070_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1070_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8731/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2091/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1070_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
