-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1340_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:06.596835+00:00
-- url     : https://prove2.me/submissions/0013e551-686f-4549-bbfc-70868bf9d49d

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
theorem support_rectangle_w1340_s6_0 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1022848337/5000000000 : ℝ)*x 0 + (5412825247/10000000000 : ℝ)*x 1 + (1048906719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022848337/5000000000 : ℝ)^1075 ≤ (6228687453159/50000000000000 : ℝ)^819 := by
    have hnat : (1022848337 : ℕ)^1075*50000000000000^819 ≤ 6228687453159^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022848337 5000000000 6228687453159 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412825247/10000000000 : ℝ)^1075 ≤ (44678508323023/100000000000000 : ℝ)^819 := by
    have hnat : (5412825247 : ℕ)^1075*100000000000000^819 ≤ 44678508323023^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412825247 10000000000 44678508323023 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048906719/2000000000 : ℝ)^1075 ≤ (5358014594779/12500000000000 : ℝ)^819 := by
    have hnat : (1048906719 : ℕ)^1075*12500000000000^819 ≤ 5358014594779^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048906719 2000000000 5358014594779 12500000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1022848337/5000000000 : ℝ), (5412825247/10000000000 : ℝ), (1048906719/2000000000 : ℝ)] ![(6228687453159/50000000000000 : ℝ), (44678508323023/100000000000000 : ℝ), (5358014594779/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1022848337/5000000000 : ℝ)|^1075 ≤ (6228687453159/50000000000000 : ℝ)^819
        have hw : |(-1022848337/5000000000 : ℝ)|=(1022848337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412825247/10000000000 : ℝ)|^1075 ≤ (44678508323023/100000000000000 : ℝ)^819
        have hw : |(5412825247/10000000000 : ℝ)|=(5412825247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048906719/2000000000 : ℝ)|^1075 ≤ (5358014594779/12500000000000 : ℝ)^819
        have hw : |(1048906719/2000000000 : ℝ)|=(1048906719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s6_1 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349036339/10000000000 : ℝ)*x 0 + (-1065722129/5000000000 : ℝ)*x 1 + (655566713/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349036339/10000000000 : ℝ)^1075 ≤ (21994339553309/50000000000000 : ℝ)^819 := by
    have hnat : (5349036339 : ℕ)^1075*50000000000000^819 ≤ 21994339553309^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349036339 10000000000 21994339553309 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065722129/5000000000 : ℝ)^1075 ≤ (13147202956751/100000000000000 : ℝ)^819 := by
    have hnat : (1065722129 : ℕ)^1075*100000000000000^819 ≤ 13147202956751^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065722129 5000000000 13147202956751 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655566713/1250000000 : ℝ)^1075 ≤ (8572823585513/20000000000000 : ℝ)^819 := by
    have hnat : (655566713 : ℕ)^1075*20000000000000^819 ≤ 8572823585513^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655566713 1250000000 8572823585513 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349036339/10000000000 : ℝ), (-1065722129/5000000000 : ℝ), (655566713/1250000000 : ℝ)] ![(21994339553309/50000000000000 : ℝ), (13147202956751/100000000000000 : ℝ), (8572823585513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349036339/10000000000 : ℝ)|^1075 ≤ (21994339553309/50000000000000 : ℝ)^819
        have hw : |(5349036339/10000000000 : ℝ)|=(5349036339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1065722129/5000000000 : ℝ)|^1075 ≤ (13147202956751/100000000000000 : ℝ)^819
        have hw : |(-1065722129/5000000000 : ℝ)|=(1065722129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655566713/1250000000 : ℝ)|^1075 ≤ (8572823585513/20000000000000 : ℝ)^819
        have hw : |(655566713/1250000000 : ℝ)|=(655566713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s6_2 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674518191/5000000000 : ℝ)*x 0 + (5244533653/10000000000 : ℝ)*x 1 + (-532861067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674518191/5000000000 : ℝ)^1075 ≤ (2749292473173/6250000000000 : ℝ)^819 := by
    have hnat : (2674518191 : ℕ)^1075*6250000000000^819 ≤ 2749292473173^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674518191 5000000000 2749292473173 6250000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244533653/10000000000 : ℝ)^1075 ≤ (21432058690223/50000000000000 : ℝ)^819 := by
    have hnat : (5244533653 : ℕ)^1075*50000000000000^819 ≤ 21432058690223^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244533653 10000000000 21432058690223 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (532861067/2500000000 : ℝ)^1075 ≤ (13147203037713/100000000000000 : ℝ)^819 := by
    have hnat : (532861067 : ℕ)^1075*100000000000000^819 ≤ 13147203037713^819*2500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532861067 2500000000 13147203037713 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674518191/5000000000 : ℝ), (5244533653/10000000000 : ℝ), (-532861067/2500000000 : ℝ)] ![(2749292473173/6250000000000 : ℝ), (21432058690223/50000000000000 : ℝ), (13147203037713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674518191/5000000000 : ℝ)|^1075 ≤ (2749292473173/6250000000000 : ℝ)^819
        have hw : |(2674518191/5000000000 : ℝ)|=(2674518191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244533653/10000000000 : ℝ)|^1075 ≤ (21432058690223/50000000000000 : ℝ)^819
        have hw : |(5244533653/10000000000 : ℝ)|=(5244533653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-532861067/2500000000 : ℝ)|^1075 ≤ (13147203037713/100000000000000 : ℝ)^819
        have hw : |(-532861067/2500000000 : ℝ)|=(532861067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s6_3 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (865428181/2000000000 : ℝ)*x 0 + (2077188383/5000000000 : ℝ)*x 1 + (4506610141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865428181/2000000000 : ℝ)^1075 ≤ (6660642049513/20000000000000 : ℝ)^819 := by
    have hnat : (865428181 : ℕ)^1075*20000000000000^819 ≤ 6660642049513^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865428181 2000000000 6660642049513 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077188383/5000000000 : ℝ)^1075 ≤ (31568929530201/100000000000000 : ℝ)^819 := by
    have hnat : (2077188383 : ℕ)^1075*100000000000000^819 ≤ 31568929530201^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077188383 5000000000 31568929530201 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506610141/10000000000 : ℝ)^1075 ≤ (35127860206537/100000000000000 : ℝ)^819 := by
    have hnat : (4506610141 : ℕ)^1075*100000000000000^819 ≤ 35127860206537^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506610141 10000000000 35127860206537 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865428181/2000000000 : ℝ), (2077188383/5000000000 : ℝ), (4506610141/10000000000 : ℝ)] ![(6660642049513/20000000000000 : ℝ), (31568929530201/100000000000000 : ℝ), (35127860206537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865428181/2000000000 : ℝ)|^1075 ≤ (6660642049513/20000000000000 : ℝ)^819
        have hw : |(865428181/2000000000 : ℝ)|=(865428181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2077188383/5000000000 : ℝ)|^1075 ≤ (31568929530201/100000000000000 : ℝ)^819
        have hw : |(2077188383/5000000000 : ℝ)|=(2077188383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506610141/10000000000 : ℝ)|^1075 ≤ (35127860206537/100000000000000 : ℝ)^819
        have hw : |(4506610141/10000000000 : ℝ)|=(4506610141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s6_4 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2045708853/10000000000 : ℝ)*x 0 + (5245136271/10000000000 : ℝ)*x 1 + (1082443897/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2045708853/10000000000 : ℝ)^1075 ≤ (2491494450633/20000000000000 : ℝ)^819 := by
    have hnat : (2045708853 : ℕ)^1075*20000000000000^819 ≤ 2491494450633^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045708853 10000000000 2491494450633 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245136271/10000000000 : ℝ)^1075 ≤ (10717645568841/25000000000000 : ℝ)^819 := by
    have hnat : (5245136271 : ℕ)^1075*25000000000000^819 ≤ 10717645568841^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245136271 10000000000 10717645568841 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082443897/2000000000 : ℝ)^1075 ≤ (22335972727649/50000000000000 : ℝ)^819 := by
    have hnat : (1082443897 : ℕ)^1075*50000000000000^819 ≤ 22335972727649^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082443897 2000000000 22335972727649 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2045708853/10000000000 : ℝ), (5245136271/10000000000 : ℝ), (1082443897/2000000000 : ℝ)] ![(2491494450633/20000000000000 : ℝ), (10717645568841/25000000000000 : ℝ), (22335972727649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2045708853/10000000000 : ℝ)|^1075 ≤ (2491494450633/20000000000000 : ℝ)^819
        have hw : |(-2045708853/10000000000 : ℝ)|=(2045708853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245136271/10000000000 : ℝ)|^1075 ≤ (10717645568841/25000000000000 : ℝ)^819
        have hw : |(5245136271/10000000000 : ℝ)|=(5245136271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082443897/2000000000 : ℝ)|^1075 ≤ (22335972727649/50000000000000 : ℝ)^819
        have hw : |(1082443897/2000000000 : ℝ)|=(1082443897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s6_5 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305698347/10000000000 : ℝ)*x 0 + (-1963758401/10000000000 : ℝ)*x 1 + (2706109743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305698347/10000000000 : ℝ)^1075 ≤ (43521474172139/100000000000000 : ℝ)^819 := by
    have hnat : (5305698347 : ℕ)^1075*100000000000000^819 ≤ 43521474172139^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305698347 10000000000 43521474172139 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1963758401/10000000000 : ℝ)^1075 ≤ (2951645088371/25000000000000 : ℝ)^819 := by
    have hnat : (1963758401 : ℕ)^1075*25000000000000^819 ≤ 2951645088371^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963758401 10000000000 2951645088371 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706109743/5000000000 : ℝ)^1075 ≤ (11167986366533/25000000000000 : ℝ)^819 := by
    have hnat : (2706109743 : ℕ)^1075*25000000000000^819 ≤ 11167986366533^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706109743 5000000000 11167986366533 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305698347/10000000000 : ℝ), (-1963758401/10000000000 : ℝ), (2706109743/5000000000 : ℝ)] ![(43521474172139/100000000000000 : ℝ), (2951645088371/25000000000000 : ℝ), (11167986366533/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305698347/10000000000 : ℝ)|^1075 ≤ (43521474172139/100000000000000 : ℝ)^819
        have hw : |(5305698347/10000000000 : ℝ)|=(5305698347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1963758401/10000000000 : ℝ)|^1075 ≤ (2951645088371/25000000000000 : ℝ)^819
        have hw : |(-1963758401/10000000000 : ℝ)|=(1963758401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706109743/5000000000 : ℝ)|^1075 ≤ (11167986366533/25000000000000 : ℝ)^819
        have hw : |(2706109743/5000000000 : ℝ)|=(2706109743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s6_6 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305698339/10000000000 : ℝ)*x 0 + (2706109749/5000000000 : ℝ)*x 1 + (-981879197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305698339/10000000000 : ℝ)^1075 ≤ (10880368521501/25000000000000 : ℝ)^819 := by
    have hnat : (5305698339 : ℕ)^1075*25000000000000^819 ≤ 10880368521501^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305698339 10000000000 10880368521501 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706109749/5000000000 : ℝ)^1075 ≤ (22335972798069/50000000000000 : ℝ)^819 := by
    have hnat : (2706109749 : ℕ)^1075*50000000000000^819 ≤ 22335972798069^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706109749 5000000000 22335972798069 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (981879197/5000000000 : ℝ)^1075 ≤ (11806580298243/100000000000000 : ℝ)^819 := by
    have hnat : (981879197 : ℕ)^1075*100000000000000^819 ≤ 11806580298243^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981879197 5000000000 11806580298243 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305698339/10000000000 : ℝ), (2706109749/5000000000 : ℝ), (-981879197/5000000000 : ℝ)] ![(10880368521501/25000000000000 : ℝ), (22335972798069/50000000000000 : ℝ), (11806580298243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305698339/10000000000 : ℝ)|^1075 ≤ (10880368521501/25000000000000 : ℝ)^819
        have hw : |(5305698339/10000000000 : ℝ)|=(5305698339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706109749/5000000000 : ℝ)|^1075 ≤ (22335972798069/50000000000000 : ℝ)^819
        have hw : |(2706109749/5000000000 : ℝ)|=(2706109749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-981879197/5000000000 : ℝ)|^1075 ≤ (11806580298243/100000000000000 : ℝ)^819
        have hw : |(-981879197/5000000000 : ℝ)|=(981879197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s6_7 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (540895803/1250000000 : ℝ)*x 0 + (563168629/1250000000 : ℝ)*x 1 + (831128881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540895803/1250000000 : ℝ)^1075 ≤ (33303468042083/100000000000000 : ℝ)^819 := by
    have hnat : (540895803 : ℕ)^1075*100000000000000^819 ≤ 33303468042083^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540895803 1250000000 33303468042083 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563168629/1250000000 : ℝ)^1075 ≤ (2194684882597/6250000000000 : ℝ)^819 := by
    have hnat : (563168629 : ℕ)^1075*6250000000000^819 ≤ 2194684882597^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563168629 1250000000 2194684882597 6250000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831128881/2000000000 : ℝ)^1075 ≤ (1263262953263/4000000000000 : ℝ)^819 := by
    have hnat : (831128881 : ℕ)^1075*4000000000000^819 ≤ 1263262953263^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831128881 2000000000 1263262953263 4000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540895803/1250000000 : ℝ), (563168629/1250000000 : ℝ), (831128881/2000000000 : ℝ)] ![(33303468042083/100000000000000 : ℝ), (2194684882597/6250000000000 : ℝ), (1263262953263/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540895803/1250000000 : ℝ)|^1075 ≤ (33303468042083/100000000000000 : ℝ)^819
        have hw : |(540895803/1250000000 : ℝ)|=(540895803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563168629/1250000000 : ℝ)|^1075 ≤ (2194684882597/6250000000000 : ℝ)^819
        have hw : |(563168629/1250000000 : ℝ)|=(563168629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831128881/2000000000 : ℝ)|^1075 ≤ (1263262953263/4000000000000 : ℝ)^819
        have hw : |(831128881/2000000000 : ℝ)|=(831128881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1340_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (348/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1393/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7353/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7357/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (348/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7357/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (348/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7357/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (348/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7357/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (348/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7357/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (348/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7357/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (348/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (348/3125 : ℝ) ^ (4299/1024 : ℝ) ≤ (4976321254166691/50000000000000000000 : ℝ) := by
    have hpowers : (348/3125 : ℝ)^4299 ≤ (4976321254166691/50000000000000000000 : ℝ)^1024 := by
      have hnat : (348 : ℕ)^4299*50000000000000000000^1024 ≤ 4976321254166691^1024*3125^4299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        348 3125 4976321254166691 50000000000000000000 4299 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (348/3125 : ℝ)) (X := (4976321254166691/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7357/50000 : ℝ) ^ (4299/1024 : ℝ) ≤ (2003605189142137/6250000000000000000 : ℝ) := by
    have hpowers : (7357/50000 : ℝ)^4299 ≤ (2003605189142137/6250000000000000000 : ℝ)^1024 := by
      have hnat : (7357 : ℕ)^4299*6250000000000000000^1024 ≤ 2003605189142137^1024*50000^4299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7357 50000 2003605189142137 6250000000000000000 4299 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7357/50000 : ℝ)) (X := (2003605189142137/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004976321254166691/25000000000000000000 : ℝ) ≤ (625029631115671/625000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (25004976321254166691/25000000000000000000 : ℝ)^1024 ≤ (625029631115671/625000000000000 : ℝ)^4299 := by
      have hnat : (25004976321254166691 : ℕ)^1024*625000000000000^4299 ≤ 625029631115671^4299*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004976321254166691 25000000000000000000 625029631115671 625000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625029631115671/625000000000000 : ℝ)) (X := (25004976321254166691/25000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021005162767303787/50000000000000000000 : ℝ) ≤ (2000200100913153/2000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (50021005162767303787/50000000000000000000 : ℝ)^1024 ≤ (2000200100913153/2000000000000000 : ℝ)^4299 := by
      have hnat : (50021005162767303787 : ℕ)^1024*2000000000000000^4299 ≤ 2000200100913153^4299*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021005162767303787 50000000000000000000 2000200100913153 2000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000200100913153/2000000000000000 : ℝ)) (X := (50021005162767303787/50000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127003605189142137/3125000000000000000 : ℝ) ≤ (5000763455640397/5000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (3127003605189142137/3125000000000000000 : ℝ)^1024 ≤ (5000763455640397/5000000000000000 : ℝ)^4299 := by
      have hnat : (3127003605189142137 : ℕ)^1024*5000000000000000^4299 ≤ 5000763455640397^4299*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127003605189142137 3125000000000000000 5000763455640397 5000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000763455640397/5000000000000000 : ℝ)) (X := (3127003605189142137/3125000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4976321254166691/50000000000000000000 : ℝ) ≤ ((223562326198455047/223625000000000000 : ℝ)+2*(526406715029/357800000000000 : ℝ)*(348/3125 : ℝ))^(4299/1024 : ℝ) := by
    rw [show (223562326198455047/223625000000000000 : ℝ)+2*(526406715029/357800000000000 : ℝ)*(348/3125 : ℝ)=(625029631115671/625000000000000 : ℝ) by norm_num, show 1+2*(4976321254166691/50000000000000000000 : ℝ)=(25004976321254166691/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2003605189142137/6250000000000000000 : ℝ)+(4976321254166691/50000000000000000000 : ℝ) ≤ ((223562326198455047/223625000000000000 : ℝ)+(526406715029/357800000000000 : ℝ)*((7357/50000 : ℝ)+(348/3125 : ℝ)))^(4299/1024 : ℝ) := by
    rw [show (223562326198455047/223625000000000000 : ℝ)+(526406715029/357800000000000 : ℝ)*((7357/50000 : ℝ)+(348/3125 : ℝ))=(2000200100913153/2000000000000000 : ℝ) by norm_num, show 1+(2003605189142137/6250000000000000000 : ℝ)+(4976321254166691/50000000000000000000 : ℝ)=(50021005162767303787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2003605189142137/6250000000000000000 : ℝ) ≤ ((223562326198455047/223625000000000000 : ℝ)+2*(526406715029/357800000000000 : ℝ)*(7357/50000 : ℝ))^(4299/1024 : ℝ) := by
    rw [show (223562326198455047/223625000000000000 : ℝ)+2*(526406715029/357800000000000 : ℝ)*(7357/50000 : ℝ)=(5000763455640397/5000000000000000 : ℝ) by norm_num, show 1+2*(2003605189142137/6250000000000000000 : ℝ)=(3127003605189142137/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (223562326198455047/223625000000000000 : ℝ)*(X 1 0+X 2 0)+(526406715029/357800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (348/3125 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (223562326198455047/223625000000000000 : ℝ)) (alpha := (526406715029/357800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (223562326198455047/223625000000000000 : ℝ)*(X 0 1+X 2 1)+(526406715029/357800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (348/3125 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (223562326198455047/223625000000000000 : ℝ)) (alpha := (526406715029/357800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (223562326198455047/223625000000000000 : ℝ)*(X 0 2+X 1 2)+(526406715029/357800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (348/3125 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (223562326198455047/223625000000000000 : ℝ)) (alpha := (526406715029/357800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1022848337/5000000000 : ℝ)*X 0 0+(5412825247/10000000000 : ℝ)*X 0 1+(1048906719/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349036339/10000000000 : ℝ)*X 1 0+(-1065722129/5000000000 : ℝ)*X 1 1+(655566713/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674518191/5000000000 : ℝ)*X 2 0+(5244533653/10000000000 : ℝ)*X 2 1+(-532861067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865428181/2000000000 : ℝ)*X 0 0+(2077188383/5000000000 : ℝ)*X 0 1+(4506610141/10000000000 : ℝ)*X 0 2+(865428181/2000000000 : ℝ)*X 1 0+(2077188383/5000000000 : ℝ)*X 1 1+(4506610141/10000000000 : ℝ)*X 1 2+(865428181/2000000000 : ℝ)*X 2 0+(2077188383/5000000000 : ℝ)*X 2 1+(4506610141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2045708853/10000000000 : ℝ)*X 0 0+(5245136271/10000000000 : ℝ)*X 0 1+(1082443897/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305698347/10000000000 : ℝ)*X 1 0+(-1963758401/10000000000 : ℝ)*X 1 1+(2706109743/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305698339/10000000000 : ℝ)*X 2 0+(2706109749/5000000000 : ℝ)*X 2 1+(-981879197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540895803/1250000000 : ℝ)*X 0 0+(563168629/1250000000 : ℝ)*X 0 1+(831128881/2000000000 : ℝ)*X 0 2+(540895803/1250000000 : ℝ)*X 1 0+(563168629/1250000000 : ℝ)*X 1 1+(831128881/2000000000 : ℝ)*X 1 2+(540895803/1250000000 : ℝ)*X 2 0+(563168629/1250000000 : ℝ)*X 2 1+(831128881/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19460190370727763140907/4472500000000000000000000000 : ℝ) := by norm_num
    linear_combination (23579259/3125000000000 : ℝ)*(base19) + (45768141/6250000000000 : ℝ)*(base23) + (37450519/100000000000000 : ℝ)*(lower2) + (122260997/100000000000000 : ℝ)*(upper3) + (16671711/25000000000000 : ℝ)*(upper5) + (1756228611927/40000000000 : ℝ)*(major0) + (1756228611927/40000000000 : ℝ)*(major1) + (1756228611927/40000000000 : ℝ)*(major2) + (5942084098890987/100000000000000 : ℝ)*(sp0) + (2971050656985357/50000000000000 : ℝ)*(sp1) + (2971050668108373/50000000000000 : ℝ)*(sp2) + (11089973321729/390625000000 : ℝ)*(sp3) + (1123101001/6250000000000 : ℝ)*(sp4) + (1918932369/25000000000000 : ℝ)*(sp7) + (28390408460921/1000000000000 : ℝ)*(f.failure) + (2971051034253501/50000000000000 : ℝ)*(f.sum) + (263932966353/447250000000000000000000000 : ℝ)*base66 + (40827294272801/8945000000000000000000000000 : ℝ)*base68 + (104897694505161/8945000000000000000000000000 : ℝ)*base70 + (77275662555053/4472500000000000000000000000 : ℝ)*base72 + (2212942337703/894500000000000000000000000 : ℝ)*base74 + (3331213710659/559062500000000000000000000 : ℝ)*base75 + (20463738026647/1118125000000000000000000000 : ℝ)*base78 + (17599525725457/4472500000000000000000000000 : ℝ)*base79 + (5018129072927/894500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1223299/100000000000000000000 : ℝ)*base89 + (1223299/100000000000000000000 : ℝ)*base91 + (1223299/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29098945850387230373943/8945000000000000000000000000 : ℝ) := by norm_num
    linear_combination (566306981/100000000000000 : ℝ)*(base19) + (129329741/20000000000000 : ℝ)*(base23) + (16683471/25000000000000 : ℝ)*(upper3) + (38142377/100000000000000 : ℝ)*(lower4) + (1645917/3125000000000 : ℝ)*(upper5) + (552787281767059/12500000000000 : ℝ)*(major0) + (552787281767059/12500000000000 : ℝ)*(major1) + (552787281767059/12500000000000 : ℝ)*(major2) + (577490323/5000000000000 : ℝ)*(sp1) + (6844689703/50000000000000 : ℝ)*(sp2) + (2992520175368273/50000000000000 : ℝ)*(sp4) + (1197005646924621/20000000000000 : ℝ)*(sp5) + (1197005202941687/20000000000000 : ℝ)*(sp6) + (714889012274963/25000000000000 : ℝ)*(sp7) + (714889012274963/25000000000000 : ℝ)*(f.failure) + (2992520175368273/50000000000000 : ℝ)*(f.sum) + (20714218429053/4472500000000000000000000000 : ℝ)*base66 + (23360900739106773/2795312500000000000000000000000 : ℝ)*base67 + (3439481064169273/2795312500000000000000000000000 : ℝ)*base69 + (62683506178277079/5590625000000000000000000000000 : ℝ)*base72 + (19273639389189/8945000000000000000000000000 : ℝ)*base73 + (9225948661361977/2795312500000000000000000000000 : ℝ)*base76 + (26461182536395829/5590625000000000000000000000000 : ℝ)*base78 + (10067057796117449/1397656250000000000000000000000 : ℝ)*base79 + (8869569551627/4472500000000000000000000000 : ℝ)*base81 + (6181697/2500000000000000000000 : ℝ)*base89 + (6181697/2500000000000000000000 : ℝ)*base91 + (6181697/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1340_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (348/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1340_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1340_s7_0 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-409140623/2000000000 : ℝ)*x 0 + (5412758807/10000000000 : ℝ)*x 1 + (655574487/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409140623/2000000000 : ℝ)^1075 ≤ (12457426389261/100000000000000 : ℝ)^819 := by
    have hnat : (409140623 : ℕ)^1075*100000000000000^819 ≤ 12457426389261^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409140623 2000000000 12457426389261 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412758807/10000000000 : ℝ)^1075 ≤ (44677788496223/100000000000000 : ℝ)^819 := by
    have hnat : (5412758807 : ℕ)^1075*100000000000000^819 ≤ 44677788496223^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412758807 10000000000 44677788496223 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655574487/1250000000 : ℝ)^1075 ≤ (42864785113529/100000000000000 : ℝ)^819 := by
    have hnat : (655574487 : ℕ)^1075*100000000000000^819 ≤ 42864785113529^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655574487 1250000000 42864785113529 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-409140623/2000000000 : ℝ), (5412758807/10000000000 : ℝ), (655574487/1250000000 : ℝ)] ![(12457426389261/100000000000000 : ℝ), (44677788496223/100000000000000 : ℝ), (42864785113529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-409140623/2000000000 : ℝ)|^1075 ≤ (12457426389261/100000000000000 : ℝ)^819
        have hw : |(-409140623/2000000000 : ℝ)|=(409140623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412758807/10000000000 : ℝ)|^1075 ≤ (44677788496223/100000000000000 : ℝ)^819
        have hw : |(5412758807/10000000000 : ℝ)|=(5412758807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655574487/1250000000 : ℝ)|^1075 ≤ (42864785113529/100000000000000 : ℝ)^819
        have hw : |(655574487/1250000000 : ℝ)|=(655574487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s7_1 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337254929/2500000000 : ℝ)*x 0 + (-1065691977/5000000000 : ℝ)*x 1 + (262229797/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337254929/2500000000 : ℝ)^1075 ≤ (8797699934987/20000000000000 : ℝ)^819 := by
    have hnat : (1337254929 : ℕ)^1075*20000000000000^819 ≤ 8797699934987^819*2500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337254929 2500000000 8797699934987 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065691977/5000000000 : ℝ)^1075 ≤ (3286678680651/25000000000000 : ℝ)^819 := by
    have hnat : (1065691977 : ℕ)^1075*25000000000000^819 ≤ 3286678680651^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065691977 5000000000 3286678680651 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262229797/500000000 : ℝ)^1075 ≤ (8572957117111/20000000000000 : ℝ)^819 := by
    have hnat : (262229797 : ℕ)^1075*20000000000000^819 ≤ 8572957117111^819*500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262229797 500000000 8572957117111 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337254929/2500000000 : ℝ), (-1065691977/5000000000 : ℝ), (262229797/500000000 : ℝ)] ![(8797699934987/20000000000000 : ℝ), (3286678680651/25000000000000 : ℝ), (8572957117111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337254929/2500000000 : ℝ)|^1075 ≤ (8797699934987/20000000000000 : ℝ)^819
        have hw : |(1337254929/2500000000 : ℝ)|=(1337254929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1065691977/5000000000 : ℝ)|^1075 ≤ (3286678680651/25000000000000 : ℝ)^819
        have hw : |(-1065691977/5000000000 : ℝ)|=(1065691977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262229797/500000000 : ℝ)|^1075 ≤ (8572957117111/20000000000000 : ℝ)^819
        have hw : |(262229797/500000000 : ℝ)|=(262229797/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s7_2 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349019807/10000000000 : ℝ)*x 0 + (327787243/625000000 : ℝ)*x 1 + (-1065691951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349019807/10000000000 : ℝ)^1075 ≤ (8797700131441/20000000000000 : ℝ)^819 := by
    have hnat : (5349019807 : ℕ)^1075*20000000000000^819 ≤ 8797700131441^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349019807 10000000000 8797700131441 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327787243/625000000 : ℝ)^1075 ≤ (21432392513853/50000000000000 : ℝ)^819 := by
    have hnat : (327787243 : ℕ)^1075*50000000000000^819 ≤ 21432392513853^819*625000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327787243 625000000 21432392513853 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065691951/5000000000 : ℝ)^1075 ≤ (13146714301603/100000000000000 : ℝ)^819 := by
    have hnat : (1065691951 : ℕ)^1075*100000000000000^819 ≤ 13146714301603^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065691951 5000000000 13146714301603 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349019807/10000000000 : ℝ), (327787243/625000000 : ℝ), (-1065691951/5000000000 : ℝ)] ![(8797700131441/20000000000000 : ℝ), (21432392513853/50000000000000 : ℝ), (13146714301603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349019807/10000000000 : ℝ)|^1075 ≤ (8797700131441/20000000000000 : ℝ)^819
        have hw : |(5349019807/10000000000 : ℝ)|=(5349019807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327787243/625000000 : ℝ)|^1075 ≤ (21432392513853/50000000000000 : ℝ)^819
        have hw : |(327787243/625000000 : ℝ)|=(327787243/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065691951/5000000000 : ℝ)|^1075 ≤ (13146714301603/100000000000000 : ℝ)^819
        have hw : |(-1065691951/5000000000 : ℝ)|=(1065691951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s7_3 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4327145343/10000000000 : ℝ)*x 0 + (166180429/400000000 : ℝ)*x 1 + (4506475163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327145343/10000000000 : ℝ)^1075 ≤ (16651627540241/50000000000000 : ℝ)^819 := by
    have hnat : (4327145343 : ℕ)^1075*50000000000000^819 ≤ 16651627540241^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327145343 10000000000 16651627540241 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166180429/400000000 : ℝ)^1075 ≤ (31570265672223/100000000000000 : ℝ)^819 := by
    have hnat : (166180429 : ℕ)^1075*100000000000000^819 ≤ 31570265672223^819*400000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166180429 400000000 31570265672223 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506475163/10000000000 : ℝ)^1075 ≤ (1756323961353/5000000000000 : ℝ)^819 := by
    have hnat : (4506475163 : ℕ)^1075*5000000000000^819 ≤ 1756323961353^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506475163 10000000000 1756323961353 5000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327145343/10000000000 : ℝ), (166180429/400000000 : ℝ), (4506475163/10000000000 : ℝ)] ![(16651627540241/50000000000000 : ℝ), (31570265672223/100000000000000 : ℝ), (1756323961353/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327145343/10000000000 : ℝ)|^1075 ≤ (16651627540241/50000000000000 : ℝ)^819
        have hw : |(4327145343/10000000000 : ℝ)|=(4327145343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166180429/400000000 : ℝ)|^1075 ≤ (31570265672223/100000000000000 : ℝ)^819
        have hw : |(166180429/400000000 : ℝ)|=(166180429/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506475163/10000000000 : ℝ)|^1075 ≤ (1756323961353/5000000000000 : ℝ)^819
        have hw : |(4506475163/10000000000 : ℝ)|=(4506475163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s7_4 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1022857409/5000000000 : ℝ)*x 0 + (5245197739/10000000000 : ℝ)*x 1 + (676519277/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022857409/5000000000 : ℝ)^1075 ≤ (6228759965763/50000000000000 : ℝ)^819 := by
    have hnat : (1022857409 : ℕ)^1075*50000000000000^819 ≤ 6228759965763^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022857409 5000000000 6228759965763 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245197739/10000000000 : ℝ)^1075 ≤ (10717810429509/25000000000000 : ℝ)^819 := by
    have hnat : (5245197739 : ℕ)^1075*25000000000000^819 ≤ 10717810429509^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245197739 10000000000 10717810429509 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676519277/1250000000 : ℝ)^1075 ≤ (8934247668021/20000000000000 : ℝ)^819 := by
    have hnat : (676519277 : ℕ)^1075*20000000000000^819 ≤ 8934247668021^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676519277 1250000000 8934247668021 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1022857409/5000000000 : ℝ), (5245197739/10000000000 : ℝ), (676519277/1250000000 : ℝ)] ![(6228759965763/50000000000000 : ℝ), (10717810429509/25000000000000 : ℝ), (8934247668021/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1022857409/5000000000 : ℝ)|^1075 ≤ (6228759965763/50000000000000 : ℝ)^819
        have hw : |(-1022857409/5000000000 : ℝ)|=(1022857409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245197739/10000000000 : ℝ)|^1075 ≤ (10717810429509/25000000000000 : ℝ)^819
        have hw : |(5245197739/10000000000 : ℝ)|=(5245197739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676519277/1250000000 : ℝ)|^1075 ≤ (8934247668021/20000000000000 : ℝ)^819
        have hw : |(676519277/1250000000 : ℝ)|=(676519277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s7_5 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305714317/10000000000 : ℝ)*x 0 + (-1963825951/10000000000 : ℝ)*x 1 + (541215441/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305714317/10000000000 : ℝ)^1075 ≤ (43521646117603/100000000000000 : ℝ)^819 := by
    have hnat : (5305714317 : ℕ)^1075*100000000000000^819 ≤ 43521646117603^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305714317 10000000000 43521646117603 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1963825951/10000000000 : ℝ)^1075 ≤ (2951778357123/25000000000000 : ℝ)^819 := by
    have hnat : (1963825951 : ℕ)^1075*25000000000000^819 ≤ 2951778357123^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963825951 10000000000 2951778357123 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541215441/1000000000 : ℝ)^1075 ≤ (4467124044187/10000000000000 : ℝ)^819 := by
    have hnat : (541215441 : ℕ)^1075*10000000000000^819 ≤ 4467124044187^819*1000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541215441 1000000000 4467124044187 10000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305714317/10000000000 : ℝ), (-1963825951/10000000000 : ℝ), (541215441/1000000000 : ℝ)] ![(43521646117603/100000000000000 : ℝ), (2951778357123/25000000000000 : ℝ), (4467124044187/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305714317/10000000000 : ℝ)|^1075 ≤ (43521646117603/100000000000000 : ℝ)^819
        have hw : |(5305714317/10000000000 : ℝ)|=(5305714317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1963825951/10000000000 : ℝ)|^1075 ≤ (2951778357123/25000000000000 : ℝ)^819
        have hw : |(-1963825951/10000000000 : ℝ)|=(1963825951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541215441/1000000000 : ℝ)|^1075 ≤ (4467124044187/10000000000000 : ℝ)^819
        have hw : |(541215441/1000000000 : ℝ)|=(541215441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s7_6 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1061142861/2000000000 : ℝ)*x 0 + (541215457/1000000000 : ℝ)*x 1 + (-981912873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061142861/2000000000 : ℝ)^1075 ≤ (21760822994201/50000000000000 : ℝ)^819 := by
    have hnat : (1061142861 : ℕ)^1075*50000000000000^819 ≤ 21760822994201^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061142861 2000000000 21760822994201 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541215457/1000000000 : ℝ)^1075 ≤ (11167810543821/25000000000000 : ℝ)^819 := by
    have hnat : (541215457 : ℕ)^1075*25000000000000^819 ≤ 11167810543821^819*1000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541215457 1000000000 11167810543821 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (981912873/5000000000 : ℝ)^1075 ≤ (11807111810713/100000000000000 : ℝ)^819 := by
    have hnat : (981912873 : ℕ)^1075*100000000000000^819 ≤ 11807111810713^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981912873 5000000000 11807111810713 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061142861/2000000000 : ℝ), (541215457/1000000000 : ℝ), (-981912873/5000000000 : ℝ)] ![(21760822994201/50000000000000 : ℝ), (11167810543821/25000000000000 : ℝ), (11807111810713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061142861/2000000000 : ℝ)|^1075 ≤ (21760822994201/50000000000000 : ℝ)^819
        have hw : |(1061142861/2000000000 : ℝ)|=(1061142861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541215457/1000000000 : ℝ)|^1075 ≤ (11167810543821/25000000000000 : ℝ)^819
        have hw : |(541215457/1000000000 : ℝ)|=(541215457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-981912873/5000000000 : ℝ)|^1075 ≤ (11807111810713/100000000000000 : ℝ)^819
        have hw : |(-981912873/5000000000 : ℝ)|=(981912873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s7_7 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2163585443/5000000000 : ℝ)*x 0 + (2252607919/5000000000 : ℝ)*x 1 + (831155297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163585443/5000000000 : ℝ)^1075 ≤ (8325878279383/25000000000000 : ℝ)^819 := by
    have hnat : (2163585443 : ℕ)^1075*25000000000000^819 ≤ 8325878279383^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163585443 5000000000 8325878279383 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252607919/5000000000 : ℝ)^1075 ≤ (8778398878391/25000000000000 : ℝ)^819 := by
    have hnat : (2252607919 : ℕ)^1075*25000000000000^819 ≤ 8778398878391^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252607919 5000000000 8778398878391 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831155297/2000000000 : ℝ)^1075 ≤ (31582891357503/100000000000000 : ℝ)^819 := by
    have hnat : (831155297 : ℕ)^1075*100000000000000^819 ≤ 31582891357503^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831155297 2000000000 31582891357503 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163585443/5000000000 : ℝ), (2252607919/5000000000 : ℝ), (831155297/2000000000 : ℝ)] ![(8325878279383/25000000000000 : ℝ), (8778398878391/25000000000000 : ℝ), (31582891357503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163585443/5000000000 : ℝ)|^1075 ≤ (8325878279383/25000000000000 : ℝ)^819
        have hw : |(2163585443/5000000000 : ℝ)|=(2163585443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252607919/5000000000 : ℝ)|^1075 ≤ (8778398878391/25000000000000 : ℝ)^819
        have hw : |(2252607919/5000000000 : ℝ)|=(2252607919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831155297/2000000000 : ℝ)|^1075 ≤ (31582891357503/100000000000000 : ℝ)^819
        have hw : |(831155297/2000000000 : ℝ)|=(831155297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1340_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2229/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2941/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1393/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1393/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1393/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1393/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1393/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1393/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1393/12500 : ℝ) ^ (4299/1024 : ℝ) ≤ (9982693966434763/100000000000000000000 : ℝ) := by
    have hpowers : (1393/12500 : ℝ)^4299 ≤ (9982693966434763/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1393 : ℕ)^4299*100000000000000000000^1024 ≤ 9982693966434763^1024*12500^4299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1393 12500 9982693966434763 100000000000000000000 4299 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1393/12500 : ℝ)) (X := (9982693966434763/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7353/50000 : ℝ) ^ (4299/1024 : ℝ) ≤ (3998071534374843/12500000000000000000 : ℝ) := by
    have hpowers : (7353/50000 : ℝ)^4299 ≤ (3998071534374843/12500000000000000000 : ℝ)^1024 := by
      have hnat : (7353 : ℕ)^4299*12500000000000000000^1024 ≤ 3998071534374843^1024*50000^4299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7353 50000 3998071534374843 12500000000000000000 4299 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7353/50000 : ℝ)) (X := (3998071534374843/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009982693966434763/50000000000000000000 : ℝ) ≤ (10000475529254343/10000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (50009982693966434763/50000000000000000000 : ℝ)^1024 ≤ (10000475529254343/10000000000000000 : ℝ)^4299 := by
      have hnat : (50009982693966434763 : ℕ)^1024*10000000000000000^4299 ≤ 10000475529254343^4299*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009982693966434763 50000000000000000000 10000475529254343 10000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000475529254343/10000000000000000 : ℝ)) (X := (50009982693966434763/50000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041967266241433507/100000000000000000000 : ℝ) ≤ (10000999479243193/10000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (100041967266241433507/100000000000000000000 : ℝ)^1024 ≤ (10000999479243193/10000000000000000 : ℝ)^4299 := by
      have hnat : (100041967266241433507 : ℕ)^1024*10000000000000000^4299 ≤ 10000999479243193^4299*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041967266241433507 100000000000000000000 10000999479243193 10000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000999479243193/10000000000000000 : ℝ)) (X := (100041967266241433507/100000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253998071534374843/6250000000000000000 : ℝ) ≤ (10001523429232043/10000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (6253998071534374843/6250000000000000000 : ℝ)^1024 ≤ (10001523429232043/10000000000000000 : ℝ)^4299 := by
      have hnat : (6253998071534374843 : ℕ)^1024*10000000000000000^4299 ≤ 10001523429232043^4299*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253998071534374843 6250000000000000000 10001523429232043 10000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001523429232043/10000000000000000 : ℝ)) (X := (6253998071534374843/6250000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9982693966434763/100000000000000000000 : ℝ) ≤ ((17805008018926240483/17810000000000000000 : ℝ)+2*(10478999777/7124000000000 : ℝ)*(1393/12500 : ℝ))^(4299/1024 : ℝ) := by
    rw [show (17805008018926240483/17810000000000000000 : ℝ)+2*(10478999777/7124000000000 : ℝ)*(1393/12500 : ℝ)=(10000475529254343/10000000000000000 : ℝ) by norm_num, show 1+2*(9982693966434763/100000000000000000000 : ℝ)=(50009982693966434763/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3998071534374843/12500000000000000000 : ℝ)+(9982693966434763/100000000000000000000 : ℝ) ≤ ((17805008018926240483/17810000000000000000 : ℝ)+(10478999777/7124000000000 : ℝ)*((7353/50000 : ℝ)+(1393/12500 : ℝ)))^(4299/1024 : ℝ) := by
    rw [show (17805008018926240483/17810000000000000000 : ℝ)+(10478999777/7124000000000 : ℝ)*((7353/50000 : ℝ)+(1393/12500 : ℝ))=(10000999479243193/10000000000000000 : ℝ) by norm_num, show 1+(3998071534374843/12500000000000000000 : ℝ)+(9982693966434763/100000000000000000000 : ℝ)=(100041967266241433507/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3998071534374843/12500000000000000000 : ℝ) ≤ ((17805008018926240483/17810000000000000000 : ℝ)+2*(10478999777/7124000000000 : ℝ)*(7353/50000 : ℝ))^(4299/1024 : ℝ) := by
    rw [show (17805008018926240483/17810000000000000000 : ℝ)+2*(10478999777/7124000000000 : ℝ)*(7353/50000 : ℝ)=(10001523429232043/10000000000000000 : ℝ) by norm_num, show 1+2*(3998071534374843/12500000000000000000 : ℝ)=(6253998071534374843/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17805008018926240483/17810000000000000000 : ℝ)*(X 1 0+X 2 0)+(10478999777/7124000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (1393/12500 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (17805008018926240483/17810000000000000000 : ℝ)) (alpha := (10478999777/7124000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17805008018926240483/17810000000000000000 : ℝ)*(X 0 1+X 2 1)+(10478999777/7124000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (1393/12500 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (17805008018926240483/17810000000000000000 : ℝ)) (alpha := (10478999777/7124000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17805008018926240483/17810000000000000000 : ℝ)*(X 0 2+X 1 2)+(10478999777/7124000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (1393/12500 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (17805008018926240483/17810000000000000000 : ℝ)) (alpha := (10478999777/7124000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-409140623/2000000000 : ℝ)*X 0 0+(5412758807/10000000000 : ℝ)*X 0 1+(655574487/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337254929/2500000000 : ℝ)*X 1 0+(-1065691977/5000000000 : ℝ)*X 1 1+(262229797/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349019807/10000000000 : ℝ)*X 2 0+(327787243/625000000 : ℝ)*X 2 1+(-1065691951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4327145343/10000000000 : ℝ)*X 0 0+(166180429/400000000 : ℝ)*X 0 1+(4506475163/10000000000 : ℝ)*X 0 2+(4327145343/10000000000 : ℝ)*X 1 0+(166180429/400000000 : ℝ)*X 1 1+(4506475163/10000000000 : ℝ)*X 1 2+(4327145343/10000000000 : ℝ)*X 2 0+(166180429/400000000 : ℝ)*X 2 1+(4506475163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1022857409/5000000000 : ℝ)*X 0 0+(5245197739/10000000000 : ℝ)*X 0 1+(676519277/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305714317/10000000000 : ℝ)*X 1 0+(-1963825951/10000000000 : ℝ)*X 1 1+(541215441/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061142861/2000000000 : ℝ)*X 2 0+(541215457/1000000000 : ℝ)*X 2 1+(-981912873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163585443/5000000000 : ℝ)*X 0 0+(2252607919/5000000000 : ℝ)*X 0 1+(831155297/2000000000 : ℝ)*X 0 2+(2163585443/5000000000 : ℝ)*X 1 0+(2252607919/5000000000 : ℝ)*X 1 1+(831155297/2000000000 : ℝ)*X 1 2+(2163585443/5000000000 : ℝ)*X 2 0+(2252607919/5000000000 : ℝ)*X 2 1+(831155297/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1670393384364089909402254419/222625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80188297/6250000000000 : ℝ)*(base19) + (1337927627/100000000000000 : ℝ)*(base23) + (6185159/25000000000000 : ℝ)*(lower2) + (119582587/100000000000000 : ℝ)*(upper3) + (16715429/10000000000000 : ℝ)*(upper5) + (1098487222820177/25000000000000 : ℝ)*(major0) + (1098487222820177/25000000000000 : ℝ)*(major1) + (1098487222820177/25000000000000 : ℝ)*(major2) + (2973320986073311/50000000000000 : ℝ)*(sp0) + (2973335763293271/50000000000000 : ℝ)*(sp1) + (5946671471671667/100000000000000 : ℝ)*(sp2) + (1420605223338449/50000000000000 : ℝ)*(sp3) + (240917599/781250000000 : ℝ)*(sp4) + (3569044881/25000000000000 : ℝ)*(sp7) + (1420612361428211/50000000000000 : ℝ)*(f.failure) + (2973336404799647/50000000000000 : ℝ)*(f.sum) + (1440745034371/222625000000000000000000000 : ℝ)*base65 + (8494256580671874509/445250000000000000000000000000000 : ℝ)*base68 + (2661733260015374509/445250000000000000000000000000000 : ℝ)*base70 + (3135247895648374509/445250000000000000000000000000000 : ℝ)*base72 + (3830716570917/890500000000000000000000000 : ℝ)*base74 + (11885136439889374509/445250000000000000000000000000000 : ℝ)*base76 + (840182814862624509/445250000000000000000000000000000 : ℝ)*base78 + (6096405776485374509/445250000000000000000000000000000 : ℝ)*base80 + (25527909887/17810000000000000000000000 : ℝ)*base82 + (12643809/5000000000000000000000 : ℝ)*base89 + (12643809/5000000000000000000000 : ℝ)*base91 + (12643809/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4923220913070225708902635557/445250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4266553/1250000000000 : ℝ)*(base23) + (128457/400000000000 : ℝ)*(lower1) + (27052063/25000000000000 : ℝ)*(lower2) + (21020903/25000000000000 : ℝ)*(upper3) + (240675437/100000000000000 : ℝ)*(lower4) + (78859501/100000000000000 : ℝ)*(upper5) + (2212826569799293/50000000000000 : ℝ)*(major0) + (2212826569799293/50000000000000 : ℝ)*(major1) + (2212826569799293/50000000000000 : ℝ)*(major2) + (80557317/625000000000 : ℝ)*(sp2) + (5989580518239833/100000000000000 : ℝ)*(sp4) + (5989580518239833/100000000000000 : ℝ)*(sp5) + (5989567287744873/100000000000000 : ℝ)*(sp6) + (14308626961919/500000000000 : ℝ)*(sp7) + (14308626961919/500000000000 : ℝ)*(f.failure) + (5989580518239833/100000000000000 : ℝ)*(f.sum) + (7385943756869/445250000000000000000000000 : ℝ)*base66 + (3516677849090378519/890500000000000000000000000000000 : ℝ)*base67 + (4640005561870121481/890500000000000000000000000000000 : ℝ)*base70 + (5760795035706621481/890500000000000000000000000000000 : ℝ)*base72 + (7450856167867/1781000000000000000000000000 : ℝ)*base74 + (5119564391451121481/890500000000000000000000000000000 : ℝ)*base76 + (3711301862011378519/890500000000000000000000000000000 : ℝ)*base77 + (38275984422471121481/890500000000000000000000000000000 : ℝ)*base80 + (2785706198563/445250000000000000000000000 : ℝ)*base82 + (242661/50000000000000000000 : ℝ)*base89 + (242661/50000000000000000000 : ℝ)*base91 + (242661/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1340_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2229/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1340_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1340_box_0 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1878286743/10000000000 : ℝ)*x 0 + (5390024679/10000000000 : ℝ)*x 1 + (5390024529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1878286743/10000000000 : ℝ)^1075 ≤ (2784178480961/25000000000000 : ℝ)^819 := by
    have hnat : (1878286743 : ℕ)^1075*25000000000000^819 ≤ 2784178480961^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878286743 10000000000 2784178480961 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390024679/10000000000 : ℝ)^1075 ≤ (44431643843743/100000000000000 : ℝ)^819 := by
    have hnat : (5390024679 : ℕ)^1075*100000000000000^819 ≤ 44431643843743^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390024679 10000000000 44431643843743 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390024529/10000000000 : ℝ)^1075 ≤ (44431642220747/100000000000000 : ℝ)^819 := by
    have hnat : (5390024529 : ℕ)^1075*100000000000000^819 ≤ 44431642220747^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390024529 10000000000 44431642220747 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1878286743/10000000000 : ℝ), (5390024679/10000000000 : ℝ), (5390024529/10000000000 : ℝ)] ![(2784178480961/25000000000000 : ℝ), (44431643843743/100000000000000 : ℝ), (44431642220747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1878286743/10000000000 : ℝ)|^1075 ≤ (2784178480961/25000000000000 : ℝ)^819
        have hw : |(-1878286743/10000000000 : ℝ)|=(1878286743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390024679/10000000000 : ℝ)|^1075 ≤ (44431643843743/100000000000000 : ℝ)^819
        have hw : |(5390024679/10000000000 : ℝ)|=(5390024679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390024529/10000000000 : ℝ)|^1075 ≤ (44431642220747/100000000000000 : ℝ)^819
        have hw : |(5390024529/10000000000 : ℝ)|=(5390024529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_1 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5285136449/10000000000 : ℝ)*x 0 + (-1010988887/5000000000 : ℝ)*x 1 + (42109567/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285136449/10000000000 : ℝ)^1075 ≤ (21650111534103/50000000000000 : ℝ)^819 := by
    have hnat : (5285136449 : ℕ)^1075*50000000000000^819 ≤ 21650111534103^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285136449 10000000000 21650111534103 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010988887/5000000000 : ℝ)^1075 ≤ (3067033545299/25000000000000 : ℝ)^819 := by
    have hnat : (1010988887 : ℕ)^1075*25000000000000^819 ≤ 3067033545299^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010988887 5000000000 3067033545299 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42109567/78125000 : ℝ)^1075 ≤ (22215821364643/50000000000000 : ℝ)^819 := by
    have hnat : (42109567 : ℕ)^1075*50000000000000^819 ≤ 22215821364643^819*78125000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42109567 78125000 22215821364643 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285136449/10000000000 : ℝ), (-1010988887/5000000000 : ℝ), (42109567/78125000 : ℝ)] ![(21650111534103/50000000000000 : ℝ), (3067033545299/25000000000000 : ℝ), (22215821364643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285136449/10000000000 : ℝ)|^1075 ≤ (21650111534103/50000000000000 : ℝ)^819
        have hw : |(5285136449/10000000000 : ℝ)|=(5285136449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1010988887/5000000000 : ℝ)|^1075 ≤ (3067033545299/25000000000000 : ℝ)^819
        have hw : |(-1010988887/5000000000 : ℝ)|=(1010988887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42109567/78125000 : ℝ)|^1075 ≤ (22215821364643/50000000000000 : ℝ)^819
        have hw : |(42109567/78125000 : ℝ)|=(42109567/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_2 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642568127/5000000000 : ℝ)*x 0 + (673753099/1250000000 : ℝ)*x 1 + (-404395549/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642568127/5000000000 : ℝ)^1075 ≤ (1353131905351/3125000000000 : ℝ)^819 := by
    have hnat : (2642568127 : ℕ)^1075*3125000000000^819 ≤ 1353131905351^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642568127 5000000000 1353131905351 3125000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673753099/1250000000 : ℝ)^1075 ≤ (55539556333/125000000000 : ℝ)^819 := by
    have hnat : (673753099 : ℕ)^1075*125000000000^819 ≤ 55539556333^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673753099 1250000000 55539556333 125000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404395549/2000000000 : ℝ)^1075 ≤ (12268133950243/100000000000000 : ℝ)^819 := by
    have hnat : (404395549 : ℕ)^1075*100000000000000^819 ≤ 12268133950243^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404395549 2000000000 12268133950243 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642568127/5000000000 : ℝ), (673753099/1250000000 : ℝ), (-404395549/2000000000 : ℝ)] ![(1353131905351/3125000000000 : ℝ), (55539556333/125000000000 : ℝ), (12268133950243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642568127/5000000000 : ℝ)|^1075 ≤ (1353131905351/3125000000000 : ℝ)^819
        have hw : |(2642568127/5000000000 : ℝ)|=(2642568127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673753099/1250000000 : ℝ)|^1075 ≤ (55539556333/125000000000 : ℝ)^819
        have hw : |(673753099/1250000000 : ℝ)|=(673753099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-404395549/2000000000 : ℝ)|^1075 ≤ (12268133950243/100000000000000 : ℝ)^819
        have hw : |(-404395549/2000000000 : ℝ)|=(404395549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_3 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4475383531/10000000000 : ℝ)*x 0 + (4256919797/10000000000 : ℝ)*x 1 + (133028747/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4475383531/10000000000 : ℝ)^1075 ≤ (17404360635477/50000000000000 : ℝ)^819 := by
    have hnat : (4475383531 : ℕ)^1075*50000000000000^819 ≤ 17404360635477^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475383531 10000000000 17404360635477 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4256919797/10000000000 : ℝ)^1075 ≤ (32595638820309/100000000000000 : ℝ)^819 := by
    have hnat : (4256919797 : ℕ)^1075*100000000000000^819 ≤ 32595638820309^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256919797 10000000000 32595638820309 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133028747/312500000 : ℝ)^1075 ≤ (6519127979143/20000000000000 : ℝ)^819 := by
    have hnat : (133028747 : ℕ)^1075*20000000000000^819 ≤ 6519127979143^819*312500000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133028747 312500000 6519127979143 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4475383531/10000000000 : ℝ), (4256919797/10000000000 : ℝ), (133028747/312500000 : ℝ)] ![(17404360635477/50000000000000 : ℝ), (32595638820309/100000000000000 : ℝ), (6519127979143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4475383531/10000000000 : ℝ)|^1075 ≤ (17404360635477/50000000000000 : ℝ)^819
        have hw : |(4475383531/10000000000 : ℝ)|=(4475383531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4256919797/10000000000 : ℝ)|^1075 ≤ (32595638820309/100000000000000 : ℝ)^819
        have hw : |(4256919797/10000000000 : ℝ)|=(4256919797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(133028747/312500000 : ℝ)|^1075 ≤ (6519127979143/20000000000000 : ℝ)^819
        have hw : |(133028747/312500000 : ℝ)|=(133028747/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_4 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1107935139/5000000000 : ℝ)*x 0 + (2632440833/5000000000 : ℝ)*x 1 + (1316220187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107935139/5000000000 : ℝ)^1075 ≤ (6917465426127/50000000000000 : ℝ)^819 := by
    have hnat : (1107935139 : ℕ)^1075*50000000000000^819 ≤ 6917465426127^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107935139 5000000000 6917465426127 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632440833/5000000000 : ℝ)^1075 ≤ (5385317437037/12500000000000 : ℝ)^819 := by
    have hnat : (2632440833 : ℕ)^1075*12500000000000^819 ≤ 5385317437037^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632440833 5000000000 5385317437037 12500000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316220187/2500000000 : ℝ)^1075 ≤ (10770632409057/25000000000000 : ℝ)^819 := by
    have hnat : (1316220187 : ℕ)^1075*25000000000000^819 ≤ 10770632409057^819*2500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316220187 2500000000 10770632409057 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1107935139/5000000000 : ℝ), (2632440833/5000000000 : ℝ), (1316220187/2500000000 : ℝ)] ![(6917465426127/50000000000000 : ℝ), (5385317437037/12500000000000 : ℝ), (10770632409057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1107935139/5000000000 : ℝ)|^1075 ≤ (6917465426127/50000000000000 : ℝ)^819
        have hw : |(-1107935139/5000000000 : ℝ)|=(1107935139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632440833/5000000000 : ℝ)|^1075 ≤ (5385317437037/12500000000000 : ℝ)^819
        have hw : |(2632440833/5000000000 : ℝ)|=(2632440833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316220187/2500000000 : ℝ)|^1075 ≤ (10770632409057/25000000000000 : ℝ)^819
        have hw : |(1316220187/2500000000 : ℝ)|=(1316220187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_5 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (671630379/1250000000 : ℝ)*x 0 + (-32377807/156250000 : ℝ)*x 1 + (5264880429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671630379/1250000000 : ℝ)^1075 ≤ (8849598683013/20000000000000 : ℝ)^819 := by
    have hnat : (671630379 : ℕ)^1075*20000000000000^819 ≤ 8849598683013^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671630379 1250000000 8849598683013 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32377807/156250000 : ℝ)^1075 ≤ (1583685044549/12500000000000 : ℝ)^819 := by
    have hnat : (32377807 : ℕ)^1075*12500000000000^819 ≤ 1583685044549^819*156250000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32377807 156250000 1583685044549 12500000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264880429/10000000000 : ℝ)^1075 ≤ (43082526209909/100000000000000 : ℝ)^819 := by
    have hnat : (5264880429 : ℕ)^1075*100000000000000^819 ≤ 43082526209909^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264880429 10000000000 43082526209909 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671630379/1250000000 : ℝ), (-32377807/156250000 : ℝ), (5264880429/10000000000 : ℝ)] ![(8849598683013/20000000000000 : ℝ), (1583685044549/12500000000000 : ℝ), (43082526209909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671630379/1250000000 : ℝ)|^1075 ≤ (8849598683013/20000000000000 : ℝ)^819
        have hw : |(671630379/1250000000 : ℝ)|=(671630379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32377807/156250000 : ℝ)|^1075 ≤ (1583685044549/12500000000000 : ℝ)^819
        have hw : |(-32377807/156250000 : ℝ)|=(32377807/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264880429/10000000000 : ℝ)|^1075 ≤ (43082526209909/100000000000000 : ℝ)^819
        have hw : |(5264880429/10000000000 : ℝ)|=(5264880429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_6 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1074608467/2000000000 : ℝ)*x 0 + (41131881/78125000 : ℝ)*x 1 + (-2072180133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074608467/2000000000 : ℝ)^1075 ≤ (44247985880979/100000000000000 : ℝ)^819 := by
    have hnat : (1074608467 : ℕ)^1075*100000000000000^819 ≤ 44247985880979^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074608467 2000000000 44247985880979 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41131881/78125000 : ℝ)^1075 ≤ (8616505970209/20000000000000 : ℝ)^819 := by
    have hnat : (41131881 : ℕ)^1075*20000000000000^819 ≤ 8616505970209^819*78125000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41131881 78125000 8616505970209 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072180133/10000000000 : ℝ)^1075 ≤ (2533896849723/20000000000000 : ℝ)^819 := by
    have hnat : (2072180133 : ℕ)^1075*20000000000000^819 ≤ 2533896849723^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072180133 10000000000 2533896849723 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074608467/2000000000 : ℝ), (41131881/78125000 : ℝ), (-2072180133/10000000000 : ℝ)] ![(44247985880979/100000000000000 : ℝ), (8616505970209/20000000000000 : ℝ), (2533896849723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074608467/2000000000 : ℝ)|^1075 ≤ (44247985880979/100000000000000 : ℝ)^819
        have hw : |(1074608467/2000000000 : ℝ)|=(1074608467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41131881/78125000 : ℝ)|^1075 ≤ (8616505970209/20000000000000 : ℝ)^819
        have hw : |(41131881/78125000 : ℝ)|=(41131881/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072180133/10000000000 : ℝ)|^1075 ≤ (2533896849723/20000000000000 : ℝ)^819
        have hw : |(-2072180133/10000000000 : ℝ)|=(2072180133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_7 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1044495921/2500000000 : ℝ)*x 0 + (4405565653/10000000000 : ℝ)*x 1 + (4405566559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044495921/2500000000 : ℝ)^1075 ≤ (15902299371727/50000000000000 : ℝ)^819 := by
    have hnat : (1044495921 : ℕ)^1075*50000000000000^819 ≤ 15902299371727^819*2500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044495921 2500000000 15902299371727 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4405565653/10000000000 : ℝ)^1075 ≤ (17048848009527/50000000000000 : ℝ)^819 := by
    have hnat : (4405565653 : ℕ)^1075*50000000000000^819 ≤ 17048848009527^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405565653 10000000000 17048848009527 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4405566559/10000000000 : ℝ)^1075 ≤ (8524426305761/25000000000000 : ℝ)^819 := by
    have hnat : (4405566559 : ℕ)^1075*25000000000000^819 ≤ 8524426305761^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405566559 10000000000 8524426305761 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044495921/2500000000 : ℝ), (4405565653/10000000000 : ℝ), (4405566559/10000000000 : ℝ)] ![(15902299371727/50000000000000 : ℝ), (17048848009527/50000000000000 : ℝ), (8524426305761/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044495921/2500000000 : ℝ)|^1075 ≤ (15902299371727/50000000000000 : ℝ)^819
        have hw : |(1044495921/2500000000 : ℝ)|=(1044495921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4405565653/10000000000 : ℝ)|^1075 ≤ (17048848009527/50000000000000 : ℝ)^819
        have hw : |(4405565653/10000000000 : ℝ)|=(4405565653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4405566559/10000000000 : ℝ)|^1075 ≤ (8524426305761/25000000000000 : ℝ)^819
        have hw : |(4405566559/10000000000 : ℝ)|=(4405566559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_8 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144983971/10000000000 : ℝ)*x 0 + (5178737853/10000000000 : ℝ)*x 1 + (1080809051/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144983971/10000000000 : ℝ)^1075 ≤ (1325693254191/10000000000000 : ℝ)^819 := by
    have hnat : (2144983971 : ℕ)^1075*10000000000000^819 ≤ 1325693254191^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144983971 10000000000 1325693254191 10000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178737853/10000000000 : ℝ)^1075 ≤ (10539914925083/25000000000000 : ℝ)^819 := by
    have hnat : (5178737853 : ℕ)^1075*25000000000000^819 ≤ 10539914925083^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178737853 10000000000 10539914925083 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080809051/2000000000 : ℝ)^1075 ≤ (5572925967257/12500000000000 : ℝ)^819 := by
    have hnat : (1080809051 : ℕ)^1075*12500000000000^819 ≤ 5572925967257^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080809051 2000000000 5572925967257 12500000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144983971/10000000000 : ℝ), (5178737853/10000000000 : ℝ), (1080809051/2000000000 : ℝ)] ![(1325693254191/10000000000000 : ℝ), (10539914925083/25000000000000 : ℝ), (5572925967257/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144983971/10000000000 : ℝ)|^1075 ≤ (1325693254191/10000000000000 : ℝ)^819
        have hw : |(-2144983971/10000000000 : ℝ)|=(2144983971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178737853/10000000000 : ℝ)|^1075 ≤ (10539914925083/25000000000000 : ℝ)^819
        have hw : |(5178737853/10000000000 : ℝ)|=(5178737853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080809051/2000000000 : ℝ)|^1075 ≤ (5572925967257/12500000000000 : ℝ)^819
        have hw : |(1080809051/2000000000 : ℝ)|=(1080809051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_9 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1055056483/2000000000 : ℝ)*x 0 + (-252027599/1250000000 : ℝ)*x 1 + (1351011297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055056483/2000000000 : ℝ)^1075 ≤ (43194286494113/100000000000000 : ℝ)^819 := by
    have hnat : (1055056483 : ℕ)^1075*100000000000000^819 ≤ 43194286494113^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055056483 2000000000 43194286494113 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252027599/1250000000 : ℝ)^1075 ≤ (763894154487/6250000000000 : ℝ)^819 := by
    have hnat : (252027599 : ℕ)^1075*6250000000000^819 ≤ 763894154487^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252027599 1250000000 763894154487 6250000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351011297/2500000000 : ℝ)^1075 ≤ (2786462938283/6250000000000 : ℝ)^819 := by
    have hnat : (1351011297 : ℕ)^1075*6250000000000^819 ≤ 2786462938283^819*2500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351011297 2500000000 2786462938283 6250000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055056483/2000000000 : ℝ), (-252027599/1250000000 : ℝ), (1351011297/2500000000 : ℝ)] ![(43194286494113/100000000000000 : ℝ), (763894154487/6250000000000 : ℝ), (2786462938283/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055056483/2000000000 : ℝ)|^1075 ≤ (43194286494113/100000000000000 : ℝ)^819
        have hw : |(1055056483/2000000000 : ℝ)|=(1055056483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-252027599/1250000000 : ℝ)|^1075 ≤ (763894154487/6250000000000 : ℝ)^819
        have hw : |(-252027599/1250000000 : ℝ)|=(252027599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351011297/2500000000 : ℝ)|^1075 ≤ (2786462938283/6250000000000 : ℝ)^819
        have hw : |(1351011297/2500000000 : ℝ)|=(1351011297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_10 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1318820523/2500000000 : ℝ)*x 0 + (675505697/1250000000 : ℝ)*x 1 + (-2016220701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318820523/2500000000 : ℝ)^1075 ≤ (1349821344459/3125000000000 : ℝ)^819 := by
    have hnat : (1318820523 : ℕ)^1075*3125000000000^819 ≤ 1349821344459^819*2500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318820523 2500000000 1349821344459 3125000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675505697/1250000000 : ℝ)^1075 ≤ (5572926401761/12500000000000 : ℝ)^819 := by
    have hnat : (675505697 : ℕ)^1075*12500000000000^819 ≤ 5572926401761^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675505697 1250000000 5572926401761 12500000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016220701/10000000000 : ℝ)^1075 ≤ (12222305747721/100000000000000 : ℝ)^819 := by
    have hnat : (2016220701 : ℕ)^1075*100000000000000^819 ≤ 12222305747721^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016220701 10000000000 12222305747721 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318820523/2500000000 : ℝ), (675505697/1250000000 : ℝ), (-2016220701/10000000000 : ℝ)] ![(1349821344459/3125000000000 : ℝ), (5572926401761/12500000000000 : ℝ), (12222305747721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318820523/2500000000 : ℝ)|^1075 ≤ (1349821344459/3125000000000 : ℝ)^819
        have hw : |(1318820523/2500000000 : ℝ)|=(1318820523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675505697/1250000000 : ℝ)|^1075 ≤ (5572926401761/12500000000000 : ℝ)^819
        have hw : |(675505697/1250000000 : ℝ)|=(675505697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2016220701/10000000000 : ℝ)|^1075 ≤ (12222305747721/100000000000000 : ℝ)^819
        have hw : |(-2016220701/10000000000 : ℝ)|=(2016220701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_11 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (281759031/625000000 : ℝ)*x 0 + (530031457/1250000000 : ℝ)*x 1 + (848050427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (281759031/625000000 : ℝ)^1075 ≤ (1757177966181/5000000000000 : ℝ)^819 := by
    have hnat : (281759031 : ℕ)^1075*5000000000000^819 ≤ 1757177966181^819*625000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281759031 625000000 1757177966181 5000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530031457/1250000000 : ℝ)^1075 ≤ (3242821792149/10000000000000 : ℝ)^819 := by
    have hnat : (530031457 : ℕ)^1075*10000000000000^819 ≤ 3242821792149^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530031457 1250000000 3242821792149 10000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848050427/2000000000 : ℝ)^1075 ≤ (32428222729789/100000000000000 : ℝ)^819 := by
    have hnat : (848050427 : ℕ)^1075*100000000000000^819 ≤ 32428222729789^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848050427 2000000000 32428222729789 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(281759031/625000000 : ℝ), (530031457/1250000000 : ℝ), (848050427/2000000000 : ℝ)] ![(1757177966181/5000000000000 : ℝ), (3242821792149/10000000000000 : ℝ), (32428222729789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(281759031/625000000 : ℝ)|^1075 ≤ (1757177966181/5000000000000 : ℝ)^819
        have hw : |(281759031/625000000 : ℝ)|=(281759031/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530031457/1250000000 : ℝ)|^1075 ≤ (3242821792149/10000000000000 : ℝ)^819
        have hw : |(530031457/1250000000 : ℝ)|=(530031457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848050427/2000000000 : ℝ)|^1075 ≤ (32428222729789/100000000000000 : ℝ)^819
        have hw : |(848050427/2000000000 : ℝ)|=(848050427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_12 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-77980597/400000000 : ℝ)*x 0 + (273697901/500000000 : ℝ)*x 1 + (5253812989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77980597/400000000 : ℝ)^1075 ≤ (22840440069/195312500000 : ℝ)^819 := by
    have hnat : (77980597 : ℕ)^1075*195312500000^819 ≤ 22840440069^819*400000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77980597 400000000 22840440069 195312500000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273697901/500000000 : ℝ)^1075 ≤ (1416937584811/3125000000000 : ℝ)^819 := by
    have hnat : (273697901 : ℕ)^1075*3125000000000^819 ≤ 1416937584811^819*500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273697901 500000000 1416937584811 3125000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253812989/10000000000 : ℝ)^1075 ≤ (1718547678577/4000000000000 : ℝ)^819 := by
    have hnat : (5253812989 : ℕ)^1075*4000000000000^819 ≤ 1718547678577^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253812989 10000000000 1718547678577 4000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77980597/400000000 : ℝ), (273697901/500000000 : ℝ), (5253812989/10000000000 : ℝ)] ![(22840440069/195312500000 : ℝ), (1416937584811/3125000000000 : ℝ), (1718547678577/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77980597/400000000 : ℝ)|^1075 ≤ (22840440069/195312500000 : ℝ)^819
        have hw : |(-77980597/400000000 : ℝ)|=(77980597/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273697901/500000000 : ℝ)|^1075 ≤ (1416937584811/3125000000000 : ℝ)^819
        have hw : |(273697901/500000000 : ℝ)|=(273697901/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253812989/10000000000 : ℝ)|^1075 ≤ (1718547678577/4000000000000 : ℝ)^819
        have hw : |(5253812989/10000000000 : ℝ)|=(5253812989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_13 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2690407109/5000000000 : ℝ)*x 0 + (-1038258063/5000000000 : ℝ)*x 1 + (5253813143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690407109/5000000000 : ℝ)^1075 ≤ (44332013526721/100000000000000 : ℝ)^819 := by
    have hnat : (2690407109 : ℕ)^1075*100000000000000^819 ≤ 44332013526721^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690407109 5000000000 44332013526721 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038258063/5000000000 : ℝ)^1075 ≤ (12704292844193/100000000000000 : ℝ)^819 := by
    have hnat : (1038258063 : ℕ)^1075*100000000000000^819 ≤ 12704292844193^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038258063 5000000000 12704292844193 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253813143/10000000000 : ℝ)^1075 ≤ (42963693617423/100000000000000 : ℝ)^819 := by
    have hnat : (5253813143 : ℕ)^1075*100000000000000^819 ≤ 42963693617423^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253813143 10000000000 42963693617423 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690407109/5000000000 : ℝ), (-1038258063/5000000000 : ℝ), (5253813143/10000000000 : ℝ)] ![(44332013526721/100000000000000 : ℝ), (12704292844193/100000000000000 : ℝ), (42963693617423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690407109/5000000000 : ℝ)|^1075 ≤ (44332013526721/100000000000000 : ℝ)^819
        have hw : |(2690407109/5000000000 : ℝ)|=(2690407109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1038258063/5000000000 : ℝ)|^1075 ≤ (12704292844193/100000000000000 : ℝ)^819
        have hw : |(-1038258063/5000000000 : ℝ)|=(1038258063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253813143/10000000000 : ℝ)|^1075 ≤ (42963693617423/100000000000000 : ℝ)^819
        have hw : |(5253813143/10000000000 : ℝ)|=(5253813143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_14 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2690407289/5000000000 : ℝ)*x 0 + (5253812901/10000000000 : ℝ)*x 1 + (-519128991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690407289/5000000000 : ℝ)^1075 ≤ (4433201741983/10000000000000 : ℝ)^819 := by
    have hnat : (2690407289 : ℕ)^1075*10000000000000^819 ≤ 4433201741983^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690407289 5000000000 4433201741983 10000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253812901/10000000000 : ℝ)^1075 ≤ (8592738203971/20000000000000 : ℝ)^819 := by
    have hnat : (5253812901 : ℕ)^1075*20000000000000^819 ≤ 8592738203971^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253812901 10000000000 8592738203971 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519128991/2500000000 : ℝ)^1075 ≤ (12704291543261/100000000000000 : ℝ)^819 := by
    have hnat : (519128991 : ℕ)^1075*100000000000000^819 ≤ 12704291543261^819*2500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519128991 2500000000 12704291543261 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690407289/5000000000 : ℝ), (5253812901/10000000000 : ℝ), (-519128991/2500000000 : ℝ)] ![(4433201741983/10000000000000 : ℝ), (8592738203971/20000000000000 : ℝ), (12704291543261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690407289/5000000000 : ℝ)|^1075 ≤ (4433201741983/10000000000000 : ℝ)^819
        have hw : |(2690407289/5000000000 : ℝ)|=(2690407289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253812901/10000000000 : ℝ)|^1075 ≤ (8592738203971/20000000000000 : ℝ)^819
        have hw : |(5253812901/10000000000 : ℝ)|=(5253812901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519128991/2500000000 : ℝ)|^1075 ≤ (12704291543261/100000000000000 : ℝ)^819
        have hw : |(-519128991/2500000000 : ℝ)|=(519128991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_box_15 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (103780849/250000000 : ℝ)*x 0 + (55233771/125000000 : ℝ)*x 1 + (1104675457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103780849/250000000 : ℝ)^1075 ≤ (31537586227911/100000000000000 : ℝ)^819 := by
    have hnat : (103780849 : ℕ)^1075*100000000000000^819 ≤ 31537586227911^819*250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103780849 250000000 31537586227911 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55233771/125000000 : ℝ)^1075 ≤ (17115603063839/50000000000000 : ℝ)^819 := by
    have hnat : (55233771 : ℕ)^1075*50000000000000^819 ≤ 17115603063839^819*125000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55233771 125000000 17115603063839 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104675457/2500000000 : ℝ)^1075 ≤ (34231207632599/100000000000000 : ℝ)^819 := by
    have hnat : (1104675457 : ℕ)^1075*100000000000000^819 ≤ 34231207632599^819*2500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104675457 2500000000 34231207632599 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103780849/250000000 : ℝ), (55233771/125000000 : ℝ), (1104675457/2500000000 : ℝ)] ![(31537586227911/100000000000000 : ℝ), (17115603063839/50000000000000 : ℝ), (34231207632599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103780849/250000000 : ℝ)|^1075 ≤ (31537586227911/100000000000000 : ℝ)^819
        have hw : |(103780849/250000000 : ℝ)|=(103780849/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55233771/125000000 : ℝ)|^1075 ≤ (17115603063839/50000000000000 : ℝ)^819
        have hw : |(55233771/125000000 : ℝ)|=(55233771/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1104675457/2500000000 : ℝ)|^1075 ≤ (34231207632599/100000000000000 : ℝ)^819
        have hw : |(1104675457/2500000000 : ℝ)|=(1104675457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1340_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2229/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12571/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58937/100000 : ℝ) ∧ (79943/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10543/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2229/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2229/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2229/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2229/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2229/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2229/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2229/20000 : ℝ) ^ (4299/1024 : ℝ) ≤ (9986455253337171/100000000000000000000 : ℝ) := by
    have hpowers : (2229/20000 : ℝ)^4299 ≤ (9986455253337171/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2229 : ℕ)^4299*100000000000000000000^1024 ≤ 9986455253337171^1024*20000^4299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2229 20000 9986455253337171 100000000000000000000 4299 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2229/20000 : ℝ)) (X := (9986455253337171/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2941/20000 : ℝ) ^ (4299/1024 : ℝ) ≤ (15987721185099313/50000000000000000000 : ℝ) := by
    have hpowers : (2941/20000 : ℝ)^4299 ≤ (15987721185099313/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2941 : ℕ)^4299*50000000000000000000^1024 ≤ 15987721185099313^1024*20000^4299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2941 20000 15987721185099313 50000000000000000000 4299 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2941/20000 : ℝ)) (X := (15987721185099313/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009986455253337171/50000000000000000000 : ℝ) ≤ (5000237854205491/5000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (50009986455253337171/50000000000000000000 : ℝ)^1024 ≤ (5000237854205491/5000000000000000 : ℝ)^4299 := by
      have hnat : (50009986455253337171 : ℕ)^1024*5000000000000000^4299 ≤ 5000237854205491^4299*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009986455253337171 50000000000000000000 5000237854205491 5000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000237854205491/5000000000000000 : ℝ)) (X := (50009986455253337171/50000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041961897623535797/100000000000000000000 : ℝ) ≤ (10000999351406303/10000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (100041961897623535797/100000000000000000000 : ℝ)^1024 ≤ (10000999351406303/10000000000000000 : ℝ)^4299 := by
      have hnat : (100041961897623535797 : ℕ)^1024*10000000000000000^4299 ≤ 10000999351406303^4299*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041961897623535797 100000000000000000000 10000999351406303 10000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000999351406303/10000000000000000 : ℝ)) (X := (100041961897623535797/100000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015987721185099313/25000000000000000000 : ℝ) ≤ (1250190374300203/1250000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (25015987721185099313/25000000000000000000 : ℝ)^1024 ≤ (1250190374300203/1250000000000000 : ℝ)^4299 := by
      have hnat : (25015987721185099313 : ℕ)^1024*1250000000000000^4299 ≤ 1250190374300203^4299*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015987721185099313 25000000000000000000 1250190374300203 1250000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250190374300203/1250000000000000 : ℝ)) (X := (25015987721185099313/25000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9986455253337171/100000000000000000000 : ℝ) ≤ ((3559002151957739083/3560000000000000000 : ℝ)+2*(523642995321/356000000000000 : ℝ)*(2229/20000 : ℝ))^(4299/1024 : ℝ) := by
    rw [show (3559002151957739083/3560000000000000000 : ℝ)+2*(523642995321/356000000000000 : ℝ)*(2229/20000 : ℝ)=(5000237854205491/5000000000000000 : ℝ) by norm_num, show 1+2*(9986455253337171/100000000000000000000 : ℝ)=(50009986455253337171/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15987721185099313/50000000000000000000 : ℝ)+(9986455253337171/100000000000000000000 : ℝ) ≤ ((3559002151957739083/3560000000000000000 : ℝ)+(523642995321/356000000000000 : ℝ)*((2941/20000 : ℝ)+(2229/20000 : ℝ)))^(4299/1024 : ℝ) := by
    rw [show (3559002151957739083/3560000000000000000 : ℝ)+(523642995321/356000000000000 : ℝ)*((2941/20000 : ℝ)+(2229/20000 : ℝ))=(10000999351406303/10000000000000000 : ℝ) by norm_num, show 1+(15987721185099313/50000000000000000000 : ℝ)+(9986455253337171/100000000000000000000 : ℝ)=(100041961897623535797/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15987721185099313/50000000000000000000 : ℝ) ≤ ((3559002151957739083/3560000000000000000 : ℝ)+2*(523642995321/356000000000000 : ℝ)*(2941/20000 : ℝ))^(4299/1024 : ℝ) := by
    rw [show (3559002151957739083/3560000000000000000 : ℝ)+2*(523642995321/356000000000000 : ℝ)*(2941/20000 : ℝ)=(1250190374300203/1250000000000000 : ℝ) by norm_num, show 1+2*(15987721185099313/50000000000000000000 : ℝ)=(25015987721185099313/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3559002151957739083/3560000000000000000 : ℝ)*(X 1 0+X 2 0)+(523642995321/356000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (2229/20000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (3559002151957739083/3560000000000000000 : ℝ)) (alpha := (523642995321/356000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3559002151957739083/3560000000000000000 : ℝ)*(X 0 1+X 2 1)+(523642995321/356000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (2229/20000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (3559002151957739083/3560000000000000000 : ℝ)) (alpha := (523642995321/356000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3559002151957739083/3560000000000000000 : ℝ)*(X 0 2+X 1 2)+(523642995321/356000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (2229/20000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (3559002151957739083/3560000000000000000 : ℝ)) (alpha := (523642995321/356000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1878286743/10000000000 : ℝ)*X 0 0+(5390024679/10000000000 : ℝ)*X 0 1+(5390024529/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285136449/10000000000 : ℝ)*X 1 0+(-1010988887/5000000000 : ℝ)*X 1 1+(42109567/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642568127/5000000000 : ℝ)*X 2 0+(673753099/1250000000 : ℝ)*X 2 1+(-404395549/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4475383531/10000000000 : ℝ)*X 0 0+(4256919797/10000000000 : ℝ)*X 0 1+(133028747/312500000 : ℝ)*X 0 2+(4475383531/10000000000 : ℝ)*X 1 0+(4256919797/10000000000 : ℝ)*X 1 1+(133028747/312500000 : ℝ)*X 1 2+(4475383531/10000000000 : ℝ)*X 2 0+(4256919797/10000000000 : ℝ)*X 2 1+(133028747/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1107935139/5000000000 : ℝ)*X 0 0+(2632440833/5000000000 : ℝ)*X 0 1+(1316220187/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((671630379/1250000000 : ℝ)*X 1 0+(-32377807/156250000 : ℝ)*X 1 1+(5264880429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1074608467/2000000000 : ℝ)*X 2 0+(41131881/78125000 : ℝ)*X 2 1+(-2072180133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1044495921/2500000000 : ℝ)*X 0 0+(4405565653/10000000000 : ℝ)*X 0 1+(4405566559/10000000000 : ℝ)*X 0 2+(1044495921/2500000000 : ℝ)*X 1 0+(4405565653/10000000000 : ℝ)*X 1 1+(4405566559/10000000000 : ℝ)*X 1 2+(1044495921/2500000000 : ℝ)*X 2 0+(4405565653/10000000000 : ℝ)*X 2 1+(4405566559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2144983971/10000000000 : ℝ)*X 0 0+(5178737853/10000000000 : ℝ)*X 0 1+(1080809051/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1055056483/2000000000 : ℝ)*X 1 0+(-252027599/1250000000 : ℝ)*X 1 1+(1351011297/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1318820523/2500000000 : ℝ)*X 2 0+(675505697/1250000000 : ℝ)*X 2 1+(-2016220701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((281759031/625000000 : ℝ)*X 0 0+(530031457/1250000000 : ℝ)*X 0 1+(848050427/2000000000 : ℝ)*X 0 2+(281759031/625000000 : ℝ)*X 1 0+(530031457/1250000000 : ℝ)*X 1 1+(848050427/2000000000 : ℝ)*X 1 2+(281759031/625000000 : ℝ)*X 2 0+(530031457/1250000000 : ℝ)*X 2 1+(848050427/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-77980597/400000000 : ℝ)*X 0 0+(273697901/500000000 : ℝ)*X 0 1+(5253812989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2690407109/5000000000 : ℝ)*X 1 0+(-1038258063/5000000000 : ℝ)*X 1 1+(5253813143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690407289/5000000000 : ℝ)*X 2 0+(5253812901/10000000000 : ℝ)*X 2 1+(-519128991/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((103780849/250000000 : ℝ)*X 0 0+(55233771/125000000 : ℝ)*X 0 1+(1104675457/2500000000 : ℝ)*X 0 2+(103780849/250000000 : ℝ)*X 1 0+(55233771/125000000 : ℝ)*X 1 1+(1104675457/2500000000 : ℝ)*X 1 2+(103780849/250000000 : ℝ)*X 2 0+(55233771/125000000 : ℝ)*X 2 1+(1104675457/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12571/20000 : ℝ) ≤ (-111876638604411706068551488523931/178000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5482883/25000000000000 : ℝ)*(lower3) + (163674963/50000000000000 : ℝ)*(lower4) + (7319181/50000000000000 : ℝ)*(lower5) + (2918355311211273/100000000000000 : ℝ)*(major0) + (2918355311211273/100000000000000 : ℝ)*(major1) + (2918355311211273/100000000000000 : ℝ)*(major2) + (16520154183/100000000000000 : ℝ)*(sp1) + (22276384629/100000000000000 : ℝ)*(sp2) + (4011594107/50000000000000 : ℝ)*(sp3) + (992645189691581/25000000000000 : ℝ)*(sp4) + (496321446096717/12500000000000 : ℝ)*(sp5) + (3970565812543291/100000000000000 : ℝ)*(sp6) + (471766297923249/25000000000000 : ℝ)*(sp7) + (1466032319/20000000000000 : ℝ)*(sp8) + (188707321488121/10000000000000 : ℝ)*(f.failure) + (49632351111599/1250000000000 : ℝ)*(f.sum) + (8893591811833/17800000000000000000000000000 : ℝ)*base65 + (4138240447418612659/356000000000000000000000000000000 : ℝ)*base67 + (2223268732026612659/356000000000000000000000000000000 : ℝ)*base69 + (1659984058106612659/356000000000000000000000000000000 : ℝ)*base71 + (7774618239167/17800000000000000000000000000 : ℝ)*base74 + (2731101993326612659/356000000000000000000000000000000 : ℝ)*base75 + (1422553228714612659/356000000000000000000000000000000 : ℝ)*base77 + (2802571759446612659/356000000000000000000000000000000 : ℝ)*base79 + (53690208379967/17800000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6699901/1000000000000000000000 : ℝ)*base90 + (6699901/1000000000000000000000 : ℝ)*base92 + (6699901/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58937/100000 : ℝ) ≤ (13114096972326028382255954150577/22250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14637411/100000000000000 : ℝ)*(lower1) + (25321491/100000000000000 : ℝ)*(upper2) + (582731/20000000000000 : ℝ)*(upper3) + (9729769/100000000000000 : ℝ)*(lower5) + (746744421283673/25000000000000 : ℝ)*(major0) + (746744421283673/25000000000000 : ℝ)*(major1) + (746744421283673/25000000000000 : ℝ)*(major2) + (502857731637321/12500000000000 : ℝ)*(sp0) + (4022862820515413/100000000000000 : ℝ)*(sp1) + (2011428388604737/50000000000000 : ℝ)*(sp2) + (96572264974037/5000000000000 : ℝ)*(sp3) + (6043305939/100000000000000 : ℝ)*(sp6) + (663048769/100000000000000 : ℝ)*(sp7) + (193483369/20000000000000 : ℝ)*(sp8) + (482861490632377/25000000000000 : ℝ)*(f.failure) + (4022862820515413/100000000000000 : ℝ)*(f.sum) + (19537563061617/4450000000000000000000000000 : ℝ)*base66 + (257232920463778141/89000000000000000000000000000000 : ℝ)*base68 + (139411120360221859/89000000000000000000000000000000 : ℝ)*base69 + (108036166594778141/89000000000000000000000000000000 : ℝ)*base72 + (5774638029717/4450000000000000000000000000 : ℝ)*base74 + (399278729388778141/89000000000000000000000000000000 : ℝ)*base76 + (230946014230778141/89000000000000000000000000000000 : ℝ)*base78 + (243675292630778141/89000000000000000000000000000000 : ℝ)*base80 + (50315527028267/4450000000000000000000000000 : ℝ)*base82 + (1410237/2500000000000000000000 : ℝ)*base90 + (1410237/2500000000000000000000 : ℝ)*base92 + (1410237/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79943/100000 : ℝ) ≤ (35575594729014597040555919029251/44500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16314993/20000000000000 : ℝ)*(upper0) + (20476339/50000000000000 : ℝ)*(upper2) + (1170427/100000000000000 : ℝ)*(lower3) + (824793738127167/25000000000000 : ℝ)*(major0) + (824793738127167/25000000000000 : ℝ)*(major1) + (824793738127167/25000000000000 : ℝ)*(major2) + (699037193/25000000000000 : ℝ)*(sp0) + (103922643887/100000000000000 : ℝ)*(sp2) + (1257825527/4000000000000 : ℝ)*(sp3) + (554797181107679/12500000000000 : ℝ)*(sp8) + (138699433923701/3125000000000 : ℝ)*(sp9) + (2219138981457273/50000000000000 : ℝ)*(sp10) + (2133288188255911/100000000000000 : ℝ)*(sp11) + (410137057/25000000000000 : ℝ)*(sp12) + (1066659816947043/50000000000000 : ℝ)*(f.failure) + (138699433923701/3125000000000 : ℝ)*(f.sum) + (15077569967757/4450000000000000000000000000 : ℝ)*base65 + (1090958059101037861/89000000000000000000000000000000 : ℝ)*base67 + (544950633891037861/89000000000000000000000000000000 : ℝ)*base69 + (869839541487037861/89000000000000000000000000000000 : ℝ)*base71 + (15458498271457/4450000000000000000000000000 : ℝ)*base73 + (791502156227037861/89000000000000000000000000000000 : ℝ)*base75 + (463045795237037861/89000000000000000000000000000000 : ℝ)*base77 + (312076627817037861/89000000000000000000000000000000 : ℝ)*base79 + (2225654858807/4450000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (67464783/5000000000000000000000 : ℝ)*base90 + (67464783/5000000000000000000000 : ℝ)*base92 + (67464783/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-10543/12500 : ℝ) ≤ (-1876604665749306861016159219869/2225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23280669/50000000000000 : ℝ)*(lower1) + (114479989/100000000000000 : ℝ)*(lower2) + (3452049/4000000000000 : ℝ)*(upper5) + (83390436177619/2500000000000 : ℝ)*(major0) + (83390436177619/2500000000000 : ℝ)*(major1) + (83390436177619/2500000000000 : ℝ)*(major2) + (4139108559/50000000000000 : ℝ)*(sp0) + (2018702987/2500000000000 : ℝ)*(sp5) + (143844711033/100000000000000 : ℝ)*(sp6) + (4732488267/100000000000000 : ℝ)*(sp7) + (4542456385104833/100000000000000 : ℝ)*(sp12) + (4542383915202471/100000000000000 : ℝ)*(sp13) + (2271160409305459/50000000000000 : ℝ)*(sp14) + (8425310257719/390625000000 : ℝ)*(sp15) + (215688415846433/10000000000000 : ℝ)*(f.failure) + (4542464663321951/100000000000000 : ℝ)*(f.sum) + (293190664497/222500000000000000000000000 : ℝ)*base65 + (56628794158526623/8900000000000000000000000000000 : ℝ)*base68 + (60582395332426623/8900000000000000000000000000000 : ℝ)*base70 + (29183138390226623/8900000000000000000000000000000 : ℝ)*base72 + (687860922563/222500000000000000000000000 : ℝ)*base74 + (134468148457026623/8900000000000000000000000000000 : ℝ)*base76 + (6310518882873377/8900000000000000000000000000000 : ℝ)*base77 + (10042640210526623/8900000000000000000000000000000 : ℝ)*base80 + (2156036206581/445000000000000000000000000 : ℝ)*base82 + (4754373/1000000000000000000000 : ℝ)*base90 + (4754373/1000000000000000000000 : ℝ)*base92 + (4754373/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1340_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2229/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12571/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58937/100000 : ℝ) else (79943/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10543/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1340_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1340_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (348/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12571/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58937/100000 : ℝ) else (79943/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10543/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1340_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1340_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1340_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (348/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12571/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58937/100000 : ℝ) else (79943/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10543/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1340_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
