-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1060_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:02:54.173229+00:00
-- url     : https://prove2.me/submissions/48cc289e-c2b9-4a2c-9071-3f918a5e1066

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
theorem support_rectangle_w1060_s6_0 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-441334979/2000000000 : ℝ)*x 0 + (2697519709/5000000000 : ℝ)*x 1 + (5263797971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441334979/2000000000 : ℝ)^8253 ≤ (13400931702487/100000000000000 : ℝ)^6205 := by
    have hnat : (441334979 : ℕ)^8253*100000000000000^6205 ≤ 13400931702487^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441334979 2000000000 13400931702487 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697519709/5000000000 : ℝ)^8253 ≤ (22004308981789/50000000000000 : ℝ)^6205 := by
    have hnat : (2697519709 : ℕ)^8253*50000000000000^6205 ≤ 22004308981789^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697519709 5000000000 22004308981789 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263797971/10000000000 : ℝ)^8253 ≤ (42590450317107/100000000000000 : ℝ)^6205 := by
    have hnat : (5263797971 : ℕ)^8253*100000000000000^6205 ≤ 42590450317107^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263797971 10000000000 42590450317107 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441334979/2000000000 : ℝ), (2697519709/5000000000 : ℝ), (5263797971/10000000000 : ℝ)] ![(13400931702487/100000000000000 : ℝ), (22004308981789/50000000000000 : ℝ), (42590450317107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441334979/2000000000 : ℝ)|^8253 ≤ (13400931702487/100000000000000 : ℝ)^6205
        have hw : |(-441334979/2000000000 : ℝ)|=(441334979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697519709/5000000000 : ℝ)|^8253 ≤ (22004308981789/50000000000000 : ℝ)^6205
        have hw : |(2697519709/5000000000 : ℝ)|=(2697519709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263797971/10000000000 : ℝ)|^8253 ≤ (42590450317107/100000000000000 : ℝ)^6205
        have hw : |(5263797971/10000000000 : ℝ)|=(5263797971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s6_1 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069027411/2000000000 : ℝ)*x 0 + (-2273272617/10000000000 : ℝ)*x 1 + (2631898989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069027411/2000000000 : ℝ)^8253 ≤ (1738721046073/4000000000000 : ℝ)^6205 := by
    have hnat : (1069027411 : ℕ)^8253*4000000000000^6205 ≤ 1738721046073^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069027411 2000000000 1738721046073 4000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2273272617/10000000000 : ℝ)^8253 ≤ (13941523451683/100000000000000 : ℝ)^6205 := by
    have hnat : (2273272617 : ℕ)^8253*100000000000000^6205 ≤ 13941523451683^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273272617 10000000000 13941523451683 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631898989/5000000000 : ℝ)^8253 ≤ (1064761259811/2500000000000 : ℝ)^6205 := by
    have hnat : (2631898989 : ℕ)^8253*2500000000000^6205 ≤ 1064761259811^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631898989 5000000000 1064761259811 2500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069027411/2000000000 : ℝ), (-2273272617/10000000000 : ℝ), (2631898989/5000000000 : ℝ)] ![(1738721046073/4000000000000 : ℝ), (13941523451683/100000000000000 : ℝ), (1064761259811/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069027411/2000000000 : ℝ)|^8253 ≤ (1738721046073/4000000000000 : ℝ)^6205
        have hw : |(1069027411/2000000000 : ℝ)|=(1069027411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2273272617/10000000000 : ℝ)|^8253 ≤ (13941523451683/100000000000000 : ℝ)^6205
        have hw : |(-2273272617/10000000000 : ℝ)|=(2273272617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631898989/5000000000 : ℝ)|^8253 ≤ (1064761259811/2500000000000 : ℝ)^6205
        have hw : |(2631898989/5000000000 : ℝ)|=(2631898989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s6_2 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069027401/2000000000 : ℝ)*x 0 + (657974751/1250000000 : ℝ)*x 1 + (-2273272643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069027401/2000000000 : ℝ)^8253 ≤ (43468025611007/100000000000000 : ℝ)^6205 := by
    have hnat : (1069027401 : ℕ)^8253*100000000000000^6205 ≤ 43468025611007^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069027401 2000000000 43468025611007 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657974751/1250000000 : ℝ)^8253 ≤ (10647612678823/25000000000000 : ℝ)^6205 := by
    have hnat : (657974751 : ℕ)^8253*25000000000000^6205 ≤ 10647612678823^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657974751 1250000000 10647612678823 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273272643/10000000000 : ℝ)^8253 ≤ (3485380915941/25000000000000 : ℝ)^6205 := by
    have hnat : (2273272643 : ℕ)^8253*25000000000000^6205 ≤ 3485380915941^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273272643 10000000000 3485380915941 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069027401/2000000000 : ℝ), (657974751/1250000000 : ℝ), (-2273272643/10000000000 : ℝ)] ![(43468025611007/100000000000000 : ℝ), (10647612678823/25000000000000 : ℝ), (3485380915941/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069027401/2000000000 : ℝ)|^8253 ≤ (43468025611007/100000000000000 : ℝ)^6205
        have hw : |(1069027401/2000000000 : ℝ)|=(1069027401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657974751/1250000000 : ℝ)|^8253 ≤ (10647612678823/25000000000000 : ℝ)^6205
        have hw : |(657974751/1250000000 : ℝ)|=(657974751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2273272643/10000000000 : ℝ)|^8253 ≤ (3485380915941/25000000000000 : ℝ)^6205
        have hw : |(-2273272643/10000000000 : ℝ)|=(2273272643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s6_3 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188163543/5000000000 : ℝ)*x 0 + (2124892663/5000000000 : ℝ)*x 1 + (140834187/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188163543/5000000000 : ℝ)^8253 ≤ (33316222615641/100000000000000 : ℝ)^6205 := by
    have hnat : (2188163543 : ℕ)^8253*100000000000000^6205 ≤ 33316222615641^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188163543 5000000000 33316222615641 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124892663/5000000000 : ℝ)^8253 ≤ (32041079372803/100000000000000 : ℝ)^6205 := by
    have hnat : (2124892663 : ℕ)^8253*100000000000000^6205 ≤ 32041079372803^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124892663 5000000000 32041079372803 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140834187/312500000 : ℝ)^8253 ≤ (34642697990997/100000000000000 : ℝ)^6205 := by
    have hnat : (140834187 : ℕ)^8253*100000000000000^6205 ≤ 34642697990997^6205*312500000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140834187 312500000 34642697990997 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188163543/5000000000 : ℝ), (2124892663/5000000000 : ℝ), (140834187/312500000 : ℝ)] ![(33316222615641/100000000000000 : ℝ), (32041079372803/100000000000000 : ℝ), (34642697990997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188163543/5000000000 : ℝ)|^8253 ≤ (33316222615641/100000000000000 : ℝ)^6205
        have hw : |(2188163543/5000000000 : ℝ)|=(2188163543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2124892663/5000000000 : ℝ)|^8253 ≤ (32041079372803/100000000000000 : ℝ)^6205
        have hw : |(2124892663/5000000000 : ℝ)|=(2124892663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140834187/312500000 : ℝ)|^8253 ≤ (34642697990997/100000000000000 : ℝ)^6205
        have hw : |(140834187/312500000 : ℝ)|=(140834187/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s6_4 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2206680089/10000000000 : ℝ)*x 0 + (1316032363/2500000000 : ℝ)*x 1 + (5394706747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2206680089/10000000000 : ℝ)^8253 ≤ (13400973656047/100000000000000 : ℝ)^6205 := by
    have hnat : (2206680089 : ℕ)^8253*100000000000000^6205 ≤ 13400973656047^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206680089 10000000000 13400973656047 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316032363/2500000000 : ℝ)^8253 ≤ (4259401767131/10000000000000 : ℝ)^6205 := by
    have hnat : (1316032363 : ℕ)^8253*10000000000000^6205 ≤ 4259401767131^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316032363 2500000000 4259401767131 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394706747/10000000000 : ℝ)^8253 ≤ (44005008657677/100000000000000 : ℝ)^6205 := by
    have hnat : (5394706747 : ℕ)^8253*100000000000000^6205 ≤ 44005008657677^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394706747 10000000000 44005008657677 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2206680089/10000000000 : ℝ), (1316032363/2500000000 : ℝ), (5394706747/10000000000 : ℝ)] ![(13400973656047/100000000000000 : ℝ), (4259401767131/10000000000000 : ℝ), (44005008657677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2206680089/10000000000 : ℝ)|^8253 ≤ (13400973656047/100000000000000 : ℝ)^6205
        have hw : |(-2206680089/10000000000 : ℝ)|=(2206680089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316032363/2500000000 : ℝ)|^8253 ≤ (4259401767131/10000000000000 : ℝ)^6205
        have hw : |(1316032363/2500000000 : ℝ)|=(1316032363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394706747/10000000000 : ℝ)|^8253 ≤ (44005008657677/100000000000000 : ℝ)^6205
        have hw : |(5394706747/10000000000 : ℝ)|=(5394706747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s6_5 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312095771/10000000000 : ℝ)*x 0 + (-214236387/1000000000 : ℝ)*x 1 + (5394706747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312095771/10000000000 : ℝ)^8253 ≤ (8622200962993/20000000000000 : ℝ)^6205 := by
    have hnat : (5312095771 : ℕ)^8253*20000000000000^6205 ≤ 8622200962993^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312095771 10000000000 8622200962993 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214236387/1000000000 : ℝ)^8253 ≤ (6441993257009/50000000000000 : ℝ)^6205 := by
    have hnat : (214236387 : ℕ)^8253*50000000000000^6205 ≤ 6441993257009^6205*1000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214236387 1000000000 6441993257009 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394706747/10000000000 : ℝ)^8253 ≤ (44005008657677/100000000000000 : ℝ)^6205 := by
    have hnat : (5394706747 : ℕ)^8253*100000000000000^6205 ≤ 44005008657677^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394706747 10000000000 44005008657677 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312095771/10000000000 : ℝ), (-214236387/1000000000 : ℝ), (5394706747/10000000000 : ℝ)] ![(8622200962993/20000000000000 : ℝ), (6441993257009/50000000000000 : ℝ), (44005008657677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312095771/10000000000 : ℝ)|^8253 ≤ (8622200962993/20000000000000 : ℝ)^6205
        have hw : |(5312095771/10000000000 : ℝ)|=(5312095771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-214236387/1000000000 : ℝ)|^8253 ≤ (6441993257009/50000000000000 : ℝ)^6205
        have hw : |(-214236387/1000000000 : ℝ)|=(214236387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394706747/10000000000 : ℝ)|^8253 ≤ (44005008657677/100000000000000 : ℝ)^6205
        have hw : |(5394706747/10000000000 : ℝ)|=(5394706747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s6_6 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312095771/10000000000 : ℝ)*x 0 + (5394706747/10000000000 : ℝ)*x 1 + (-214236387/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312095771/10000000000 : ℝ)^8253 ≤ (8622200962993/20000000000000 : ℝ)^6205 := by
    have hnat : (5312095771 : ℕ)^8253*20000000000000^6205 ≤ 8622200962993^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312095771 10000000000 8622200962993 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394706747/10000000000 : ℝ)^8253 ≤ (44005008657677/100000000000000 : ℝ)^6205 := by
    have hnat : (5394706747 : ℕ)^8253*100000000000000^6205 ≤ 44005008657677^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394706747 10000000000 44005008657677 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214236387/1000000000 : ℝ)^8253 ≤ (6441993257009/50000000000000 : ℝ)^6205 := by
    have hnat : (214236387 : ℕ)^8253*50000000000000^6205 ≤ 6441993257009^6205*1000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214236387 1000000000 6441993257009 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312095771/10000000000 : ℝ), (5394706747/10000000000 : ℝ), (-214236387/1000000000 : ℝ)] ![(8622200962993/20000000000000 : ℝ), (44005008657677/100000000000000 : ℝ), (6441993257009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312095771/10000000000 : ℝ)|^8253 ≤ (8622200962993/20000000000000 : ℝ)^6205
        have hw : |(5312095771/10000000000 : ℝ)|=(5312095771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394706747/10000000000 : ℝ)|^8253 ≤ (44005008657677/100000000000000 : ℝ)^6205
        have hw : |(5394706747/10000000000 : ℝ)|=(5394706747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214236387/1000000000 : ℝ)|^8253 ≤ (6441993257009/50000000000000 : ℝ)^6205
        have hw : |(-214236387/1000000000 : ℝ)|=(214236387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s6_7 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094084321/2500000000 : ℝ)*x 0 + (2253022551/5000000000 : ℝ)*x 1 + (1062609143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094084321/2500000000 : ℝ)^8253 ≤ (16658162937713/50000000000000 : ℝ)^6205 := by
    have hnat : (1094084321 : ℕ)^8253*50000000000000^6205 ≤ 16658162937713^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094084321 2500000000 16658162937713 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253022551/5000000000 : ℝ)^8253 ≤ (3463606393543/10000000000000 : ℝ)^6205 := by
    have hnat : (2253022551 : ℕ)^8253*10000000000000^6205 ≤ 3463606393543^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253022551 5000000000 3463606393543 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062609143/2500000000 : ℝ)^8253 ≤ (16023805085437/50000000000000 : ℝ)^6205 := by
    have hnat : (1062609143 : ℕ)^8253*50000000000000^6205 ≤ 16023805085437^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062609143 2500000000 16023805085437 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094084321/2500000000 : ℝ), (2253022551/5000000000 : ℝ), (1062609143/2500000000 : ℝ)] ![(16658162937713/50000000000000 : ℝ), (3463606393543/10000000000000 : ℝ), (16023805085437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094084321/2500000000 : ℝ)|^8253 ≤ (16658162937713/50000000000000 : ℝ)^6205
        have hw : |(1094084321/2500000000 : ℝ)|=(1094084321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253022551/5000000000 : ℝ)|^8253 ≤ (3463606393543/10000000000000 : ℝ)^6205
        have hw : |(2253022551/5000000000 : ℝ)|=(2253022551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062609143/2500000000 : ℝ)|^8253 ≤ (16023805085437/50000000000000 : ℝ)^6205
        have hw : |(1062609143/2500000000 : ℝ)|=(1062609143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1060_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11231/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14011/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11189/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11189/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11189/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11189/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11189/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11189/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11189/100000 : ℝ) ^ (2063/512 : ℝ) ≤ (14699333801700523/100000000000000000000 : ℝ) := by
    have hpowers : (11189/100000 : ℝ)^2063 ≤ (14699333801700523/100000000000000000000 : ℝ)^512 := by
      have hnat : (11189 : ℕ)^2063*100000000000000000000^512 ≤ 14699333801700523^512*100000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11189 100000 14699333801700523 100000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11189/100000 : ℝ)) (X := (14699333801700523/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1757/12500 : ℝ) ^ (2063/512 : ℝ) ≤ (18426888605500081/50000000000000000000 : ℝ) := by
    have hpowers : (1757/12500 : ℝ)^2063 ≤ (18426888605500081/50000000000000000000 : ℝ)^512 := by
      have hnat : (1757 : ℕ)^2063*50000000000000000000^512 ≤ 18426888605500081^512*12500^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1757 12500 18426888605500081 50000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1757/12500 : ℝ)) (X := (18426888605500081/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014699333801700523/50000000000000000000 : ℝ) ≤ (10000729542154911/10000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (50014699333801700523/50000000000000000000 : ℝ)^512 ≤ (10000729542154911/10000000000000000 : ℝ)^2063 := by
      have hnat : (50014699333801700523 : ℕ)^512*10000000000000000^2063 ≤ 10000729542154911^2063*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014699333801700523 50000000000000000000 10000729542154911 10000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000729542154911/10000000000000000 : ℝ)) (X := (50014699333801700523/50000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010310622202540137/20000000000000000000 : ℝ) ≤ (1250159901109923/1250000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (20010310622202540137/20000000000000000000 : ℝ)^512 ≤ (1250159901109923/1250000000000000 : ℝ)^2063 := by
      have hnat : (20010310622202540137 : ℕ)^512*1250000000000000^2063 ≤ 1250159901109923^2063*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010310622202540137 20000000000000000000 1250159901109923 1250000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250159901109923/1250000000000000 : ℝ)) (X := (20010310622202540137/20000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018426888605500081/25000000000000000000 : ℝ) ≤ (10001828875603857/10000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (25018426888605500081/25000000000000000000 : ℝ)^512 ≤ (10001828875603857/10000000000000000 : ℝ)^2063 := by
      have hnat : (25018426888605500081 : ℕ)^512*10000000000000000^2063 ≤ 10001828875603857^2063*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018426888605500081 25000000000000000000 10001828875603857 10000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001828875603857/10000000000000000 : ℝ)) (X := (25018426888605500081/25000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14699333801700523/100000000000000000000 : ℝ) ≤ ((28659791155397873043/28670000000000000000 : ℝ)+2*(549666724473/286700000000000 : ℝ)*(11189/100000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (28659791155397873043/28670000000000000000 : ℝ)+2*(549666724473/286700000000000 : ℝ)*(11189/100000 : ℝ)=(10000729542154911/10000000000000000 : ℝ) by norm_num, show 1+2*(14699333801700523/100000000000000000000 : ℝ)=(50014699333801700523/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18426888605500081/50000000000000000000 : ℝ)+(14699333801700523/100000000000000000000 : ℝ) ≤ ((28659791155397873043/28670000000000000000 : ℝ)+(549666724473/286700000000000 : ℝ)*((1757/12500 : ℝ)+(11189/100000 : ℝ)))^(2063/512 : ℝ) := by
    rw [show (28659791155397873043/28670000000000000000 : ℝ)+(549666724473/286700000000000 : ℝ)*((1757/12500 : ℝ)+(11189/100000 : ℝ))=(1250159901109923/1250000000000000 : ℝ) by norm_num, show 1+(18426888605500081/50000000000000000000 : ℝ)+(14699333801700523/100000000000000000000 : ℝ)=(20010310622202540137/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18426888605500081/50000000000000000000 : ℝ) ≤ ((28659791155397873043/28670000000000000000 : ℝ)+2*(549666724473/286700000000000 : ℝ)*(1757/12500 : ℝ))^(2063/512 : ℝ) := by
    rw [show (28659791155397873043/28670000000000000000 : ℝ)+2*(549666724473/286700000000000 : ℝ)*(1757/12500 : ℝ)=(10001828875603857/10000000000000000 : ℝ) by norm_num, show 1+2*(18426888605500081/50000000000000000000 : ℝ)=(25018426888605500081/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28659791155397873043/28670000000000000000 : ℝ)*(X 1 0+X 2 0)+(549666724473/286700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11189/100000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (28659791155397873043/28670000000000000000 : ℝ)) (alpha := (549666724473/286700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28659791155397873043/28670000000000000000 : ℝ)*(X 0 1+X 2 1)+(549666724473/286700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11189/100000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (28659791155397873043/28670000000000000000 : ℝ)) (alpha := (549666724473/286700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28659791155397873043/28670000000000000000 : ℝ)*(X 0 2+X 1 2)+(549666724473/286700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11189/100000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (28659791155397873043/28670000000000000000 : ℝ)) (alpha := (549666724473/286700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-441334979/2000000000 : ℝ)*X 0 0+(2697519709/5000000000 : ℝ)*X 0 1+(5263797971/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069027411/2000000000 : ℝ)*X 1 0+(-2273272617/10000000000 : ℝ)*X 1 1+(2631898989/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069027401/2000000000 : ℝ)*X 2 0+(657974751/1250000000 : ℝ)*X 2 1+(-2273272643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188163543/5000000000 : ℝ)*X 0 0+(2124892663/5000000000 : ℝ)*X 0 1+(140834187/312500000 : ℝ)*X 0 2+(2188163543/5000000000 : ℝ)*X 1 0+(2124892663/5000000000 : ℝ)*X 1 1+(140834187/312500000 : ℝ)*X 1 2+(2188163543/5000000000 : ℝ)*X 2 0+(2124892663/5000000000 : ℝ)*X 2 1+(140834187/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2206680089/10000000000 : ℝ)*X 0 0+(1316032363/2500000000 : ℝ)*X 0 1+(5394706747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312095771/10000000000 : ℝ)*X 1 0+(-214236387/1000000000 : ℝ)*X 1 1+(5394706747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312095771/10000000000 : ℝ)*X 2 0+(5394706747/10000000000 : ℝ)*X 2 1+(-214236387/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1094084321/2500000000 : ℝ)*X 0 0+(2253022551/5000000000 : ℝ)*X 0 1+(1062609143/2500000000 : ℝ)*X 0 2+(1094084321/2500000000 : ℝ)*X 1 0+(2253022551/5000000000 : ℝ)*X 1 1+(1062609143/2500000000 : ℝ)*X 1 2+(1094084321/2500000000 : ℝ)*X 2 0+(2253022551/5000000000 : ℝ)*X 2 1+(1062609143/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (625707867868527780176381673/57340000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (560559513/25000000000000 : ℝ)*(base19) + (2041740689/100000000000000 : ℝ)*(base23) + (69070269/100000000000000 : ℝ)*(lower2) + (38091979/12500000000000 : ℝ)*(upper3) + (15375149/10000000000000 : ℝ)*(upper5) + (230243277150863/4000000000000 : ℝ)*(major0) + (230243277150863/4000000000000 : ℝ)*(major1) + (230243277150863/4000000000000 : ℝ)*(major2) + (761960811967959/10000000000000 : ℝ)*(sp0) + (3809832064620457/50000000000000 : ℝ)*(sp1) + (3809832164869139/50000000000000 : ℝ)*(sp2) + (973115955049291/25000000000000 : ℝ)*(sp3) + (3640737461/6250000000000 : ℝ)*(sp4) + (1665106283/5000000000000 : ℝ)*(sp7) + (155699884892913/4000000000000 : ℝ)*(f.failure) + (3809833185739483/50000000000000 : ℝ)*(f.sum) + (2630406338603/573400000000000000000000000 : ℝ)*base66 + (1042943998985706109/114680000000000000000000000000000 : ℝ)*base67 + (947224352792346109/114680000000000000000000000000000 : ℝ)*base69 + (1445706779217733891/114680000000000000000000000000000 : ℝ)*base72 + (13260759665513/2867000000000000000000000000 : ℝ)*base73 + (2761648866283946109/114680000000000000000000000000000 : ℝ)*base75 + (474115650900666109/114680000000000000000000000000000 : ℝ)*base77 + (805795039105653891/114680000000000000000000000000000 : ℝ)*base80 + (10578138453881/2867000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2342203/400000000000000000000 : ℝ)*base89 + (2342203/400000000000000000000 : ℝ)*base91 + (2342203/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (437437093081641865080725949/143350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56890147/10000000000000 : ℝ)*(base19) + (309875749/50000000000000 : ℝ)*(base23) + (30608261/50000000000000 : ℝ)*(upper3) + (23163807/100000000000000 : ℝ)*(lower4) + (2505737/4000000000000 : ℝ)*(upper5) + (1157053111278581/20000000000000 : ℝ)*(major0) + (1157053111278581/20000000000000 : ℝ)*(major1) + (1157053111278581/20000000000000 : ℝ)*(major2) + (15337344327/100000000000000 : ℝ)*(sp1) + (3300407663/20000000000000 : ℝ)*(sp2) + (1531659746141763/20000000000000 : ℝ)*(sp4) + (3829141412231509/50000000000000 : ℝ)*(sp5) + (3829140804459501/50000000000000 : ℝ)*(sp6) + (3912232280359259/100000000000000 : ℝ)*(sp7) + (3912232280359259/100000000000000 : ℝ)*(f.failure) + (1531659746141763/20000000000000 : ℝ)*(f.sum) + (295829961697/1433500000000000000000000000 : ℝ)*base66 + (335310795848708017/573400000000000000000000000000000 : ℝ)*base68 + (6772285523125708017/573400000000000000000000000000000 : ℝ)*base70 + (5106182026269891983/573400000000000000000000000000000 : ℝ)*base71 + (31568787079/35837500000000000000000000 : ℝ)*base74 + (15852692904635508017/573400000000000000000000000000000 : ℝ)*base76 + (1221088149573708017/573400000000000000000000000000000 : ℝ)*base78 + (3790082283584308017/573400000000000000000000000000000 : ℝ)*base80 + (1458160915449/358375000000000000000000000 : ℝ)*base81 + (82798729/10000000000000000000000 : ℝ)*base89 + (82798729/10000000000000000000000 : ℝ)*base91 + (82798729/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1060_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1060_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1060_s7_0 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2206720033/10000000000 : ℝ)*x 0 + (2697281447/5000000000 : ℝ)*x 1 + (1316061123/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2206720033/10000000000 : ℝ)^8253 ≤ (13401296297293/100000000000000 : ℝ)^6205 := by
    have hnat : (2206720033 : ℕ)^8253*100000000000000^6205 ≤ 13401296297293^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206720033 10000000000 13401296297293 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697281447/5000000000 : ℝ)^8253 ≤ (11000861987703/25000000000000 : ℝ)^6205 := by
    have hnat : (2697281447 : ℕ)^8253*25000000000000^6205 ≤ 11000861987703^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697281447 5000000000 11000861987703 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316061123/2500000000 : ℝ)^8253 ≤ (2129762786687/5000000000000 : ℝ)^6205 := by
    have hnat : (1316061123 : ℕ)^8253*5000000000000^6205 ≤ 2129762786687^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316061123 2500000000 2129762786687 5000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2206720033/10000000000 : ℝ), (2697281447/5000000000 : ℝ), (1316061123/2500000000 : ℝ)] ![(13401296297293/100000000000000 : ℝ), (11000861987703/25000000000000 : ℝ), (2129762786687/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2206720033/10000000000 : ℝ)|^8253 ≤ (13401296297293/100000000000000 : ℝ)^6205
        have hw : |(-2206720033/10000000000 : ℝ)|=(2206720033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697281447/5000000000 : ℝ)|^8253 ≤ (11000861987703/25000000000000 : ℝ)^6205
        have hw : |(2697281447/5000000000 : ℝ)|=(2697281447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316061123/2500000000 : ℝ)|^8253 ≤ (2129762786687/5000000000000 : ℝ)^6205
        have hw : |(1316061123/2500000000 : ℝ)|=(1316061123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s7_1 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334063567/625000000 : ℝ)*x 0 + (-2272842297/10000000000 : ℝ)*x 1 + (5264244717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334063567/625000000 : ℝ)^8253 ≤ (4346672837731/10000000000000 : ℝ)^6205 := by
    have hnat : (334063567 : ℕ)^8253*10000000000000^6205 ≤ 4346672837731^6205*625000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334063567 625000000 4346672837731 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2272842297/10000000000 : ℝ)^8253 ≤ (13938013454759/100000000000000 : ℝ)^6205 := by
    have hnat : (2272842297 : ℕ)^8253*100000000000000^6205 ≤ 13938013454759^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272842297 10000000000 13938013454759 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264244717/10000000000 : ℝ)^8253 ≤ (21297629077601/50000000000000 : ℝ)^6205 := by
    have hnat : (5264244717 : ℕ)^8253*50000000000000^6205 ≤ 21297629077601^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264244717 10000000000 21297629077601 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334063567/625000000 : ℝ), (-2272842297/10000000000 : ℝ), (5264244717/10000000000 : ℝ)] ![(4346672837731/10000000000000 : ℝ), (13938013454759/100000000000000 : ℝ), (21297629077601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334063567/625000000 : ℝ)|^8253 ≤ (4346672837731/10000000000000 : ℝ)^6205
        have hw : |(334063567/625000000 : ℝ)|=(334063567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2272842297/10000000000 : ℝ)|^8253 ≤ (13938013454759/100000000000000 : ℝ)^6205
        have hw : |(-2272842297/10000000000 : ℝ)|=(2272842297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264244717/10000000000 : ℝ)|^8253 ≤ (21297629077601/50000000000000 : ℝ)^6205
        have hw : |(5264244717/10000000000 : ℝ)|=(5264244717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s7_2 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672508581/5000000000 : ℝ)*x 0 + (65803057/125000000 : ℝ)*x 1 + (-142052649/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672508581/5000000000 : ℝ)^8253 ≤ (1738669174031/4000000000000 : ℝ)^6205 := by
    have hnat : (2672508581 : ℕ)^8253*4000000000000^6205 ≤ 1738669174031^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672508581 5000000000 1738669174031 4000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65803057/125000000 : ℝ)^8253 ≤ (42595256465559/100000000000000 : ℝ)^6205 := by
    have hnat : (65803057 : ℕ)^8253*100000000000000^6205 ≤ 42595256465559^6205*125000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65803057 125000000 42595256465559 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142052649/625000000 : ℝ)^8253 ≤ (13938014164371/100000000000000 : ℝ)^6205 := by
    have hnat : (142052649 : ℕ)^8253*100000000000000^6205 ≤ 13938014164371^6205*625000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142052649 625000000 13938014164371 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672508581/5000000000 : ℝ), (65803057/125000000 : ℝ), (-142052649/625000000 : ℝ)] ![(1738669174031/4000000000000 : ℝ), (42595256465559/100000000000000 : ℝ), (13938014164371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672508581/5000000000 : ℝ)|^8253 ≤ (1738669174031/4000000000000 : ℝ)^6205
        have hw : |(2672508581/5000000000 : ℝ)|=(2672508581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65803057/125000000 : ℝ)|^8253 ≤ (42595256465559/100000000000000 : ℝ)^6205
        have hw : |(65803057/125000000 : ℝ)|=(65803057/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-142052649/625000000 : ℝ)|^8253 ≤ (13938014164371/100000000000000 : ℝ)^6205
        have hw : |(-142052649/625000000 : ℝ)|=(142052649/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s7_3 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188175401/5000000000 : ℝ)*x 0 + (850137177/2000000000 : ℝ)*x 1 + (901157431/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188175401/5000000000 : ℝ)^8253 ≤ (8329115687993/25000000000000 : ℝ)^6205 := by
    have hnat : (2188175401 : ℕ)^8253*25000000000000^6205 ≤ 8329115687993^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188175401 5000000000 8329115687993 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (850137177/2000000000 : ℝ)^8253 ≤ (32050110408561/100000000000000 : ℝ)^6205 := by
    have hnat : (850137177 : ℕ)^8253*100000000000000^6205 ≤ 32050110408561^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850137177 2000000000 32050110408561 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901157431/2000000000 : ℝ)^8253 ≤ (17316713409101/50000000000000 : ℝ)^6205 := by
    have hnat : (901157431 : ℕ)^8253*50000000000000^6205 ≤ 17316713409101^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901157431 2000000000 17316713409101 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188175401/5000000000 : ℝ), (850137177/2000000000 : ℝ), (901157431/2000000000 : ℝ)] ![(8329115687993/25000000000000 : ℝ), (32050110408561/100000000000000 : ℝ), (17316713409101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188175401/5000000000 : ℝ)|^8253 ≤ (8329115687993/25000000000000 : ℝ)^6205
        have hw : |(2188175401/5000000000 : ℝ)|=(2188175401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(850137177/2000000000 : ℝ)|^8253 ≤ (32050110408561/100000000000000 : ℝ)^6205
        have hw : |(850137177/2000000000 : ℝ)|=(850137177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901157431/2000000000 : ℝ)|^8253 ≤ (17316713409101/50000000000000 : ℝ)^6205
        have hw : |(901157431/2000000000 : ℝ)|=(901157431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s7_4 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2206725011/10000000000 : ℝ)*x 0 + (1316142869/2500000000 : ℝ)*x 1 + (2697117413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2206725011/10000000000 : ℝ)^8253 ≤ (1675167063303/12500000000000 : ℝ)^6205 := by
    have hnat : (2206725011 : ℕ)^8253*12500000000000^6205 ≤ 1675167063303^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206725011 10000000000 1675167063303 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316142869/2500000000 : ℝ)^8253 ≤ (10649693697463/25000000000000 : ℝ)^6205 := by
    have hnat : (1316142869 : ℕ)^8253*25000000000000^6205 ≤ 10649693697463^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316142869 2500000000 10649693697463 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697117413/5000000000 : ℝ)^8253 ≤ (43999888688317/100000000000000 : ℝ)^6205 := by
    have hnat : (2697117413 : ℕ)^8253*100000000000000^6205 ≤ 43999888688317^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697117413 5000000000 43999888688317 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2206725011/10000000000 : ℝ), (1316142869/2500000000 : ℝ), (2697117413/5000000000 : ℝ)] ![(1675167063303/12500000000000 : ℝ), (10649693697463/25000000000000 : ℝ), (43999888688317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2206725011/10000000000 : ℝ)|^8253 ≤ (1675167063303/12500000000000 : ℝ)^6205
        have hw : |(-2206725011/10000000000 : ℝ)|=(2206725011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316142869/2500000000 : ℝ)|^8253 ≤ (10649693697463/25000000000000 : ℝ)^6205
        have hw : |(1316142869/2500000000 : ℝ)|=(1316142869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697117413/5000000000 : ℝ)|^8253 ≤ (43999888688317/100000000000000 : ℝ)^6205
        have hw : |(2697117413/5000000000 : ℝ)|=(2697117413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s7_5 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656104117/5000000000 : ℝ)*x 0 + (-2142852173/10000000000 : ℝ)*x 1 + (5394234827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656104117/5000000000 : ℝ)^8253 ≤ (21556109386243/50000000000000 : ℝ)^6205 := by
    have hnat : (2656104117 : ℕ)^8253*50000000000000^6205 ≤ 21556109386243^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656104117 5000000000 21556109386243 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142852173/10000000000 : ℝ)^8253 ≤ (515515700767/4000000000000 : ℝ)^6205 := by
    have hnat : (2142852173 : ℕ)^8253*4000000000000^6205 ≤ 515515700767^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142852173 10000000000 515515700767 4000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394234827/10000000000 : ℝ)^8253 ≤ (21999944349583/50000000000000 : ℝ)^6205 := by
    have hnat : (5394234827 : ℕ)^8253*50000000000000^6205 ≤ 21999944349583^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394234827 10000000000 21999944349583 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656104117/5000000000 : ℝ), (-2142852173/10000000000 : ℝ), (5394234827/10000000000 : ℝ)] ![(21556109386243/50000000000000 : ℝ), (515515700767/4000000000000 : ℝ), (21999944349583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656104117/5000000000 : ℝ)|^8253 ≤ (21556109386243/50000000000000 : ℝ)^6205
        have hw : |(2656104117/5000000000 : ℝ)|=(2656104117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2142852173/10000000000 : ℝ)|^8253 ≤ (515515700767/4000000000000 : ℝ)^6205
        have hw : |(-2142852173/10000000000 : ℝ)|=(2142852173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394234827/10000000000 : ℝ)|^8253 ≤ (21999944349583/50000000000000 : ℝ)^6205
        have hw : |(5394234827/10000000000 : ℝ)|=(5394234827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s7_6 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656104117/5000000000 : ℝ)*x 0 + (5394234827/10000000000 : ℝ)*x 1 + (-535713043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656104117/5000000000 : ℝ)^8253 ≤ (21556109386243/50000000000000 : ℝ)^6205 := by
    have hnat : (2656104117 : ℕ)^8253*50000000000000^6205 ≤ 21556109386243^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656104117 5000000000 21556109386243 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394234827/10000000000 : ℝ)^8253 ≤ (21999944349583/50000000000000 : ℝ)^6205 := by
    have hnat : (5394234827 : ℕ)^8253*50000000000000^6205 ≤ 21999944349583^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394234827 10000000000 21999944349583 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535713043/2500000000 : ℝ)^8253 ≤ (515515700447/4000000000000 : ℝ)^6205 := by
    have hnat : (535713043 : ℕ)^8253*4000000000000^6205 ≤ 515515700447^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535713043 2500000000 515515700447 4000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656104117/5000000000 : ℝ), (5394234827/10000000000 : ℝ), (-535713043/2500000000 : ℝ)] ![(21556109386243/50000000000000 : ℝ), (21999944349583/50000000000000 : ℝ), (515515700447/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656104117/5000000000 : ℝ)|^8253 ≤ (21556109386243/50000000000000 : ℝ)^6205
        have hw : |(2656104117/5000000000 : ℝ)|=(2656104117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394234827/10000000000 : ℝ)|^8253 ≤ (21999944349583/50000000000000 : ℝ)^6205
        have hw : |(5394234827/10000000000 : ℝ)|=(5394234827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535713043/2500000000 : ℝ)|^8253 ≤ (515515700447/4000000000000 : ℝ)^6205
        have hw : |(-535713043/2500000000 : ℝ)|=(535713043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s7_7 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376360747/10000000000 : ℝ)*x 0 + (1126286857/2500000000 : ℝ)*x 1 + (2125663983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376360747/10000000000 : ℝ)^8253 ≤ (16658281725093/50000000000000 : ℝ)^6205 := by
    have hnat : (4376360747 : ℕ)^8253*50000000000000^6205 ≤ 16658281725093^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376360747 10000000000 16658281725093 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126286857/2500000000 : ℝ)^8253 ≤ (34626886793987/100000000000000 : ℝ)^6205 := by
    have hnat : (1126286857 : ℕ)^8253*100000000000000^6205 ≤ 34626886793987^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126286857 2500000000 34626886793987 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125663983/5000000000 : ℝ)^8253 ≤ (16028274873273/50000000000000 : ℝ)^6205 := by
    have hnat : (2125663983 : ℕ)^8253*50000000000000^6205 ≤ 16028274873273^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125663983 5000000000 16028274873273 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376360747/10000000000 : ℝ), (1126286857/2500000000 : ℝ), (2125663983/5000000000 : ℝ)] ![(16658281725093/50000000000000 : ℝ), (34626886793987/100000000000000 : ℝ), (16028274873273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376360747/10000000000 : ℝ)|^8253 ≤ (16658281725093/50000000000000 : ℝ)^6205
        have hw : |(4376360747/10000000000 : ℝ)|=(4376360747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126286857/2500000000 : ℝ)|^8253 ≤ (34626886793987/100000000000000 : ℝ)^6205
        have hw : |(1126286857/2500000000 : ℝ)|=(1126286857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125663983/5000000000 : ℝ)|^8253 ≤ (16028274873273/50000000000000 : ℝ)^6205
        have hw : |(2125663983/5000000000 : ℝ)|=(2125663983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1060_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11241/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14001/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11231/100000 : ℝ) ^ (2063/512 : ℝ) ≤ (7461462157027301/50000000000000000000 : ℝ) := by
    have hpowers : (11231/100000 : ℝ)^2063 ≤ (7461462157027301/50000000000000000000 : ℝ)^512 := by
      have hnat : (11231 : ℕ)^2063*50000000000000000000^512 ≤ 7461462157027301^512*100000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11231 100000 7461462157027301 50000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11231/100000 : ℝ)) (X := (7461462157027301/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14011/100000 : ℝ) ^ (2063/512 : ℝ) ≤ (1136896074253927/3125000000000000000 : ℝ) := by
    have hpowers : (14011/100000 : ℝ)^2063 ≤ (1136896074253927/3125000000000000000 : ℝ)^512 := by
      have hnat : (14011 : ℕ)^2063*3125000000000000000^512 ≤ 1136896074253927^512*100000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14011 100000 1136896074253927 3125000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14011/100000 : ℝ)) (X := (1136896074253927/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007461462157027301/25000000000000000000 : ℝ) ≤ (10000740637923597/10000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (25007461462157027301/25000000000000000000 : ℝ)^512 ≤ (10000740637923597/10000000000000000 : ℝ)^2063 := by
      have hnat : (25007461462157027301 : ℕ)^512*10000000000000000^2063 ≤ 10000740637923597^2063*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007461462157027301 25000000000000000000 10000740637923597 10000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000740637923597/10000000000000000 : ℝ)) (X := (25007461462157027301/25000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025651799345090133/50000000000000000000 : ℝ) ≤ (10001273018819421/10000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (50025651799345090133/50000000000000000000 : ℝ)^512 ≤ (10001273018819421/10000000000000000 : ℝ)^2063 := by
      have hnat : (50025651799345090133 : ℕ)^512*10000000000000000^2063 ≤ 10001273018819421^2063*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025651799345090133 50000000000000000000 10001273018819421 10000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001273018819421/10000000000000000 : ℝ)) (X := (50025651799345090133/50000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563636896074253927/1562500000000000000 : ℝ) ≤ (2000361079943049/2000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (1563636896074253927/1562500000000000000 : ℝ)^512 ≤ (2000361079943049/2000000000000000 : ℝ)^2063 := by
      have hnat : (1563636896074253927 : ℕ)^512*2000000000000000^2063 ≤ 2000361079943049^2063*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563636896074253927 1562500000000000000 2000361079943049 2000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000361079943049/2000000000000000 : ℝ)) (X := (1563636896074253927/1562500000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7461462157027301/50000000000000000000 : ℝ) ≤ ((6947525158436400243/6950000000000000000 : ℝ)+2*(33273805989/17375000000000 : ℝ)*(11231/100000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (6947525158436400243/6950000000000000000 : ℝ)+2*(33273805989/17375000000000 : ℝ)*(11231/100000 : ℝ)=(10000740637923597/10000000000000000 : ℝ) by norm_num, show 1+2*(7461462157027301/50000000000000000000 : ℝ)=(25007461462157027301/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1136896074253927/3125000000000000000 : ℝ)+(7461462157027301/50000000000000000000 : ℝ) ≤ ((6947525158436400243/6950000000000000000 : ℝ)+(33273805989/17375000000000 : ℝ)*((14011/100000 : ℝ)+(11231/100000 : ℝ)))^(2063/512 : ℝ) := by
    rw [show (6947525158436400243/6950000000000000000 : ℝ)+(33273805989/17375000000000 : ℝ)*((14011/100000 : ℝ)+(11231/100000 : ℝ))=(10001273018819421/10000000000000000 : ℝ) by norm_num, show 1+(1136896074253927/3125000000000000000 : ℝ)+(7461462157027301/50000000000000000000 : ℝ)=(50025651799345090133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1136896074253927/3125000000000000000 : ℝ) ≤ ((6947525158436400243/6950000000000000000 : ℝ)+2*(33273805989/17375000000000 : ℝ)*(14011/100000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (6947525158436400243/6950000000000000000 : ℝ)+2*(33273805989/17375000000000 : ℝ)*(14011/100000 : ℝ)=(2000361079943049/2000000000000000 : ℝ) by norm_num, show 1+2*(1136896074253927/3125000000000000000 : ℝ)=(1563636896074253927/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6947525158436400243/6950000000000000000 : ℝ)*(X 1 0+X 2 0)+(33273805989/17375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (6947525158436400243/6950000000000000000 : ℝ)) (alpha := (33273805989/17375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6947525158436400243/6950000000000000000 : ℝ)*(X 0 1+X 2 1)+(33273805989/17375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (6947525158436400243/6950000000000000000 : ℝ)) (alpha := (33273805989/17375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6947525158436400243/6950000000000000000 : ℝ)*(X 0 2+X 1 2)+(33273805989/17375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (6947525158436400243/6950000000000000000 : ℝ)) (alpha := (33273805989/17375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2206720033/10000000000 : ℝ)*X 0 0+(2697281447/5000000000 : ℝ)*X 0 1+(1316061123/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334063567/625000000 : ℝ)*X 1 0+(-2272842297/10000000000 : ℝ)*X 1 1+(5264244717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672508581/5000000000 : ℝ)*X 2 0+(65803057/125000000 : ℝ)*X 2 1+(-142052649/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188175401/5000000000 : ℝ)*X 0 0+(850137177/2000000000 : ℝ)*X 0 1+(901157431/2000000000 : ℝ)*X 0 2+(2188175401/5000000000 : ℝ)*X 1 0+(850137177/2000000000 : ℝ)*X 1 1+(901157431/2000000000 : ℝ)*X 1 2+(2188175401/5000000000 : ℝ)*X 2 0+(850137177/2000000000 : ℝ)*X 2 1+(901157431/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2206725011/10000000000 : ℝ)*X 0 0+(1316142869/2500000000 : ℝ)*X 0 1+(2697117413/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656104117/5000000000 : ℝ)*X 1 0+(-2142852173/10000000000 : ℝ)*X 1 1+(5394234827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656104117/5000000000 : ℝ)*X 2 0+(5394234827/10000000000 : ℝ)*X 2 1+(-535713043/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4376360747/10000000000 : ℝ)*X 0 0+(1126286857/2500000000 : ℝ)*X 0 1+(2125663983/5000000000 : ℝ)*X 0 2+(4376360747/10000000000 : ℝ)*X 1 0+(1126286857/2500000000 : ℝ)*X 1 1+(2125663983/5000000000 : ℝ)*X 1 2+(4376360747/10000000000 : ℝ)*X 2 0+(1126286857/2500000000 : ℝ)*X 2 1+(2125663983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (251699550429175178962528341/43437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (290104029/20000000000000 : ℝ)*(base19) + (189152319/12500000000000 : ℝ)*(base23) + (128125993/50000000000000 : ℝ)*(upper3) + (17775041/50000000000000 : ℝ)*(upper4) + (47701539/50000000000000 : ℝ)*(upper5) + (1449208285931829/25000000000000 : ℝ)*(major0) + (1449208285931829/25000000000000 : ℝ)*(major1) + (1449208285931829/25000000000000 : ℝ)*(major2) + (7673564926242511/100000000000000 : ℝ)*(sp0) + (7673609889566643/100000000000000 : ℝ)*(sp1) + (1534721965373647/20000000000000 : ℝ)*(sp2) + (1960015558314203/50000000000000 : ℝ)*(sp3) + (11603461069/25000000000000 : ℝ)*(sp4) + (4727517739/20000000000000 : ℝ)*(sp7) + (3920054754217101/100000000000000 : ℝ)*(f.failure) + (1918402835021697/25000000000000 : ℝ)*(f.sum) + (1649530559477/1737500000000000000000000000 : ℝ)*base66 + (624956961184434447/173750000000000000000000000000000 : ℝ)*base67 + (654119424330565553/173750000000000000000000000000000 : ℝ)*base70 + (516151739974315553/173750000000000000000000000000000 : ℝ)*base72 + (5557637094429/3475000000000000000000000000 : ℝ)*base74 + (3591227587301815553/173750000000000000000000000000000 : ℝ)*base76 + (1084474050706815553/173750000000000000000000000000000 : ℝ)*base78 + (3599616765328065553/173750000000000000000000000000000 : ℝ)*base80 + (638322499649/868750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (73336431/10000000000000000000000 : ℝ)*base89 + (73336431/10000000000000000000000 : ℝ)*base91 + (73336431/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (255930040503582950645004987/86875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55048189/10000000000000 : ℝ)*(base19) + (149861929/25000000000000 : ℝ)*(base23) + (59695799/100000000000000 : ℝ)*(upper3) + (5517229/25000000000000 : ℝ)*(lower4) + (11961457/20000000000000 : ℝ)*(upper5) + (2913021783808203/50000000000000 : ℝ)*(major0) + (2913021783808203/50000000000000 : ℝ)*(major1) + (2913021783808203/50000000000000 : ℝ)*(major2) + (2994296409/20000000000000 : ℝ)*(sp1) + (8086586147/50000000000000 : ℝ)*(sp2) + (7712279004052657/100000000000000 : ℝ)*(sp4) + (7712263482088721/100000000000000 : ℝ)*(sp5) + (3856131115716323/50000000000000 : ℝ)*(sp6) + (984952008245391/25000000000000 : ℝ)*(sp7) + (984952008245391/25000000000000 : ℝ)*(f.failure) + (7712279004052657/100000000000000 : ℝ)*(f.sum) + (12268429640661/3475000000000000000000000000 : ℝ)*base65 + (7387364112228606671/347500000000000000000000000000000 : ℝ)*base68 + (10437587889973606671/347500000000000000000000000000000 : ℝ)*base70 + (2254322189816393329/347500000000000000000000000000000 : ℝ)*base71 + (10717719862257/1737500000000000000000000000 : ℝ)*base74 + (11496232687848606671/347500000000000000000000000000000 : ℝ)*base76 + (1995365063888606671/347500000000000000000000000000000 : ℝ)*base78 + (1600089086853606671/347500000000000000000000000000000 : ℝ)*base80 + (2029945307933/434375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (18740421/2500000000000000000000 : ℝ)*base89 + (18740421/2500000000000000000000 : ℝ)*base91 + (18740421/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1060_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1060_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1060_s8_0 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2206727857/10000000000 : ℝ)*x 0 + (674307013/1250000000 : ℝ)*x 1 + (210573851/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2206727857/10000000000 : ℝ)^8253 ≤ (13401359494623/100000000000000 : ℝ)^6205 := by
    have hnat : (2206727857 : ℕ)^8253*100000000000000^6205 ≤ 13401359494623^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206727857 10000000000 13401359494623 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674307013/1250000000 : ℝ)^8253 ≤ (11000572340271/25000000000000 : ℝ)^6205 := by
    have hnat : (674307013 : ℕ)^8253*25000000000000^6205 ≤ 11000572340271^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674307013 1250000000 11000572340271 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210573851/400000000 : ℝ)^8253 ≤ (10649087782889/25000000000000 : ℝ)^6205 := by
    have hnat : (210573851 : ℕ)^8253*25000000000000^6205 ≤ 10649087782889^6205*400000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210573851 400000000 10649087782889 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2206727857/10000000000 : ℝ), (674307013/1250000000 : ℝ), (210573851/400000000 : ℝ)] ![(13401359494623/100000000000000 : ℝ), (11000572340271/25000000000000 : ℝ), (10649087782889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2206727857/10000000000 : ℝ)|^8253 ≤ (13401359494623/100000000000000 : ℝ)^6205
        have hw : |(-2206727857/10000000000 : ℝ)|=(2206727857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674307013/1250000000 : ℝ)|^8253 ≤ (11000572340271/25000000000000 : ℝ)^6205
        have hw : |(674307013/1250000000 : ℝ)|=(674307013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210573851/400000000 : ℝ)|^8253 ≤ (10649087782889/25000000000000 : ℝ)^6205
        have hw : |(210573851/400000000 : ℝ)|=(210573851/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s8_1 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668123843/1250000000 : ℝ)*x 0 + (-45454861/200000000 : ℝ)*x 1 + (1052869279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668123843/1250000000 : ℝ)^8253 ≤ (1738657744261/4000000000000 : ℝ)^6205 := by
    have hnat : (668123843 : ℕ)^8253*4000000000000^6205 ≤ 1738657744261^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668123843 1250000000 1738657744261 4000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45454861/200000000 : ℝ)^8253 ≤ (13937203956547/100000000000000 : ℝ)^6205 := by
    have hnat : (45454861 : ℕ)^8253*100000000000000^6205 ≤ 13937203956547^6205*200000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45454861 200000000 13937203956547 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052869279/2000000000 : ℝ)^8253 ≤ (42596352423011/100000000000000 : ℝ)^6205 := by
    have hnat : (1052869279 : ℕ)^8253*100000000000000^6205 ≤ 42596352423011^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052869279 2000000000 42596352423011 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668123843/1250000000 : ℝ), (-45454861/200000000 : ℝ), (1052869279/2000000000 : ℝ)] ![(1738657744261/4000000000000 : ℝ), (13937203956547/100000000000000 : ℝ), (42596352423011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668123843/1250000000 : ℝ)|^8253 ≤ (1738657744261/4000000000000 : ℝ)^6205
        have hw : |(668123843/1250000000 : ℝ)|=(668123843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45454861/200000000 : ℝ)|^8253 ≤ (13937203956547/100000000000000 : ℝ)^6205
        have hw : |(-45454861/200000000 : ℝ)|=(45454861/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052869279/2000000000 : ℝ)|^8253 ≤ (42596352423011/100000000000000 : ℝ)^6205
        have hw : |(1052869279/2000000000 : ℝ)|=(1052869279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s8_2 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344990741/10000000000 : ℝ)*x 0 + (2632173311/5000000000 : ℝ)*x 1 + (-1136371377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344990741/10000000000 : ℝ)^8253 ≤ (43466443574077/100000000000000 : ℝ)^6205 := by
    have hnat : (5344990741 : ℕ)^8253*100000000000000^6205 ≤ 43466443574077^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344990741 10000000000 43466443574077 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632173311/5000000000 : ℝ)^8253 ≤ (42596354866013/100000000000000 : ℝ)^6205 := by
    have hnat : (2632173311 : ℕ)^8253*100000000000000^6205 ≤ 42596354866013^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632173311 5000000000 42596354866013 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136371377/5000000000 : ℝ)^8253 ≤ (1393720154227/10000000000000 : ℝ)^6205 := by
    have hnat : (1136371377 : ℕ)^8253*10000000000000^6205 ≤ 1393720154227^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136371377 5000000000 1393720154227 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344990741/10000000000 : ℝ), (2632173311/5000000000 : ℝ), (-1136371377/5000000000 : ℝ)] ![(43466443574077/100000000000000 : ℝ), (42596354866013/100000000000000 : ℝ), (1393720154227/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344990741/10000000000 : ℝ)|^8253 ≤ (43466443574077/100000000000000 : ℝ)^6205
        have hw : |(5344990741/10000000000 : ℝ)|=(5344990741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632173311/5000000000 : ℝ)|^8253 ≤ (42596354866013/100000000000000 : ℝ)^6205
        have hw : |(2632173311/5000000000 : ℝ)|=(2632173311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1136371377/5000000000 : ℝ)|^8253 ≤ (1393720154227/10000000000000 : ℝ)^6205
        have hw : |(-1136371377/5000000000 : ℝ)|=(1136371377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s8_3 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376355939/10000000000 : ℝ)*x 0 + (66420147/156250000 : ℝ)*x 1 + (225279121/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376355939/10000000000 : ℝ)^8253 ≤ (8329128691679/25000000000000 : ℝ)^6205 := by
    have hnat : (4376355939 : ℕ)^8253*25000000000000^6205 ≤ 8329128691679^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376355939 10000000000 8329128691679 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66420147/156250000 : ℝ)^8253 ≤ (32052151476701/100000000000000 : ℝ)^6205 := by
    have hnat : (66420147 : ℕ)^8253*100000000000000^6205 ≤ 32052151476701^6205*156250000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66420147 156250000 32052151476701 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225279121/500000000 : ℝ)^8253 ≤ (6926266749703/20000000000000 : ℝ)^6205 := by
    have hnat : (225279121 : ℕ)^8253*20000000000000^6205 ≤ 6926266749703^6205*500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225279121 500000000 6926266749703 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376355939/10000000000 : ℝ), (66420147/156250000 : ℝ), (225279121/500000000 : ℝ)] ![(8329128691679/25000000000000 : ℝ), (32052151476701/100000000000000 : ℝ), (6926266749703/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376355939/10000000000 : ℝ)|^8253 ≤ (8329128691679/25000000000000 : ℝ)^6205
        have hw : |(4376355939/10000000000 : ℝ)|=(4376355939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66420147/156250000 : ℝ)|^8253 ≤ (32052151476701/100000000000000 : ℝ)^6205
        have hw : |(66420147/156250000 : ℝ)|=(66420147/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225279121/500000000 : ℝ)|^8253 ≤ (6926266749703/20000000000000 : ℝ)^6205
        have hw : |(225279121/500000000 : ℝ)|=(225279121/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s8_4 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2206732383/10000000000 : ℝ)*x 0 + (5264672537/10000000000 : ℝ)*x 1 + (1348532271/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2206732383/10000000000 : ℝ)^8253 ≤ (536055842113/4000000000000 : ℝ)^6205 := by
    have hnat : (2206732383 : ℕ)^8253*4000000000000^6205 ≤ 536055842113^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206732383 10000000000 536055842113 4000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264672537/10000000000 : ℝ)^8253 ≤ (1331245701241/3125000000000 : ℝ)^6205 := by
    have hnat : (5264672537 : ℕ)^8253*3125000000000^6205 ≤ 1331245701241^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264672537 10000000000 1331245701241 3125000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348532271/2500000000 : ℝ)^8253 ≤ (43998741491577/100000000000000 : ℝ)^6205 := by
    have hnat : (1348532271 : ℕ)^8253*100000000000000^6205 ≤ 43998741491577^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348532271 2500000000 43998741491577 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2206732383/10000000000 : ℝ), (5264672537/10000000000 : ℝ), (1348532271/2500000000 : ℝ)] ![(536055842113/4000000000000 : ℝ), (1331245701241/3125000000000 : ℝ), (43998741491577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2206732383/10000000000 : ℝ)|^8253 ≤ (536055842113/4000000000000 : ℝ)^6205
        have hw : |(-2206732383/10000000000 : ℝ)|=(2206732383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264672537/10000000000 : ℝ)|^8253 ≤ (1331245701241/3125000000000 : ℝ)^6205
        have hw : |(5264672537/10000000000 : ℝ)|=(5264672537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348532271/2500000000 : ℝ)|^8253 ≤ (43998741491577/100000000000000 : ℝ)^6205
        have hw : |(1348532271/2500000000 : ℝ)|=(1348532271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s8_5 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312234753/10000000000 : ℝ)*x 0 + (-2142960023/10000000000 : ℝ)*x 1 + (2697064459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312234753/10000000000 : ℝ)^8253 ≤ (4311250502733/10000000000000 : ℝ)^6205 := by
    have hnat : (5312234753 : ℕ)^8253*10000000000000^6205 ≤ 4311250502733^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312234753 10000000000 4311250502733 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142960023/10000000000 : ℝ)^8253 ≤ (6444377633139/50000000000000 : ℝ)^6205 := by
    have hnat : (2142960023 : ℕ)^8253*50000000000000^6205 ≤ 6444377633139^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142960023 10000000000 6444377633139 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697064459/5000000000 : ℝ)^8253 ≤ (43998739690647/100000000000000 : ℝ)^6205 := by
    have hnat : (2697064459 : ℕ)^8253*100000000000000^6205 ≤ 43998739690647^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697064459 5000000000 43998739690647 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312234753/10000000000 : ℝ), (-2142960023/10000000000 : ℝ), (2697064459/5000000000 : ℝ)] ![(4311250502733/10000000000000 : ℝ), (6444377633139/50000000000000 : ℝ), (43998739690647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312234753/10000000000 : ℝ)|^8253 ≤ (4311250502733/10000000000000 : ℝ)^6205
        have hw : |(5312234753/10000000000 : ℝ)|=(5312234753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2142960023/10000000000 : ℝ)|^8253 ≤ (6444377633139/50000000000000 : ℝ)^6205
        have hw : |(-2142960023/10000000000 : ℝ)|=(2142960023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697064459/5000000000 : ℝ)|^8253 ≤ (43998739690647/100000000000000 : ℝ)^6205
        have hw : |(2697064459/5000000000 : ℝ)|=(2697064459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s8_6 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328058703/2500000000 : ℝ)*x 0 + (2697064531/5000000000 : ℝ)*x 1 + (-535739937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328058703/2500000000 : ℝ)^8253 ≤ (10778126416049/25000000000000 : ℝ)^6205 := by
    have hnat : (1328058703 : ℕ)^8253*25000000000000^6205 ≤ 10778126416049^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328058703 2500000000 10778126416049 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697064531/5000000000 : ℝ)^8253 ≤ (439987412529/1000000000000 : ℝ)^6205 := by
    have hnat : (2697064531 : ℕ)^8253*1000000000000^6205 ≤ 439987412529^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697064531 5000000000 439987412529 1000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535739937/2500000000 : ℝ)^8253 ≤ (6444376533197/50000000000000 : ℝ)^6205 := by
    have hnat : (535739937 : ℕ)^8253*50000000000000^6205 ≤ 6444376533197^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535739937 2500000000 6444376533197 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328058703/2500000000 : ℝ), (2697064531/5000000000 : ℝ), (-535739937/2500000000 : ℝ)] ![(10778126416049/25000000000000 : ℝ), (439987412529/1000000000000 : ℝ), (6444376533197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328058703/2500000000 : ℝ)|^8253 ≤ (10778126416049/25000000000000 : ℝ)^6205
        have hw : |(1328058703/2500000000 : ℝ)|=(1328058703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697064531/5000000000 : ℝ)|^8253 ≤ (439987412529/1000000000000 : ℝ)^6205
        have hw : |(2697064531/5000000000 : ℝ)|=(2697064531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535739937/2500000000 : ℝ)|^8253 ≤ (6444376533197/50000000000000 : ℝ)^6205
        have hw : |(-535739937/2500000000 : ℝ)|=(535739937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s8_7 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (547045723/1250000000 : ℝ)*x 0 + (4504944703/10000000000 : ℝ)*x 1 + (4251529519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547045723/1250000000 : ℝ)^8253 ≤ (16658307226209/50000000000000 : ℝ)^6205 := by
    have hnat : (547045723 : ℕ)^8253*50000000000000^6205 ≤ 16658307226209^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547045723 1250000000 16658307226209 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504944703/10000000000 : ℝ)^8253 ≤ (34624814370131/100000000000000 : ℝ)^6205 := by
    have hnat : (4504944703 : ℕ)^8253*100000000000000^6205 ≤ 34624814370131^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504944703 10000000000 34624814370131 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251529519/10000000000 : ℝ)^8253 ≤ (8014642789697/25000000000000 : ℝ)^6205 := by
    have hnat : (4251529519 : ℕ)^8253*25000000000000^6205 ≤ 8014642789697^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251529519 10000000000 8014642789697 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547045723/1250000000 : ℝ), (4504944703/10000000000 : ℝ), (4251529519/10000000000 : ℝ)] ![(16658307226209/50000000000000 : ℝ), (34624814370131/100000000000000 : ℝ), (8014642789697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547045723/1250000000 : ℝ)|^8253 ≤ (16658307226209/50000000000000 : ℝ)^6205
        have hw : |(547045723/1250000000 : ℝ)|=(547045723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504944703/10000000000 : ℝ)|^8253 ≤ (34624814370131/100000000000000 : ℝ)^6205
        have hw : |(4504944703/10000000000 : ℝ)|=(4504944703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251529519/10000000000 : ℝ)|^8253 ≤ (8014642789697/25000000000000 : ℝ)^6205
        have hw : |(4251529519/10000000000 : ℝ)|=(4251529519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1060_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11243/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13999/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11241/100000 : ℝ) ^ (2063/512 : ℝ) ≤ (3744133721398539/25000000000000000000 : ℝ) := by
    have hpowers : (11241/100000 : ℝ)^2063 ≤ (3744133721398539/25000000000000000000 : ℝ)^512 := by
      have hnat : (11241 : ℕ)^2063*25000000000000000000^512 ≤ 3744133721398539^512*100000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11241 100000 3744133721398539 25000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11241/100000 : ℝ)) (X := (3744133721398539/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14001/100000 : ℝ) ^ (2063/512 : ℝ) ≤ (18138081765305979/50000000000000000000 : ℝ) := by
    have hpowers : (14001/100000 : ℝ)^2063 ≤ (18138081765305979/50000000000000000000 : ℝ)^512 := by
      have hnat : (14001 : ℕ)^2063*50000000000000000000^512 ≤ 18138081765305979^512*100000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14001 100000 18138081765305979 50000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14001/100000 : ℝ)) (X := (18138081765305979/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503744133721398539/12500000000000000000 : ℝ) ≤ (10000743298364129/10000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (12503744133721398539/12500000000000000000 : ℝ)^512 ≤ (10000743298364129/10000000000000000 : ℝ)^2063 := by
      have hnat : (12503744133721398539 : ℕ)^512*10000000000000000^2063 ≤ 10000743298364129^2063*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503744133721398539 12500000000000000000 10000743298364129 10000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000743298364129/10000000000000000 : ℝ)) (X := (12503744133721398539/12500000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025626349208103057/50000000000000000000 : ℝ) ≤ (10001271756051713/10000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (50025626349208103057/50000000000000000000 : ℝ)^512 ≤ (10001271756051713/10000000000000000 : ℝ)^2063 := by
      have hnat : (50025626349208103057 : ℕ)^512*10000000000000000^2063 ≤ 10001271756051713^2063*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025626349208103057 50000000000000000000 10001271756051713 10000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001271756051713/10000000000000000 : ℝ)) (X := (50025626349208103057/50000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018138081765305979/25000000000000000000 : ℝ) ≤ (10001800213739297/10000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (25018138081765305979/25000000000000000000 : ℝ)^512 ≤ (10001800213739297/10000000000000000 : ℝ)^2063 := by
      have hnat : (25018138081765305979 : ℕ)^512*10000000000000000^2063 ≤ 10001800213739297^2063*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018138081765305979 25000000000000000000 10001800213739297 10000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001800213739297/10000000000000000 : ℝ)) (X := (25018138081765305979/25000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3744133721398539/25000000000000000000 : ℝ) ≤ ((1149590446573030523/1150000000000000000 : ℝ)+2*(5504767579/2875000000000 : ℝ)*(11241/100000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (1149590446573030523/1150000000000000000 : ℝ)+2*(5504767579/2875000000000 : ℝ)*(11241/100000 : ℝ)=(10000743298364129/10000000000000000 : ℝ) by norm_num, show 1+2*(3744133721398539/25000000000000000000 : ℝ)=(12503744133721398539/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18138081765305979/50000000000000000000 : ℝ)+(3744133721398539/25000000000000000000 : ℝ) ≤ ((1149590446573030523/1150000000000000000 : ℝ)+(5504767579/2875000000000 : ℝ)*((14001/100000 : ℝ)+(11241/100000 : ℝ)))^(2063/512 : ℝ) := by
    rw [show (1149590446573030523/1150000000000000000 : ℝ)+(5504767579/2875000000000 : ℝ)*((14001/100000 : ℝ)+(11241/100000 : ℝ))=(10001271756051713/10000000000000000 : ℝ) by norm_num, show 1+(18138081765305979/50000000000000000000 : ℝ)+(3744133721398539/25000000000000000000 : ℝ)=(50025626349208103057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18138081765305979/50000000000000000000 : ℝ) ≤ ((1149590446573030523/1150000000000000000 : ℝ)+2*(5504767579/2875000000000 : ℝ)*(14001/100000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (1149590446573030523/1150000000000000000 : ℝ)+2*(5504767579/2875000000000 : ℝ)*(14001/100000 : ℝ)=(10001800213739297/10000000000000000 : ℝ) by norm_num, show 1+2*(18138081765305979/50000000000000000000 : ℝ)=(25018138081765305979/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1149590446573030523/1150000000000000000 : ℝ)*(X 1 0+X 2 0)+(5504767579/2875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (1149590446573030523/1150000000000000000 : ℝ)) (alpha := (5504767579/2875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1149590446573030523/1150000000000000000 : ℝ)*(X 0 1+X 2 1)+(5504767579/2875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (1149590446573030523/1150000000000000000 : ℝ)) (alpha := (5504767579/2875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1149590446573030523/1150000000000000000 : ℝ)*(X 0 2+X 1 2)+(5504767579/2875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (1149590446573030523/1150000000000000000 : ℝ)) (alpha := (5504767579/2875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2206727857/10000000000 : ℝ)*X 0 0+(674307013/1250000000 : ℝ)*X 0 1+(210573851/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668123843/1250000000 : ℝ)*X 1 0+(-45454861/200000000 : ℝ)*X 1 1+(1052869279/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344990741/10000000000 : ℝ)*X 2 0+(2632173311/5000000000 : ℝ)*X 2 1+(-1136371377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376355939/10000000000 : ℝ)*X 0 0+(66420147/156250000 : ℝ)*X 0 1+(225279121/500000000 : ℝ)*X 0 2+(4376355939/10000000000 : ℝ)*X 1 0+(66420147/156250000 : ℝ)*X 1 1+(225279121/500000000 : ℝ)*X 1 2+(4376355939/10000000000 : ℝ)*X 2 0+(66420147/156250000 : ℝ)*X 2 1+(225279121/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2206732383/10000000000 : ℝ)*X 0 0+(5264672537/10000000000 : ℝ)*X 0 1+(1348532271/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312234753/10000000000 : ℝ)*X 1 0+(-2142960023/10000000000 : ℝ)*X 1 1+(2697064459/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328058703/2500000000 : ℝ)*X 2 0+(2697064531/5000000000 : ℝ)*X 2 1+(-535739937/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((547045723/1250000000 : ℝ)*X 0 0+(4504944703/10000000000 : ℝ)*X 0 1+(4251529519/10000000000 : ℝ)*X 0 2+(547045723/1250000000 : ℝ)*X 1 0+(4504944703/10000000000 : ℝ)*X 1 1+(4251529519/10000000000 : ℝ)*X 1 2+(547045723/1250000000 : ℝ)*X 2 0+(4504944703/10000000000 : ℝ)*X 2 1+(4251529519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5159305949024813859303/575000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1439051017/100000000000000 : ℝ)*(base19) + (316347231/25000000000000 : ℝ)*(base23) + (34200399/100000000000000 : ℝ)*(upper3) + (11314557/12500000000000 : ℝ)*(upper4) + (187414331/50000000000000 : ℝ)*(upper5) + (5806123179575187/100000000000000 : ℝ)*(major0) + (5806123179575187/100000000000000 : ℝ)*(major1) + (5806123179575187/100000000000000 : ℝ)*(major2) + (7685852024110991/100000000000000 : ℝ)*(sp0) + (7685907566044493/100000000000000 : ℝ)*(sp1) + (3842953869853293/50000000000000 : ℝ)*(sp2) + (490789896934949/12500000000000 : ℝ)*(sp3) + (56980984519/100000000000000 : ℝ)*(sp4) + (3575897013/20000000000000 : ℝ)*(sp7) + (245396065935291/6250000000000 : ℝ)*(f.failure) + (768590900509551/10000000000000 : ℝ)*(f.sum) + (1534772219177/143750000000000000000000000 : ℝ)*base66 + (2438672639463632801/115000000000000000000000000000000 : ℝ)*base67 + (51151947193632801/115000000000000000000000000000000 : ℝ)*base69 + (571724869366367199/115000000000000000000000000000000 : ℝ)*base72 + (1888022334983/575000000000000000000000000 : ℝ)*base74 + (443866181583632801/115000000000000000000000000000000 : ℝ)*base75 + (163422824276367199/115000000000000000000000000000000 : ℝ)*base78 + (126443613911367199/115000000000000000000000000000000 : ℝ)*base80 + (3209217056233/575000000000000000000000000 : ℝ)*base82 + (2252679/625000000000000000000 : ℝ)*base90 + (2252679/625000000000000000000 : ℝ)*base92 + (2252679/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1399255144579238599743/287500000000000000000000000 : ℝ) := by norm_num
    linear_combination (331705057/50000000000000 : ℝ)*(base19) + (1490299007/100000000000000 : ℝ)*(base23) + (25876593/100000000000000 : ℝ)*(lower3) + (53457279/20000000000000 : ℝ)*(lower4) + (97417513/50000000000000 : ℝ)*(lower5) + (5835341595853107/100000000000000 : ℝ)*(major0) + (5835341595853107/100000000000000 : ℝ)*(major1) + (5835341595853107/100000000000000 : ℝ)*(major2) + (3914367409/25000000000000 : ℝ)*(sp1) + (6780792857/12500000000000 : ℝ)*(sp2) + (1931146822741411/25000000000000 : ℝ)*(sp4) + (3862285485042947/50000000000000 : ℝ)*(sp5) + (7724531554323781/100000000000000 : ℝ)*(sp6) + (3946095738508083/100000000000000 : ℝ)*(sp7) + (3946095738508083/100000000000000 : ℝ)*(f.failure) + (1931146822741411/25000000000000 : ℝ)*(f.sum) + (194581852461/71875000000000000000000000 : ℝ)*base66 + (615372525638415039/115000000000000000000000000000000 : ℝ)*base68 + (153502510178415039/115000000000000000000000000000000 : ℝ)*base70 + (531246214346584961/115000000000000000000000000000000 : ℝ)*base71 + (1796376095713/575000000000000000000000000 : ℝ)*base74 + (1442392185981584961/115000000000000000000000000000000 : ℝ)*base75 + (1607321052383415039/115000000000000000000000000000000 : ℝ)*base78 + (1165984716371584961/115000000000000000000000000000000 : ℝ)*base79 + (4661747629437/575000000000000000000000000 : ℝ)*base81 + (27883473/10000000000000000000000 : ℝ)*base89 + (27883473/10000000000000000000000 : ℝ)*base91 + (27883473/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1060_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1060_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1060_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1060_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1060_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1060_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1060_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
