-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310045_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:24:45.805414+00:00
-- url     : https://prove2.me/submissions/85c49cb1-9561-4618-97d4-70c3bde64dc4

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c310045_s2_s2_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-107586133/1000000000 : ℝ)*x 0 + (-1422757397/2500000000 : ℝ)*x 1 + (5453940757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107586133/1000000000 : ℝ)^9 ≤ (2845019480079/50000000000000 : ℝ)^7 := by
    have hnat : (107586133 : ℕ)^9*50000000000000^7 ≤ 2845019480079^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107586133 1000000000 2845019480079 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1422757397/2500000000 : ℝ)^9 ≤ (24222299771951/50000000000000 : ℝ)^7 := by
    have hnat : (1422757397 : ℕ)^9*50000000000000^7 ≤ 24222299771951^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422757397 2500000000 24222299771951 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453940757/10000000000 : ℝ)^9 ≤ (45865361488339/100000000000000 : ℝ)^7 := by
    have hnat : (5453940757 : ℕ)^9*100000000000000^7 ≤ 45865361488339^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453940757 10000000000 45865361488339 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107586133/1000000000 : ℝ), (-1422757397/2500000000 : ℝ), (5453940757/10000000000 : ℝ)] ![(2845019480079/50000000000000 : ℝ), (24222299771951/50000000000000 : ℝ), (45865361488339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107586133/1000000000 : ℝ)|^9 ≤ (2845019480079/50000000000000 : ℝ)^7
        have hw : |(-107586133/1000000000 : ℝ)|=(107586133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1422757397/2500000000 : ℝ)|^9 ≤ (24222299771951/50000000000000 : ℝ)^7
        have hw : |(-1422757397/2500000000 : ℝ)|=(1422757397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453940757/10000000000 : ℝ)|^9 ≤ (45865361488339/100000000000000 : ℝ)^7
        have hw : |(5453940757/10000000000 : ℝ)|=(5453940757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1383461107/2500000000 : ℝ)*x 0 + (3517302877/10000000000 : ℝ)*x 1 + (3629922017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1383461107/2500000000 : ℝ)^9 ≤ (4673110743667/10000000000000 : ℝ)^7 := by
    have hnat : (1383461107 : ℕ)^9*10000000000000^7 ≤ 4673110743667^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383461107 2500000000 4673110743667 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3517302877/10000000000 : ℝ)^9 ≤ (13047443335469/50000000000000 : ℝ)^7 := by
    have hnat : (3517302877 : ℕ)^9*50000000000000^7 ≤ 13047443335469^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3517302877 10000000000 13047443335469 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3629922017/10000000000 : ℝ)^9 ≤ (5434801175849/20000000000000 : ℝ)^7 := by
    have hnat : (3629922017 : ℕ)^9*20000000000000^7 ≤ 5434801175849^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3629922017 10000000000 5434801175849 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1383461107/2500000000 : ℝ), (3517302877/10000000000 : ℝ), (3629922017/10000000000 : ℝ)] ![(4673110743667/10000000000000 : ℝ), (13047443335469/50000000000000 : ℝ), (5434801175849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1383461107/2500000000 : ℝ)|^9 ≤ (4673110743667/10000000000000 : ℝ)^7
        have hw : |(1383461107/2500000000 : ℝ)|=(1383461107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3517302877/10000000000 : ℝ)|^9 ≤ (13047443335469/50000000000000 : ℝ)^7
        have hw : |(3517302877/10000000000 : ℝ)|=(3517302877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3629922017/10000000000 : ℝ)|^9 ≤ (5434801175849/20000000000000 : ℝ)^7
        have hw : |(3629922017/10000000000 : ℝ)|=(3629922017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1370574999/2500000000 : ℝ)*x 0 + (-70909039/200000000 : ℝ)*x 1 + (-457503033/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1370574999/2500000000 : ℝ)^9 ≤ (46172218133943/100000000000000 : ℝ)^7 := by
    have hnat : (1370574999 : ℕ)^9*100000000000000^7 ≤ 46172218133943^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370574999 2500000000 46172218133943 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70909039/200000000 : ℝ)^9 ≤ (26363699204123/100000000000000 : ℝ)^7 := by
    have hnat : (70909039 : ℕ)^9*100000000000000^7 ≤ 26363699204123^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70909039 200000000 26363699204123 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457503033/1250000000 : ℝ)^9 ≤ (13732041321569/50000000000000 : ℝ)^7 := by
    have hnat : (457503033 : ℕ)^9*50000000000000^7 ≤ 13732041321569^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457503033 1250000000 13732041321569 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1370574999/2500000000 : ℝ), (-70909039/200000000 : ℝ), (-457503033/1250000000 : ℝ)] ![(46172218133943/100000000000000 : ℝ), (26363699204123/100000000000000 : ℝ), (13732041321569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1370574999/2500000000 : ℝ)|^9 ≤ (46172218133943/100000000000000 : ℝ)^7
        have hw : |(1370574999/2500000000 : ℝ)|=(1370574999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70909039/200000000 : ℝ)|^9 ≤ (26363699204123/100000000000000 : ℝ)^7
        have hw : |(-70909039/200000000 : ℝ)|=(70909039/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-457503033/1250000000 : ℝ)|^9 ≤ (13732041321569/50000000000000 : ℝ)^7
        have hw : |(-457503033/1250000000 : ℝ)|=(457503033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_3 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (9999999999/10000000000 : ℝ)*x 0 + (41/10000000000 : ℝ)*x 1 + (41/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9999999999/10000000000 : ℝ)^9 ≤ (99999999987143/100000000000000 : ℝ)^7 := by
    have hnat : (9999999999 : ℕ)^9*100000000000000^7 ≤ 99999999987143^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 99999999987143 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41/10000000000 : ℝ)^9 ≤ (1647/100000000000000 : ℝ)^7 := by
    have hnat : (41 : ℕ)^9*100000000000000^7 ≤ 1647^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41 10000000000 1647 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41/10000000000 : ℝ)^9 ≤ (1647/100000000000000 : ℝ)^7 := by
    have hnat : (41 : ℕ)^9*100000000000000^7 ≤ 1647^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41 10000000000 1647 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9999999999/10000000000 : ℝ), (41/10000000000 : ℝ), (41/10000000000 : ℝ)] ![(99999999987143/100000000000000 : ℝ), (1647/100000000000000 : ℝ), (1647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9999999999/10000000000 : ℝ)|^9 ≤ (99999999987143/100000000000000 : ℝ)^7
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41/10000000000 : ℝ)|^9 ≤ (1647/100000000000000 : ℝ)^7
        have hw : |(41/10000000000 : ℝ)|=(41/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41/10000000000 : ℝ)|^9 ≤ (1647/100000000000000 : ℝ)^7
        have hw : |(41/10000000000 : ℝ)|=(41/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1305470363/2500000000 : ℝ)*x 0 + (-3736726261/10000000000 : ℝ)*x 1 + (3758938361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305470363/2500000000 : ℝ)^9 ≤ (2710729428991/6250000000000 : ℝ)^7 := by
    have hnat : (1305470363 : ℕ)^9*6250000000000^7 ≤ 2710729428991^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305470363 2500000000 2710729428991 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3736726261/10000000000 : ℝ)^9 ≤ (7051572013743/25000000000000 : ℝ)^7 := by
    have hnat : (3736726261 : ℕ)^9*25000000000000^7 ≤ 7051572013743^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3736726261 10000000000 7051572013743 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3758938361/10000000000 : ℝ)^9 ≤ (2842204106333/10000000000000 : ℝ)^7 := by
    have hnat : (3758938361 : ℕ)^9*10000000000000^7 ≤ 2842204106333^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3758938361 10000000000 2842204106333 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1305470363/2500000000 : ℝ), (-3736726261/10000000000 : ℝ), (3758938361/10000000000 : ℝ)] ![(2710729428991/6250000000000 : ℝ), (7051572013743/25000000000000 : ℝ), (2842204106333/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1305470363/2500000000 : ℝ)|^9 ≤ (2710729428991/6250000000000 : ℝ)^7
        have hw : |(1305470363/2500000000 : ℝ)|=(1305470363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3736726261/10000000000 : ℝ)|^9 ≤ (7051572013743/25000000000000 : ℝ)^7
        have hw : |(-3736726261/10000000000 : ℝ)|=(3736726261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3758938361/10000000000 : ℝ)|^9 ≤ (2842204106333/10000000000000 : ℝ)^7
        have hw : |(3758938361/10000000000 : ℝ)|=(3758938361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-990602677/10000000000 : ℝ)*x 0 + (-3253834529/5000000000 : ℝ)*x 1 + (4646178189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (990602677/10000000000 : ℝ)^9 ≤ (2558489527843/50000000000000 : ℝ)^7 := by
    have hnat : (990602677 : ℕ)^9*50000000000000^7 ≤ 2558489527843^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990602677 10000000000 2558489527843 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3253834529/5000000000 : ℝ)^9 ≤ (57559690157859/100000000000000 : ℝ)^7 := by
    have hnat : (3253834529 : ℕ)^9*100000000000000^7 ≤ 57559690157859^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3253834529 5000000000 57559690157859 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4646178189/10000000000 : ℝ)^9 ≤ (37323330769331/100000000000000 : ℝ)^7 := by
    have hnat : (4646178189 : ℕ)^9*100000000000000^7 ≤ 37323330769331^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4646178189 10000000000 37323330769331 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-990602677/10000000000 : ℝ), (-3253834529/5000000000 : ℝ), (4646178189/10000000000 : ℝ)] ![(2558489527843/50000000000000 : ℝ), (57559690157859/100000000000000 : ℝ), (37323330769331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-990602677/10000000000 : ℝ)|^9 ≤ (2558489527843/50000000000000 : ℝ)^7
        have hw : |(-990602677/10000000000 : ℝ)|=(990602677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3253834529/5000000000 : ℝ)|^9 ≤ (57559690157859/100000000000000 : ℝ)^7
        have hw : |(-3253834529/5000000000 : ℝ)|=(3253834529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4646178189/10000000000 : ℝ)|^9 ≤ (37323330769331/100000000000000 : ℝ)^7
        have hw : |(4646178189/10000000000 : ℝ)|=(4646178189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5064912121/10000000000 : ℝ)*x 0 + (3613990081/10000000000 : ℝ)*x 1 + (4049418369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5064912121/10000000000 : ℝ)^9 ≤ (10425668188059/25000000000000 : ℝ)^7 := by
    have hnat : (5064912121 : ℕ)^9*25000000000000^7 ≤ 10425668188059^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5064912121 10000000000 10425668188059 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3613990081/10000000000 : ℝ)^9 ≤ (13510378604341/50000000000000 : ℝ)^7 := by
    have hnat : (3613990081 : ℕ)^9*50000000000000^7 ≤ 13510378604341^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3613990081 10000000000 13510378604341 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4049418369/10000000000 : ℝ)^9 ≤ (31276570019443/100000000000000 : ℝ)^7 := by
    have hnat : (4049418369 : ℕ)^9*100000000000000^7 ≤ 31276570019443^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4049418369 10000000000 31276570019443 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5064912121/10000000000 : ℝ), (3613990081/10000000000 : ℝ), (4049418369/10000000000 : ℝ)] ![(10425668188059/25000000000000 : ℝ), (13510378604341/50000000000000 : ℝ), (31276570019443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5064912121/10000000000 : ℝ)|^9 ≤ (10425668188059/25000000000000 : ℝ)^7
        have hw : |(5064912121/10000000000 : ℝ)|=(5064912121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3613990081/10000000000 : ℝ)|^9 ≤ (13510378604341/50000000000000 : ℝ)^7
        have hw : |(3613990081/10000000000 : ℝ)|=(3613990081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4049418369/10000000000 : ℝ)|^9 ≤ (31276570019443/100000000000000 : ℝ)^7
        have hw : |(4049418369/10000000000 : ℝ)|=(4049418369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5691192223/10000000000 : ℝ)*x 0 + (-405790783/1250000000 : ℝ)*x 1 + (-3716951377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5691192223/10000000000 : ℝ)^9 ≤ (48446379522511/100000000000000 : ℝ)^7 := by
    have hnat : (5691192223 : ℕ)^9*100000000000000^7 ≤ 48446379522511^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5691192223 10000000000 48446379522511 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405790783/1250000000 : ℝ)^9 ≤ (941564158301/4000000000000 : ℝ)^7 := by
    have hnat : (405790783 : ℕ)^9*4000000000000^7 ≤ 941564158301^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405790783 1250000000 941564158301 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3716951377/10000000000 : ℝ)^9 ≤ (7003629124003/25000000000000 : ℝ)^7 := by
    have hnat : (3716951377 : ℕ)^9*25000000000000^7 ≤ 7003629124003^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3716951377 10000000000 7003629124003 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5691192223/10000000000 : ℝ), (-405790783/1250000000 : ℝ), (-3716951377/10000000000 : ℝ)] ![(48446379522511/100000000000000 : ℝ), (941564158301/4000000000000 : ℝ), (7003629124003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5691192223/10000000000 : ℝ)|^9 ≤ (48446379522511/100000000000000 : ℝ)^7
        have hw : |(5691192223/10000000000 : ℝ)|=(5691192223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-405790783/1250000000 : ℝ)|^9 ≤ (941564158301/4000000000000 : ℝ)^7
        have hw : |(-405790783/1250000000 : ℝ)|=(405790783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3716951377/10000000000 : ℝ)|^9 ≤ (7003629124003/25000000000000 : ℝ)^7
        have hw : |(-3716951377/10000000000 : ℝ)|=(3716951377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2757688543/5000000000 : ℝ)*x 0 + (-617413979/2500000000 : ℝ)*x 1 + (287867513/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757688543/5000000000 : ℝ)^9 ≤ (5816337102169/12500000000000 : ℝ)^7 := by
    have hnat : (2757688543 : ℕ)^9*12500000000000^7 ≤ 5816337102169^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757688543 5000000000 5816337102169 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (617413979/2500000000 : ℝ)^9 ≤ (8280832706261/50000000000000 : ℝ)^7 := by
    have hnat : (617413979 : ℕ)^9*50000000000000^7 ≤ 8280832706261^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617413979 2500000000 8280832706261 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287867513/625000000 : ℝ)^9 ≤ (36907637755851/100000000000000 : ℝ)^7 := by
    have hnat : (287867513 : ℕ)^9*100000000000000^7 ≤ 36907637755851^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287867513 625000000 36907637755851 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757688543/5000000000 : ℝ), (-617413979/2500000000 : ℝ), (287867513/625000000 : ℝ)] ![(5816337102169/12500000000000 : ℝ), (8280832706261/50000000000000 : ℝ), (36907637755851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757688543/5000000000 : ℝ)|^9 ≤ (5816337102169/12500000000000 : ℝ)^7
        have hw : |(2757688543/5000000000 : ℝ)|=(2757688543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-617413979/2500000000 : ℝ)|^9 ≤ (8280832706261/50000000000000 : ℝ)^7
        have hw : |(-617413979/2500000000 : ℝ)|=(617413979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(287867513/625000000 : ℝ)|^9 ≤ (36907637755851/100000000000000 : ℝ)^7
        have hw : |(287867513/625000000 : ℝ)|=(287867513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-81278997/2000000000 : ℝ)*x 0 + (-2815651047/5000000000 : ℝ)*x 1 + (1177052349/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81278997/2000000000 : ℝ)^9 ≤ (1627440084363/100000000000000 : ℝ)^7 := by
    have hnat : (81278997 : ℕ)^9*100000000000000^7 ≤ 1627440084363^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81278997 2000000000 1627440084363 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2815651047/5000000000 : ℝ)^9 ≤ (4779188989781/10000000000000 : ℝ)^7 := by
    have hnat : (2815651047 : ℕ)^9*10000000000000^7 ≤ 4779188989781^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2815651047 5000000000 4779188989781 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1177052349/2000000000 : ℝ)^9 ≤ (25290334998999/50000000000000 : ℝ)^7 := by
    have hnat : (1177052349 : ℕ)^9*50000000000000^7 ≤ 25290334998999^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177052349 2000000000 25290334998999 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81278997/2000000000 : ℝ), (-2815651047/5000000000 : ℝ), (1177052349/2000000000 : ℝ)] ![(1627440084363/100000000000000 : ℝ), (4779188989781/10000000000000 : ℝ), (25290334998999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81278997/2000000000 : ℝ)|^9 ≤ (1627440084363/100000000000000 : ℝ)^7
        have hw : |(-81278997/2000000000 : ℝ)|=(81278997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2815651047/5000000000 : ℝ)|^9 ≤ (4779188989781/10000000000000 : ℝ)^7
        have hw : |(-2815651047/5000000000 : ℝ)|=(2815651047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1177052349/2000000000 : ℝ)|^9 ≤ (25290334998999/50000000000000 : ℝ)^7
        have hw : |(1177052349/2000000000 : ℝ)|=(1177052349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5299363109/10000000000 : ℝ)*x 0 + (91010111/250000000 : ℝ)*x 1 + (3769445499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5299363109/10000000000 : ℝ)^9 ≤ (44200831904879/100000000000000 : ℝ)^7 := by
    have hnat : (5299363109 : ℕ)^9*100000000000000^7 ≤ 44200831904879^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5299363109 10000000000 44200831904879 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91010111/250000000 : ℝ)^9 ≤ (13637470409063/50000000000000 : ℝ)^7 := by
    have hnat : (91010111 : ℕ)^9*50000000000000^7 ≤ 13637470409063^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91010111 250000000 13637470409063 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3769445499/10000000000 : ℝ)^9 ≤ (5704845452073/20000000000000 : ℝ)^7 := by
    have hnat : (3769445499 : ℕ)^9*20000000000000^7 ≤ 5704845452073^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3769445499 10000000000 5704845452073 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5299363109/10000000000 : ℝ), (91010111/250000000 : ℝ), (3769445499/10000000000 : ℝ)] ![(44200831904879/100000000000000 : ℝ), (13637470409063/50000000000000 : ℝ), (5704845452073/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5299363109/10000000000 : ℝ)|^9 ≤ (44200831904879/100000000000000 : ℝ)^7
        have hw : |(5299363109/10000000000 : ℝ)|=(5299363109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91010111/250000000 : ℝ)|^9 ≤ (13637470409063/50000000000000 : ℝ)^7
        have hw : |(91010111/250000000 : ℝ)|=(91010111/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3769445499/10000000000 : ℝ)|^9 ≤ (5704845452073/20000000000000 : ℝ)^7
        have hw : |(3769445499/10000000000 : ℝ)|=(3769445499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6238395487/10000000000 : ℝ)*x 0 + (-1552667961/5000000000 : ℝ)*x 1 + (-3215410461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6238395487/10000000000 : ℝ)^9 ≤ (6814473668261/12500000000000 : ℝ)^7 := by
    have hnat : (6238395487 : ℕ)^9*12500000000000^7 ≤ 6814473668261^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6238395487 10000000000 6814473668261 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1552667961/5000000000 : ℝ)^9 ≤ (4446586556213/20000000000000 : ℝ)^7 := by
    have hnat : (1552667961 : ℕ)^9*20000000000000^7 ≤ 4446586556213^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552667961 5000000000 4446586556213 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3215410461/10000000000 : ℝ)^9 ≤ (4650255572391/20000000000000 : ℝ)^7 := by
    have hnat : (3215410461 : ℕ)^9*20000000000000^7 ≤ 4650255572391^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3215410461 10000000000 4650255572391 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6238395487/10000000000 : ℝ), (-1552667961/5000000000 : ℝ), (-3215410461/10000000000 : ℝ)] ![(6814473668261/12500000000000 : ℝ), (4446586556213/20000000000000 : ℝ), (4650255572391/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6238395487/10000000000 : ℝ)|^9 ≤ (6814473668261/12500000000000 : ℝ)^7
        have hw : |(6238395487/10000000000 : ℝ)|=(6238395487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1552667961/5000000000 : ℝ)|^9 ≤ (4446586556213/20000000000000 : ℝ)^7
        have hw : |(-1552667961/5000000000 : ℝ)|=(1552667961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3215410461/10000000000 : ℝ)|^9 ≤ (4650255572391/20000000000000 : ℝ)^7
        have hw : |(-3215410461/10000000000 : ℝ)|=(3215410461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1413286179/2500000000 : ℝ)*x 0 + (-3428212447/10000000000 : ℝ)*x 1 + (3582817479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1413286179/2500000000 : ℝ)^9 ≤ (12007590142783/25000000000000 : ℝ)^7 := by
    have hnat : (1413286179 : ℕ)^9*25000000000000^7 ≤ 12007590142783^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413286179 2500000000 12007590142783 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3428212447/10000000000 : ℝ)^9 ≤ (6312042928959/25000000000000 : ℝ)^7 := by
    have hnat : (3428212447 : ℕ)^9*25000000000000^7 ≤ 6312042928959^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3428212447 10000000000 6312042928959 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3582817479/10000000000 : ℝ)^9 ≤ (26721467693693/100000000000000 : ℝ)^7 := by
    have hnat : (3582817479 : ℕ)^9*100000000000000^7 ≤ 26721467693693^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3582817479 10000000000 26721467693693 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1413286179/2500000000 : ℝ), (-3428212447/10000000000 : ℝ), (3582817479/10000000000 : ℝ)] ![(12007590142783/25000000000000 : ℝ), (6312042928959/25000000000000 : ℝ), (26721467693693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1413286179/2500000000 : ℝ)|^9 ≤ (12007590142783/25000000000000 : ℝ)^7
        have hw : |(1413286179/2500000000 : ℝ)|=(1413286179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3428212447/10000000000 : ℝ)|^9 ≤ (6312042928959/25000000000000 : ℝ)^7
        have hw : |(-3428212447/10000000000 : ℝ)|=(3428212447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3582817479/10000000000 : ℝ)|^9 ≤ (26721467693693/100000000000000 : ℝ)^7
        have hw : |(3582817479/10000000000 : ℝ)|=(3582817479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-18620509/400000000 : ℝ)*x 0 + (-3120108691/5000000000 : ℝ)*x 1 + (654538599/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18620509/400000000 : ℝ)^9 ≤ (484485275073/25000000000000 : ℝ)^7 := by
    have hnat : (18620509 : ℕ)^9*25000000000000^7 ≤ 484485275073^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18620509 400000000 484485275073 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3120108691/5000000000 : ℝ)^9 ≤ (54536260170441/100000000000000 : ℝ)^7 := by
    have hnat : (3120108691 : ℕ)^9*100000000000000^7 ≤ 54536260170441^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120108691 5000000000 54536260170441 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654538599/1250000000 : ℝ)^9 ≤ (43525798723897/100000000000000 : ℝ)^7 := by
    have hnat : (654538599 : ℕ)^9*100000000000000^7 ≤ 43525798723897^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654538599 1250000000 43525798723897 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18620509/400000000 : ℝ), (-3120108691/5000000000 : ℝ), (654538599/1250000000 : ℝ)] ![(484485275073/25000000000000 : ℝ), (54536260170441/100000000000000 : ℝ), (43525798723897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18620509/400000000 : ℝ)|^9 ≤ (484485275073/25000000000000 : ℝ)^7
        have hw : |(-18620509/400000000 : ℝ)|=(18620509/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3120108691/5000000000 : ℝ)|^9 ≤ (54536260170441/100000000000000 : ℝ)^7
        have hw : |(-3120108691/5000000000 : ℝ)|=(3120108691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654538599/1250000000 : ℝ)|^9 ≤ (43525798723897/100000000000000 : ℝ)^7
        have hw : |(654538599/1250000000 : ℝ)|=(654538599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6154915927/10000000000 : ℝ)*x 0 + (3166036393/10000000000 : ℝ)*x 1 + (130230469/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6154915927/10000000000 : ℝ)^9 ≤ (53579650340593/100000000000000 : ℝ)^7 := by
    have hnat : (6154915927 : ℕ)^9*100000000000000^7 ≤ 53579650340593^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6154915927 10000000000 53579650340593 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3166036393/10000000000 : ℝ)^9 ≤ (22793245101229/100000000000000 : ℝ)^7 := by
    have hnat : (3166036393 : ℕ)^9*100000000000000^7 ≤ 22793245101229^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3166036393 10000000000 22793245101229 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130230469/400000000 : ℝ)^9 ≤ (23627104534249/100000000000000 : ℝ)^7 := by
    have hnat : (130230469 : ℕ)^9*100000000000000^7 ≤ 23627104534249^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130230469 400000000 23627104534249 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6154915927/10000000000 : ℝ), (3166036393/10000000000 : ℝ), (130230469/400000000 : ℝ)] ![(53579650340593/100000000000000 : ℝ), (22793245101229/100000000000000 : ℝ), (23627104534249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6154915927/10000000000 : ℝ)|^9 ≤ (53579650340593/100000000000000 : ℝ)^7
        have hw : |(6154915927/10000000000 : ℝ)|=(6154915927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3166036393/10000000000 : ℝ)|^9 ≤ (22793245101229/100000000000000 : ℝ)^7
        have hw : |(3166036393/10000000000 : ℝ)|=(3166036393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130230469/400000000 : ℝ)|^9 ≤ (23627104534249/100000000000000 : ℝ)^7
        have hw : |(130230469/400000000 : ℝ)|=(130230469/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2608440131/5000000000 : ℝ)*x 0 + (-3694279879/10000000000 : ℝ)*x 1 + (-1903325319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2608440131/5000000000 : ℝ)^9 ≤ (338423994703/781250000000 : ℝ)^7 := by
    have hnat : (2608440131 : ℕ)^9*781250000000^7 ≤ 338423994703^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608440131 5000000000 338423994703 781250000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3694279879/10000000000 : ℝ)^9 ≤ (13897506410369/50000000000000 : ℝ)^7 := by
    have hnat : (3694279879 : ℕ)^9*50000000000000^7 ≤ 13897506410369^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3694279879 10000000000 13897506410369 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1903325319/5000000000 : ℝ)^9 ≤ (28886715837079/100000000000000 : ℝ)^7 := by
    have hnat : (1903325319 : ℕ)^9*100000000000000^7 ≤ 28886715837079^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903325319 5000000000 28886715837079 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2608440131/5000000000 : ℝ), (-3694279879/10000000000 : ℝ), (-1903325319/5000000000 : ℝ)] ![(338423994703/781250000000 : ℝ), (13897506410369/50000000000000 : ℝ), (28886715837079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2608440131/5000000000 : ℝ)|^9 ≤ (338423994703/781250000000 : ℝ)^7
        have hw : |(2608440131/5000000000 : ℝ)|=(2608440131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3694279879/10000000000 : ℝ)|^9 ≤ (13897506410369/50000000000000 : ℝ)^7
        have hw : |(-3694279879/10000000000 : ℝ)|=(3694279879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1903325319/5000000000 : ℝ)|^9 ≤ (28886715837079/100000000000000 : ℝ)^7
        have hw : |(-1903325319/5000000000 : ℝ)|=(1903325319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s2_s2_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2946017211/5000000000 : ℝ)*x 0 + (-383455093/1250000000 : ℝ)*x 1 + (914846743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2946017211/5000000000 : ℝ)^9 ≤ (50655520548727/100000000000000 : ℝ)^7 := by
    have hnat : (2946017211 : ℕ)^9*100000000000000^7 ≤ 50655520548727^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2946017211 5000000000 50655520548727 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383455093/1250000000 : ℝ)^9 ≤ (21886545073807/100000000000000 : ℝ)^7 := by
    have hnat : (383455093 : ℕ)^9*100000000000000^7 ≤ 21886545073807^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383455093 1250000000 21886545073807 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914846743/2500000000 : ℝ)^9 ≤ (13728967184203/50000000000000 : ℝ)^7 := by
    have hnat : (914846743 : ℕ)^9*50000000000000^7 ≤ 13728967184203^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914846743 2500000000 13728967184203 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2946017211/5000000000 : ℝ), (-383455093/1250000000 : ℝ), (914846743/2500000000 : ℝ)] ![(50655520548727/100000000000000 : ℝ), (21886545073807/100000000000000 : ℝ), (13728967184203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2946017211/5000000000 : ℝ)|^9 ≤ (50655520548727/100000000000000 : ℝ)^7
        have hw : |(2946017211/5000000000 : ℝ)|=(2946017211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-383455093/1250000000 : ℝ)|^9 ≤ (21886545073807/100000000000000 : ℝ)^7
        have hw : |(-383455093/1250000000 : ℝ)|=(383455093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(914846743/2500000000 : ℝ)|^9 ≤ (13728967184203/50000000000000 : ℝ)^7
        have hw : |(914846743/2500000000 : ℝ)|=(914846743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310045_s2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((1093/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1093/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2363/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-2363/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68203/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(68203/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3893/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3893/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-22297/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-22297/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23791/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23791/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (1093/3125 : ℝ) ^ (35/8 : ℝ) ≤ (504619893984627331/50000000000000000000 : ℝ) := by
    have hpowers : (1093/3125 : ℝ)^35 ≤ (504619893984627331/50000000000000000000 : ℝ)^8 := by
      have hnat : (1093 : ℕ)^35*50000000000000000000^8 ≤ 504619893984627331^8*3125^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1093 3125 504619893984627331 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1093/3125 : ℝ)) (X := (504619893984627331/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (50504619893984627331/50000000000000000000 : ℝ) ≤ (10022979069432103/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50504619893984627331/50000000000000000000 : ℝ)^8 ≤ (10022979069432103/10000000000000000 : ℝ)^35 := by
      have hnat : (50504619893984627331 : ℕ)^8*10000000000000000^35 ≤ 10022979069432103^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50504619893984627331 50000000000000000000 10022979069432103 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10022979069432103/10000000000000000 : ℝ)) (X := (50504619893984627331/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (25504619893984627331/25000000000000000000 : ℝ) ≤ (78482669516989/78125000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25504619893984627331/25000000000000000000 : ℝ)^8 ≤ (78482669516989/78125000000000 : ℝ)^35 := by
      have hnat : (25504619893984627331 : ℕ)^8*78125000000000^35 ≤ 78482669516989^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25504619893984627331 25000000000000000000 78482669516989 78125000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78482669516989/78125000000000 : ℝ)) (X := (25504619893984627331/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(22979069432103/3497600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(22802628742489/3497600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1093/3125 : ℝ)) (alpha := (22979069432103/3497600000000000 : ℝ)) (beta := (22802628742489/3497600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1093/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(22979069432103/3497600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(22802628742489/3497600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (2363/4000 : ℝ) ^ (35/8 : ℝ) ≤ (9997497865490046077/100000000000000000000 : ℝ) := by
    have hpowers : (2363/4000 : ℝ)^35 ≤ (9997497865490046077/100000000000000000000 : ℝ)^8 := by
      have hnat : (2363 : ℕ)^35*100000000000000000000^8 ≤ 9997497865490046077^8*4000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2363 4000 9997497865490046077 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2363/4000 : ℝ)) (X := (9997497865490046077/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (109997497865490046077/100000000000000000000 : ℝ) ≤ (10220188998920739/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (109997497865490046077/100000000000000000000 : ℝ)^8 ≤ (10220188998920739/10000000000000000 : ℝ)^35 := by
      have hnat : (109997497865490046077 : ℕ)^8*10000000000000000^35 ≤ 10220188998920739^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109997497865490046077 100000000000000000000 10220188998920739 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10220188998920739/10000000000000000 : ℝ)) (X := (109997497865490046077/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (59997497865490046077/50000000000000000000 : ℝ) ≤ (2606360225504467/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (59997497865490046077/50000000000000000000 : ℝ)^8 ≤ (2606360225504467/2500000000000000 : ℝ)^35 := by
      have hnat : (59997497865490046077 : ℕ)^8*2500000000000000^35 ≤ 2606360225504467^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59997497865490046077 50000000000000000000 2606360225504467 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2606360225504467/2500000000000000 : ℝ)) (X := (59997497865490046077/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(220188998920739/5907500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(205251903097129/5907500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (2363/4000 : ℝ)) (alpha := (220188998920739/5907500000000000 : ℝ)) (beta := (205251903097129/5907500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (2363/4000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(220188998920739/5907500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(205251903097129/5907500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (68203/100000 : ℝ) ^ (35/8 : ℝ) ≤ (18745205966809853569/100000000000000000000 : ℝ) := by
    have hpowers : (68203/100000 : ℝ)^35 ≤ (18745205966809853569/100000000000000000000 : ℝ)^8 := by
      have hnat : (68203 : ℕ)^35*100000000000000000000^8 ≤ 18745205966809853569^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68203 100000 18745205966809853569 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68203/100000 : ℝ)) (X := (18745205966809853569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (118745205966809853569/100000000000000000000 : ℝ) ≤ (260013030947723/250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (118745205966809853569/100000000000000000000 : ℝ)^8 ≤ (260013030947723/250000000000000 : ℝ)^35 := by
      have hnat : (118745205966809853569 : ℕ)^8*250000000000000^35 ≤ 260013030947723^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        118745205966809853569 100000000000000000000 260013030947723 250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (260013030947723/250000000000000 : ℝ)) (X := (118745205966809853569/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (68745205966809853569/50000000000000000000 : ℝ) ≤ (10754868955107323/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (68745205966809853569/50000000000000000000 : ℝ)^8 ≤ (10754868955107323/10000000000000000 : ℝ)^35 := by
      have hnat : (68745205966809853569 : ℕ)^8*10000000000000000^35 ≤ 10754868955107323^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68745205966809853569 50000000000000000000 10754868955107323 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10754868955107323/10000000000000000 : ℝ)) (X := (68745205966809853569/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(10013030947723/170507500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(354347717198403/6820300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (68203/100000 : ℝ)) (alpha := (10013030947723/170507500000000 : ℝ)) (beta := (354347717198403/6820300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (68203/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(10013030947723/170507500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(354347717198403/6820300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-107586133/1000000000 : ℝ)*X 0 0+(-1422757397/2500000000 : ℝ)*X 0 1+(5453940757/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((1383461107/2500000000 : ℝ)*X 1 0+(3517302877/10000000000 : ℝ)*X 1 1+(3629922017/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1370574999/2500000000 : ℝ)*X 2 0+(-70909039/200000000 : ℝ)*X 2 1+(-457503033/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_3 : ((9999999999/10000000000 : ℝ)*X 1 0+(41/10000000000 : ℝ)*X 1 1+(41/10000000000 : ℝ)*X 1 2+(9999999999/10000000000 : ℝ)*X 2 0+(41/10000000000 : ℝ)*X 2 1+(41/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((1305470363/2500000000 : ℝ)*X 0 0+(-3736726261/10000000000 : ℝ)*X 0 1+(3758938361/10000000000 : ℝ)*X 0 2+(1305470363/2500000000 : ℝ)*X 1 0+(-3736726261/10000000000 : ℝ)*X 1 1+(3758938361/10000000000 : ℝ)*X 1 2+(1305470363/2500000000 : ℝ)*X 2 0+(-3736726261/10000000000 : ℝ)*X 2 1+(3758938361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-990602677/10000000000 : ℝ)*X 0 0+(-3253834529/5000000000 : ℝ)*X 0 1+(4646178189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((5064912121/10000000000 : ℝ)*X 1 0+(3613990081/10000000000 : ℝ)*X 1 1+(4049418369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((5691192223/10000000000 : ℝ)*X 2 0+(-405790783/1250000000 : ℝ)*X 2 1+(-3716951377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2757688543/5000000000 : ℝ)*X 0 0+(-617413979/2500000000 : ℝ)*X 0 1+(287867513/625000000 : ℝ)*X 0 2+(2757688543/5000000000 : ℝ)*X 1 0+(-617413979/2500000000 : ℝ)*X 1 1+(287867513/625000000 : ℝ)*X 1 2+(2757688543/5000000000 : ℝ)*X 2 0+(-617413979/2500000000 : ℝ)*X 2 1+(287867513/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-81278997/2000000000 : ℝ)*X 0 0+(-2815651047/5000000000 : ℝ)*X 0 1+(1177052349/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((5299363109/10000000000 : ℝ)*X 1 0+(91010111/250000000 : ℝ)*X 1 1+(3769445499/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6238395487/10000000000 : ℝ)*X 2 0+(-1552667961/5000000000 : ℝ)*X 2 1+(-3215410461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1413286179/2500000000 : ℝ)*X 0 0+(-3428212447/10000000000 : ℝ)*X 0 1+(3582817479/10000000000 : ℝ)*X 0 2+(1413286179/2500000000 : ℝ)*X 1 0+(-3428212447/10000000000 : ℝ)*X 1 1+(3582817479/10000000000 : ℝ)*X 1 2+(1413286179/2500000000 : ℝ)*X 2 0+(-3428212447/10000000000 : ℝ)*X 2 1+(3582817479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-18620509/400000000 : ℝ)*X 0 0+(-3120108691/5000000000 : ℝ)*X 0 1+(654538599/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((6154915927/10000000000 : ℝ)*X 1 0+(3166036393/10000000000 : ℝ)*X 1 1+(130230469/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2608440131/5000000000 : ℝ)*X 2 0+(-3694279879/10000000000 : ℝ)*X 2 1+(-1903325319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2946017211/5000000000 : ℝ)*X 0 0+(-383455093/1250000000 : ℝ)*X 0 1+(914846743/2500000000 : ℝ)*X 0 2+(2946017211/5000000000 : ℝ)*X 1 0+(-383455093/1250000000 : ℝ)*X 1 1+(914846743/2500000000 : ℝ)*X 1 2+(2946017211/5000000000 : ℝ)*X 2 0+(-383455093/1250000000 : ℝ)*X 2 1+(914846743/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((3893/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3893/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (765175527791358483922940476869/70460764830800000000000000000000000 : ℝ) := by norm_num
    linear_combination (88204307173/125000000000 : ℝ)*(base40) + (469714141319/1000000000000 : ℝ)*(base50) + (971621/200000000000 : ℝ)*(base60) + (43492517039/10000000000 : ℝ)*(major_s2_0) + (43492517039/10000000000 : ℝ)*(major_s2_1) + (43492517039/10000000000 : ℝ)*(major_s2_2) + (6692753/500000000000 : ℝ)*(sp_s2_0) + (7181551/100000000000 : ℝ)*(sp_s2_2) + (3005139673007/500000000000 : ℝ)*(sp_s2_7) + (3005170822589/500000000000 : ℝ)*(sp_s2_8) + (601015470807/100000000000 : ℝ)*(sp_s2_9) + (10752632571/4000000000 : ℝ)*(sp_s2_13) + (48913659/1000000000000 : ℝ)*(sp_s2_21) + (115121599/1000000000000 : ℝ)*(sp_s2_23) + (10752632571/4000000000 : ℝ)*(f.failure) + (3005170822589/500000000000 : ℝ)*(f.sum) + (527543124400872489/8058184450000000000000000000000 : ℝ)*base62 + (21764017760083/85253750000000000000000000 : ℝ)*base65 + (5303950642989/59075000000000000000000000 : ℝ)*base66 + (44038319600043/341015000000000000000000000 : ℝ)*base69 + (1598568457485594543/11927340640000000000000000000000 : ℝ)*base71 + (2461692084461/174880000000000000000000000 : ℝ)*base72 + (21036109897939/59075000000000000000000000 : ℝ)*base74 + (81969769156573/174880000000000000000000000 : ℝ)*base77 + (569961701281862821/2066207200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (197/400000000000000 : ℝ)*base86 + (197/400000000000000 : ℝ)*base88 + (197/400000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-22297/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-22297/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40380941745146692615708152603309/3523038241540000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1657350895197/1000000000000 : ℝ)*(base40) + (26417928499/200000000000 : ℝ)*(base60) + (27397792938423/1000000000000 : ℝ)*(major_s2_0) + (2869703785869/500000000000 : ℝ)*(major_s2_1) + (2869703785869/500000000000 : ℝ)*(major_s2_2) + (20995663/125000000000 : ℝ)*(sp_s2_1) + (4331677073337/200000000000 : ℝ)*(sp_s2_3) + (11671809/1000000000000 : ℝ)*(sp_s2_6) + (199738889/1000000000000 : ℝ)*(sp_s2_8) + (793143438331/100000000000 : ℝ)*(sp_s2_14) + (7931066679117/1000000000000 : ℝ)*(sp_s2_15) + (793143438331/100000000000 : ℝ)*(sp_s2_16) + (1773560479489/500000000000 : ℝ)*(sp_s2_20) + (244308721/1000000000000 : ℝ)*(sp_s2_27) + (886844234877/250000000000 : ℝ)*(f.failure) + (793143438331/100000000000 : ℝ)*(f.sum) + (71160320124071007273/201454611250000000000000000000000 : ℝ)*base63 + (1074099522397489/1705075000000000000000000000 : ℝ)*base65 + (346553852983637/1476875000000000000000000000 : ℝ)*base66 + (25840030436423/136406000000000000000000000 : ℝ)*base69 + (106849745931454395403/238546812800000000000000000000000 : ℝ)*base71 + (1060765996525153/3497600000000000000000000000 : ℝ)*base72 + (354914685510717/1476875000000000000000000000 : ℝ)*base74 + (1003427506739809/3497600000000000000000000000 : ℝ)*base77 + (13865771881840364323/206620720000000000000000000000000 : ℝ)*base78 + (4461/25000000000000000 : ℝ)*base87 + (4461/25000000000000000 : ℝ)*base89 + (4461/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23791/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23791/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (114080774881124919/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (1880059954297/1000000000000 : ℝ)*(base40) + (306609564273/1000000000000 : ℝ)*(base50) + (1602785184077/250000000000 : ℝ)*(major_s2_0) + (1602480866389/250000000000 : ℝ)*(major_s2_1) + (1602480866389/250000000000 : ℝ)*(major_s2_2) + (26057127/1000000000000 : ℝ)*(sp_s2_0) + (47256513/250000000000 : ℝ)*(sp_s2_1) + (270109983/1000000000000 : ℝ)*(sp_s2_2) + (38039711/31250000000 : ℝ)*(sp_s2_3) + (28601381/200000000000 : ℝ)*(sp_s2_7) + (4428934438891/500000000000 : ℝ)*(sp_s2_21) + (8857848915761/1000000000000 : ℝ)*(sp_s2_22) + (8857767831831/1000000000000 : ℝ)*(sp_s2_23) + (19809025933/5000000000 : ℝ)*(sp_s2_27) + (19809025933/5000000000 : ℝ)*(f.failure) + (8858037941813/1000000000000 : ℝ)*(f.sum) + (99232965009384153351/201454611250000000000000000000000 : ℝ)*base63 + (151727197180051/213134375000000000000000000 : ℝ)*base65 + (1217332994144319/1476875000000000000000000000 : ℝ)*base66 + (3502462796701/682030000000000000000000000 : ℝ)*base68 + (2784794967773741479/59636703200000000000000000000000 : ℝ)*base70 + (86704394301387/874400000000000000000000000 : ℝ)*base72 + (237173628191577/738437500000000000000000000 : ℝ)*base74 + (415937374594411/874400000000000000000000000 : ℝ)*base77 + (11228599448972847631/51655180000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (131/500000000000000 : ℝ)*base86 + (131/500000000000000 : ℝ)*base88 + (131/500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((1093/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1093/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2363/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-2363/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68203/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(68203/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3893/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3893/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-22297/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-22297/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23791/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23791/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310045_s2 p hpa hpb X hX hprev1

#print axioms solution
