-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301059_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:36:36.370991+00:00
-- url     : https://prove2.me/submissions/c3ccac51-2e78-400b-99a1-72fddd1c178e

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
theorem collision_support_c301059_s6_s6_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1819131947/5000000000 : ℝ)*x 0 + (226326787/625000000 : ℝ)*x 1 + (5737605413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1819131947/5000000000 : ℝ)^65 ≤ (26152469825367/100000000000000 : ℝ)^49 := by
    have hnat : (1819131947 : ℕ)^65*100000000000000^49 ≤ 26152469825367^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819131947 5000000000 26152469825367 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226326787/625000000 : ℝ)^65 ≤ (3248769610253/12500000000000 : ℝ)^49 := by
    have hnat : (226326787 : ℕ)^65*12500000000000^49 ≤ 3248769610253^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226326787 625000000 3248769610253 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5737605413/10000000000 : ℝ)^65 ≤ (23928686639353/50000000000000 : ℝ)^49 := by
    have hnat : (5737605413 : ℕ)^65*50000000000000^49 ≤ 23928686639353^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5737605413 10000000000 23928686639353 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1819131947/5000000000 : ℝ), (226326787/625000000 : ℝ), (5737605413/10000000000 : ℝ)] ![(26152469825367/100000000000000 : ℝ), (3248769610253/12500000000000 : ℝ), (23928686639353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1819131947/5000000000 : ℝ)|^65 ≤ (26152469825367/100000000000000 : ℝ)^49
        have hw : |(-1819131947/5000000000 : ℝ)|=(1819131947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226326787/625000000 : ℝ)|^65 ≤ (3248769610253/12500000000000 : ℝ)^49
        have hw : |(226326787/625000000 : ℝ)|=(226326787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5737605413/10000000000 : ℝ)|^65 ≤ (23928686639353/50000000000000 : ℝ)^49
        have hw : |(5737605413/10000000000 : ℝ)|=(5737605413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3621256171/10000000000 : ℝ)*x 0 + (-1802098091/5000000000 : ℝ)*x 1 + (2883435749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3621256171/10000000000 : ℝ)^65 ≤ (5198083890911/20000000000000 : ℝ)^49 := by
    have hnat : (3621256171 : ℕ)^65*20000000000000^49 ≤ 5198083890911^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3621256171 10000000000 5198083890911 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1802098091/5000000000 : ℝ)^65 ≤ (12914060283793/50000000000000 : ℝ)^49 := by
    have hnat : (1802098091 : ℕ)^65*50000000000000^49 ≤ 12914060283793^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802098091 5000000000 12914060283793 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2883435749/5000000000 : ℝ)^65 ≤ (1927258398681/4000000000000 : ℝ)^49 := by
    have hnat : (2883435749 : ℕ)^65*4000000000000^49 ≤ 1927258398681^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2883435749 5000000000 1927258398681 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3621256171/10000000000 : ℝ), (-1802098091/5000000000 : ℝ), (2883435749/5000000000 : ℝ)] ![(5198083890911/20000000000000 : ℝ), (12914060283793/50000000000000 : ℝ), (1927258398681/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3621256171/10000000000 : ℝ)|^65 ≤ (5198083890911/20000000000000 : ℝ)^49
        have hw : |(3621256171/10000000000 : ℝ)|=(3621256171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1802098091/5000000000 : ℝ)|^65 ≤ (12914060283793/50000000000000 : ℝ)^49
        have hw : |(-1802098091/5000000000 : ℝ)|=(1802098091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2883435749/5000000000 : ℝ)|^65 ≤ (1927258398681/4000000000000 : ℝ)^49
        have hw : |(2883435749/5000000000 : ℝ)|=(2883435749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5571606069/10000000000 : ℝ)*x 0 + (5553006949/10000000000 : ℝ)*x 1 + (-188749951/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5571606069/10000000000 : ℝ)^65 ≤ (46029390920999/100000000000000 : ℝ)^49 := by
    have hnat : (5571606069 : ℕ)^65*100000000000000^49 ≤ 46029390920999^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5571606069 10000000000 46029390920999 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5553006949/10000000000 : ℝ)^65 ≤ (22912836892807/50000000000000 : ℝ)^49 := by
    have hnat : (5553006949 : ℕ)^65*50000000000000^49 ≤ 22912836892807^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5553006949 10000000000 22912836892807 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188749951/1250000000 : ℝ)^65 ≤ (1018116909839/12500000000000 : ℝ)^49 := by
    have hnat : (188749951 : ℕ)^65*12500000000000^49 ≤ 1018116909839^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188749951 1250000000 1018116909839 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5571606069/10000000000 : ℝ), (5553006949/10000000000 : ℝ), (-188749951/1250000000 : ℝ)] ![(46029390920999/100000000000000 : ℝ), (22912836892807/50000000000000 : ℝ), (1018116909839/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5571606069/10000000000 : ℝ)|^65 ≤ (46029390920999/100000000000000 : ℝ)^49
        have hw : |(5571606069/10000000000 : ℝ)|=(5571606069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5553006949/10000000000 : ℝ)|^65 ≤ (22912836892807/50000000000000 : ℝ)^49
        have hw : |(5553006949/10000000000 : ℝ)|=(5553006949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188749951/1250000000 : ℝ)|^65 ≤ (1018116909839/12500000000000 : ℝ)^49
        have hw : |(-188749951/1250000000 : ℝ)|=(188749951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_5 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-127/10000000000 : ℝ)*x 0 + (127/10000000000 : ℝ)*x 1 + (9999999999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127/10000000000 : ℝ)^65 ≤ (1677/50000000000000 : ℝ)^49 := by
    have hnat : (127 : ℕ)^65*50000000000000^49 ≤ 1677^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127 10000000000 1677 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127/10000000000 : ℝ)^65 ≤ (1677/50000000000000 : ℝ)^49 := by
    have hnat : (127 : ℕ)^65*50000000000000^49 ≤ 1677^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127 10000000000 1677 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9999999999/10000000000 : ℝ)^65 ≤ (19999999997347/20000000000000 : ℝ)^49 := by
    have hnat : (9999999999 : ℕ)^65*20000000000000^49 ≤ 19999999997347^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 19999999997347 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127/10000000000 : ℝ), (127/10000000000 : ℝ), (9999999999/10000000000 : ℝ)] ![(1677/50000000000000 : ℝ), (1677/50000000000000 : ℝ), (19999999997347/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127/10000000000 : ℝ)|^65 ≤ (1677/50000000000000 : ℝ)^49
        have hw : |(-127/10000000000 : ℝ)|=(127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(127/10000000000 : ℝ)|^65 ≤ (1677/50000000000000 : ℝ)^49
        have hw : |(127/10000000000 : ℝ)|=(127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9999999999/10000000000 : ℝ)|^65 ≤ (19999999997347/20000000000000 : ℝ)^49
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2226118517/5000000000 : ℝ)*x 0 + (2277735427/5000000000 : ℝ)*x 1 + (4093109041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2226118517/5000000000 : ℝ)^65 ≤ (3418442881571/10000000000000 : ℝ)^49 := by
    have hnat : (2226118517 : ℕ)^65*10000000000000^49 ≤ 3418442881571^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226118517 5000000000 3418442881571 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2277735427/5000000000 : ℝ)^65 ≤ (35239840390187/100000000000000 : ℝ)^49 := by
    have hnat : (2277735427 : ℕ)^65*100000000000000^49 ≤ 35239840390187^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277735427 5000000000 35239840390187 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4093109041/10000000000 : ℝ)^65 ≤ (30575730777491/100000000000000 : ℝ)^49 := by
    have hnat : (4093109041 : ℕ)^65*100000000000000^49 ≤ 30575730777491^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4093109041 10000000000 30575730777491 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2226118517/5000000000 : ℝ), (2277735427/5000000000 : ℝ), (4093109041/10000000000 : ℝ)] ![(3418442881571/10000000000000 : ℝ), (35239840390187/100000000000000 : ℝ), (30575730777491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2226118517/5000000000 : ℝ)|^65 ≤ (3418442881571/10000000000000 : ℝ)^49
        have hw : |(2226118517/5000000000 : ℝ)|=(2226118517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2277735427/5000000000 : ℝ)|^65 ≤ (35239840390187/100000000000000 : ℝ)^49
        have hw : |(2277735427/5000000000 : ℝ)|=(2277735427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4093109041/10000000000 : ℝ)|^65 ≤ (30575730777491/100000000000000 : ℝ)^49
        have hw : |(4093109041/10000000000 : ℝ)|=(4093109041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-723654683/2000000000 : ℝ)*x 0 + (3521291727/10000000000 : ℝ)*x 1 + (5840122223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (723654683/2000000000 : ℝ)^65 ≤ (25962025189837/100000000000000 : ℝ)^49 := by
    have hnat : (723654683 : ℕ)^65*100000000000000^49 ≤ 25962025189837^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723654683 2000000000 25962025189837 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3521291727/10000000000 : ℝ)^65 ≤ (25042998932097/100000000000000 : ℝ)^49 := by
    have hnat : (3521291727 : ℕ)^65*100000000000000^49 ≤ 25042998932097^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3521291727 10000000000 25042998932097 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5840122223/10000000000 : ℝ)^65 ≤ (48994975858079/100000000000000 : ℝ)^49 := by
    have hnat : (5840122223 : ℕ)^65*100000000000000^49 ≤ 48994975858079^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5840122223 10000000000 48994975858079 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-723654683/2000000000 : ℝ), (3521291727/10000000000 : ℝ), (5840122223/10000000000 : ℝ)] ![(25962025189837/100000000000000 : ℝ), (25042998932097/100000000000000 : ℝ), (48994975858079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-723654683/2000000000 : ℝ)|^65 ≤ (25962025189837/100000000000000 : ℝ)^49
        have hw : |(-723654683/2000000000 : ℝ)|=(723654683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3521291727/10000000000 : ℝ)|^65 ≤ (25042998932097/100000000000000 : ℝ)^49
        have hw : |(3521291727/10000000000 : ℝ)|=(3521291727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5840122223/10000000000 : ℝ)|^65 ≤ (48994975858079/100000000000000 : ℝ)^49
        have hw : |(5840122223/10000000000 : ℝ)|=(5840122223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3601482141/10000000000 : ℝ)*x 0 + (-700731741/2000000000 : ℝ)*x 1 + (2934692173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3601482141/10000000000 : ℝ)^65 ≤ (25802323837599/100000000000000 : ℝ)^49 := by
    have hnat : (3601482141 : ℕ)^65*100000000000000^49 ≤ 25802323837599^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3601482141 10000000000 25802323837599 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (700731741/2000000000 : ℝ)^65 ≤ (24876782962217/100000000000000 : ℝ)^49 := by
    have hnat : (700731741 : ℕ)^65*100000000000000^49 ≤ 24876782962217^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700731741 2000000000 24876782962217 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2934692173/5000000000 : ℝ)^65 ≤ (2466044659229/5000000000000 : ℝ)^49 := by
    have hnat : (2934692173 : ℕ)^65*5000000000000^49 ≤ 2466044659229^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934692173 5000000000 2466044659229 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3601482141/10000000000 : ℝ), (-700731741/2000000000 : ℝ), (2934692173/5000000000 : ℝ)] ![(25802323837599/100000000000000 : ℝ), (24876782962217/100000000000000 : ℝ), (2466044659229/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3601482141/10000000000 : ℝ)|^65 ≤ (25802323837599/100000000000000 : ℝ)^49
        have hw : |(3601482141/10000000000 : ℝ)|=(3601482141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-700731741/2000000000 : ℝ)|^65 ≤ (24876782962217/100000000000000 : ℝ)^49
        have hw : |(-700731741/2000000000 : ℝ)|=(700731741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2934692173/5000000000 : ℝ)|^65 ≤ (2466044659229/5000000000000 : ℝ)^49
        have hw : |(2934692173/5000000000 : ℝ)|=(2934692173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5543737483/10000000000 : ℝ)*x 0 + (705789481/1250000000 : ℝ)*x 1 + (-70418413/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5543737483/10000000000 : ℝ)^65 ≤ (9144845590447/20000000000000 : ℝ)^49 := by
    have hnat : (5543737483 : ℕ)^65*20000000000000^49 ≤ 9144845590447^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5543737483 10000000000 9144845590447 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (705789481/1250000000 : ℝ)^65 ≤ (46849924661887/100000000000000 : ℝ)^49 := by
    have hnat : (705789481 : ℕ)^65*100000000000000^49 ≤ 46849924661887^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      705789481 1250000000 46849924661887 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70418413/500000000 : ℝ)^65 ≤ (742584736029/10000000000000 : ℝ)^49 := by
    have hnat : (70418413 : ℕ)^65*10000000000000^49 ≤ 742584736029^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70418413 500000000 742584736029 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5543737483/10000000000 : ℝ), (705789481/1250000000 : ℝ), (-70418413/500000000 : ℝ)] ![(9144845590447/20000000000000 : ℝ), (46849924661887/100000000000000 : ℝ), (742584736029/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5543737483/10000000000 : ℝ)|^65 ≤ (9144845590447/20000000000000 : ℝ)^49
        have hw : |(5543737483/10000000000 : ℝ)|=(5543737483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(705789481/1250000000 : ℝ)|^65 ≤ (46849924661887/100000000000000 : ℝ)^49
        have hw : |(705789481/1250000000 : ℝ)|=(705789481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-70418413/500000000 : ℝ)|^65 ≤ (742584736029/10000000000000 : ℝ)^49
        have hw : |(-70418413/500000000 : ℝ)|=(70418413/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (885706443/2000000000 : ℝ)*x 0 + (4768378263/10000000000 : ℝ)*x 1 + (3893704529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (885706443/2000000000 : ℝ)^65 ≤ (33943201859909/100000000000000 : ℝ)^49 := by
    have hnat : (885706443 : ℕ)^65*100000000000000^49 ≤ 33943201859909^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885706443 2000000000 33943201859909 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4768378263/10000000000 : ℝ)^65 ≤ (18720562395219/50000000000000 : ℝ)^49 := by
    have hnat : (4768378263 : ℕ)^65*50000000000000^49 ≤ 18720562395219^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4768378263 10000000000 18720562395219 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3893704529/10000000000 : ℝ)^65 ≤ (894239791611/3125000000000 : ℝ)^49 := by
    have hnat : (3893704529 : ℕ)^65*3125000000000^49 ≤ 894239791611^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3893704529 10000000000 894239791611 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(885706443/2000000000 : ℝ), (4768378263/10000000000 : ℝ), (3893704529/10000000000 : ℝ)] ![(33943201859909/100000000000000 : ℝ), (18720562395219/50000000000000 : ℝ), (894239791611/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(885706443/2000000000 : ℝ)|^65 ≤ (33943201859909/100000000000000 : ℝ)^49
        have hw : |(885706443/2000000000 : ℝ)|=(885706443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4768378263/10000000000 : ℝ)|^65 ≤ (18720562395219/50000000000000 : ℝ)^49
        have hw : |(4768378263/10000000000 : ℝ)|=(4768378263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3893704529/10000000000 : ℝ)|^65 ≤ (894239791611/3125000000000 : ℝ)^49
        have hw : |(3893704529/10000000000 : ℝ)|=(3893704529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-176886421/500000000 : ℝ)*x 0 + (1800858957/5000000000 : ℝ)*x 1 + (1460081701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176886421/500000000 : ℝ)^65 ≤ (12599091395737/50000000000000 : ℝ)^49 := by
    have hnat : (176886421 : ℕ)^65*50000000000000^49 ≤ 12599091395737^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176886421 500000000 12599091395737 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1800858957/5000000000 : ℝ)^65 ≤ (5160912917663/20000000000000 : ℝ)^49 := by
    have hnat : (1800858957 : ℕ)^65*20000000000000^49 ≤ 5160912917663^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800858957 5000000000 5160912917663 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1460081701/2500000000 : ℝ)^65 ≤ (6124656575567/12500000000000 : ℝ)^49 := by
    have hnat : (1460081701 : ℕ)^65*12500000000000^49 ≤ 6124656575567^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460081701 2500000000 6124656575567 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-176886421/500000000 : ℝ), (1800858957/5000000000 : ℝ), (1460081701/2500000000 : ℝ)] ![(12599091395737/50000000000000 : ℝ), (5160912917663/20000000000000 : ℝ), (6124656575567/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-176886421/500000000 : ℝ)|^65 ≤ (12599091395737/50000000000000 : ℝ)^49
        have hw : |(-176886421/500000000 : ℝ)|=(176886421/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1800858957/5000000000 : ℝ)|^65 ≤ (5160912917663/20000000000000 : ℝ)^49
        have hw : |(1800858957/5000000000 : ℝ)|=(1800858957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1460081701/2500000000 : ℝ)|^65 ≤ (6124656575567/12500000000000 : ℝ)^49
        have hw : |(1460081701/2500000000 : ℝ)|=(1460081701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (110021031/312500000 : ℝ)*x 0 + (-448044249/1250000000 : ℝ)*x 1 + (2934794269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110021031/312500000 : ℝ)^65 ≤ (782411308641/3125000000000 : ℝ)^49 := by
    have hnat : (110021031 : ℕ)^65*3125000000000^49 ≤ 782411308641^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110021031 312500000 782411308641 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448044249/1250000000 : ℝ)^65 ≤ (12819834392657/50000000000000 : ℝ)^49 := by
    have hnat : (448044249 : ℕ)^65*50000000000000^49 ≤ 12819834392657^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448044249 1250000000 12819834392657 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2934794269/5000000000 : ℝ)^65 ≤ (49323169313463/100000000000000 : ℝ)^49 := by
    have hnat : (2934794269 : ℕ)^65*100000000000000^49 ≤ 49323169313463^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934794269 5000000000 49323169313463 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(110021031/312500000 : ℝ), (-448044249/1250000000 : ℝ), (2934794269/5000000000 : ℝ)] ![(782411308641/3125000000000 : ℝ), (12819834392657/50000000000000 : ℝ), (49323169313463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(110021031/312500000 : ℝ)|^65 ≤ (782411308641/3125000000000 : ℝ)^49
        have hw : |(110021031/312500000 : ℝ)|=(110021031/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-448044249/1250000000 : ℝ)|^65 ≤ (12819834392657/50000000000000 : ℝ)^49
        have hw : |(-448044249/1250000000 : ℝ)|=(448044249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2934794269/5000000000 : ℝ)|^65 ≤ (49323169313463/100000000000000 : ℝ)^49
        have hw : |(2934794269/5000000000 : ℝ)|=(2934794269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5668307243/10000000000 : ℝ)*x 0 + (1104343199/2000000000 : ℝ)*x 1 + (-704082209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5668307243/10000000000 : ℝ)^65 ≤ (47092133295033/100000000000000 : ℝ)^49 := by
    have hnat : (5668307243 : ℕ)^65*100000000000000^49 ≤ 47092133295033^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5668307243 10000000000 47092133295033 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104343199/2000000000 : ℝ)^65 ≤ (45483445041/100000000000 : ℝ)^49 := by
    have hnat : (1104343199 : ℕ)^65*100000000000^49 ≤ 45483445041^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104343199 2000000000 45483445041 100000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (704082209/5000000000 : ℝ)^65 ≤ (3712210826329/50000000000000 : ℝ)^49 := by
    have hnat : (704082209 : ℕ)^65*50000000000000^49 ≤ 3712210826329^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704082209 5000000000 3712210826329 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5668307243/10000000000 : ℝ), (1104343199/2000000000 : ℝ), (-704082209/5000000000 : ℝ)] ![(47092133295033/100000000000000 : ℝ), (45483445041/100000000000 : ℝ), (3712210826329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5668307243/10000000000 : ℝ)|^65 ≤ (47092133295033/100000000000000 : ℝ)^49
        have hw : |(5668307243/10000000000 : ℝ)|=(5668307243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1104343199/2000000000 : ℝ)|^65 ≤ (45483445041/100000000000 : ℝ)^49
        have hw : |(1104343199/2000000000 : ℝ)|=(1104343199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-704082209/5000000000 : ℝ)|^65 ≤ (3712210826329/50000000000000 : ℝ)^49
        have hw : |(-704082209/5000000000 : ℝ)|=(704082209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2329897967/5000000000 : ℝ)*x 0 + (4539286359/10000000000 : ℝ)*x 1 + (486663031/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2329897967/5000000000 : ℝ)^65 ≤ (18157186006701/50000000000000 : ℝ)^49 := by
    have hnat : (2329897967 : ℕ)^65*50000000000000^49 ≤ 18157186006701^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2329897967 5000000000 18157186006701 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4539286359/10000000000 : ℝ)^65 ≤ (35073856894759/100000000000000 : ℝ)^49 := by
    have hnat : (4539286359 : ℕ)^65*100000000000000^49 ≤ 35073856894759^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539286359 10000000000 35073856894759 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (486663031/1250000000 : ℝ)^65 ≤ (5722354214781/20000000000000 : ℝ)^49 := by
    have hnat : (486663031 : ℕ)^65*20000000000000^49 ≤ 5722354214781^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486663031 1250000000 5722354214781 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2329897967/5000000000 : ℝ), (4539286359/10000000000 : ℝ), (486663031/1250000000 : ℝ)] ![(18157186006701/50000000000000 : ℝ), (35073856894759/100000000000000 : ℝ), (5722354214781/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2329897967/5000000000 : ℝ)|^65 ≤ (18157186006701/50000000000000 : ℝ)^49
        have hw : |(2329897967/5000000000 : ℝ)|=(2329897967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4539286359/10000000000 : ℝ)|^65 ≤ (35073856894759/100000000000000 : ℝ)^49
        have hw : |(4539286359/10000000000 : ℝ)|=(4539286359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(486663031/1250000000 : ℝ)|^65 ≤ (5722354214781/20000000000000 : ℝ)^49
        have hw : |(486663031/1250000000 : ℝ)|=(486663031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-145541399/400000000 : ℝ)*x 0 + (3621833437/10000000000 : ℝ)*x 1 + (1147370263/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (145541399/400000000 : ℝ)^65 ≤ (26155054703971/100000000000000 : ℝ)^49 := by
    have hnat : (145541399 : ℕ)^65*100000000000000^49 ≤ 26155054703971^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145541399 400000000 26155054703971 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3621833437/10000000000 : ℝ)^65 ≤ (25995915604827/100000000000000 : ℝ)^49 := by
    have hnat : (3621833437 : ℕ)^65*100000000000000^49 ≤ 25995915604827^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3621833437 10000000000 25995915604827 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147370263/2000000000 : ℝ)^65 ≤ (1196225741751/2500000000000 : ℝ)^49 := by
    have hnat : (1147370263 : ℕ)^65*2500000000000^49 ≤ 1196225741751^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147370263 2000000000 1196225741751 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-145541399/400000000 : ℝ), (3621833437/10000000000 : ℝ), (1147370263/2000000000 : ℝ)] ![(26155054703971/100000000000000 : ℝ), (25995915604827/100000000000000 : ℝ), (1196225741751/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-145541399/400000000 : ℝ)|^65 ≤ (26155054703971/100000000000000 : ℝ)^49
        have hw : |(-145541399/400000000 : ℝ)|=(145541399/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3621833437/10000000000 : ℝ)|^65 ≤ (25995915604827/100000000000000 : ℝ)^49
        have hw : |(3621833437/10000000000 : ℝ)|=(3621833437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1147370263/2000000000 : ℝ)|^65 ≤ (1196225741751/2500000000000 : ℝ)^49
        have hw : |(1147370263/2000000000 : ℝ)|=(1147370263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (452733731/1250000000 : ℝ)*x 0 + (-3604465447/10000000000 : ℝ)*x 1 + (5766113337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (452733731/1250000000 : ℝ)^65 ≤ (3249532785449/12500000000000 : ℝ)^49 := by
    have hnat : (452733731 : ℕ)^65*12500000000000^49 ≤ 3249532785449^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452733731 1250000000 3249532785449 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3604465447/10000000000 : ℝ)^65 ≤ (3228835031823/12500000000000 : ℝ)^49 := by
    have hnat : (3604465447 : ℕ)^65*12500000000000^49 ≤ 3228835031823^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3604465447 10000000000 3228835031823 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5766113337/10000000000 : ℝ)^65 ≤ (9634611491257/20000000000000 : ℝ)^49 := by
    have hnat : (5766113337 : ℕ)^65*20000000000000^49 ≤ 9634611491257^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5766113337 10000000000 9634611491257 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(452733731/1250000000 : ℝ), (-3604465447/10000000000 : ℝ), (5766113337/10000000000 : ℝ)] ![(3249532785449/12500000000000 : ℝ), (3228835031823/12500000000000 : ℝ), (9634611491257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(452733731/1250000000 : ℝ)|^65 ≤ (3249532785449/12500000000000 : ℝ)^49
        have hw : |(452733731/1250000000 : ℝ)|=(452733731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3604465447/10000000000 : ℝ)|^65 ≤ (3228835031823/12500000000000 : ℝ)^49
        have hw : |(-3604465447/10000000000 : ℝ)|=(3604465447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5766113337/10000000000 : ℝ)|^65 ≤ (9634611491257/20000000000000 : ℝ)^49
        have hw : |(5766113337/10000000000 : ℝ)|=(5766113337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1142039613/2000000000 : ℝ)*x 0 + (5415632827/10000000000 : ℝ)*x 1 + (-1506192219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1142039613/2000000000 : ℝ)^65 ≤ (47554358873361/100000000000000 : ℝ)^49 := by
    have hnat : (1142039613 : ℕ)^65*100000000000000^49 ≤ 47554358873361^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142039613 2000000000 47554358873361 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415632827/10000000000 : ℝ)^65 ≤ (22163968820717/50000000000000 : ℝ)^49 := by
    have hnat : (5415632827 : ℕ)^65*50000000000000^49 ≤ 22163968820717^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415632827 10000000000 22163968820717 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506192219/10000000000 : ℝ)^65 ≤ (4058851737487/50000000000000 : ℝ)^49 := by
    have hnat : (1506192219 : ℕ)^65*50000000000000^49 ≤ 4058851737487^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506192219 10000000000 4058851737487 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1142039613/2000000000 : ℝ), (5415632827/10000000000 : ℝ), (-1506192219/10000000000 : ℝ)] ![(47554358873361/100000000000000 : ℝ), (22163968820717/50000000000000 : ℝ), (4058851737487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1142039613/2000000000 : ℝ)|^65 ≤ (47554358873361/100000000000000 : ℝ)^49
        have hw : |(1142039613/2000000000 : ℝ)|=(1142039613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415632827/10000000000 : ℝ)|^65 ≤ (22163968820717/50000000000000 : ℝ)^49
        have hw : |(5415632827/10000000000 : ℝ)|=(5415632827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1506192219/10000000000 : ℝ)|^65 ≤ (4058851737487/50000000000000 : ℝ)^49
        have hw : |(-1506192219/10000000000 : ℝ)|=(1506192219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s6_s6_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (167285337/400000000 : ℝ)*x 0 + (965165911/2000000000 : ℝ)*x 1 + (817058181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167285337/400000000 : ℝ)^65 ≤ (7865253275647/25000000000000 : ℝ)^49 := by
    have hnat : (167285337 : ℕ)^65*25000000000000^49 ≤ 7865253275647^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167285337 400000000 7865253275647 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965165911/2000000000 : ℝ)^65 ≤ (4755087975669/12500000000000 : ℝ)^49 := by
    have hnat : (965165911 : ℕ)^65*12500000000000^49 ≤ 4755087975669^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965165911 2000000000 4755087975669 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (817058181/2000000000 : ℝ)^65 ≤ (15249141539589/50000000000000 : ℝ)^49 := by
    have hnat : (817058181 : ℕ)^65*50000000000000^49 ≤ 15249141539589^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817058181 2000000000 15249141539589 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167285337/400000000 : ℝ), (965165911/2000000000 : ℝ), (817058181/2000000000 : ℝ)] ![(7865253275647/25000000000000 : ℝ), (4755087975669/12500000000000 : ℝ), (15249141539589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167285337/400000000 : ℝ)|^65 ≤ (7865253275647/25000000000000 : ℝ)^49
        have hw : |(167285337/400000000 : ℝ)|=(167285337/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(965165911/2000000000 : ℝ)|^65 ≤ (4755087975669/12500000000000 : ℝ)^49
        have hw : |(965165911/2000000000 : ℝ)|=(965165911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(817058181/2000000000 : ℝ)|^65 ≤ (15249141539589/50000000000000 : ℝ)^49
        have hw : |(817058181/2000000000 : ℝ)|=(817058181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301059_s6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((28449/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28449/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54773/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(54773/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(24513/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(24513/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20189/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20189/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9957/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9957/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(79/4000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(79/4000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (28449/50000 : ℝ) ^ (129/32 : ℝ) ≤ (102975707634983083/1000000000000000000 : ℝ) := by
    have hpowers : (28449/50000 : ℝ)^129 ≤ (102975707634983083/1000000000000000000 : ℝ)^32 := by
      have hnat : (28449 : ℕ)^129*1000000000000000000^32 ≤ 102975707634983083^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28449 50000 102975707634983083 1000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28449/50000 : ℝ)) (X := (102975707634983083/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner0a : (1102975707634983083/1000000000000000000 : ℝ) ≤ (2049221908774573/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (1102975707634983083/1000000000000000000 : ℝ)^32 ≤ (2049221908774573/2000000000000000 : ℝ)^129 := by
      have hnat : (1102975707634983083 : ℕ)^32*2000000000000000^129 ≤ 2049221908774573^129*1000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1102975707634983083 1000000000000000000 2049221908774573 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2049221908774573/2000000000000000 : ℝ)) (X := (1102975707634983083/1000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner0b : (602975707634983083/500000000000000000 : ℝ) ≤ (5237750913916533/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (602975707634983083/500000000000000000 : ℝ)^32 ≤ (5237750913916533/5000000000000000 : ℝ)^129 := by
      have hnat : (602975707634983083 : ℕ)^32*5000000000000000^129 ≤ 5237750913916533^129*500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        602975707634983083 500000000000000000 5237750913916533 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5237750913916533/5000000000000000 : ℝ)) (X := (602975707634983083/500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(49221908774573/1137960000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(229392283960201/5689800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (28449/50000 : ℝ)) (alpha := (49221908774573/1137960000000000 : ℝ)) (beta := (229392283960201/5689800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (28449/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(49221908774573/1137960000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(229392283960201/5689800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (54773/100000 : ℝ) ^ (129/32 : ℝ) ≤ (2208189430869940703/25000000000000000000 : ℝ) := by
    have hpowers : (54773/100000 : ℝ)^129 ≤ (2208189430869940703/25000000000000000000 : ℝ)^32 := by
      have hnat : (54773 : ℕ)^129*25000000000000000000^32 ≤ 2208189430869940703^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54773 100000 2208189430869940703 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (54773/100000 : ℝ)) (X := (2208189430869940703/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner1a : (27208189430869940703/25000000000000000000 : ℝ) ≤ (10212184886421047/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (27208189430869940703/25000000000000000000 : ℝ)^32 ≤ (10212184886421047/10000000000000000 : ℝ)^129 := by
      have hnat : (27208189430869940703 : ℕ)^32*10000000000000000^129 ≤ 10212184886421047^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27208189430869940703 25000000000000000000 10212184886421047 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10212184886421047/10000000000000000 : ℝ)) (X := (27208189430869940703/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner1b : (14708189430869940703/12500000000000000000 : ℝ) ≤ (2602947399912939/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (14708189430869940703/12500000000000000000 : ℝ)^32 ≤ (2602947399912939/2500000000000000 : ℝ)^129 := by
      have hnat : (14708189430869940703 : ℕ)^32*2500000000000000^129 ≤ 2602947399912939^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14708189430869940703 12500000000000000000 2602947399912939 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2602947399912939/2500000000000000 : ℝ)) (X := (14708189430869940703/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(212184886421047/5477300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(199604713230709/5477300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (54773/100000 : ℝ)) (alpha := (212184886421047/5477300000000000 : ℝ)) (beta := (199604713230709/5477300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (54773/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(212184886421047/5477300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(199604713230709/5477300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (24513/100000 : ℝ) ^ (129/32 : ℝ) ≤ (34554491029660067/10000000000000000000 : ℝ) := by
    have hpowers : (24513/100000 : ℝ)^129 ≤ (34554491029660067/10000000000000000000 : ℝ)^32 := by
      have hnat : (24513 : ℕ)^129*10000000000000000000^32 ≤ 34554491029660067^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24513 100000 34554491029660067 10000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24513/100000 : ℝ)) (X := (34554491029660067/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner2a : (10034554491029660067/10000000000000000000 : ℝ) ≤ (5004280271655251/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (10034554491029660067/10000000000000000000 : ℝ)^32 ≤ (5004280271655251/5000000000000000 : ℝ)^129 := by
      have hnat : (10034554491029660067 : ℕ)^32*5000000000000000^129 ≤ 5004280271655251^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10034554491029660067 10000000000000000000 5004280271655251 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004280271655251/5000000000000000 : ℝ)) (X := (10034554491029660067/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner2b : (5034554491029660067/5000000000000000000 : ℝ) ≤ (1252137368638743/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (5034554491029660067/5000000000000000000 : ℝ)^32 ≤ (1252137368638743/1250000000000000 : ℝ)^129 := by
      have hnat : (5034554491029660067 : ℕ)^32*1250000000000000^129 ≤ 1252137368638743^129*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5034554491029660067 5000000000000000000 1252137368638743 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252137368638743/1250000000000000 : ℝ)) (X := (5034554491029660067/5000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1426757218417/408550000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(4269202899721/1225650000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (24513/100000 : ℝ)) (alpha := (1426757218417/408550000000000 : ℝ)) (beta := (4269202899721/1225650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (24513/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1426757218417/408550000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(4269202899721/1225650000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-1819131947/5000000000 : ℝ)*X 0 0+(226326787/625000000 : ℝ)*X 0 1+(5737605413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((3621256171/10000000000 : ℝ)*X 1 0+(-1802098091/5000000000 : ℝ)*X 1 1+(2883435749/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((5571606069/10000000000 : ℝ)*X 2 0+(5553006949/10000000000 : ℝ)*X 2 1+(-188749951/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_5 : ((-127/10000000000 : ℝ)*X 0 0+(127/10000000000 : ℝ)*X 0 1+(9999999999/10000000000 : ℝ)*X 0 2+(-127/10000000000 : ℝ)*X 1 0+(127/10000000000 : ℝ)*X 1 1+(9999999999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_5 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((2226118517/5000000000 : ℝ)*X 0 0+(2277735427/5000000000 : ℝ)*X 0 1+(4093109041/10000000000 : ℝ)*X 0 2+(2226118517/5000000000 : ℝ)*X 1 0+(2277735427/5000000000 : ℝ)*X 1 1+(4093109041/10000000000 : ℝ)*X 1 2+(2226118517/5000000000 : ℝ)*X 2 0+(2277735427/5000000000 : ℝ)*X 2 1+(4093109041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-723654683/2000000000 : ℝ)*X 0 0+(3521291727/10000000000 : ℝ)*X 0 1+(5840122223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((3601482141/10000000000 : ℝ)*X 1 0+(-700731741/2000000000 : ℝ)*X 1 1+(2934692173/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((5543737483/10000000000 : ℝ)*X 2 0+(705789481/1250000000 : ℝ)*X 2 1+(-70418413/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((885706443/2000000000 : ℝ)*X 0 0+(4768378263/10000000000 : ℝ)*X 0 1+(3893704529/10000000000 : ℝ)*X 0 2+(885706443/2000000000 : ℝ)*X 1 0+(4768378263/10000000000 : ℝ)*X 1 1+(3893704529/10000000000 : ℝ)*X 1 2+(885706443/2000000000 : ℝ)*X 2 0+(4768378263/10000000000 : ℝ)*X 2 1+(3893704529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-176886421/500000000 : ℝ)*X 0 0+(1800858957/5000000000 : ℝ)*X 0 1+(1460081701/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((110021031/312500000 : ℝ)*X 1 0+(-448044249/1250000000 : ℝ)*X 1 1+(2934794269/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((5668307243/10000000000 : ℝ)*X 2 0+(1104343199/2000000000 : ℝ)*X 2 1+(-704082209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((2329897967/5000000000 : ℝ)*X 0 0+(4539286359/10000000000 : ℝ)*X 0 1+(486663031/1250000000 : ℝ)*X 0 2+(2329897967/5000000000 : ℝ)*X 1 0+(4539286359/10000000000 : ℝ)*X 1 1+(486663031/1250000000 : ℝ)*X 1 2+(2329897967/5000000000 : ℝ)*X 2 0+(4539286359/10000000000 : ℝ)*X 2 1+(486663031/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-145541399/400000000 : ℝ)*X 0 0+(3621833437/10000000000 : ℝ)*X 0 1+(1147370263/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((452733731/1250000000 : ℝ)*X 1 0+(-3604465447/10000000000 : ℝ)*X 1 1+(5766113337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((1142039613/2000000000 : ℝ)*X 2 0+(5415632827/10000000000 : ℝ)*X 2 1+(-1506192219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((167285337/400000000 : ℝ)*X 0 0+(965165911/2000000000 : ℝ)*X 0 1+(817058181/2000000000 : ℝ)*X 0 2+(167285337/400000000 : ℝ)*X 1 0+(965165911/2000000000 : ℝ)*X 1 1+(817058181/2000000000 : ℝ)*X 1 2+(167285337/400000000 : ℝ)*X 2 0+(965165911/2000000000 : ℝ)*X 2 1+(817058181/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((20189/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20189/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1396429601523429468795983984191/212205919269450000000000000000000000 : ℝ) := by norm_num
    linear_combination (2015520973603/250000000000 : ℝ)*(base60) + (4689024784619/125000000000 : ℝ)*(major_s6_0) + (4689024784619/125000000000 : ℝ)*(major_s6_1) + (18756345980841/500000000000 : ℝ)*(major_s6_2) + (19958931/200000000000 : ℝ)*(sp_s6_0) + (24085139/200000000000 : ℝ)*(sp_s6_1) + (61924057/250000000000 : ℝ)*(sp_s6_2) + (493684731/1000000000000 : ℝ)*(sp_s6_5) + (49665192407217/1000000000000 : ℝ)*(sp_s6_7) + (9932972250541/200000000000 : ℝ)*(sp_s6_8) + (9933008901129/200000000000 : ℝ)*(sp_s6_9) + (25358969049311/1000000000000 : ℝ)*(sp_s6_13) + (310523473/1000000000000 : ℝ)*(sp_s6_15) + (66554599/500000000000 : ℝ)*(sp_s6_27) + (6339775539627/250000000000 : ℝ)*(f.failure) + (49665292201873/1000000000000 : ℝ)*(f.sum) + (2974656239245277789/4475501830000000000000000000000 : ℝ)*base62 + (54424635849771/408550000000000000000000000 : ℝ)*base64 + (132893618479511/171165625000000000000000000 : ℝ)*base66 + (93044653934007/204275000000000000000000000 : ℝ)*base68 + (4030476293113241659/11622838950000000000000000000000 : ℝ)*base70 + (964770162698851/711225000000000000000000000 : ℝ)*base72 + (493569668432779/1369325000000000000000000000 : ℝ)*base74 + (112910408517361/284490000000000000000000000 : ℝ)*base76 + (3138497593973900027/15582370770000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (3913/6250000000000000 : ℝ)*base86 + (3913/6250000000000000 : ℝ)*base88 + (2337/6250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9957/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9957/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (542511202571606321019371810157/70735306423150000000000000000000000 : ℝ) := by norm_num
    linear_combination (404143/250000000000 : ℝ)*(base40) + (803516757627/100000000000 : ℝ)*(base60) + (37390557851823/1000000000000 : ℝ)*(major_s6_0) + (37390557851823/1000000000000 : ℝ)*(major_s6_1) + (42396938809447/1000000000000 : ℝ)*(major_s6_2) + (625797619703/125000000000 : ℝ)*(sp_s6_5) + (42272193/250000000000 : ℝ)*(sp_s6_6) + (12375997438553/250000000000 : ℝ)*(sp_s6_14) + (49503999975919/1000000000000 : ℝ)*(sp_s6_15) + (12376001155579/250000000000 : ℝ)*(sp_s6_16) + (12638350683103/500000000000 : ℝ)*(sp_s6_20) + (63234479/250000000000 : ℝ)*(sp_s6_21) + (15169763/62500000000 : ℝ)*(sp_s6_22) + (59517453/250000000000 : ℝ)*(sp_s6_23) + (25276870454979/1000000000000 : ℝ)*(f.failure) + (1547007584129/31250000000 : ℝ)*(f.sum) + (24116957837848150477/44755018300000000000000000000000 : ℝ)*base63 + (735793262293537/1225650000000000000000000000 : ℝ)*base65 + (2283287387638587/5477300000000000000000000000 : ℝ)*base67 + (390558646371821/408550000000000000000000000 : ℝ)*base69 + (424151968916879083/15497118600000000000000000000000 : ℝ)*base71 + (2176533480887701/1896600000000000000000000000 : ℝ)*base73 + (2479683559008081/5477300000000000000000000000 : ℝ)*base75 + (119283783640841/379320000000000000000000000 : ℝ)*base77 + (10535371681117882087/20776494360000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (3399/25000000000000000 : ℝ)*base87 + (3399/25000000000000000 : ℝ)*base89 + (3399/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(79/4000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(79/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (155151208628111386199/10213750000000000000000000 : ℝ) := by norm_num
    linear_combination (4070549/1000000000000 : ℝ)*(base40) + (4147231/1000000000000 : ℝ)*(base50) + (5411997468647/1000000000000 : ℝ)*(base60) + (27371496829703/1000000000000 : ℝ)*(major_s6_0) + (27371496829703/1000000000000 : ℝ)*(major_s6_1) + (27371496829703/1000000000000 : ℝ)*(major_s6_2) + (500141681/1000000000000 : ℝ)*(sp_s6_2) + (14678151/500000000000 : ℝ)*(sp_s6_8) + (124606671/200000000000 : ℝ)*(sp_s6_13) + (325881071/1000000000000 : ℝ)*(sp_s6_16) + (18119616026113/500000000000 : ℝ)*(sp_s6_21) + (9059800673981/250000000000 : ℝ)*(sp_s6_22) + (18119203014737/500000000000 : ℝ)*(sp_s6_23) + (3700626702069/200000000000 : ℝ)*(sp_s6_27) + (185037565437/10000000000 : ℝ)*(f.failure) + (18119616026113/500000000000 : ℝ)*(f.sum) + (7249720616231200913/8951003660000000000000000000000 : ℝ)*base63 + (36540098143733/1225650000000000000000000000 : ℝ)*base65 + (3269697215493873/5477300000000000000000000000 : ℝ)*base66 + (4954856003029/408550000000000000000000000 : ℝ)*base69 + (23746117893700661401/46491355800000000000000000000000 : ℝ)*base71 + (1668540819171697/5689800000000000000000000000 : ℝ)*base72 + (2363119363336419/5477300000000000000000000000 : ℝ)*base74 + (809924624940773/1137960000000000000000000000 : ℝ)*base76 + (23156913940496666429/62329483080000000000000000000000 : ℝ)*base79 + (53/250000000000000 : ℝ)*base86 + (53/250000000000000 : ℝ)*base88 + (53/250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((28449/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28449/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54773/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(54773/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(24513/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(24513/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20189/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20189/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9957/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9957/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(79/4000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(79/4000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301059_s6 p hpa hpb X hX hprev5

#print axioms solution
