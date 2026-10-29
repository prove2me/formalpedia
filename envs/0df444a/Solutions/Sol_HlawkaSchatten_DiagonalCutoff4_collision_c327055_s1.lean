-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c327055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:16:55.88031+00:00
-- url     : https://prove2.me/submissions/2abf2d12-31b1-4304-ac0b-26cf50460cac

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
theorem collision_support_c327055_s1_s1_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (294628421/625000000 : ℝ)*x 0 + (-21436769/250000000 : ℝ)*x 1 + (6088499767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (294628421/625000000 : ℝ)^91 ≤ (40153074695801/100000000000000 : ℝ)^75 := by
    have hnat : (294628421 : ℕ)^91*100000000000000^75 ≤ 40153074695801^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294628421 625000000 40153074695801 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21436769/250000000 : ℝ)^91 ≤ (1269344336217/25000000000000 : ℝ)^75 := by
    have hnat : (21436769 : ℕ)^91*25000000000000^75 ≤ 1269344336217^75*250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21436769 250000000 1269344336217 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6088499767/10000000000 : ℝ)^91 ≤ (10953909590047/20000000000000 : ℝ)^75 := by
    have hnat : (6088499767 : ℕ)^91*20000000000000^75 ≤ 10953909590047^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6088499767 10000000000 10953909590047 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(294628421/625000000 : ℝ), (-21436769/250000000 : ℝ), (6088499767/10000000000 : ℝ)] ![(40153074695801/100000000000000 : ℝ), (1269344336217/25000000000000 : ℝ), (10953909590047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(294628421/625000000 : ℝ)|^91 ≤ (40153074695801/100000000000000 : ℝ)^75
        have hw : |(294628421/625000000 : ℝ)|=(294628421/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21436769/250000000 : ℝ)|^91 ≤ (1269344336217/25000000000000 : ℝ)^75
        have hw : |(-21436769/250000000 : ℝ)|=(21436769/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6088499767/10000000000 : ℝ)|^91 ≤ (10953909590047/20000000000000 : ℝ)^75
        have hw : |(6088499767/10000000000 : ℝ)|=(6088499767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4704275671/10000000000 : ℝ)*x 0 + (5527189111/10000000000 : ℝ)*x 1 + (-1651067711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4704275671/10000000000 : ℝ)^91 ≤ (40052031869321/100000000000000 : ℝ)^75 := by
    have hnat : (4704275671 : ℕ)^91*100000000000000^75 ≤ 40052031869321^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4704275671 10000000000 40052031869321 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5527189111/10000000000 : ℝ)^91 ≤ (48704816699673/100000000000000 : ℝ)^75 := by
    have hnat : (5527189111 : ℕ)^91*100000000000000^75 ≤ 48704816699673^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527189111 10000000000 48704816699673 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1651067711/10000000000 : ℝ)^91 ≤ (2810787854097/25000000000000 : ℝ)^75 := by
    have hnat : (1651067711 : ℕ)^91*25000000000000^75 ≤ 2810787854097^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1651067711 10000000000 2810787854097 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4704275671/10000000000 : ℝ), (5527189111/10000000000 : ℝ), (-1651067711/10000000000 : ℝ)] ![(40052031869321/100000000000000 : ℝ), (48704816699673/100000000000000 : ℝ), (2810787854097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4704275671/10000000000 : ℝ)|^91 ≤ (40052031869321/100000000000000 : ℝ)^75
        have hw : |(4704275671/10000000000 : ℝ)|=(4704275671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5527189111/10000000000 : ℝ)|^91 ≤ (48704816699673/100000000000000 : ℝ)^75
        have hw : |(5527189111/10000000000 : ℝ)|=(5527189111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1651067711/10000000000 : ℝ)|^91 ≤ (2810787854097/25000000000000 : ℝ)^75
        have hw : |(-1651067711/10000000000 : ℝ)|=(1651067711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_7 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-345382229/2500000000 : ℝ)*x 0 + (310801591/625000000 : ℝ)*x 1 + (5470598313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (345382229/2500000000 : ℝ)^91 ≤ (56604391437/625000000000 : ℝ)^75 := by
    have hnat : (345382229 : ℕ)^91*625000000000^75 ≤ 56604391437^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345382229 2500000000 56604391437 625000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310801591/625000000 : ℝ)^91 ≤ (8568574248851/20000000000000 : ℝ)^75 := by
    have hnat : (310801591 : ℕ)^91*20000000000000^75 ≤ 8568574248851^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310801591 625000000 8568574248851 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470598313/10000000000 : ℝ)^91 ≤ (12025106527161/25000000000000 : ℝ)^75 := by
    have hnat : (5470598313 : ℕ)^91*25000000000000^75 ≤ 12025106527161^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470598313 10000000000 12025106527161 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-345382229/2500000000 : ℝ), (310801591/625000000 : ℝ), (5470598313/10000000000 : ℝ)] ![(56604391437/625000000000 : ℝ), (8568574248851/20000000000000 : ℝ), (12025106527161/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-345382229/2500000000 : ℝ)|^91 ≤ (56604391437/625000000000 : ℝ)^75
        have hw : |(-345382229/2500000000 : ℝ)|=(345382229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(310801591/625000000 : ℝ)|^91 ≤ (8568574248851/20000000000000 : ℝ)^75
        have hw : |(310801591/625000000 : ℝ)|=(310801591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470598313/10000000000 : ℝ)|^91 ≤ (12025106527161/25000000000000 : ℝ)^75
        have hw : |(5470598313/10000000000 : ℝ)|=(5470598313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_8 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4682426699/10000000000 : ℝ)*x 0 + (-84305989/2500000000 : ℝ)*x 1 + (3215830519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4682426699/10000000000 : ℝ)^91 ≤ (19913218957807/50000000000000 : ℝ)^75 := by
    have hnat : (4682426699 : ℕ)^91*50000000000000^75 ≤ 19913218957807^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4682426699 10000000000 19913218957807 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84305989/2500000000 : ℝ)^91 ≤ (1636343019599/100000000000000 : ℝ)^75 := by
    have hnat : (84305989 : ℕ)^91*100000000000000^75 ≤ 1636343019599^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84305989 2500000000 1636343019599 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3215830519/5000000000 : ℝ)^91 ≤ (29268609524029/50000000000000 : ℝ)^75 := by
    have hnat : (3215830519 : ℕ)^91*50000000000000^75 ≤ 29268609524029^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3215830519 5000000000 29268609524029 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4682426699/10000000000 : ℝ), (-84305989/2500000000 : ℝ), (3215830519/5000000000 : ℝ)] ![(19913218957807/50000000000000 : ℝ), (1636343019599/100000000000000 : ℝ), (29268609524029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4682426699/10000000000 : ℝ)|^91 ≤ (19913218957807/50000000000000 : ℝ)^75
        have hw : |(4682426699/10000000000 : ℝ)|=(4682426699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84305989/2500000000 : ℝ)|^91 ≤ (1636343019599/100000000000000 : ℝ)^75
        have hw : |(-84305989/2500000000 : ℝ)|=(84305989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3215830519/5000000000 : ℝ)|^91 ≤ (29268609524029/50000000000000 : ℝ)^75
        have hw : |(3215830519/5000000000 : ℝ)|=(3215830519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_9 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4672601521/10000000000 : ℝ)*x 0 + (6080202077/10000000000 : ℝ)*x 1 + (-11612809/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4672601521/10000000000 : ℝ)^91 ≤ (39725064573361/100000000000000 : ℝ)^75 := by
    have hnat : (4672601521 : ℕ)^91*100000000000000^75 ≤ 39725064573361^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4672601521 10000000000 39725064573361 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6080202077/10000000000 : ℝ)^91 ≤ (54678994909869/100000000000000 : ℝ)^75 := by
    have hnat : (6080202077 : ℕ)^91*100000000000000^75 ≤ 54678994909869^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6080202077 10000000000 54678994909869 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11612809/125000000 : ℝ)^91 ≤ (5595940494787/100000000000000 : ℝ)^75 := by
    have hnat : (11612809 : ℕ)^91*100000000000000^75 ≤ 5595940494787^75*125000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11612809 125000000 5595940494787 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4672601521/10000000000 : ℝ), (6080202077/10000000000 : ℝ), (-11612809/125000000 : ℝ)] ![(39725064573361/100000000000000 : ℝ), (54678994909869/100000000000000 : ℝ), (5595940494787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4672601521/10000000000 : ℝ)|^91 ≤ (39725064573361/100000000000000 : ℝ)^75
        have hw : |(4672601521/10000000000 : ℝ)|=(4672601521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6080202077/10000000000 : ℝ)|^91 ≤ (54678994909869/100000000000000 : ℝ)^75
        have hw : |(6080202077/10000000000 : ℝ)|=(6080202077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11612809/125000000 : ℝ)|^91 ≤ (5595940494787/100000000000000 : ℝ)^75
        have hw : |(-11612809/125000000 : ℝ)|=(11612809/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_13 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (332526919/625000000 : ℝ)*x 0 + (5506404479/10000000000 : ℝ)*x 1 + (16973341/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332526919/625000000 : ℝ)^91 ≤ (46503121590487/100000000000000 : ℝ)^75 := by
    have hnat : (332526919 : ℕ)^91*100000000000000^75 ≤ 46503121590487^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332526919 625000000 46503121590487 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506404479/10000000000 : ℝ)^91 ≤ (12120670596623/25000000000000 : ℝ)^75 := by
    have hnat : (5506404479 : ℕ)^91*25000000000000^75 ≤ 12120670596623^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506404479 10000000000 12120670596623 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16973341/200000000 : ℝ)^91 ≤ (250709800401/5000000000000 : ℝ)^75 := by
    have hnat : (16973341 : ℕ)^91*5000000000000^75 ≤ 250709800401^75*200000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16973341 200000000 250709800401 5000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332526919/625000000 : ℝ), (5506404479/10000000000 : ℝ), (16973341/200000000 : ℝ)] ![(46503121590487/100000000000000 : ℝ), (12120670596623/25000000000000 : ℝ), (250709800401/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332526919/625000000 : ℝ)|^91 ≤ (46503121590487/100000000000000 : ℝ)^75
        have hw : |(332526919/625000000 : ℝ)|=(332526919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5506404479/10000000000 : ℝ)|^91 ≤ (12120670596623/25000000000000 : ℝ)^75
        have hw : |(5506404479/10000000000 : ℝ)|=(5506404479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16973341/200000000 : ℝ)|^91 ≤ (250709800401/5000000000000 : ℝ)^75
        have hw : |(16973341/200000000 : ℝ)|=(16973341/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_14 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-212807881/2500000000 : ℝ)*x 0 + (2626658479/5000000000 : ℝ)*x 1 + (1392783959/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212807881/2500000000 : ℝ)^91 ≤ (5032586029841/100000000000000 : ℝ)^75 := by
    have hnat : (212807881 : ℕ)^91*100000000000000^75 ≤ 5032586029841^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212807881 2500000000 5032586029841 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626658479/5000000000 : ℝ)^91 ≤ (45792333359923/100000000000000 : ℝ)^75 := by
    have hnat : (2626658479 : ℕ)^91*100000000000000^75 ≤ 45792333359923^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626658479 5000000000 45792333359923 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1392783959/2500000000 : ℝ)^91 ≤ (49175080600403/100000000000000 : ℝ)^75 := by
    have hnat : (1392783959 : ℕ)^91*100000000000000^75 ≤ 49175080600403^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392783959 2500000000 49175080600403 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212807881/2500000000 : ℝ), (2626658479/5000000000 : ℝ), (1392783959/2500000000 : ℝ)] ![(5032586029841/100000000000000 : ℝ), (45792333359923/100000000000000 : ℝ), (49175080600403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212807881/2500000000 : ℝ)|^91 ≤ (5032586029841/100000000000000 : ℝ)^75
        have hw : |(-212807881/2500000000 : ℝ)|=(212807881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626658479/5000000000 : ℝ)|^91 ≤ (45792333359923/100000000000000 : ℝ)^75
        have hw : |(2626658479/5000000000 : ℝ)|=(2626658479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1392783959/2500000000 : ℝ)|^91 ≤ (49175080600403/100000000000000 : ℝ)^75
        have hw : |(1392783959/2500000000 : ℝ)|=(1392783959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_15 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4418709323/10000000000 : ℝ)*x 0 + (-149894481/2000000000 : ℝ)*x 1 + (6434293209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4418709323/10000000000 : ℝ)^91 ≤ (37121466563307/100000000000000 : ℝ)^75 := by
    have hnat : (4418709323 : ℕ)^91*100000000000000^75 ≤ 37121466563307^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418709323 10000000000 37121466563307 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149894481/2000000000 : ℝ)^91 ≤ (539030738153/12500000000000 : ℝ)^75 := by
    have hnat : (149894481 : ℕ)^91*12500000000000^75 ≤ 539030738153^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149894481 2000000000 539030738153 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6434293209/10000000000 : ℝ)^91 ≤ (915098242417/1562500000000 : ℝ)^75 := by
    have hnat : (6434293209 : ℕ)^91*1562500000000^75 ≤ 915098242417^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6434293209 10000000000 915098242417 1562500000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4418709323/10000000000 : ℝ), (-149894481/2000000000 : ℝ), (6434293209/10000000000 : ℝ)] ![(37121466563307/100000000000000 : ℝ), (539030738153/12500000000000 : ℝ), (915098242417/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4418709323/10000000000 : ℝ)|^91 ≤ (37121466563307/100000000000000 : ℝ)^75
        have hw : |(4418709323/10000000000 : ℝ)|=(4418709323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149894481/2000000000 : ℝ)|^91 ≤ (539030738153/12500000000000 : ℝ)^75
        have hw : |(-149894481/2000000000 : ℝ)|=(149894481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6434293209/10000000000 : ℝ)|^91 ≤ (915098242417/1562500000000 : ℝ)^75
        have hw : |(6434293209/10000000000 : ℝ)|=(6434293209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_16 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1111702463/2000000000 : ℝ)*x 0 + (5281460933/10000000000 : ℝ)*x 1 + (-414244669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1111702463/2000000000 : ℝ)^91 ≤ (49039917879061/100000000000000 : ℝ)^75 := by
    have hnat : (1111702463 : ℕ)^91*100000000000000^75 ≤ 49039917879061^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111702463 2000000000 49039917879061 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281460933/10000000000 : ℝ)^91 ≤ (9218033227903/20000000000000 : ℝ)^75 := by
    have hnat : (5281460933 : ℕ)^91*20000000000000^75 ≤ 9218033227903^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281460933 10000000000 9218033227903 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414244669/5000000000 : ℝ)^91 ≤ (4869915969319/100000000000000 : ℝ)^75 := by
    have hnat : (414244669 : ℕ)^91*100000000000000^75 ≤ 4869915969319^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414244669 5000000000 4869915969319 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1111702463/2000000000 : ℝ), (5281460933/10000000000 : ℝ), (-414244669/5000000000 : ℝ)] ![(49039917879061/100000000000000 : ℝ), (9218033227903/20000000000000 : ℝ), (4869915969319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1111702463/2000000000 : ℝ)|^91 ≤ (49039917879061/100000000000000 : ℝ)^75
        have hw : |(1111702463/2000000000 : ℝ)|=(1111702463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281460933/10000000000 : ℝ)|^91 ≤ (9218033227903/20000000000000 : ℝ)^75
        have hw : |(5281460933/10000000000 : ℝ)|=(5281460933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-414244669/5000000000 : ℝ)|^91 ≤ (4869915969319/100000000000000 : ℝ)^75
        have hw : |(-414244669/5000000000 : ℝ)|=(414244669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_20 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7322256949/10000000000 : ℝ)*x 0 + (837639531/2500000000 : ℝ)*x 1 + (840152267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7322256949/10000000000 : ℝ)^91 ≤ (34256203379119/50000000000000 : ℝ)^75 := by
    have hnat : (7322256949 : ℕ)^91*50000000000000^75 ≤ 34256203379119^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7322256949 10000000000 34256203379119 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (837639531/2500000000 : ℝ)^91 ≤ (26534372173167/100000000000000 : ℝ)^75 := by
    have hnat : (837639531 : ℕ)^91*100000000000000^75 ≤ 26534372173167^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837639531 2500000000 26534372173167 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (840152267/10000000000 : ℝ)^91 ≤ (4953221062791/100000000000000 : ℝ)^75 := by
    have hnat : (840152267 : ℕ)^91*100000000000000^75 ≤ 4953221062791^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840152267 10000000000 4953221062791 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7322256949/10000000000 : ℝ), (837639531/2500000000 : ℝ), (840152267/10000000000 : ℝ)] ![(34256203379119/50000000000000 : ℝ), (26534372173167/100000000000000 : ℝ), (4953221062791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7322256949/10000000000 : ℝ)|^91 ≤ (34256203379119/50000000000000 : ℝ)^75
        have hw : |(7322256949/10000000000 : ℝ)|=(7322256949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(837639531/2500000000 : ℝ)|^91 ≤ (26534372173167/100000000000000 : ℝ)^75
        have hw : |(837639531/2500000000 : ℝ)|=(837639531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(840152267/10000000000 : ℝ)|^91 ≤ (4953221062791/100000000000000 : ℝ)^75
        have hw : |(840152267/10000000000 : ℝ)|=(840152267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_21 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-186048271/2000000000 : ℝ)*x 0 + (1505865989/2500000000 : ℝ)*x 1 + (2365808457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (186048271/2000000000 : ℝ)^91 ≤ (5604833466147/100000000000000 : ℝ)^75 := by
    have hnat : (186048271 : ℕ)^91*100000000000000^75 ≤ 5604833466147^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186048271 2000000000 5604833466147 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1505865989/2500000000 : ℝ)^91 ≤ (10812103447949/20000000000000 : ℝ)^75 := by
    have hnat : (1505865989 : ℕ)^91*20000000000000^75 ≤ 10812103447949^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505865989 2500000000 10812103447949 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2365808457/5000000000 : ℝ)^91 ≤ (20167324642297/50000000000000 : ℝ)^75 := by
    have hnat : (2365808457 : ℕ)^91*50000000000000^75 ≤ 20167324642297^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2365808457 5000000000 20167324642297 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-186048271/2000000000 : ℝ), (1505865989/2500000000 : ℝ), (2365808457/5000000000 : ℝ)] ![(5604833466147/100000000000000 : ℝ), (10812103447949/20000000000000 : ℝ), (20167324642297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-186048271/2000000000 : ℝ)|^91 ≤ (5604833466147/100000000000000 : ℝ)^75
        have hw : |(-186048271/2000000000 : ℝ)|=(186048271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1505865989/2500000000 : ℝ)|^91 ≤ (10812103447949/20000000000000 : ℝ)^75
        have hw : |(1505865989/2500000000 : ℝ)|=(1505865989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2365808457/5000000000 : ℝ)|^91 ≤ (20167324642297/50000000000000 : ℝ)^75
        have hw : |(2365808457/5000000000 : ℝ)|=(2365808457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_22 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (21442689/39062500 : ℝ)*x 0 + (-36542921/1250000000 : ℝ)*x 1 + (177442681/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21442689/39062500 : ℝ)^91 ≤ (9660063315187/20000000000000 : ℝ)^75 := by
    have hnat : (21442689 : ℕ)^91*20000000000000^75 ≤ 9660063315187^75*39062500^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21442689 39062500 9660063315187 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36542921/1250000000 : ℝ)^91 ≤ (42999871743/3125000000000 : ℝ)^75 := by
    have hnat : (36542921 : ℕ)^91*3125000000000^75 ≤ 42999871743^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36542921 1250000000 42999871743 3125000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177442681/312500000 : ℝ)^91 ≤ (10064737505041/20000000000000 : ℝ)^75 := by
    have hnat : (177442681 : ℕ)^91*20000000000000^75 ≤ 10064737505041^75*312500000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177442681 312500000 10064737505041 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21442689/39062500 : ℝ), (-36542921/1250000000 : ℝ), (177442681/312500000 : ℝ)] ![(9660063315187/20000000000000 : ℝ), (42999871743/3125000000000 : ℝ), (10064737505041/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21442689/39062500 : ℝ)|^91 ≤ (9660063315187/20000000000000 : ℝ)^75
        have hw : |(21442689/39062500 : ℝ)|=(21442689/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36542921/1250000000 : ℝ)|^91 ≤ (42999871743/3125000000000 : ℝ)^75
        have hw : |(-36542921/1250000000 : ℝ)|=(36542921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(177442681/312500000 : ℝ)|^91 ≤ (10064737505041/20000000000000 : ℝ)^75
        have hw : |(177442681/312500000 : ℝ)|=(177442681/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_23 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4305232429/10000000000 : ℝ)*x 0 + (3062542193/5000000000 : ℝ)*x 1 + (-339280107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305232429/10000000000 : ℝ)^91 ≤ (35967965933077/100000000000000 : ℝ)^75 := by
    have hnat : (4305232429 : ℕ)^91*100000000000000^75 ≤ 35967965933077^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305232429 10000000000 35967965933077 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3062542193/5000000000 : ℝ)^91 ≤ (55169111035847/100000000000000 : ℝ)^75 := by
    have hnat : (3062542193 : ℕ)^91*100000000000000^75 ≤ 55169111035847^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3062542193 5000000000 55169111035847 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339280107/2500000000 : ℝ)^91 ≤ (2215730754629/25000000000000 : ℝ)^75 := by
    have hnat : (339280107 : ℕ)^91*25000000000000^75 ≤ 2215730754629^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339280107 2500000000 2215730754629 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305232429/10000000000 : ℝ), (3062542193/5000000000 : ℝ), (-339280107/2500000000 : ℝ)] ![(35967965933077/100000000000000 : ℝ), (55169111035847/100000000000000 : ℝ), (2215730754629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305232429/10000000000 : ℝ)|^91 ≤ (35967965933077/100000000000000 : ℝ)^75
        have hw : |(4305232429/10000000000 : ℝ)|=(4305232429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3062542193/5000000000 : ℝ)|^91 ≤ (55169111035847/100000000000000 : ℝ)^75
        have hw : |(3062542193/5000000000 : ℝ)|=(3062542193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-339280107/2500000000 : ℝ)|^91 ≤ (2215730754629/25000000000000 : ℝ)^75
        have hw : |(-339280107/2500000000 : ℝ)|=(339280107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327055_s1_s1_27 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (765727341/1000000000 : ℝ)*x 0 + (2110507029/10000000000 : ℝ)*x 1 + (902142649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (765727341/1000000000 : ℝ)^91 ≤ (18083534366137/25000000000000 : ℝ)^75 := by
    have hnat : (765727341 : ℕ)^91*25000000000000^75 ≤ 18083534366137^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765727341 1000000000 18083534366137 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110507029/10000000000 : ℝ)^91 ≤ (15144536544387/100000000000000 : ℝ)^75 := by
    have hnat : (2110507029 : ℕ)^91*100000000000000^75 ≤ 15144536544387^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110507029 10000000000 15144536544387 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902142649/5000000000 : ℝ)^91 ≤ (3130331493343/25000000000000 : ℝ)^75 := by
    have hnat : (902142649 : ℕ)^91*25000000000000^75 ≤ 3130331493343^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902142649 5000000000 3130331493343 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(765727341/1000000000 : ℝ), (2110507029/10000000000 : ℝ), (902142649/5000000000 : ℝ)] ![(18083534366137/25000000000000 : ℝ), (15144536544387/100000000000000 : ℝ), (3130331493343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(765727341/1000000000 : ℝ)|^91 ≤ (18083534366137/25000000000000 : ℝ)^75
        have hw : |(765727341/1000000000 : ℝ)|=(765727341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2110507029/10000000000 : ℝ)|^91 ≤ (15144536544387/100000000000000 : ℝ)^75
        have hw : |(2110507029/10000000000 : ℝ)|=(2110507029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902142649/5000000000 : ℝ)|^91 ≤ (3130331493343/25000000000000 : ℝ)^75
        have hw : |(902142649/5000000000 : ℝ)|=(902142649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327055_s1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((16217/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16217/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61793/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61793/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15711/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15711/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((32951/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32951/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1681/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1681/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32733/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32733/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (16217/25000 : ℝ) ^ (89/16 : ℝ) ≤ (9003672736120047069/100000000000000000000 : ℝ) := by
    have hpowers : (16217/25000 : ℝ)^89 ≤ (9003672736120047069/100000000000000000000 : ℝ)^16 := by
      have hnat : (16217 : ℕ)^89*100000000000000000000^16 ≤ 9003672736120047069^16*25000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16217 25000 9003672736120047069 100000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16217/25000 : ℝ)) (X := (9003672736120047069/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (109003672736120047069/100000000000000000000 : ℝ) ≤ (5078097021679631/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (109003672736120047069/100000000000000000000 : ℝ)^16 ≤ (5078097021679631/5000000000000000 : ℝ)^89 := by
      have hnat : (109003672736120047069 : ℕ)^16*5000000000000000^89 ≤ 5078097021679631^89*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109003672736120047069 100000000000000000000 5078097021679631 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5078097021679631/5000000000000000 : ℝ)) (X := (109003672736120047069/100000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (59003672736120047069/50000000000000000000 : ℝ) ≤ (10302140490788831/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (59003672736120047069/50000000000000000000 : ℝ)^16 ≤ (10302140490788831/10000000000000000 : ℝ)^89 := by
      have hnat : (59003672736120047069 : ℕ)^16*10000000000000000^89 ≤ 10302140490788831^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59003672736120047069 50000000000000000000 10302140490788831 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10302140490788831/10000000000000000 : ℝ)) (X := (59003672736120047069/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(78097021679631/3243400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(145946447429569/6486800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (16217/25000 : ℝ)) (alpha := (78097021679631/3243400000000000 : ℝ)) (beta := (145946447429569/6486800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16217/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(78097021679631/3243400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(145946447429569/6486800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (61793/100000 : ℝ) ^ (89/16 : ℝ) ≤ (3436131306694509639/50000000000000000000 : ℝ) := by
    have hpowers : (61793/100000 : ℝ)^89 ≤ (3436131306694509639/50000000000000000000 : ℝ)^16 := by
      have hnat : (61793 : ℕ)^89*50000000000000000000^16 ≤ 3436131306694509639^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61793 100000 3436131306694509639 50000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61793/100000 : ℝ)) (X := (3436131306694509639/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (53436131306694509639/50000000000000000000 : ℝ) ≤ (10120202770496891/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (53436131306694509639/50000000000000000000 : ℝ)^16 ≤ (10120202770496891/10000000000000000 : ℝ)^89 := by
      have hnat : (53436131306694509639 : ℕ)^16*10000000000000000^89 ≤ 10120202770496891^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53436131306694509639 50000000000000000000 10120202770496891 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10120202770496891/10000000000000000 : ℝ)) (X := (53436131306694509639/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (28436131306694509639/25000000000000000000 : ℝ) ≤ (2046844816334697/2000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (28436131306694509639/25000000000000000000 : ℝ)^16 ≤ (2046844816334697/2000000000000000 : ℝ)^89 := by
      have hnat : (28436131306694509639 : ℕ)^16*2000000000000000^89 ≤ 2046844816334697^89*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28436131306694509639 25000000000000000000 2046844816334697 2000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2046844816334697/2000000000000000 : ℝ)) (X := (28436131306694509639/25000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(120202770496891/6179300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(57010655588297/3089650000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (61793/100000 : ℝ)) (alpha := (120202770496891/6179300000000000 : ℝ)) (beta := (57010655588297/3089650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (61793/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(120202770496891/6179300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(57010655588297/3089650000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (15711/25000 : ℝ) ^ (89/16 : ℝ) ≤ (754818435052952853/10000000000000000000 : ℝ) := by
    have hpowers : (15711/25000 : ℝ)^89 ≤ (754818435052952853/10000000000000000000 : ℝ)^16 := by
      have hnat : (15711 : ℕ)^89*10000000000000000000^16 ≤ 754818435052952853^16*25000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15711 25000 754818435052952853 10000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15711/25000 : ℝ)) (X := (754818435052952853/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (10754818435052952853/10000000000000000000 : ℝ) ≤ (202633594670927/200000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (10754818435052952853/10000000000000000000 : ℝ)^16 ≤ (202633594670927/200000000000000 : ℝ)^89 := by
      have hnat : (10754818435052952853 : ℕ)^16*200000000000000^89 ≤ 202633594670927^89*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10754818435052952853 10000000000000000000 202633594670927 200000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (202633594670927/200000000000000 : ℝ)) (X := (10754818435052952853/10000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5754818435052952853/5000000000000000000 : ℝ) ≤ (2051196967987919/2000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (5754818435052952853/5000000000000000000 : ℝ)^16 ≤ (2051196967987919/2000000000000000 : ℝ)^89 := by
      have hnat : (5754818435052952853 : ℕ)^16*2000000000000000^89 ≤ 2051196967987919^89*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5754818435052952853 5000000000000000000 2051196967987919 2000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2051196967987919/2000000000000000 : ℝ)) (X := (5754818435052952853/5000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(877864890309/41896000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(8287007092883/418960000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (15711/25000 : ℝ)) (alpha := (877864890309/41896000000000 : ℝ)) (beta := (8287007092883/418960000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (15711/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(877864890309/41896000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(8287007092883/418960000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((294628421/625000000 : ℝ)*X 1 0+(-21436769/250000000 : ℝ)*X 1 1+(6088499767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4704275671/10000000000 : ℝ)*X 2 0+(5527189111/10000000000 : ℝ)*X 2 1+(-1651067711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-345382229/2500000000 : ℝ)*X 0 0+(310801591/625000000 : ℝ)*X 0 1+(5470598313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4682426699/10000000000 : ℝ)*X 1 0+(-84305989/2500000000 : ℝ)*X 1 1+(3215830519/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4672601521/10000000000 : ℝ)*X 2 0+(6080202077/10000000000 : ℝ)*X 2 1+(-11612809/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((332526919/625000000 : ℝ)*X 0 0+(5506404479/10000000000 : ℝ)*X 0 1+(16973341/200000000 : ℝ)*X 0 2+(332526919/625000000 : ℝ)*X 1 0+(5506404479/10000000000 : ℝ)*X 1 1+(16973341/200000000 : ℝ)*X 1 2+(332526919/625000000 : ℝ)*X 2 0+(5506404479/10000000000 : ℝ)*X 2 1+(16973341/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-212807881/2500000000 : ℝ)*X 0 0+(2626658479/5000000000 : ℝ)*X 0 1+(1392783959/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4418709323/10000000000 : ℝ)*X 1 0+(-149894481/2000000000 : ℝ)*X 1 1+(6434293209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1111702463/2000000000 : ℝ)*X 2 0+(5281460933/10000000000 : ℝ)*X 2 1+(-414244669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7322256949/10000000000 : ℝ)*X 0 0+(837639531/2500000000 : ℝ)*X 0 1+(840152267/10000000000 : ℝ)*X 0 2+(7322256949/10000000000 : ℝ)*X 1 0+(837639531/2500000000 : ℝ)*X 1 1+(840152267/10000000000 : ℝ)*X 1 2+(7322256949/10000000000 : ℝ)*X 2 0+(837639531/2500000000 : ℝ)*X 2 1+(840152267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-186048271/2000000000 : ℝ)*X 0 0+(1505865989/2500000000 : ℝ)*X 0 1+(2365808457/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((21442689/39062500 : ℝ)*X 1 0+(-36542921/1250000000 : ℝ)*X 1 1+(177442681/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4305232429/10000000000 : ℝ)*X 2 0+(3062542193/5000000000 : ℝ)*X 2 1+(-339280107/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((765727341/1000000000 : ℝ)*X 0 0+(2110507029/10000000000 : ℝ)*X 0 1+(902142649/5000000000 : ℝ)*X 0 2+(765727341/1000000000 : ℝ)*X 1 0+(2110507029/10000000000 : ℝ)*X 1 1+(902142649/5000000000 : ℝ)*X 1 2+(765727341/1000000000 : ℝ)*X 2 0+(2110507029/10000000000 : ℝ)*X 2 1+(902142649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((32951/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32951/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1335411547744063424952103353627/262399120659850000000000000000000000 : ℝ) := by norm_num
    linear_combination (128416840551/200000000000 : ℝ)*(base49) + (1516571235713/250000000000 : ℝ)*(major_s1_0) + (1516571235713/250000000000 : ℝ)*(major_s1_1) + (1516571235713/250000000000 : ℝ)*(major_s1_2) + (6911733/250000000000 : ℝ)*(sp_s1_1) + (2674289/200000000000 : ℝ)*(sp_s1_2) + (9265832044727/1000000000000 : ℝ)*(sp_s1_7) + (4632904208459/500000000000 : ℝ)*(sp_s1_8) + (9265794272467/1000000000000 : ℝ)*(sp_s1_9) + (2866709983991/1000000000000 : ℝ)*(sp_s1_13) + (20830683/1000000000000 : ℝ)*(sp_s1_14) + (420289/25000000000 : ℝ)*(sp_s1_15) + (166559/31250000000 : ℝ)*(sp_s1_20) + (22615749/500000000000 : ℝ)*(sp_s1_23) + (2866715313879/1000000000000 : ℝ)*(f.failure) + (926585287541/100000000000 : ℝ)*(f.sum) + (974404849443676493/16180497050000000000000000000000 : ℝ)*base62 + (27833904488619/104740000000000000000000000 : ℝ)*base64 + (1055679020271569/3089650000000000000000000000 : ℝ)*base66 + (2194755118069/10474000000000000000000000 : ℝ)*base68 + (1220591291985502933/8492842900000000000000000000000 : ℝ)*base70 + (249302415320683/1621700000000000000000000000 : ℝ)*base72 + (309911833575617/1544825000000000000000000000 : ℝ)*base74 + (56445447379663/202712500000000000000000000 : ℝ)*base76 + (4506873175094014129/20041941620000000000000000000000 : ℝ)*base78 + (49069/100000000000000000 : ℝ)*base87 + (49069/100000000000000000 : ℝ)*base89 + (49069/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1681/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1681/5000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4320749487385102836166513577379/262399120659850000000000000000000000 : ℝ) := by norm_num
    linear_combination (2121253/1000000000000 : ℝ)*(base39) + (103520835199/200000000000 : ℝ)*(base49) + (2383339/1000000000000 : ℝ)*(base60) + (1423707674221/250000000000 : ℝ)*(major_s1_0) + (1423707674221/250000000000 : ℝ)*(major_s1_1) + (1423707674221/250000000000 : ℝ)*(major_s1_2) + (25025777/1000000000000 : ℝ)*(sp_s1_2) + (7807807/125000000000 : ℝ)*(sp_s1_7) + (27010753/250000000000 : ℝ)*(sp_s1_8) + (4349207244139/500000000000 : ℝ)*(sp_s1_14) + (8698368907723/1000000000000 : ℝ)*(sp_s1_15) + (8698451924957/1000000000000 : ℝ)*(sp_s1_16) + (336390034353/125000000000 : ℝ)*(sp_s1_20) + (58679429/1000000000000 : ℝ)*(sp_s1_27) + (2691178954253/1000000000000 : ℝ)*(f.failure) + (1739695390147/200000000000 : ℝ)*(f.sum) + (3759172997120442149/16180497050000000000000000000000 : ℝ)*base63 + (3704247278511/20948000000000000000000000 : ℝ)*base64 + (696042460519481/1544825000000000000000000000 : ℝ)*base67 + (754010930063/26185000000000000000000000 : ℝ)*base68 + (2768642895000553771/8492842900000000000000000000000 : ℝ)*base70 + (1186714184135461/1621700000000000000000000000 : ℝ)*base72 + (138423338705451/1544825000000000000000000000 : ℝ)*base75 + (83232162254563/405425000000000000000000000 : ℝ)*base77 + (1574164459459262769/20041941620000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (31583/100000000000000000 : ℝ)*base87 + (31583/100000000000000000 : ℝ)*base89 + (31583/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32733/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32733/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (31592179880460379180503938031/2623991206598500000000000000000000 : ℝ) := by norm_num
    linear_combination (39891/3906250000 : ℝ)*(base15) + (62572932281/1000000000000 : ℝ)*(base40) + (640327277517/1000000000000 : ℝ)*(base49) + (1271619/1000000000000 : ℝ)*(base59) + (17422883789/3125000000 : ℝ)*(major_s1_0) + (17422883789/3125000000 : ℝ)*(major_s1_1) + (17422883789/3125000000 : ℝ)*(major_s1_2) + (9327831/500000000000 : ℝ)*(sp_s1_1) + (1574197/15625000000 : ℝ)*(sp_s1_9) + (24999473/1000000000000 : ℝ)*(sp_s1_20) + (1703187585567/200000000000 : ℝ)*(sp_s1_21) + (8515909060077/1000000000000 : ℝ)*(sp_s1_22) + (8515837179227/1000000000000 : ℝ)*(sp_s1_23) + (6586696711/2500000000 : ℝ)*(sp_s1_27) + (2634703683873/1000000000000 : ℝ)*(f.failure) + (1703187585567/200000000000 : ℝ)*(f.sum) + (90080548858114679/809024852500000000000000000000 : ℝ)*base62 + (2686951413/409140625000000000000000 : ℝ)*base64 + (86304111728269/123586000000000000000000000 : ℝ)*base66 + (22038693809049/52370000000000000000000000 : ℝ)*base68 + (129046101010396501/212321072500000000000000000000 : ℝ)*base71 + (17313058449833/32434000000000000000000000 : ℝ)*base72 + (46527245522809/154482500000000000000000000 : ℝ)*base74 + (17577168316007/81085000000000000000000000 : ℝ)*base77 + (371821948570704783/400838832400000000000000000000 : ℝ)*base78 + (49403/100000000000000000 : ℝ)*base87 + (49403/100000000000000000 : ℝ)*base89 + (49403/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((16217/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16217/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61793/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61793/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15711/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15711/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((32951/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32951/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1681/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1681/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32733/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32733/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c327055_s1 p hpa hpb X hX hprev0

#print axioms solution
