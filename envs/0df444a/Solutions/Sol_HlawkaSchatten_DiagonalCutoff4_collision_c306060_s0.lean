-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306060_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:58:06.615273+00:00
-- url     : https://prove2.me/submissions/e52119e6-7721-47b6-a397-90fb79b611fe

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
theorem collision_support_c306060_s0_s0_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4279764917/10000000000 : ℝ)*x 0 + (-14165471/80000000 : ℝ)*x 1 + (-3246649337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4279764917/10000000000 : ℝ)^135 ≤ (32878318363021/100000000000000 : ℝ)^103 := by
    have hnat : (4279764917 : ℕ)^135*100000000000000^103 ≤ 32878318363021^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4279764917 10000000000 32878318363021 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14165471/80000000 : ℝ)^135 ≤ (10340791467953/100000000000000 : ℝ)^103 := by
    have hnat : (14165471 : ℕ)^135*100000000000000^103 ≤ 10340791467953^103*80000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14165471 80000000 10340791467953 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3246649337/5000000000 : ℝ)^135 ≤ (14195222538693/25000000000000 : ℝ)^103 := by
    have hnat : (3246649337 : ℕ)^135*25000000000000^103 ≤ 14195222538693^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3246649337 5000000000 14195222538693 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4279764917/10000000000 : ℝ), (-14165471/80000000 : ℝ), (-3246649337/5000000000 : ℝ)] ![(32878318363021/100000000000000 : ℝ), (10340791467953/100000000000000 : ℝ), (14195222538693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4279764917/10000000000 : ℝ)|^135 ≤ (32878318363021/100000000000000 : ℝ)^103
        have hw : |(4279764917/10000000000 : ℝ)|=(4279764917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-14165471/80000000 : ℝ)|^135 ≤ (10340791467953/100000000000000 : ℝ)^103
        have hw : |(-14165471/80000000 : ℝ)|=(14165471/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3246649337/5000000000 : ℝ)|^135 ≤ (14195222538693/25000000000000 : ℝ)^103
        have hw : |(-3246649337/5000000000 : ℝ)|=(3246649337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s0_s0_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-100728681/1250000000 : ℝ)*x 0 + (90348531/400000000 : ℝ)*x 1 + (-8601969661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100728681/1250000000 : ℝ)^135 ≤ (3684980344783/100000000000000 : ℝ)^103 := by
    have hnat : (100728681 : ℕ)^135*100000000000000^103 ≤ 3684980344783^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100728681 1250000000 3684980344783 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90348531/400000000 : ℝ)^135 ≤ (14227183176647/100000000000000 : ℝ)^103 := by
    have hnat : (90348531 : ℕ)^135*100000000000000^103 ≤ 14227183176647^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90348531 400000000 14227183176647 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8601969661/10000000000 : ℝ)^135 ≤ (41043918237191/50000000000000 : ℝ)^103 := by
    have hnat : (8601969661 : ℕ)^135*50000000000000^103 ≤ 41043918237191^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8601969661 10000000000 41043918237191 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100728681/1250000000 : ℝ), (90348531/400000000 : ℝ), (-8601969661/10000000000 : ℝ)] ![(3684980344783/100000000000000 : ℝ), (14227183176647/100000000000000 : ℝ), (41043918237191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100728681/1250000000 : ℝ)|^135 ≤ (3684980344783/100000000000000 : ℝ)^103
        have hw : |(-100728681/1250000000 : ℝ)|=(100728681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90348531/400000000 : ℝ)|^135 ≤ (14227183176647/100000000000000 : ℝ)^103
        have hw : |(90348531/400000000 : ℝ)|=(90348531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8601969661/10000000000 : ℝ)|^135 ≤ (41043918237191/50000000000000 : ℝ)^103
        have hw : |(-8601969661/10000000000 : ℝ)|=(8601969661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s0_s0_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2449837001/10000000000 : ℝ)*x 0 + (-261090957/5000000000 : ℝ)*x 1 + (-8601969273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2449837001/10000000000 : ℝ)^135 ≤ (247271802719/1562500000000 : ℝ)^103 := by
    have hnat : (2449837001 : ℕ)^135*1562500000000^103 ≤ 247271802719^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2449837001 10000000000 247271802719 1562500000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261090957/5000000000 : ℝ)^135 ≤ (417354599637/20000000000000 : ℝ)^103 := by
    have hnat : (261090957 : ℕ)^135*20000000000000^103 ≤ 417354599637^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261090957 5000000000 417354599637 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8601969273/10000000000 : ℝ)^135 ≤ (41043915810697/50000000000000 : ℝ)^103 := by
    have hnat : (8601969273 : ℕ)^135*50000000000000^103 ≤ 41043915810697^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8601969273 10000000000 41043915810697 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2449837001/10000000000 : ℝ), (-261090957/5000000000 : ℝ), (-8601969273/10000000000 : ℝ)] ![(247271802719/1562500000000 : ℝ), (417354599637/20000000000000 : ℝ), (41043915810697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2449837001/10000000000 : ℝ)|^135 ≤ (247271802719/1562500000000 : ℝ)^103
        have hw : |(2449837001/10000000000 : ℝ)|=(2449837001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261090957/5000000000 : ℝ)|^135 ≤ (417354599637/20000000000000 : ℝ)^103
        have hw : |(-261090957/5000000000 : ℝ)|=(261090957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8601969273/10000000000 : ℝ)|^135 ≤ (41043915810697/50000000000000 : ℝ)^103
        have hw : |(-8601969273/10000000000 : ℝ)|=(8601969273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s0_s0_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1706428693/10000000000 : ℝ)*x 0 + (208282177/250000000 : ℝ)*x 1 + (95559849/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1706428693/10000000000 : ℝ)^135 ≤ (2462938665759/25000000000000 : ℝ)^103 := by
    have hnat : (1706428693 : ℕ)^135*25000000000000^103 ≤ 2462938665759^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706428693 10000000000 2462938665759 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208282177/250000000 : ℝ)^135 ≤ (39359445365097/50000000000000 : ℝ)^103 := by
    have hnat : (208282177 : ℕ)^135*50000000000000^103 ≤ 39359445365097^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208282177 250000000 39359445365097 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95559849/500000000 : ℝ)^135 ≤ (11429354596731/100000000000000 : ℝ)^103 := by
    have hnat : (95559849 : ℕ)^135*100000000000000^103 ≤ 11429354596731^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95559849 500000000 11429354596731 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1706428693/10000000000 : ℝ), (208282177/250000000 : ℝ), (95559849/500000000 : ℝ)] ![(2462938665759/25000000000000 : ℝ), (39359445365097/50000000000000 : ℝ), (11429354596731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1706428693/10000000000 : ℝ)|^135 ≤ (2462938665759/25000000000000 : ℝ)^103
        have hw : |(1706428693/10000000000 : ℝ)|=(1706428693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208282177/250000000 : ℝ)|^135 ≤ (39359445365097/50000000000000 : ℝ)^103
        have hw : |(208282177/250000000 : ℝ)|=(208282177/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95559849/500000000 : ℝ)|^135 ≤ (11429354596731/100000000000000 : ℝ)^103
        have hw : |(95559849/500000000 : ℝ)|=(95559849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s0_s0_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3543466029/10000000000 : ℝ)*x 0 + (3987199897/5000000000 : ℝ)*x 1 + (271/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3543466029/10000000000 : ℝ)^135 ≤ (6417780114411/25000000000000 : ℝ)^103 := by
    have hnat : (3543466029 : ℕ)^135*25000000000000^103 ≤ 6417780114411^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3543466029 10000000000 6417780114411 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3987199897/5000000000 : ℝ)^135 ≤ (74328878400447/100000000000000 : ℝ)^103 := by
    have hnat : (3987199897 : ℕ)^135*100000000000000^103 ≤ 74328878400447^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3987199897 5000000000 74328878400447 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271/312500000 : ℝ)^135 ≤ (283633/25000000000000 : ℝ)^103 := by
    have hnat : (271 : ℕ)^135*25000000000000^103 ≤ 283633^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271 312500000 283633 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3543466029/10000000000 : ℝ), (3987199897/5000000000 : ℝ), (271/312500000 : ℝ)] ![(6417780114411/25000000000000 : ℝ), (74328878400447/100000000000000 : ℝ), (283633/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3543466029/10000000000 : ℝ)|^135 ≤ (6417780114411/25000000000000 : ℝ)^103
        have hw : |(3543466029/10000000000 : ℝ)|=(3543466029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3987199897/5000000000 : ℝ)|^135 ≤ (74328878400447/100000000000000 : ℝ)^103
        have hw : |(3987199897/5000000000 : ℝ)|=(3987199897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271/312500000 : ℝ)|^135 ≤ (283633/25000000000000 : ℝ)^103
        have hw : |(271/312500000 : ℝ)|=(271/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s0_s0_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-112716111/1000000000 : ℝ)*x 0 + (6877969/50000000 : ℝ)*x 1 + (-898029261/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112716111/1000000000 : ℝ)^135 ≤ (357550500933/6250000000000 : ℝ)^103 := by
    have hnat : (112716111 : ℕ)^135*6250000000000^103 ≤ 357550500933^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112716111 1000000000 357550500933 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6877969/50000000 : ℝ)^135 ≤ (7427397765253/100000000000000 : ℝ)^103 := by
    have hnat : (6877969 : ℕ)^135*100000000000000^103 ≤ 7427397765253^103*50000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6877969 50000000 7427397765253 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898029261/1000000000 : ℝ)^135 ≤ (86851794206249/100000000000000 : ℝ)^103 := by
    have hnat : (898029261 : ℕ)^135*100000000000000^103 ≤ 86851794206249^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898029261 1000000000 86851794206249 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-112716111/1000000000 : ℝ), (6877969/50000000 : ℝ), (-898029261/1000000000 : ℝ)] ![(357550500933/6250000000000 : ℝ), (7427397765253/100000000000000 : ℝ), (86851794206249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-112716111/1000000000 : ℝ)|^135 ≤ (357550500933/6250000000000 : ℝ)^103
        have hw : |(-112716111/1000000000 : ℝ)|=(112716111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6877969/50000000 : ℝ)|^135 ≤ (7427397765253/100000000000000 : ℝ)^103
        have hw : |(6877969/50000000 : ℝ)|=(6877969/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-898029261/1000000000 : ℝ)|^135 ≤ (86851794206249/100000000000000 : ℝ)^103
        have hw : |(-898029261/1000000000 : ℝ)|=(898029261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s0_s0_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (234199863/2000000000 : ℝ)*x 0 + (-1333941553/10000000000 : ℝ)*x 1 + (-2245073229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234199863/2000000000 : ℝ)^135 ≤ (6014176647459/100000000000000 : ℝ)^103 := by
    have hnat : (234199863 : ℕ)^135*100000000000000^103 ≤ 6014176647459^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234199863 2000000000 6014176647459 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1333941553/10000000000 : ℝ)^135 ≤ (3567012627507/50000000000000 : ℝ)^103 := by
    have hnat : (1333941553 : ℕ)^135*50000000000000^103 ≤ 3567012627507^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333941553 10000000000 3567012627507 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245073229/2500000000 : ℝ)^135 ≤ (86851798085129/100000000000000 : ℝ)^103 := by
    have hnat : (2245073229 : ℕ)^135*100000000000000^103 ≤ 86851798085129^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245073229 2500000000 86851798085129 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(234199863/2000000000 : ℝ), (-1333941553/10000000000 : ℝ), (-2245073229/2500000000 : ℝ)] ![(6014176647459/100000000000000 : ℝ), (3567012627507/50000000000000 : ℝ), (86851798085129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(234199863/2000000000 : ℝ)|^135 ≤ (6014176647459/100000000000000 : ℝ)^103
        have hw : |(234199863/2000000000 : ℝ)|=(234199863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1333941553/10000000000 : ℝ)|^135 ≤ (3567012627507/50000000000000 : ℝ)^103
        have hw : |(-1333941553/10000000000 : ℝ)|=(1333941553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2245073229/2500000000 : ℝ)|^135 ≤ (86851798085129/100000000000000 : ℝ)^103
        have hw : |(-2245073229/2500000000 : ℝ)|=(2245073229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s0_s0_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7139049949/10000000000 : ℝ)*x 0 + (1464145911/5000000000 : ℝ)*x 1 + (2436435063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7139049949/10000000000 : ℝ)^135 ≤ (64293857488167/100000000000000 : ℝ)^103 := by
    have hnat : (7139049949 : ℕ)^135*100000000000000^103 ≤ 64293857488167^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7139049949 10000000000 64293857488167 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1464145911/5000000000 : ℝ)^135 ≤ (4998530174199/25000000000000 : ℝ)^103 := by
    have hnat : (1464145911 : ℕ)^135*25000000000000^103 ≤ 4998530174199^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464145911 5000000000 4998530174199 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2436435063/10000000000 : ℝ)^135 ≤ (7856010899057/50000000000000 : ℝ)^103 := by
    have hnat : (2436435063 : ℕ)^135*50000000000000^103 ≤ 7856010899057^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436435063 10000000000 7856010899057 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7139049949/10000000000 : ℝ), (1464145911/5000000000 : ℝ), (2436435063/10000000000 : ℝ)] ![(64293857488167/100000000000000 : ℝ), (4998530174199/25000000000000 : ℝ), (7856010899057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7139049949/10000000000 : ℝ)|^135 ≤ (64293857488167/100000000000000 : ℝ)^103
        have hw : |(7139049949/10000000000 : ℝ)|=(7139049949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1464145911/5000000000 : ℝ)|^135 ≤ (4998530174199/25000000000000 : ℝ)^103
        have hw : |(1464145911/5000000000 : ℝ)|=(1464145911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2436435063/10000000000 : ℝ)|^135 ≤ (7856010899057/50000000000000 : ℝ)^103
        have hw : |(2436435063/10000000000 : ℝ)|=(2436435063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s0_s0_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8998319233/10000000000 : ℝ)*x 0 + (2098489461/10000000000 : ℝ)*x 1 + (739421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8998319233/10000000000 : ℝ)^135 ≤ (87080372278611/100000000000000 : ℝ)^103 := by
    have hnat : (8998319233 : ℕ)^135*100000000000000^103 ≤ 87080372278611^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8998319233 10000000000 87080372278611 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2098489461/10000000000 : ℝ)^135 ≤ (3229810683357/25000000000000 : ℝ)^103 := by
    have hnat : (2098489461 : ℕ)^135*25000000000000^103 ≤ 3229810683357^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098489461 10000000000 3229810683357 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (739421/10000000000 : ℝ)^135 ≤ (38498223/10000000000000 : ℝ)^103 := by
    have hnat : (739421 : ℕ)^135*10000000000000^103 ≤ 38498223^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739421 10000000000 38498223 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8998319233/10000000000 : ℝ), (2098489461/10000000000 : ℝ), (739421/10000000000 : ℝ)] ![(87080372278611/100000000000000 : ℝ), (3229810683357/25000000000000 : ℝ), (38498223/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8998319233/10000000000 : ℝ)|^135 ≤ (87080372278611/100000000000000 : ℝ)^103
        have hw : |(8998319233/10000000000 : ℝ)|=(8998319233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2098489461/10000000000 : ℝ)|^135 ≤ (3229810683357/25000000000000 : ℝ)^103
        have hw : |(2098489461/10000000000 : ℝ)|=(2098489461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(739421/10000000000 : ℝ)|^135 ≤ (38498223/10000000000000 : ℝ)^103
        have hw : |(739421/10000000000 : ℝ)|=(739421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s0_s0_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1643291/39062500 : ℝ)*x 0 + (151079863/1250000000 : ℝ)*x 1 + (-4698015203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1643291/39062500 : ℝ)^135 ≤ (78598660871/5000000000000 : ℝ)^103 := by
    have hnat : (1643291 : ℕ)^135*5000000000000^103 ≤ 78598660871^103*39062500^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1643291 39062500 78598660871 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151079863/1250000000 : ℝ)^135 ≤ (1253761182357/20000000000000 : ℝ)^103 := by
    have hnat : (151079863 : ℕ)^135*20000000000000^103 ≤ 1253761182357^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151079863 1250000000 1253761182357 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4698015203/5000000000 : ℝ)^135 ≤ (92159220850117/100000000000000 : ℝ)^103 := by
    have hnat : (4698015203 : ℕ)^135*100000000000000^103 ≤ 92159220850117^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4698015203 5000000000 92159220850117 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1643291/39062500 : ℝ), (151079863/1250000000 : ℝ), (-4698015203/5000000000 : ℝ)] ![(78598660871/5000000000000 : ℝ), (1253761182357/20000000000000 : ℝ), (92159220850117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1643291/39062500 : ℝ)|^135 ≤ (78598660871/5000000000000 : ℝ)^103
        have hw : |(-1643291/39062500 : ℝ)|=(1643291/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(151079863/1250000000 : ℝ)|^135 ≤ (1253761182357/20000000000000 : ℝ)^103
        have hw : |(151079863/1250000000 : ℝ)|=(151079863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4698015203/5000000000 : ℝ)|^135 ≤ (92159220850117/100000000000000 : ℝ)^103
        have hw : |(-4698015203/5000000000 : ℝ)|=(4698015203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s0_s0_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (998184547/1250000000 : ℝ)*x 0 + (-67661037/400000000 : ℝ)*x 1 + (-2446439181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998184547/1250000000 : ℝ)^135 ≤ (37232113778341/50000000000000 : ℝ)^103 := by
    have hnat : (998184547 : ℕ)^135*50000000000000^103 ≤ 37232113778341^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998184547 1250000000 37232113778341 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67661037/400000000 : ℝ)^135 ≤ (9739139164929/100000000000000 : ℝ)^103 := by
    have hnat : (67661037 : ℕ)^135*100000000000000^103 ≤ 9739139164929^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67661037 400000000 9739139164929 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2446439181/10000000000 : ℝ)^135 ≤ (15796633267989/100000000000000 : ℝ)^103 := by
    have hnat : (2446439181 : ℕ)^135*100000000000000^103 ≤ 15796633267989^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2446439181 10000000000 15796633267989 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(998184547/1250000000 : ℝ), (-67661037/400000000 : ℝ), (-2446439181/10000000000 : ℝ)] ![(37232113778341/50000000000000 : ℝ), (9739139164929/100000000000000 : ℝ), (15796633267989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(998184547/1250000000 : ℝ)|^135 ≤ (37232113778341/50000000000000 : ℝ)^103
        have hw : |(998184547/1250000000 : ℝ)|=(998184547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67661037/400000000 : ℝ)|^135 ≤ (9739139164929/100000000000000 : ℝ)^103
        have hw : |(-67661037/400000000 : ℝ)|=(67661037/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2446439181/10000000000 : ℝ)|^135 ≤ (15796633267989/100000000000000 : ℝ)^103
        have hw : |(-2446439181/10000000000 : ℝ)|=(2446439181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s0_s0_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1568664231/10000000000 : ℝ)*x 0 + (3953582081/5000000000 : ℝ)*x 1 + (2664693999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1568664231/10000000000 : ℝ)^135 ≤ (8822619808879/100000000000000 : ℝ)^103 := by
    have hnat : (1568664231 : ℕ)^135*100000000000000^103 ≤ 8822619808879^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568664231 10000000000 8822619808879 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3953582081/5000000000 : ℝ)^135 ≤ (73508554589367/100000000000000 : ℝ)^103 := by
    have hnat : (3953582081 : ℕ)^135*100000000000000^103 ≤ 73508554589367^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3953582081 5000000000 73508554589367 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2664693999/10000000000 : ℝ)^135 ≤ (17668825586197/100000000000000 : ℝ)^103 := by
    have hnat : (2664693999 : ℕ)^135*100000000000000^103 ≤ 17668825586197^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2664693999 10000000000 17668825586197 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1568664231/10000000000 : ℝ), (3953582081/5000000000 : ℝ), (2664693999/10000000000 : ℝ)] ![(8822619808879/100000000000000 : ℝ), (73508554589367/100000000000000 : ℝ), (17668825586197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1568664231/10000000000 : ℝ)|^135 ≤ (8822619808879/100000000000000 : ℝ)^103
        have hw : |(1568664231/10000000000 : ℝ)|=(1568664231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3953582081/5000000000 : ℝ)|^135 ≤ (73508554589367/100000000000000 : ℝ)^103
        have hw : |(3953582081/5000000000 : ℝ)|=(3953582081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2664693999/10000000000 : ℝ)|^135 ≤ (17668825586197/100000000000000 : ℝ)^103
        have hw : |(2664693999/10000000000 : ℝ)|=(2664693999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s0_s0_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (9037021841/10000000000 : ℝ)*x 0 + (1018285931/5000000000 : ℝ)*x 1 + (397879/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9037021841/10000000000 : ℝ)^135 ≤ (87571602907849/100000000000000 : ℝ)^103 := by
    have hnat : (9037021841 : ℕ)^135*100000000000000^103 ≤ 87571602907849^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9037021841 10000000000 87571602907849 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018285931/5000000000 : ℝ)^135 ≤ (6210963582143/50000000000000 : ℝ)^103 := by
    have hnat : (1018285931 : ℕ)^135*50000000000000^103 ≤ 6210963582143^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018285931 5000000000 6210963582143 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397879/625000000 : ℝ)^135 ≤ (6469919603/100000000000000 : ℝ)^103 := by
    have hnat : (397879 : ℕ)^135*100000000000000^103 ≤ 6469919603^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397879 625000000 6469919603 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9037021841/10000000000 : ℝ), (1018285931/5000000000 : ℝ), (397879/625000000 : ℝ)] ![(87571602907849/100000000000000 : ℝ), (6210963582143/50000000000000 : ℝ), (6469919603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9037021841/10000000000 : ℝ)|^135 ≤ (87571602907849/100000000000000 : ℝ)^103
        have hw : |(9037021841/10000000000 : ℝ)|=(9037021841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1018285931/5000000000 : ℝ)|^135 ≤ (6210963582143/50000000000000 : ℝ)^103
        have hw : |(1018285931/5000000000 : ℝ)|=(1018285931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(397879/625000000 : ℝ)|^135 ≤ (6469919603/100000000000000 : ℝ)^103
        have hw : |(397879/625000000 : ℝ)|=(397879/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306060_s0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]]) : (0 : ℝ) ≤ ((47731/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47731/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47773/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(47773/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-90627/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-90627/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((4279764917/10000000000 : ℝ)*X 1 0+(-14165471/80000000 : ℝ)*X 1 1+(-3246649337/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-100728681/1250000000 : ℝ)*X 0 0+(90348531/400000000 : ℝ)*X 0 1+(-8601969661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2449837001/10000000000 : ℝ)*X 1 0+(-261090957/5000000000 : ℝ)*X 1 1+(-8601969273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1706428693/10000000000 : ℝ)*X 2 0+(208282177/250000000 : ℝ)*X 2 1+(95559849/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3543466029/10000000000 : ℝ)*X 0 0+(3987199897/5000000000 : ℝ)*X 0 1+(271/312500000 : ℝ)*X 0 2+(3543466029/10000000000 : ℝ)*X 1 0+(3987199897/5000000000 : ℝ)*X 1 1+(271/312500000 : ℝ)*X 1 2+(3543466029/10000000000 : ℝ)*X 2 0+(3987199897/5000000000 : ℝ)*X 2 1+(271/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-112716111/1000000000 : ℝ)*X 0 0+(6877969/50000000 : ℝ)*X 0 1+(-898029261/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((234199863/2000000000 : ℝ)*X 1 0+(-1333941553/10000000000 : ℝ)*X 1 1+(-2245073229/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7139049949/10000000000 : ℝ)*X 2 0+(1464145911/5000000000 : ℝ)*X 2 1+(2436435063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((8998319233/10000000000 : ℝ)*X 0 0+(2098489461/10000000000 : ℝ)*X 0 1+(739421/10000000000 : ℝ)*X 0 2+(8998319233/10000000000 : ℝ)*X 1 0+(2098489461/10000000000 : ℝ)*X 1 1+(739421/10000000000 : ℝ)*X 1 2+(8998319233/10000000000 : ℝ)*X 2 0+(2098489461/10000000000 : ℝ)*X 2 1+(739421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1643291/39062500 : ℝ)*X 0 0+(151079863/1250000000 : ℝ)*X 0 1+(-4698015203/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((998184547/1250000000 : ℝ)*X 1 0+(-67661037/400000000 : ℝ)*X 1 1+(-2446439181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1568664231/10000000000 : ℝ)*X 2 0+(3953582081/5000000000 : ℝ)*X 2 1+(2664693999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((9037021841/10000000000 : ℝ)*X 0 0+(1018285931/5000000000 : ℝ)*X 0 1+(397879/625000000 : ℝ)*X 0 2+(9037021841/10000000000 : ℝ)*X 1 0+(1018285931/5000000000 : ℝ)*X 1 1+(397879/625000000 : ℝ)*X 1 2+(9037021841/10000000000 : ℝ)*X 2 0+(1018285931/5000000000 : ℝ)*X 2 1+(397879/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((47731/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47731/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27937946835376784937201/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (445926816749/1000000000000 : ℝ)*(base5) + (958221616857/1000000000000 : ℝ)*(base7) + (489051/250000000000 : ℝ)*(base43) + (536206663707/1000000000000 : ℝ)*(base53) + (1543760778311/1000000000000 : ℝ)*(major_s0_0) + (1543758822107/1000000000000 : ℝ)*(major_s0_1) + (251888528651/250000000000 : ℝ)*(major_s0_2) + (14909113/1000000000000 : ℝ)*(sp_s0_1) + (955998190939/1000000000000 : ℝ)*(sp_s0_7) + (955951840117/1000000000000 : ℝ)*(sp_s0_8) + (77524656463/40000000000 : ℝ)*(sp_s0_9) + (756763791397/500000000000 : ℝ)*(sp_s0_13) + (33397913/1000000000000 : ℝ)*(sp_s0_15) + (762991/50000000000 : ℝ)*(sp_s0_23) + (200246556537/200000000000 : ℝ)*(f.failure) + (1492206810851/1000000000000 : ℝ)*(f.sum) + (269774259710933/2000000000000000000000000000 : ℝ)*base62 + (135227895795969/625000000000000000000000000 : ℝ)*base64 + (262192708201267/2500000000000000000000000000 : ℝ)*base66 + (44601618468753/500000000000000000000000000 : ℝ)*base68 + (3755587530314169/10000000000000000000000000000 : ℝ)*base70 + (483799495716991/2500000000000000000000000000 : ℝ)*base72 + (621144571035921/2000000000000000000000000000 : ℝ)*base74 + (780179680115733/2000000000000000000000000000 : ℝ)*base76 + (93146252209129/1250000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (3059/10000000000000000 : ℝ)*base86 + (3059/10000000000000000 : ℝ)*base88 + (3059/10000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47773/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(47773/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (60124319846333189795601/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1211294227/25000000000 : ℝ)*(base5) + (979710108623/1000000000000 : ℝ)*(base7) + (193129/125000000000 : ℝ)*(base34) + (367974977367/1000000000000 : ℝ)*(base53) + (122663078589/1000000000000 : ℝ)*(base60) + (761524931293/500000000000 : ℝ)*(major_s0_0) + (761525703809/500000000000 : ℝ)*(major_s0_1) + (1155076430251/1000000000000 : ℝ)*(major_s0_2) + (32650887/1000000000000 : ℝ)*(sp_s0_8) + (1082920249653/1000000000000 : ℝ)*(sp_s0_14) + (1082889143799/1000000000000 : ℝ)*(sp_s0_15) + (1499348541133/1000000000000 : ℝ)*(sp_s0_16) + (959436276323/500000000000 : ℝ)*(sp_s0_20) + (185603609/1000000000000 : ℝ)*(sp_s0_27) + (61737585109/62500000000 : ℝ)*(f.failure) + (1450896772053/1000000000000 : ℝ)*(f.sum) + (2257311575436807/2000000000000000000000000000 : ℝ)*base62 + (1655518826673869/2500000000000000000000000000 : ℝ)*base64 + (133109073780729/1250000000000000000000000000 : ℝ)*base66 + (1933589276503553/2000000000000000000000000000 : ℝ)*base68 + (1242184110569133/5000000000000000000000000000 : ℝ)*base70 + (577308725830867/1250000000000000000000000000 : ℝ)*base73 + (1000109080066627/1000000000000000000000000000 : ℝ)*base74 + (649530996944279/1000000000000000000000000000 : ℝ)*base76 + (59247099099931/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1887/3125000000000000 : ℝ)*base87 + (1887/3125000000000000 : ℝ)*base89 + (1887/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-90627/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-90627/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (36079810856794754416611/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2706601/250000000000 : ℝ)*(base5) + (91462693751/125000000000 : ℝ)*(base7) + (55076366367/1000000000000 : ℝ)*(base34) + (208181/1000000000000 : ℝ)*(base40) + (433261862859/500000000000 : ℝ)*(base43) + (16977302099/250000000000 : ℝ)*(base50) + (1378574077499/1000000000000 : ℝ)*(major_s0_0) + (141781679537/250000000000 : ℝ)*(major_s0_1) + (716825221933/500000000000 : ℝ)*(major_s0_2) + (56827311/500000000000 : ℝ)*(sp_s0_7) + (28106279499/50000000000 : ℝ)*(sp_s0_21) + (1483839336687/1000000000000 : ℝ)*(sp_s0_22) + (308663218687/500000000000 : ℝ)*(sp_s0_23) + (80321658799/50000000000 : ℝ)*(sp_s0_27) + (464909409371/500000000000 : ℝ)*(f.failure) + (1483839336687/1000000000000 : ℝ)*(f.sum) + (415118414432621/1000000000000000000000000000 : ℝ)*base62 + (570558638402027/1250000000000000000000000000 : ℝ)*base64 + (324730930222097/625000000000000000000000000 : ℝ)*base66 + (755006806208199/1000000000000000000000000000 : ℝ)*base68 + (1012898042314701/10000000000000000000000000000 : ℝ)*base70 + (129808079998381/2500000000000000000000000000 : ℝ)*base73 + (361478485212211/500000000000000000000000000 : ℝ)*base74 + (1512418745619697/2000000000000000000000000000 : ℝ)*base76 + (596131709640007/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (11497/25000000000000000 : ℝ)*base86 + (11497/25000000000000000 : ℝ)*base88 + (11497/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]]) : (0 : ℝ) ≤ ((47731/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47731/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47773/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(47773/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-90627/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-90627/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306060_s0 p hpa hpb X hX

#print axioms solution
