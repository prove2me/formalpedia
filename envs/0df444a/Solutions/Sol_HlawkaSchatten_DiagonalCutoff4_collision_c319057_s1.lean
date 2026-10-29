-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c319057_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:30:18.536213+00:00
-- url     : https://prove2.me/submissions/97a1cf3f-deb5-45b0-b358-a0bbda26c9c6

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
theorem collision_support_c319057_s1_s1_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1616836691/5000000000 : ℝ)*x 0 + (64573859/200000000 : ℝ)*x 1 + (5860566753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1616836691/5000000000 : ℝ)^5 ≤ (24384855685999/100000000000000 : ℝ)^4 := by
    have hnat : (1616836691 : ℕ)^5*100000000000000^4 ≤ 24384855685999^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616836691 5000000000 24384855685999 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64573859/200000000 : ℝ)^5 ≤ (24337918460531/100000000000000 : ℝ)^4 := by
    have hnat : (64573859 : ℕ)^5*100000000000000^4 ≤ 24337918460531^4*200000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64573859 200000000 24337918460531 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5860566753/10000000000 : ℝ)^5 ≤ (10255445167303/20000000000000 : ℝ)^4 := by
    have hnat : (5860566753 : ℕ)^5*20000000000000^4 ≤ 10255445167303^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5860566753 10000000000 10255445167303 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1616836691/5000000000 : ℝ), (64573859/200000000 : ℝ), (5860566753/10000000000 : ℝ)] ![(24384855685999/100000000000000 : ℝ), (24337918460531/100000000000000 : ℝ), (10255445167303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1616836691/5000000000 : ℝ)|^5 ≤ (24384855685999/100000000000000 : ℝ)^4
        have hw : |(-1616836691/5000000000 : ℝ)|=(1616836691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64573859/200000000 : ℝ)|^5 ≤ (24337918460531/100000000000000 : ℝ)^4
        have hw : |(64573859/200000000 : ℝ)|=(64573859/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5860566753/10000000000 : ℝ)|^5 ≤ (10255445167303/20000000000000 : ℝ)^4
        have hw : |(5860566753/10000000000 : ℝ)|=(5860566753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1614765129/5000000000 : ℝ)*x 0 + (-3224556207/10000000000 : ℝ)*x 1 + (2933849639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1614765129/5000000000 : ℝ)^5 ≤ (6086452065237/25000000000000 : ℝ)^4 := by
    have hnat : (1614765129 : ℕ)^5*25000000000000^4 ≤ 6086452065237^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614765129 5000000000 6086452065237 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3224556207/10000000000 : ℝ)^5 ≤ (24298946194583/100000000000000 : ℝ)^4 := by
    have hnat : (3224556207 : ℕ)^5*100000000000000^4 ≤ 24298946194583^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3224556207 10000000000 24298946194583 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2933849639/5000000000 : ℝ)^5 ≤ (12838811383577/25000000000000 : ℝ)^4 := by
    have hnat : (2933849639 : ℕ)^5*25000000000000^4 ≤ 12838811383577^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2933849639 5000000000 12838811383577 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1614765129/5000000000 : ℝ), (-3224556207/10000000000 : ℝ), (2933849639/5000000000 : ℝ)] ![(6086452065237/25000000000000 : ℝ), (24298946194583/100000000000000 : ℝ), (12838811383577/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1614765129/5000000000 : ℝ)|^5 ≤ (6086452065237/25000000000000 : ℝ)^4
        have hw : |(1614765129/5000000000 : ℝ)|=(1614765129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3224556207/10000000000 : ℝ)|^5 ≤ (24298946194583/100000000000000 : ℝ)^4
        have hw : |(-3224556207/10000000000 : ℝ)|=(3224556207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2933849639/5000000000 : ℝ)|^5 ≤ (12838811383577/25000000000000 : ℝ)^4
        have hw : |(2933849639/5000000000 : ℝ)|=(2933849639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5589096523/10000000000 : ℝ)*x 0 + (5596791811/10000000000 : ℝ)*x 1 + (-258963/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5589096523/10000000000 : ℝ)^5 ≤ (48325573019073/100000000000000 : ℝ)^4 := by
    have hnat : (5589096523 : ℕ)^5*100000000000000^4 ≤ 48325573019073^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5589096523 10000000000 48325573019073 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5596791811/10000000000 : ℝ)^5 ≤ (12102189504039/25000000000000 : ℝ)^4 := by
    have hnat : (5596791811 : ℕ)^5*25000000000000^4 ≤ 12102189504039^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5596791811 10000000000 12102189504039 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258963/4000000 : ℝ)^5 ≤ (653133791249/20000000000000 : ℝ)^4 := by
    have hnat : (258963 : ℕ)^5*20000000000000^4 ≤ 653133791249^4*4000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258963 4000000 653133791249 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5589096523/10000000000 : ℝ), (5596791811/10000000000 : ℝ), (-258963/4000000 : ℝ)] ![(48325573019073/100000000000000 : ℝ), (12102189504039/25000000000000 : ℝ), (653133791249/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5589096523/10000000000 : ℝ)|^5 ≤ (48325573019073/100000000000000 : ℝ)^4
        have hw : |(5589096523/10000000000 : ℝ)|=(5589096523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5596791811/10000000000 : ℝ)|^5 ≤ (12102189504039/25000000000000 : ℝ)^4
        have hw : |(5596791811/10000000000 : ℝ)|=(5596791811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258963/4000000 : ℝ)|^5 ≤ (653133791249/20000000000000 : ℝ)^4
        have hw : |(-258963/4000000 : ℝ)|=(258963/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2218273961/5000000000 : ℝ)*x 0 + (277666021/625000000 : ℝ)*x 1 + (3562343507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2218273961/5000000000 : ℝ)^5 ≤ (905204032309/2500000000000 : ℝ)^4 := by
    have hnat : (2218273961 : ℕ)^5*2500000000000^4 ≤ 905204032309^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218273961 5000000000 905204032309 2500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277666021/625000000 : ℝ)^5 ≤ (36270488042617/100000000000000 : ℝ)^4 := by
    have hnat : (277666021 : ℕ)^5*100000000000000^4 ≤ 36270488042617^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277666021 625000000 36270488042617 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3562343507/10000000000 : ℝ)^5 ≤ (5504270129977/20000000000000 : ℝ)^4 := by
    have hnat : (3562343507 : ℕ)^5*20000000000000^4 ≤ 5504270129977^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3562343507 10000000000 5504270129977 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2218273961/5000000000 : ℝ), (277666021/625000000 : ℝ), (3562343507/10000000000 : ℝ)] ![(905204032309/2500000000000 : ℝ), (36270488042617/100000000000000 : ℝ), (5504270129977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2218273961/5000000000 : ℝ)|^5 ≤ (905204032309/2500000000000 : ℝ)^4
        have hw : |(2218273961/5000000000 : ℝ)|=(2218273961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(277666021/625000000 : ℝ)|^5 ≤ (36270488042617/100000000000000 : ℝ)^4
        have hw : |(277666021/625000000 : ℝ)|=(277666021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3562343507/10000000000 : ℝ)|^5 ≤ (5504270129977/20000000000000 : ℝ)^4
        have hw : |(3562343507/10000000000 : ℝ)|=(3562343507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-318628817/1000000000 : ℝ)*x 0 + (47461147/156250000 : ℝ)*x 1 + (1515981649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (318628817/1000000000 : ℝ)^5 ≤ (23939017041651/100000000000000 : ℝ)^4 := by
    have hnat : (318628817 : ℕ)^5*100000000000000^4 ≤ 23939017041651^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318628817 1000000000 23939017041651 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47461147/156250000 : ℝ)^5 ≤ (22550062741257/100000000000000 : ℝ)^4 := by
    have hnat : (47461147 : ℕ)^5*100000000000000^4 ≤ 22550062741257^4*156250000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47461147 156250000 22550062741257 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1515981649/2500000000 : ℝ)^5 ≤ (53510920200881/100000000000000 : ℝ)^4 := by
    have hnat : (1515981649 : ℕ)^5*100000000000000^4 ≤ 53510920200881^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1515981649 2500000000 53510920200881 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-318628817/1000000000 : ℝ), (47461147/156250000 : ℝ), (1515981649/2500000000 : ℝ)] ![(23939017041651/100000000000000 : ℝ), (22550062741257/100000000000000 : ℝ), (53510920200881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-318628817/1000000000 : ℝ)|^5 ≤ (23939017041651/100000000000000 : ℝ)^4
        have hw : |(-318628817/1000000000 : ℝ)|=(318628817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(47461147/156250000 : ℝ)|^5 ≤ (22550062741257/100000000000000 : ℝ)^4
        have hw : |(47461147/156250000 : ℝ)|=(47461147/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1515981649/2500000000 : ℝ)|^5 ≤ (53510920200881/100000000000000 : ℝ)^4
        have hw : |(1515981649/2500000000 : ℝ)|=(1515981649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (99436591/312500000 : ℝ)*x 0 + (-3033397733/10000000000 : ℝ)*x 1 + (3035531241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99436591/312500000 : ℝ)^5 ≤ (11949239363387/50000000000000 : ℝ)^4 := by
    have hnat : (99436591 : ℕ)^5*50000000000000^4 ≤ 11949239363387^4*312500000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99436591 312500000 11949239363387 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3033397733/10000000000 : ℝ)^5 ≤ (22511876487899/100000000000000 : ℝ)^4 := by
    have hnat : (3033397733 : ℕ)^5*100000000000000^4 ≤ 22511876487899^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3033397733 10000000000 22511876487899 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3035531241/5000000000 : ℝ)^5 ≤ (53589644764173/100000000000000 : ℝ)^4 := by
    have hnat : (3035531241 : ℕ)^5*100000000000000^4 ≤ 53589644764173^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3035531241 5000000000 53589644764173 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(99436591/312500000 : ℝ), (-3033397733/10000000000 : ℝ), (3035531241/5000000000 : ℝ)] ![(11949239363387/50000000000000 : ℝ), (22511876487899/100000000000000 : ℝ), (53589644764173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(99436591/312500000 : ℝ)|^5 ≤ (11949239363387/50000000000000 : ℝ)^4
        have hw : |(99436591/312500000 : ℝ)|=(99436591/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3033397733/10000000000 : ℝ)|^5 ≤ (22511876487899/100000000000000 : ℝ)^4
        have hw : |(-3033397733/10000000000 : ℝ)|=(3033397733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3035531241/5000000000 : ℝ)|^5 ≤ (53589644764173/100000000000000 : ℝ)^4
        have hw : |(3035531241/5000000000 : ℝ)|=(3035531241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1364679211/2500000000 : ℝ)*x 0 + (1459257797/2500000000 : ℝ)*x 1 + (-44772111/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1364679211/2500000000 : ℝ)^5 ≤ (46920562377657/100000000000000 : ℝ)^4 := by
    have hnat : (1364679211 : ℕ)^5*100000000000000^4 ≤ 46920562377657^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364679211 2500000000 46920562377657 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1459257797/2500000000 : ℝ)^5 ≤ (2040797946417/4000000000000 : ℝ)^4 := by
    have hnat : (1459257797 : ℕ)^5*4000000000000^4 ≤ 2040797946417^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459257797 2500000000 2040797946417 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44772111/1000000000 : ℝ)^5 ≤ (2059488943463/100000000000000 : ℝ)^4 := by
    have hnat : (44772111 : ℕ)^5*100000000000000^4 ≤ 2059488943463^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44772111 1000000000 2059488943463 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1364679211/2500000000 : ℝ), (1459257797/2500000000 : ℝ), (-44772111/1000000000 : ℝ)] ![(46920562377657/100000000000000 : ℝ), (2040797946417/4000000000000 : ℝ), (2059488943463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1364679211/2500000000 : ℝ)|^5 ≤ (46920562377657/100000000000000 : ℝ)^4
        have hw : |(1364679211/2500000000 : ℝ)|=(1364679211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1459257797/2500000000 : ℝ)|^5 ≤ (2040797946417/4000000000000 : ℝ)^4
        have hw : |(1459257797/2500000000 : ℝ)|=(1459257797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44772111/1000000000 : ℝ)|^5 ≤ (2059488943463/100000000000000 : ℝ)^4
        have hw : |(-44772111/1000000000 : ℝ)|=(44772111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_12 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2265475919/5000000000 : ℝ)*x 0 + (4844967773/10000000000 : ℝ)*x 1 + (3021828331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2265475919/5000000000 : ℝ)^5 ≤ (4646723387177/12500000000000 : ℝ)^4 := by
    have hnat : (2265475919 : ℕ)^5*12500000000000^4 ≤ 4646723387177^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265475919 5000000000 4646723387177 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4844967773/10000000000 : ℝ)^5 ≤ (8084322153183/20000000000000 : ℝ)^4 := by
    have hnat : (4844967773 : ℕ)^5*20000000000000^4 ≤ 8084322153183^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844967773 10000000000 8084322153183 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3021828331/10000000000 : ℝ)^5 ≤ (11202301059697/50000000000000 : ℝ)^4 := by
    have hnat : (3021828331 : ℕ)^5*50000000000000^4 ≤ 11202301059697^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021828331 10000000000 11202301059697 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2265475919/5000000000 : ℝ), (4844967773/10000000000 : ℝ), (3021828331/10000000000 : ℝ)] ![(4646723387177/12500000000000 : ℝ), (8084322153183/20000000000000 : ℝ), (11202301059697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2265475919/5000000000 : ℝ)|^5 ≤ (4646723387177/12500000000000 : ℝ)^4
        have hw : |(2265475919/5000000000 : ℝ)|=(2265475919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4844967773/10000000000 : ℝ)|^5 ≤ (8084322153183/20000000000000 : ℝ)^4
        have hw : |(4844967773/10000000000 : ℝ)|=(4844967773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3021828331/10000000000 : ℝ)|^5 ≤ (11202301059697/50000000000000 : ℝ)^4
        have hw : |(3021828331/10000000000 : ℝ)|=(3021828331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-760621509/2500000000 : ℝ)*x 0 + (3181373829/10000000000 : ℝ)*x 1 + (3031962809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (760621509/2500000000 : ℝ)^5 ≤ (22596217274249/100000000000000 : ℝ)^4 := by
    have hnat : (760621509 : ℕ)^5*100000000000000^4 ≤ 22596217274249^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760621509 2500000000 22596217274249 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3181373829/10000000000 : ℝ)^5 ≤ (4778574660259/20000000000000 : ℝ)^4 := by
    have hnat : (3181373829 : ℕ)^5*20000000000000^4 ≤ 4778574660259^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3181373829 10000000000 4778574660259 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3031962809/5000000000 : ℝ)^5 ≤ (53510909412971/100000000000000 : ℝ)^4 := by
    have hnat : (3031962809 : ℕ)^5*100000000000000^4 ≤ 53510909412971^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3031962809 5000000000 53510909412971 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-760621509/2500000000 : ℝ), (3181373829/10000000000 : ℝ), (3031962809/5000000000 : ℝ)] ![(22596217274249/100000000000000 : ℝ), (4778574660259/20000000000000 : ℝ), (53510909412971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-760621509/2500000000 : ℝ)|^5 ≤ (22596217274249/100000000000000 : ℝ)^4
        have hw : |(-760621509/2500000000 : ℝ)|=(760621509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3181373829/10000000000 : ℝ)|^5 ≤ (4778574660259/20000000000000 : ℝ)^4
        have hw : |(3181373829/10000000000 : ℝ)|=(3181373829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3031962809/5000000000 : ℝ)|^5 ≤ (53510909412971/100000000000000 : ℝ)^4
        have hw : |(3031962809/5000000000 : ℝ)|=(3031962809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1519181483/5000000000 : ℝ)*x 0 + (-3177062543/10000000000 : ℝ)*x 1 + (6071062643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1519181483/5000000000 : ℝ)^5 ≤ (2819743345299/12500000000000 : ℝ)^4 := by
    have hnat : (1519181483 : ℕ)^5*12500000000000^4 ≤ 2819743345299^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519181483 5000000000 2819743345299 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3177062543/10000000000 : ℝ)^5 ≤ (11926203340977/50000000000000 : ℝ)^4 := by
    have hnat : (3177062543 : ℕ)^5*50000000000000^4 ≤ 11926203340977^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3177062543 10000000000 11926203340977 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6071062643/10000000000 : ℝ)^5 ≤ (2679482327031/5000000000000 : ℝ)^4 := by
    have hnat : (6071062643 : ℕ)^5*5000000000000^4 ≤ 2679482327031^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6071062643 10000000000 2679482327031 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1519181483/5000000000 : ℝ), (-3177062543/10000000000 : ℝ), (6071062643/10000000000 : ℝ)] ![(2819743345299/12500000000000 : ℝ), (11926203340977/50000000000000 : ℝ), (2679482327031/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1519181483/5000000000 : ℝ)|^5 ≤ (2819743345299/12500000000000 : ℝ)^4
        have hw : |(1519181483/5000000000 : ℝ)|=(1519181483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3177062543/10000000000 : ℝ)|^5 ≤ (11926203340977/50000000000000 : ℝ)^4
        have hw : |(-3177062543/10000000000 : ℝ)|=(3177062543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6071062643/10000000000 : ℝ)|^5 ≤ (2679482327031/5000000000000 : ℝ)^4
        have hw : |(6071062643/10000000000 : ℝ)|=(6071062643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5829429147/10000000000 : ℝ)*x 0 + (2733222271/5000000000 : ℝ)*x 1 + (-111930343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5829429147/10000000000 : ℝ)^5 ≤ (50936902894851/100000000000000 : ℝ)^4 := by
    have hnat : (5829429147 : ℕ)^5*100000000000000^4 ≤ 50936902894851^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5829429147 10000000000 50936902894851 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733222271/5000000000 : ℝ)^5 ≤ (9400721327321/20000000000000 : ℝ)^4 := by
    have hnat : (2733222271 : ℕ)^5*20000000000000^4 ≤ 9400721327321^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733222271 5000000000 9400721327321 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111930343/2500000000 : ℝ)^5 ≤ (2059490449943/100000000000000 : ℝ)^4 := by
    have hnat : (111930343 : ℕ)^5*100000000000000^4 ≤ 2059490449943^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111930343 2500000000 2059490449943 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5829429147/10000000000 : ℝ), (2733222271/5000000000 : ℝ), (-111930343/2500000000 : ℝ)] ![(50936902894851/100000000000000 : ℝ), (9400721327321/20000000000000 : ℝ), (2059490449943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5829429147/10000000000 : ℝ)|^5 ≤ (50936902894851/100000000000000 : ℝ)^4
        have hw : |(5829429147/10000000000 : ℝ)|=(5829429147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733222271/5000000000 : ℝ)|^5 ≤ (9400721327321/20000000000000 : ℝ)^4
        have hw : |(2733222271/5000000000 : ℝ)|=(2733222271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111930343/2500000000 : ℝ)|^5 ≤ (2059490449943/100000000000000 : ℝ)^4
        have hw : |(-111930343/2500000000 : ℝ)|=(111930343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_18 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4838658077/10000000000 : ℝ)*x 0 + (283585401/625000000 : ℝ)*x 1 + (302182781/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4838658077/10000000000 : ℝ)^5 ≤ (40355819166537/100000000000000 : ℝ)^4 := by
    have hnat : (4838658077 : ℕ)^5*100000000000000^4 ≤ 40355819166537^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838658077 10000000000 40355819166537 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283585401/625000000 : ℝ)^5 ≤ (37239583520733/100000000000000 : ℝ)^4 := by
    have hnat : (283585401 : ℕ)^5*100000000000000^4 ≤ 37239583520733^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283585401 625000000 37239583520733 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302182781/1000000000 : ℝ)^5 ≤ (22404597290861/100000000000000 : ℝ)^4 := by
    have hnat : (302182781 : ℕ)^5*100000000000000^4 ≤ 22404597290861^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302182781 1000000000 22404597290861 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4838658077/10000000000 : ℝ), (283585401/625000000 : ℝ), (302182781/1000000000 : ℝ)] ![(40355819166537/100000000000000 : ℝ), (37239583520733/100000000000000 : ℝ), (22404597290861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4838658077/10000000000 : ℝ)|^5 ≤ (40355819166537/100000000000000 : ℝ)^4
        have hw : |(4838658077/10000000000 : ℝ)|=(4838658077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283585401/625000000 : ℝ)|^5 ≤ (37239583520733/100000000000000 : ℝ)^4
        have hw : |(283585401/625000000 : ℝ)|=(283585401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(302182781/1000000000 : ℝ)|^5 ≤ (22404597290861/100000000000000 : ℝ)^4
        have hw : |(302182781/1000000000 : ℝ)|=(302182781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_19 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-65519951/200000000 : ℝ)*x 0 + (3190000249/10000000000 : ℝ)*x 1 + (5857314273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65519951/200000000 : ℝ)^5 ≤ (6196114990959/25000000000000 : ℝ)^4 := by
    have hnat : (65519951 : ℕ)^5*25000000000000^4 ≤ 6196114990959^4*200000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65519951 200000000 6196114990959 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3190000249/10000000000 : ℝ)^5 ≤ (23973883810941/100000000000000 : ℝ)^4 := by
    have hnat : (3190000249 : ℕ)^5*100000000000000^4 ≤ 23973883810941^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3190000249 10000000000 23973883810941 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5857314273/10000000000 : ℝ)^5 ≤ (10248331240137/20000000000000 : ℝ)^4 := by
    have hnat : (5857314273 : ℕ)^5*20000000000000^4 ≤ 10248331240137^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5857314273 10000000000 10248331240137 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65519951/200000000 : ℝ), (3190000249/10000000000 : ℝ), (5857314273/10000000000 : ℝ)] ![(6196114990959/25000000000000 : ℝ), (23973883810941/100000000000000 : ℝ), (10248331240137/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65519951/200000000 : ℝ)|^5 ≤ (6196114990959/25000000000000 : ℝ)^4
        have hw : |(-65519951/200000000 : ℝ)|=(65519951/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3190000249/10000000000 : ℝ)|^5 ≤ (23973883810941/100000000000000 : ℝ)^4
        have hw : |(3190000249/10000000000 : ℝ)|=(3190000249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5857314273/10000000000 : ℝ)|^5 ≤ (10248331240137/20000000000000 : ℝ)^4
        have hw : |(5857314273/10000000000 : ℝ)|=(5857314273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1595427991/5000000000 : ℝ)*x 0 + (-1633445487/5000000000 : ℝ)*x 1 + (2932225293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1595427991/5000000000 : ℝ)^5 ≤ (23981922968379/100000000000000 : ℝ)^4 := by
    have hnat : (1595427991 : ℕ)^5*100000000000000^4 ≤ 23981922968379^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595427991 5000000000 23981922968379 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1633445487/5000000000 : ℝ)^5 ≤ (3087296312961/12500000000000 : ℝ)^4 := by
    have hnat : (1633445487 : ℕ)^5*12500000000000^4 ≤ 3087296312961^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633445487 5000000000 3087296312961 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2932225293/5000000000 : ℝ)^5 ≤ (2052788260557/4000000000000 : ℝ)^4 := by
    have hnat : (2932225293 : ℕ)^5*4000000000000^4 ≤ 2052788260557^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2932225293 5000000000 2052788260557 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1595427991/5000000000 : ℝ), (-1633445487/5000000000 : ℝ), (2932225293/5000000000 : ℝ)] ![(23981922968379/100000000000000 : ℝ), (3087296312961/12500000000000 : ℝ), (2052788260557/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1595427991/5000000000 : ℝ)|^5 ≤ (23981922968379/100000000000000 : ℝ)^4
        have hw : |(1595427991/5000000000 : ℝ)|=(1595427991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1633445487/5000000000 : ℝ)|^5 ≤ (3087296312961/12500000000000 : ℝ)^4
        have hw : |(-1633445487/5000000000 : ℝ)|=(1633445487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2932225293/5000000000 : ℝ)|^5 ≤ (2052788260557/4000000000000 : ℝ)^4
        have hw : |(2932225293/5000000000 : ℝ)|=(2932225293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5611245443/10000000000 : ℝ)*x 0 + (2788469527/5000000000 : ℝ)*x 1 + (-321723191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5611245443/10000000000 : ℝ)^5 ≤ (9713015411/20000000000 : ℝ)^4 := by
    have hnat : (5611245443 : ℕ)^5*20000000000^4 ≤ 9713015411^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5611245443 10000000000 9713015411 20000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2788469527/5000000000 : ℝ)^5 ≤ (24097105408411/50000000000000 : ℝ)^4 := by
    have hnat : (2788469527 : ℕ)^5*50000000000000^4 ≤ 24097105408411^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788469527 5000000000 24097105408411 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321723191/5000000000 : ℝ)^5 ≤ (1620356062637/50000000000000 : ℝ)^4 := by
    have hnat : (321723191 : ℕ)^5*50000000000000^4 ≤ 1620356062637^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321723191 5000000000 1620356062637 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5611245443/10000000000 : ℝ), (2788469527/5000000000 : ℝ), (-321723191/5000000000 : ℝ)] ![(9713015411/20000000000 : ℝ), (24097105408411/50000000000000 : ℝ), (1620356062637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5611245443/10000000000 : ℝ)|^5 ≤ (9713015411/20000000000 : ℝ)^4
        have hw : |(5611245443/10000000000 : ℝ)|=(5611245443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2788469527/5000000000 : ℝ)|^5 ≤ (24097105408411/50000000000000 : ℝ)^4
        have hw : |(2788469527/5000000000 : ℝ)|=(2788469527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-321723191/5000000000 : ℝ)|^5 ≤ (1620356062637/50000000000000 : ℝ)^4
        have hw : |(-321723191/5000000000 : ℝ)|=(321723191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319057_s1_s1_25 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4385225937/10000000000 : ℝ)*x 0 + (4504834651/10000000000 : ℝ)*x 1 + (1775327167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4385225937/10000000000 : ℝ)^5 ≤ (7137070115359/20000000000000 : ℝ)^4 := by
    have hnat : (4385225937 : ℕ)^5*20000000000000^4 ≤ 7137070115359^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4385225937 10000000000 7137070115359 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504834651/10000000000 : ℝ)^5 ≤ (9226533805717/25000000000000 : ℝ)^4 := by
    have hnat : (4504834651 : ℕ)^5*25000000000000^4 ≤ 9226533805717^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504834651 10000000000 9226533805717 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1775327167/5000000000 : ℝ)^5 ≤ (13704257097507/50000000000000 : ℝ)^4 := by
    have hnat : (1775327167 : ℕ)^5*50000000000000^4 ≤ 13704257097507^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775327167 5000000000 13704257097507 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4385225937/10000000000 : ℝ), (4504834651/10000000000 : ℝ), (1775327167/5000000000 : ℝ)] ![(7137070115359/20000000000000 : ℝ), (9226533805717/25000000000000 : ℝ), (13704257097507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4385225937/10000000000 : ℝ)|^5 ≤ (7137070115359/20000000000000 : ℝ)^4
        have hw : |(4385225937/10000000000 : ℝ)|=(4385225937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504834651/10000000000 : ℝ)|^5 ≤ (9226533805717/25000000000000 : ℝ)^4
        have hw : |(4504834651/10000000000 : ℝ)|=(4504834651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1775327167/5000000000 : ℝ)|^5 ≤ (13704257097507/50000000000000 : ℝ)^4
        have hw : |(1775327167/5000000000 : ℝ)|=(1775327167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319057_s1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((9273/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9273/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18413/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18413/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(34773/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(34773/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3193/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3193/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25507/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25507/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(541/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(541/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (9273/12500 : ℝ) ^ (79/16 : ℝ) ≤ (2861322806443758999/12500000000000000000 : ℝ) := by
    have hpowers : (9273/12500 : ℝ)^79 ≤ (2861322806443758999/12500000000000000000 : ℝ)^16 := by
      have hnat : (9273 : ℕ)^79*12500000000000000000^16 ≤ 2861322806443758999^16*12500^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9273 12500 2861322806443758999 12500000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9273/12500 : ℝ)) (X := (2861322806443758999/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (15361322806443758999/12500000000000000000 : ℝ) ≤ (2606575798248519/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (15361322806443758999/12500000000000000000 : ℝ)^16 ≤ (2606575798248519/2500000000000000 : ℝ)^79 := by
      have hnat : (15361322806443758999 : ℕ)^16*2500000000000000^79 ≤ 2606575798248519^79*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15361322806443758999 12500000000000000000 2606575798248519 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2606575798248519/2500000000000000 : ℝ)) (X := (15361322806443758999/12500000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (9111322806443758999/6250000000000000000 : ℝ) ≤ (10793311649933011/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (9111322806443758999/6250000000000000000 : ℝ)^16 ≤ (10793311649933011/10000000000000000 : ℝ)^79 := by
      have hnat : (9111322806443758999 : ℕ)^16*10000000000000000^79 ≤ 10793311649933011^79*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9111322806443758999 6250000000000000000 10793311649933011 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10793311649933011/10000000000000000 : ℝ)) (X := (9111322806443758999/6250000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(106575798248519/1854600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(73401691387787/1483680000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (9273/12500 : ℝ)) (alpha := (106575798248519/1854600000000000 : ℝ)) (beta := (73401691387787/1483680000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (9273/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(106575798248519/1854600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(73401691387787/1483680000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (18413/25000 : ℝ) ^ (79/16 : ℝ) ≤ (22091422843711405773/100000000000000000000 : ℝ) := by
    have hpowers : (18413/25000 : ℝ)^79 ≤ (22091422843711405773/100000000000000000000 : ℝ)^16 := by
      have hnat : (18413 : ℕ)^79*100000000000000000000^16 ≤ 22091422843711405773^16*25000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18413 25000 22091422843711405773 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18413/25000 : ℝ)) (X := (22091422843711405773/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (122091422843711405773/100000000000000000000 : ℝ) ≤ (1041253530838339/1000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (122091422843711405773/100000000000000000000 : ℝ)^16 ≤ (1041253530838339/1000000000000000 : ℝ)^79 := by
      have hnat : (122091422843711405773 : ℕ)^16*1000000000000000^79 ≤ 1041253530838339^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        122091422843711405773 100000000000000000000 1041253530838339 1000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1041253530838339/1000000000000000 : ℝ)) (X := (122091422843711405773/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (72091422843711405773/50000000000000000000 : ℝ) ≤ (10769239400609591/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (72091422843711405773/50000000000000000000 : ℝ)^16 ≤ (10769239400609591/10000000000000000 : ℝ)^79 := by
      have hnat : (72091422843711405773 : ℕ)^16*10000000000000000^79 ≤ 10769239400609591^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72091422843711405773 50000000000000000000 10769239400609591 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10769239400609591/10000000000000000 : ℝ)) (X := (72091422843711405773/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(41253530838339/736520000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(356704092226201/7365200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (18413/25000 : ℝ)) (alpha := (41253530838339/736520000000000 : ℝ)) (beta := (356704092226201/7365200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (18413/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(41253530838339/736520000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(356704092226201/7365200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (34773/100000 : ℝ) ^ (79/16 : ℝ) ≤ (543104207962377063/100000000000000000000 : ℝ) := by
    have hpowers : (34773/100000 : ℝ)^79 ≤ (543104207962377063/100000000000000000000 : ℝ)^16 := by
      have hnat : (34773 : ℕ)^79*100000000000000000000^16 ≤ 543104207962377063^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34773 100000 543104207962377063 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34773/100000 : ℝ)) (X := (543104207962377063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100543104207962377063/100000000000000000000 : ℝ) ≤ (5005487918031281/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (100543104207962377063/100000000000000000000 : ℝ)^16 ≤ (5005487918031281/5000000000000000 : ℝ)^79 := by
      have hnat : (100543104207962377063 : ℕ)^16*5000000000000000^79 ≤ 5005487918031281^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100543104207962377063 100000000000000000000 5005487918031281 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005487918031281/5000000000000000 : ℝ)) (X := (100543104207962377063/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50543104207962377063/50000000000000000000 : ℝ) ≤ (5010952246502959/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (50543104207962377063/50000000000000000000 : ℝ)^16 ≤ (5010952246502959/5000000000000000 : ℝ)^79 := by
      have hnat : (50543104207962377063 : ℕ)^16*5000000000000000^79 ≤ 5010952246502959^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50543104207962377063 50000000000000000000 5010952246502959 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010952246502959/5000000000000000 : ℝ)) (X := (50543104207962377063/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1829306010427/579550000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(2732164235839/869325000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (34773/100000 : ℝ)) (alpha := (1829306010427/579550000000000 : ℝ)) (beta := (2732164235839/869325000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (34773/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1829306010427/579550000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(2732164235839/869325000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1616836691/5000000000 : ℝ)*X 0 0+(64573859/200000000 : ℝ)*X 0 1+(5860566753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1614765129/5000000000 : ℝ)*X 1 0+(-3224556207/10000000000 : ℝ)*X 1 1+(2933849639/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5589096523/10000000000 : ℝ)*X 2 0+(5596791811/10000000000 : ℝ)*X 2 1+(-258963/4000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2218273961/5000000000 : ℝ)*X 0 0+(277666021/625000000 : ℝ)*X 0 1+(3562343507/10000000000 : ℝ)*X 0 2+(2218273961/5000000000 : ℝ)*X 1 0+(277666021/625000000 : ℝ)*X 1 1+(3562343507/10000000000 : ℝ)*X 1 2+(2218273961/5000000000 : ℝ)*X 2 0+(277666021/625000000 : ℝ)*X 2 1+(3562343507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-318628817/1000000000 : ℝ)*X 0 0+(47461147/156250000 : ℝ)*X 0 1+(1515981649/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((99436591/312500000 : ℝ)*X 1 0+(-3033397733/10000000000 : ℝ)*X 1 1+(3035531241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1364679211/2500000000 : ℝ)*X 2 0+(1459257797/2500000000 : ℝ)*X 2 1+(-44772111/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((2265475919/5000000000 : ℝ)*X 0 0+(4844967773/10000000000 : ℝ)*X 0 1+(3021828331/10000000000 : ℝ)*X 0 2+(2265475919/5000000000 : ℝ)*X 1 0+(4844967773/10000000000 : ℝ)*X 1 1+(3021828331/10000000000 : ℝ)*X 1 2+(2265475919/5000000000 : ℝ)*X 2 0+(4844967773/10000000000 : ℝ)*X 2 1+(3021828331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-760621509/2500000000 : ℝ)*X 0 0+(3181373829/10000000000 : ℝ)*X 0 1+(3031962809/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((1519181483/5000000000 : ℝ)*X 1 0+(-3177062543/10000000000 : ℝ)*X 1 1+(6071062643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((5829429147/10000000000 : ℝ)*X 2 0+(2733222271/5000000000 : ℝ)*X 2 1+(-111930343/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((4838658077/10000000000 : ℝ)*X 0 0+(283585401/625000000 : ℝ)*X 0 1+(302182781/1000000000 : ℝ)*X 0 2+(4838658077/10000000000 : ℝ)*X 1 0+(283585401/625000000 : ℝ)*X 1 1+(302182781/1000000000 : ℝ)*X 1 2+(4838658077/10000000000 : ℝ)*X 2 0+(283585401/625000000 : ℝ)*X 2 1+(302182781/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-65519951/200000000 : ℝ)*X 0 0+(3190000249/10000000000 : ℝ)*X 0 1+(5857314273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1595427991/5000000000 : ℝ)*X 1 0+(-1633445487/5000000000 : ℝ)*X 1 1+(2932225293/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((5611245443/10000000000 : ℝ)*X 2 0+(2788469527/5000000000 : ℝ)*X 2 1+(-321723191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((4385225937/10000000000 : ℝ)*X 0 0+(4504834651/10000000000 : ℝ)*X 0 1+(1775327167/5000000000 : ℝ)*X 0 2+(4385225937/10000000000 : ℝ)*X 1 0+(4504834651/10000000000 : ℝ)*X 1 1+(1775327167/5000000000 : ℝ)*X 1 2+(4385225937/10000000000 : ℝ)*X 2 0+(4504834651/10000000000 : ℝ)*X 2 1+(1775327167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319057_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((3193/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3193/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (188145745946675290954251539167/65969693155300000000000000000000000 : ℝ) := by norm_num
    linear_combination (2510767/500000000000 : ℝ)*(base23) + (10025776491677/1000000000000 : ℝ)*(base59) + (4848471078977/1000000000000 : ℝ)*(base60) + (8874250873043/500000000000 : ℝ)*(major_s1_0) + (8874250873043/500000000000 : ℝ)*(major_s1_1) + (8874250873043/500000000000 : ℝ)*(major_s1_2) + (54391567/1000000000000 : ℝ)*(sp_s1_0) + (667059/15625000000 : ℝ)*(sp_s1_2) + (12954009207239/500000000000 : ℝ)*(sp_s1_7) + (12954045009043/500000000000 : ℝ)*(sp_s1_8) + (25908042304777/1000000000000 : ℝ)*(sp_s1_9) + (383556201621/40000000000 : ℝ)*(sp_s1_12) + (8606021/500000000000 : ℝ)*(sp_s1_13) + (935361/125000000000 : ℝ)*(sp_s1_25) + (9588912523413/1000000000000 : ℝ)*(f.failure) + (12954045009043/500000000000 : ℝ)*(f.sum) + (9372307408781957463/21342508300000000000000000000000 : ℝ)*base63 + (865728413642633/1738650000000000000000000000 : ℝ)*base64 + (554273840918477/3682600000000000000000000000 : ℝ)*base66 + (89760025212997/144887500000000000000000000 : ℝ)*base69 + (7254585813115491959/10748334300000000000000000000000 : ℝ)*base70 + (67389069270629/148368000000000000000000000 : ℝ)*base73 + (10197950763857/73652000000000000000000000 : ℝ)*base75 + (331314060683933/927300000000000000000000000 : ℝ)*base76 + (1926744990962103377/68297499600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (2911/50000000000000000 : ℝ)*base87 + (2911/50000000000000000 : ℝ)*base89 + (2911/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25507/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25507/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (457243066911419503536708232301/32984846577650000000000000000000000 : ℝ) := by norm_num
    linear_combination (128289/8000000000 : ℝ)*(base21) + (5012387529429/500000000000 : ℝ)*(base59) + (5180601490351/1000000000000 : ℝ)*(base60) + (4436858995331/250000000000 : ℝ)*(major_s1_0) + (4436858995331/250000000000 : ℝ)*(major_s1_1) + (4436858995331/250000000000 : ℝ)*(major_s1_2) + (90581107/1000000000000 : ℝ)*(sp_s1_1) + (84149273/1000000000000 : ℝ)*(sp_s1_6) + (44224559/125000000000 : ℝ)*(sp_s1_8) + (25906530614983/1000000000000 : ℝ)*(sp_s1_13) + (5181217247481/200000000000 : ℝ)*(sp_s1_14) + (809571420781/31250000000 : ℝ)*(sp_s1_15) + (4794126288823/500000000000 : ℝ)*(sp_s1_18) + (229113867/1000000000000 : ℝ)*(sp_s1_21) + (9588336726919/1000000000000 : ℝ)*(f.failure) + (25906530614983/1000000000000 : ℝ)*(f.sum) + (3506275808476490029/10671254150000000000000000000000 : ℝ)*base62 + (1329618231654413/1738650000000000000000000000 : ℝ)*base65 + (995208111786081/1841300000000000000000000000 : ℝ)*base67 + (11481571219461/72443750000000000000000000 : ℝ)*base68 + (3206350181867473987/5374167150000000000000000000000 : ℝ)*base71 + (4287104074483/74184000000000000000000000 : ℝ)*base72 + (218002411779/9206500000000000000000000 : ℝ)*base74 + (27012888828499/463650000000000000000000000 : ℝ)*base77 + (2897397281083390291/34148749800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (27307/50000000000000000 : ℝ)*base86 + (27307/50000000000000000 : ℝ)*base88 + (27307/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(541/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(541/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (111431638804938981818422815079/10555150904848000000000000000000000 : ℝ) := by norm_num
    linear_combination (2276057/1000000000000 : ℝ)*(base40) + (568491/250000000000 : ℝ)*(base50) + (489249516463/500000000000 : ℝ)*(base59) + (3399691413497/1000000000000 : ℝ)*(major_s1_0) + (3399691413497/1000000000000 : ℝ)*(major_s1_1) + (3399691413497/1000000000000 : ℝ)*(major_s1_2) + (789987/1000000000000 : ℝ)*(sp_s1_1) + (5106959/200000000000 : ℝ)*(sp_s1_9) + (143080593/1000000000000 : ℝ)*(sp_s1_12) + (7311801/62500000000 : ℝ)*(sp_s1_15) + (4962641534993/1000000000000 : ℝ)*(sp_s1_19) + (2481320372503/500000000000 : ℝ)*(sp_s1_20) + (4962499011381/1000000000000 : ℝ)*(sp_s1_21) + (14692757539/8000000000 : ℝ)*(sp_s1_25) + (229592221621/125000000000 : ℝ)*(f.failure) + (4962641534993/1000000000000 : ℝ)*(f.sum) + (2961674898242542463/42685016600000000000000000000000 : ℝ)*base62 + (822443859707881/1738650000000000000000000000 : ℝ)*base64 + (1605401537440543/7365200000000000000000000000 : ℝ)*base66 + (252653122717/1131933593750000000000000 : ℝ)*base68 + (2242515239358042229/21496668600000000000000000000000 : ℝ)*base71 + (956353690626941/1483680000000000000000000000 : ℝ)*base72 + (24721752257167/147304000000000000000000000 : ℝ)*base75 + (1102753451963743/1854600000000000000000000000 : ℝ)*base77 + (48494240994620679083/136594999200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (2437/6250000000000000 : ℝ)*base87 + (2437/6250000000000000 : ℝ)*base89 + (2437/6250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((9273/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9273/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18413/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18413/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(34773/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(34773/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3193/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3193/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25507/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25507/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(541/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(541/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c319057_s1 p hpa hpb X hX hprev0

#print axioms solution
