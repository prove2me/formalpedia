-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306055_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:56:11.865276+00:00
-- url     : https://prove2.me/submissions/8f53609c-a513-4674-bb82-7d4df8464198

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
theorem collision_support_c306055_s4_s4_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1844804181/10000000000 : ℝ)*x 0 + (732314257/1250000000 : ℝ)*x 1 + (122999743/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1844804181/10000000000 : ℝ)^135 ≤ (5455894889357/50000000000000 : ℝ)^103 := by
    have hnat : (1844804181 : ℕ)^135*50000000000000^103 ≤ 5455894889357^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844804181 10000000000 5455894889357 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (732314257/1250000000 : ℝ)^135 ≤ (9923703391167/20000000000000 : ℝ)^103 := by
    have hnat : (732314257 : ℕ)^135*20000000000000^103 ≤ 9923703391167^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732314257 1250000000 9923703391167 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122999743/250000000 : ℝ)^135 ≤ (39469693250577/100000000000000 : ℝ)^103 := by
    have hnat : (122999743 : ℕ)^135*100000000000000^103 ≤ 39469693250577^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122999743 250000000 39469693250577 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1844804181/10000000000 : ℝ), (732314257/1250000000 : ℝ), (122999743/250000000 : ℝ)] ![(5455894889357/50000000000000 : ℝ), (9923703391167/20000000000000 : ℝ), (39469693250577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1844804181/10000000000 : ℝ)|^135 ≤ (5455894889357/50000000000000 : ℝ)^103
        have hw : |(-1844804181/10000000000 : ℝ)|=(1844804181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(732314257/1250000000 : ℝ)|^135 ≤ (9923703391167/20000000000000 : ℝ)^103
        have hw : |(732314257/1250000000 : ℝ)|=(732314257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(122999743/250000000 : ℝ)|^135 ≤ (39469693250577/100000000000000 : ℝ)^103
        have hw : |(122999743/250000000 : ℝ)|=(122999743/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2436042541/5000000000 : ℝ)*x 0 + (-103536099/1250000000 : ℝ)*x 1 + (204092901/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2436042541/5000000000 : ℝ)^135 ≤ (38966754827651/100000000000000 : ℝ)^103 := by
    have hnat : (2436042541 : ℕ)^135*100000000000000^103 ≤ 38966754827651^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436042541 5000000000 38966754827651 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103536099/1250000000 : ℝ)^135 ≤ (1910086020457/50000000000000 : ℝ)^103 := by
    have hnat : (103536099 : ℕ)^135*50000000000000^103 ≤ 1910086020457^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103536099 1250000000 1910086020457 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204092901/312500000 : ℝ)^135 ≤ (28606536558187/50000000000000 : ℝ)^103 := by
    have hnat : (204092901 : ℕ)^135*50000000000000^103 ≤ 28606536558187^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204092901 312500000 28606536558187 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2436042541/5000000000 : ℝ), (-103536099/1250000000 : ℝ), (204092901/312500000 : ℝ)] ![(38966754827651/100000000000000 : ℝ), (1910086020457/50000000000000 : ℝ), (28606536558187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2436042541/5000000000 : ℝ)|^135 ≤ (38966754827651/100000000000000 : ℝ)^103
        have hw : |(2436042541/5000000000 : ℝ)|=(2436042541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103536099/1250000000 : ℝ)|^135 ≤ (1910086020457/50000000000000 : ℝ)^103
        have hw : |(-103536099/1250000000 : ℝ)|=(103536099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(204092901/312500000 : ℝ)|^135 ≤ (28606536558187/50000000000000 : ℝ)^103
        have hw : |(204092901/312500000 : ℝ)|=(204092901/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-655052581/5000000000 : ℝ)*x 0 + (5006025179/10000000000 : ℝ)*x 1 + (6130189289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655052581/5000000000 : ℝ)^135 ≤ (6967406955287/100000000000000 : ℝ)^103 := by
    have hnat : (655052581 : ℕ)^135*100000000000000^103 ≤ 6967406955287^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655052581 5000000000 6967406955287 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5006025179/10000000000 : ℝ)^135 ≤ (40376776216239/100000000000000 : ℝ)^103 := by
    have hnat : (5006025179 : ℕ)^135*100000000000000^103 ≤ 40376776216239^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5006025179 10000000000 40376776216239 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6130189289/10000000000 : ℝ)^135 ≤ (26327908405709/50000000000000 : ℝ)^103 := by
    have hnat : (6130189289 : ℕ)^135*50000000000000^103 ≤ 26327908405709^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6130189289 10000000000 26327908405709 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-655052581/5000000000 : ℝ), (5006025179/10000000000 : ℝ), (6130189289/10000000000 : ℝ)] ![(6967406955287/100000000000000 : ℝ), (40376776216239/100000000000000 : ℝ), (26327908405709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-655052581/5000000000 : ℝ)|^135 ≤ (6967406955287/100000000000000 : ℝ)^103
        have hw : |(-655052581/5000000000 : ℝ)|=(655052581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5006025179/10000000000 : ℝ)|^135 ≤ (40376776216239/100000000000000 : ℝ)^103
        have hw : |(5006025179/10000000000 : ℝ)|=(5006025179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6130189289/10000000000 : ℝ)|^135 ≤ (26327908405709/50000000000000 : ℝ)^103
        have hw : |(6130189289/10000000000 : ℝ)|=(6130189289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4507493261/10000000000 : ℝ)*x 0 + (-30201/1000000000 : ℝ)*x 1 + (7182721377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4507493261/10000000000 : ℝ)^135 ≤ (35190041016647/100000000000000 : ℝ)^103 := by
    have hnat : (4507493261 : ℕ)^135*100000000000000^103 ≤ 35190041016647^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507493261 10000000000 35190041016647 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30201/1000000000 : ℝ)^135 ≤ (119057321/100000000000000 : ℝ)^103 := by
    have hnat : (30201 : ℕ)^135*100000000000000^103 ≤ 119057321^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30201 1000000000 119057321 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7182721377/10000000000 : ℝ)^135 ≤ (64809839920711/100000000000000 : ℝ)^103 := by
    have hnat : (7182721377 : ℕ)^135*100000000000000^103 ≤ 64809839920711^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7182721377 10000000000 64809839920711 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4507493261/10000000000 : ℝ), (-30201/1000000000 : ℝ), (7182721377/10000000000 : ℝ)] ![(35190041016647/100000000000000 : ℝ), (119057321/100000000000000 : ℝ), (64809839920711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4507493261/10000000000 : ℝ)|^135 ≤ (35190041016647/100000000000000 : ℝ)^103
        have hw : |(4507493261/10000000000 : ℝ)|=(4507493261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30201/1000000000 : ℝ)|^135 ≤ (119057321/100000000000000 : ℝ)^103
        have hw : |(-30201/1000000000 : ℝ)|=(30201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7182721377/10000000000 : ℝ)|^135 ≤ (64809839920711/100000000000000 : ℝ)^103
        have hw : |(7182721377/10000000000 : ℝ)|=(7182721377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (447249299/1000000000 : ℝ)*x 0 + (3455416773/5000000000 : ℝ)*x 1 + (-783912301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (447249299/1000000000 : ℝ)^135 ≤ (34832333935899/100000000000000 : ℝ)^103 := by
    have hnat : (447249299 : ℕ)^135*100000000000000^103 ≤ 34832333935899^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447249299 1000000000 34832333935899 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3455416773/5000000000 : ℝ)^135 ≤ (30806745030153/50000000000000 : ℝ)^103 := by
    have hnat : (3455416773 : ℕ)^135*50000000000000^103 ≤ 30806745030153^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3455416773 5000000000 30806745030153 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (783912301/10000000000 : ℝ)^135 ≤ (1777087997309/50000000000000 : ℝ)^103 := by
    have hnat : (783912301 : ℕ)^135*50000000000000^103 ≤ 1777087997309^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783912301 10000000000 1777087997309 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(447249299/1000000000 : ℝ), (3455416773/5000000000 : ℝ), (-783912301/10000000000 : ℝ)] ![(34832333935899/100000000000000 : ℝ), (30806745030153/50000000000000 : ℝ), (1777087997309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(447249299/1000000000 : ℝ)|^135 ≤ (34832333935899/100000000000000 : ℝ)^103
        have hw : |(447249299/1000000000 : ℝ)|=(447249299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3455416773/5000000000 : ℝ)|^135 ≤ (30806745030153/50000000000000 : ℝ)^103
        have hw : |(3455416773/5000000000 : ℝ)|=(3455416773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-783912301/10000000000 : ℝ)|^135 ≤ (1777087997309/50000000000000 : ℝ)^103
        have hw : |(-783912301/10000000000 : ℝ)|=(783912301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5035866059/10000000000 : ℝ)*x 0 + (6005173531/10000000000 : ℝ)*x 1 + (731683323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5035866059/10000000000 : ℝ)^135 ≤ (40692529731297/100000000000000 : ℝ)^103 := by
    have hnat : (5035866059 : ℕ)^135*100000000000000^103 ≤ 40692529731297^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5035866059 10000000000 40692529731297 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6005173531/10000000000 : ℝ)^135 ≤ (25626421998971/50000000000000 : ℝ)^103 := by
    have hnat : (6005173531 : ℕ)^135*50000000000000^103 ≤ 25626421998971^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6005173531 10000000000 25626421998971 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (731683323/5000000000 : ℝ)^135 ≤ (805462625711/10000000000000 : ℝ)^103 := by
    have hnat : (731683323 : ℕ)^135*10000000000000^103 ≤ 805462625711^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731683323 5000000000 805462625711 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5035866059/10000000000 : ℝ), (6005173531/10000000000 : ℝ), (731683323/5000000000 : ℝ)] ![(40692529731297/100000000000000 : ℝ), (25626421998971/50000000000000 : ℝ), (805462625711/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5035866059/10000000000 : ℝ)|^135 ≤ (40692529731297/100000000000000 : ℝ)^103
        have hw : |(5035866059/10000000000 : ℝ)|=(5035866059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6005173531/10000000000 : ℝ)|^135 ≤ (25626421998971/50000000000000 : ℝ)^103
        have hw : |(6005173531/10000000000 : ℝ)|=(6005173531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(731683323/5000000000 : ℝ)|^135 ≤ (805462625711/10000000000000 : ℝ)^103
        have hw : |(731683323/5000000000 : ℝ)|=(731683323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-101621357/2000000000 : ℝ)*x 0 + (5186665487/10000000000 : ℝ)*x 1 + (6397865919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101621357/2000000000 : ℝ)^135 ≤ (2013360734141/100000000000000 : ℝ)^103 := by
    have hnat : (101621357 : ℕ)^135*100000000000000^103 ≤ 2013360734141^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101621357 2000000000 2013360734141 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186665487/10000000000 : ℝ)^135 ≤ (42297025591411/100000000000000 : ℝ)^103 := by
    have hnat : (5186665487 : ℕ)^135*100000000000000^103 ≤ 42297025591411^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186665487 10000000000 42297025591411 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6397865919/10000000000 : ℝ)^135 ≤ (55689613670053/100000000000000 : ℝ)^103 := by
    have hnat : (6397865919 : ℕ)^135*100000000000000^103 ≤ 55689613670053^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6397865919 10000000000 55689613670053 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-101621357/2000000000 : ℝ), (5186665487/10000000000 : ℝ), (6397865919/10000000000 : ℝ)] ![(2013360734141/100000000000000 : ℝ), (42297025591411/100000000000000 : ℝ), (55689613670053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-101621357/2000000000 : ℝ)|^135 ≤ (2013360734141/100000000000000 : ℝ)^103
        have hw : |(-101621357/2000000000 : ℝ)|=(101621357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186665487/10000000000 : ℝ)|^135 ≤ (42297025591411/100000000000000 : ℝ)^103
        have hw : |(5186665487/10000000000 : ℝ)|=(5186665487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6397865919/10000000000 : ℝ)|^135 ≤ (55689613670053/100000000000000 : ℝ)^103
        have hw : |(6397865919/10000000000 : ℝ)|=(6397865919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2079151413/5000000000 : ℝ)*x 0 + (-382344961/10000000000 : ℝ)*x 1 + (3681592223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079151413/5000000000 : ℝ)^135 ≤ (31660744240903/100000000000000 : ℝ)^103 := by
    have hnat : (2079151413 : ℕ)^135*100000000000000^103 ≤ 31660744240903^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079151413 5000000000 31660744240903 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (382344961/10000000000 : ℝ)^135 ≤ (1386925573071/100000000000000 : ℝ)^103 := by
    have hnat : (382344961 : ℕ)^135*100000000000000^103 ≤ 1386925573071^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382344961 10000000000 1386925573071 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3681592223/5000000000 : ℝ)^135 ≤ (66952330169997/100000000000000 : ℝ)^103 := by
    have hnat : (3681592223 : ℕ)^135*100000000000000^103 ≤ 66952330169997^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3681592223 5000000000 66952330169997 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2079151413/5000000000 : ℝ), (-382344961/10000000000 : ℝ), (3681592223/5000000000 : ℝ)] ![(31660744240903/100000000000000 : ℝ), (1386925573071/100000000000000 : ℝ), (66952330169997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2079151413/5000000000 : ℝ)|^135 ≤ (31660744240903/100000000000000 : ℝ)^103
        have hw : |(2079151413/5000000000 : ℝ)|=(2079151413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-382344961/10000000000 : ℝ)|^135 ≤ (1386925573071/100000000000000 : ℝ)^103
        have hw : |(-382344961/10000000000 : ℝ)|=(382344961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3681592223/5000000000 : ℝ)|^135 ≤ (66952330169997/100000000000000 : ℝ)^103
        have hw : |(3681592223/5000000000 : ℝ)|=(3681592223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (395038621/625000000 : ℝ)*x 0 + (2632410673/5000000000 : ℝ)*x 1 + (-103247057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (395038621/625000000 : ℝ)^135 ≤ (54809973264467/100000000000000 : ℝ)^103 := by
    have hnat : (395038621 : ℕ)^135*100000000000000^103 ≤ 54809973264467^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395038621 625000000 54809973264467 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632410673/5000000000 : ℝ)^135 ≤ (4313434580059/10000000000000 : ℝ)^103 := by
    have hnat : (2632410673 : ℕ)^135*10000000000000^103 ≤ 4313434580059^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632410673 5000000000 4313434580059 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103247057/2000000000 : ℝ)^135 ≤ (1027840458497/50000000000000 : ℝ)^103 := by
    have hnat : (103247057 : ℕ)^135*50000000000000^103 ≤ 1027840458497^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103247057 2000000000 1027840458497 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(395038621/625000000 : ℝ), (2632410673/5000000000 : ℝ), (-103247057/2000000000 : ℝ)] ![(54809973264467/100000000000000 : ℝ), (4313434580059/10000000000000 : ℝ), (1027840458497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(395038621/625000000 : ℝ)|^135 ≤ (54809973264467/100000000000000 : ℝ)^103
        have hw : |(395038621/625000000 : ℝ)|=(395038621/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632410673/5000000000 : ℝ)|^135 ≤ (4313434580059/10000000000000 : ℝ)^103
        have hw : |(2632410673/5000000000 : ℝ)|=(2632410673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103247057/2000000000 : ℝ)|^135 ≤ (1027840458497/50000000000000 : ℝ)^103
        have hw : |(-103247057/2000000000 : ℝ)|=(103247057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (496456921/625000000 : ℝ)*x 0 + (2995016793/10000000000 : ℝ)*x 1 + (135916853/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (496456921/625000000 : ℝ)^135 ≤ (73949300995069/100000000000000 : ℝ)^103 := by
    have hnat : (496456921 : ℕ)^135*100000000000000^103 ≤ 73949300995069^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496456921 625000000 73949300995069 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2995016793/10000000000 : ℝ)^135 ≤ (20593358871069/100000000000000 : ℝ)^103 := by
    have hnat : (2995016793 : ℕ)^135*100000000000000^103 ≤ 20593358871069^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2995016793 10000000000 20593358871069 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135916853/1250000000 : ℝ)^135 ≤ (5457340113659/100000000000000 : ℝ)^103 := by
    have hnat : (135916853 : ℕ)^135*100000000000000^103 ≤ 5457340113659^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135916853 1250000000 5457340113659 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(496456921/625000000 : ℝ), (2995016793/10000000000 : ℝ), (135916853/1250000000 : ℝ)] ![(73949300995069/100000000000000 : ℝ), (20593358871069/100000000000000 : ℝ), (5457340113659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(496456921/625000000 : ℝ)|^135 ≤ (73949300995069/100000000000000 : ℝ)^103
        have hw : |(496456921/625000000 : ℝ)|=(496456921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2995016793/10000000000 : ℝ)|^135 ≤ (20593358871069/100000000000000 : ℝ)^103
        have hw : |(2995016793/10000000000 : ℝ)|=(2995016793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135916853/1250000000 : ℝ)|^135 ≤ (5457340113659/100000000000000 : ℝ)^103
        have hw : |(135916853/1250000000 : ℝ)|=(135916853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-348388099/5000000000 : ℝ)*x 0 + (3394590959/5000000000 : ℝ)*x 1 + (4659989791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (348388099/5000000000 : ℝ)^135 ≤ (3045551757349/100000000000000 : ℝ)^103 := by
    have hnat : (348388099 : ℕ)^135*100000000000000^103 ≤ 3045551757349^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348388099 5000000000 3045551757349 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3394590959/5000000000 : ℝ)^135 ≤ (60195850547047/100000000000000 : ℝ)^103 := by
    have hnat : (3394590959 : ℕ)^135*100000000000000^103 ≤ 60195850547047^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3394590959 5000000000 60195850547047 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4659989791/10000000000 : ℝ)^135 ≤ (36758597688181/100000000000000 : ℝ)^103 := by
    have hnat : (4659989791 : ℕ)^135*100000000000000^103 ≤ 36758597688181^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4659989791 10000000000 36758597688181 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-348388099/5000000000 : ℝ), (3394590959/5000000000 : ℝ), (4659989791/10000000000 : ℝ)] ![(3045551757349/100000000000000 : ℝ), (60195850547047/100000000000000 : ℝ), (36758597688181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-348388099/5000000000 : ℝ)|^135 ≤ (3045551757349/100000000000000 : ℝ)^103
        have hw : |(-348388099/5000000000 : ℝ)|=(348388099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3394590959/5000000000 : ℝ)|^135 ≤ (60195850547047/100000000000000 : ℝ)^103
        have hw : |(3394590959/5000000000 : ℝ)|=(3394590959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4659989791/10000000000 : ℝ)|^135 ≤ (36758597688181/100000000000000 : ℝ)^103
        have hw : |(4659989791/10000000000 : ℝ)|=(4659989791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6319251743/10000000000 : ℝ)*x 0 + (-9634823/5000000000 : ℝ)*x 1 + (681760063/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6319251743/10000000000 : ℝ)^135 ≤ (13698611507889/25000000000000 : ℝ)^103 := by
    have hnat : (6319251743 : ℕ)^135*25000000000000^103 ≤ 13698611507889^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6319251743 10000000000 13698611507889 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9634823/5000000000 : ℝ)^135 ≤ (27627358497/100000000000000 : ℝ)^103 := by
    have hnat : (9634823 : ℕ)^135*100000000000000^103 ≤ 27627358497^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9634823 5000000000 27627358497 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681760063/1250000000 : ℝ)^135 ≤ (22588963300961/50000000000000 : ℝ)^103 := by
    have hnat : (681760063 : ℕ)^135*50000000000000^103 ≤ 22588963300961^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681760063 1250000000 22588963300961 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6319251743/10000000000 : ℝ), (-9634823/5000000000 : ℝ), (681760063/1250000000 : ℝ)] ![(13698611507889/25000000000000 : ℝ), (27627358497/100000000000000 : ℝ), (22588963300961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6319251743/10000000000 : ℝ)|^135 ≤ (13698611507889/25000000000000 : ℝ)^103
        have hw : |(6319251743/10000000000 : ℝ)|=(6319251743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9634823/5000000000 : ℝ)|^135 ≤ (27627358497/100000000000000 : ℝ)^103
        have hw : |(-9634823/5000000000 : ℝ)|=(9634823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681760063/1250000000 : ℝ)|^135 ≤ (22588963300961/50000000000000 : ℝ)^103
        have hw : |(681760063/1250000000 : ℝ)|=(681760063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4024067999/10000000000 : ℝ)*x 0 + (1761305269/2500000000 : ℝ)*x 1 + (-1240091737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4024067999/10000000000 : ℝ)^135 ≤ (15163968985013/50000000000000 : ℝ)^103 := by
    have hnat : (4024067999 : ℕ)^135*50000000000000^103 ≤ 15163968985013^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024067999 10000000000 15163968985013 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1761305269/2500000000 : ℝ)^135 ≤ (63188578714779/100000000000000 : ℝ)^103 := by
    have hnat : (1761305269 : ℕ)^135*100000000000000^103 ≤ 63188578714779^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761305269 2500000000 63188578714779 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1240091737/10000000000 : ℝ)^135 ≤ (202608853159/3125000000000 : ℝ)^103 := by
    have hnat : (1240091737 : ℕ)^135*3125000000000^103 ≤ 202608853159^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240091737 10000000000 202608853159 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4024067999/10000000000 : ℝ), (1761305269/2500000000 : ℝ), (-1240091737/10000000000 : ℝ)] ![(15163968985013/50000000000000 : ℝ), (63188578714779/100000000000000 : ℝ), (202608853159/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4024067999/10000000000 : ℝ)|^135 ≤ (15163968985013/50000000000000 : ℝ)^103
        have hw : |(4024067999/10000000000 : ℝ)|=(4024067999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1761305269/2500000000 : ℝ)|^135 ≤ (63188578714779/100000000000000 : ℝ)^103
        have hw : |(1761305269/2500000000 : ℝ)|=(1761305269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1240091737/10000000000 : ℝ)|^135 ≤ (202608853159/3125000000000 : ℝ)^103
        have hw : |(-1240091737/10000000000 : ℝ)|=(1240091737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s4_s4_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (485346561/625000000 : ℝ)*x 0 + (605026529/2500000000 : ℝ)*x 1 + (2063551839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (485346561/625000000 : ℝ)^135 ≤ (35893896358143/50000000000000 : ℝ)^103 := by
    have hnat : (485346561 : ℕ)^135*50000000000000^103 ≤ 35893896358143^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485346561 625000000 35893896358143 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605026529/2500000000 : ℝ)^135 ≤ (3893537226681/25000000000000 : ℝ)^103 := by
    have hnat : (605026529 : ℕ)^135*25000000000000^103 ≤ 3893537226681^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605026529 2500000000 3893537226681 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063551839/10000000000 : ℝ)^135 ≤ (12638058369543/100000000000000 : ℝ)^103 := by
    have hnat : (2063551839 : ℕ)^135*100000000000000^103 ≤ 12638058369543^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063551839 10000000000 12638058369543 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(485346561/625000000 : ℝ), (605026529/2500000000 : ℝ), (2063551839/10000000000 : ℝ)] ![(35893896358143/50000000000000 : ℝ), (3893537226681/25000000000000 : ℝ), (12638058369543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(485346561/625000000 : ℝ)|^135 ≤ (35893896358143/50000000000000 : ℝ)^103
        have hw : |(485346561/625000000 : ℝ)|=(485346561/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605026529/2500000000 : ℝ)|^135 ≤ (3893537226681/25000000000000 : ℝ)^103
        have hw : |(605026529/2500000000 : ℝ)|=(605026529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2063551839/10000000000 : ℝ)|^135 ≤ (12638058369543/100000000000000 : ℝ)^103
        have hw : |(2063551839/10000000000 : ℝ)|=(2063551839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306055_s4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((35967/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35967/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35273/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35273/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72123/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72123/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((57271/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57271/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14381/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14381/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59467/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59467/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (35967/50000 : ℝ) ^ (67/16 : ℝ) ≤ (6292917170844752101/25000000000000000000 : ℝ) := by
    have hpowers : (35967/50000 : ℝ)^67 ≤ (6292917170844752101/25000000000000000000 : ℝ)^16 := by
      have hnat : (35967 : ℕ)^67*25000000000000000000^16 ≤ 6292917170844752101^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35967 50000 6292917170844752101 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35967/50000 : ℝ)) (X := (6292917170844752101/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (31292917170844752101/25000000000000000000 : ℝ) ≤ (2637697778715437/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (31292917170844752101/25000000000000000000 : ℝ)^16 ≤ (2637697778715437/2500000000000000 : ℝ)^67 := by
      have hnat : (31292917170844752101 : ℕ)^16*2500000000000000^67 ≤ 2637697778715437^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31292917170844752101 25000000000000000000 2637697778715437 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2637697778715437/2500000000000000 : ℝ)) (X := (31292917170844752101/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (18792917170844752101/12500000000000000000 : ℝ) ≤ (5511359814872767/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (18792917170844752101/12500000000000000000 : ℝ)^16 ≤ (5511359814872767/5000000000000000 : ℝ)^67 := by
      have hnat : (18792917170844752101 : ℕ)^16*5000000000000000^67 ≤ 5511359814872767^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18792917170844752101 12500000000000000000 5511359814872767 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5511359814872767/5000000000000000 : ℝ)) (X := (18792917170844752101/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(137697778715437/1798350000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(78654752480631/1198900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (35967/50000 : ℝ)) (alpha := (137697778715437/1798350000000000 : ℝ)) (beta := (78654752480631/1198900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (35967/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(137697778715437/1798350000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(78654752480631/1198900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (35273/50000 : ℝ) ^ (67/16 : ℝ) ≤ (23199474627260698207/100000000000000000000 : ℝ) := by
    have hpowers : (35273/50000 : ℝ)^67 ≤ (23199474627260698207/100000000000000000000 : ℝ)^16 := by
      have hnat : (35273 : ℕ)^67*100000000000000000000^16 ≤ 23199474627260698207^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35273 50000 23199474627260698207 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35273/50000 : ℝ)) (X := (23199474627260698207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (123199474627260698207/100000000000000000000 : ℝ) ≤ (2627713089260959/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (123199474627260698207/100000000000000000000 : ℝ)^16 ≤ (2627713089260959/2500000000000000 : ℝ)^67 := by
      have hnat : (123199474627260698207 : ℕ)^16*2500000000000000^67 ≤ 2627713089260959^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123199474627260698207 100000000000000000000 2627713089260959 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2627713089260959/2500000000000000 : ℝ)) (X := (123199474627260698207/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (73199474627260698207/50000000000000000000 : ℝ) ≤ (1095295877484197/1000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (73199474627260698207/50000000000000000000 : ℝ)^16 ≤ (1095295877484197/1000000000000000 : ℝ)^67 := by
      have hnat : (73199474627260698207 : ℕ)^16*1000000000000000^67 ≤ 1095295877484197^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73199474627260698207 50000000000000000000 1095295877484197 1000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1095295877484197/1000000000000000 : ℝ)) (X := (73199474627260698207/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(127713089260959/1763650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(221053208899067/3527300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (35273/50000 : ℝ)) (alpha := (127713089260959/1763650000000000 : ℝ)) (beta := (221053208899067/3527300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (35273/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(127713089260959/1763650000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(221053208899067/3527300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (72123/100000 : ℝ) ^ (67/16 : ℝ) ≤ (25449776166296177419/100000000000000000000 : ℝ) := by
    have hpowers : (72123/100000 : ℝ)^67 ≤ (25449776166296177419/100000000000000000000 : ℝ)^16 := by
      have hnat : (72123 : ℕ)^67*100000000000000000000^16 ≤ 25449776166296177419^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72123 100000 25449776166296177419 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72123/100000 : ℝ)) (X := (25449776166296177419/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (125449776166296177419/100000000000000000000 : ℝ) ≤ (2111276887613271/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (125449776166296177419/100000000000000000000 : ℝ)^16 ≤ (2111276887613271/2000000000000000 : ℝ)^67 := by
      have hnat : (125449776166296177419 : ℕ)^16*2000000000000000^67 ≤ 2111276887613271^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125449776166296177419 100000000000000000000 2111276887613271 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2111276887613271/2000000000000000 : ℝ)) (X := (125449776166296177419/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (75449776166296177419/50000000000000000000 : ℝ) ≤ (55162222274707/50000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (75449776166296177419/50000000000000000000 : ℝ)^16 ≤ (55162222274707/50000000000000 : ℝ)^67 := by
      have hnat : (75449776166296177419 : ℕ)^16*50000000000000^67 ≤ 55162222274707^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75449776166296177419 50000000000000000000 55162222274707 50000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (55162222274707/50000000000000 : ℝ)) (X := (75449776166296177419/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(111276887613271/1442460000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(95212003375009/1442460000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (72123/100000 : ℝ)) (alpha := (111276887613271/1442460000000000 : ℝ)) (beta := (95212003375009/1442460000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (72123/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(111276887613271/1442460000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(95212003375009/1442460000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-1844804181/10000000000 : ℝ)*X 0 0+(732314257/1250000000 : ℝ)*X 0 1+(122999743/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((2436042541/5000000000 : ℝ)*X 1 0+(-103536099/1250000000 : ℝ)*X 1 1+(204092901/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-655052581/5000000000 : ℝ)*X 0 0+(5006025179/10000000000 : ℝ)*X 0 1+(6130189289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((4507493261/10000000000 : ℝ)*X 1 0+(-30201/1000000000 : ℝ)*X 1 1+(7182721377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((447249299/1000000000 : ℝ)*X 2 0+(3455416773/5000000000 : ℝ)*X 2 1+(-783912301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((5035866059/10000000000 : ℝ)*X 0 0+(6005173531/10000000000 : ℝ)*X 0 1+(731683323/5000000000 : ℝ)*X 0 2+(5035866059/10000000000 : ℝ)*X 1 0+(6005173531/10000000000 : ℝ)*X 1 1+(731683323/5000000000 : ℝ)*X 1 2+(5035866059/10000000000 : ℝ)*X 2 0+(6005173531/10000000000 : ℝ)*X 2 1+(731683323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-101621357/2000000000 : ℝ)*X 0 0+(5186665487/10000000000 : ℝ)*X 0 1+(6397865919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((2079151413/5000000000 : ℝ)*X 1 0+(-382344961/10000000000 : ℝ)*X 1 1+(3681592223/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((395038621/625000000 : ℝ)*X 2 0+(2632410673/5000000000 : ℝ)*X 2 1+(-103247057/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((496456921/625000000 : ℝ)*X 0 0+(2995016793/10000000000 : ℝ)*X 0 1+(135916853/1250000000 : ℝ)*X 0 2+(496456921/625000000 : ℝ)*X 1 0+(2995016793/10000000000 : ℝ)*X 1 1+(135916853/1250000000 : ℝ)*X 1 2+(496456921/625000000 : ℝ)*X 2 0+(2995016793/10000000000 : ℝ)*X 2 1+(135916853/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-348388099/5000000000 : ℝ)*X 0 0+(3394590959/5000000000 : ℝ)*X 0 1+(4659989791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((6319251743/10000000000 : ℝ)*X 1 0+(-9634823/5000000000 : ℝ)*X 1 1+(681760063/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((4024067999/10000000000 : ℝ)*X 2 0+(1761305269/2500000000 : ℝ)*X 2 1+(-1240091737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((485346561/625000000 : ℝ)*X 0 0+(605026529/2500000000 : ℝ)*X 0 1+(2063551839/10000000000 : ℝ)*X 0 2+(485346561/625000000 : ℝ)*X 1 0+(605026529/2500000000 : ℝ)*X 1 1+(2063551839/10000000000 : ℝ)*X 1 2+(485346561/625000000 : ℝ)*X 2 0+(605026529/2500000000 : ℝ)*X 2 1+(2063551839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((57271/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57271/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (44219708720719307954247827853/3344292873643750000000000000000000 : ℝ) := by norm_num
    linear_combination (2790421/250000000000 : ℝ)*(base19) + (56587260989/1000000000000 : ℝ)*(base49) + (394617/1000000000000 : ℝ)*(base60) + (4050891282821/1000000000000 : ℝ)*(major_s4_0) + (4050891282821/1000000000000 : ℝ)*(major_s4_1) + (4050891282821/1000000000000 : ℝ)*(major_s4_2) + (6442833/500000000000 : ℝ)*(sp_s4_0) + (2737241055149/500000000000 : ℝ)*(sp_s4_7) + (5474457744403/1000000000000 : ℝ)*(sp_s4_8) + (2737191063391/500000000000 : ℝ)*(sp_s4_9) + (2627275681853/1000000000000 : ℝ)*(sp_s4_13) + (4196277/125000000000 : ℝ)*(sp_s4_15) + (3740169/500000000000 : ℝ)*(sp_s4_21) + (120349521/1000000000000 : ℝ)*(sp_s4_23) + (2627275681853/1000000000000 : ℝ)*(f.failure) + (5474502476303/1000000000000 : ℝ)*(f.sum) + (31061839742662045619/254399457900000000000000000000000 : ℝ)*base63 + (816931239602401/1442460000000000000000000000 : ℝ)*base64 + (1049617841688253/3527300000000000000000000000 : ℝ)*base67 + (35195346080861/288492000000000000000000000 : ℝ)*base68 + (973561890562414703/1516987100000000000000000000000 : ℝ)*base70 + (50455898834021/63100000000000000000000000 : ℝ)*base72 + (1233289045205551/1763650000000000000000000000 : ℝ)*base74 + (19173524959183/23662500000000000000000000 : ℝ)*base76 + (86304537329045123/222572630000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (43329/50000000000000000 : ℝ)*base87 + (43329/50000000000000000 : ℝ)*base89 + (43329/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14381/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14381/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (267561431818836743571391626863/31770782299615625000000000000000000 : ℝ) := by norm_num
    linear_combination (4032713/1000000000000 : ℝ)*(base13) + (4002473/1000000000000 : ℝ)*(base21) + (449367/500000000000 : ℝ)*(base39) + (7342202251/1000000000000 : ℝ)*(base49) + (420943790753/125000000000 : ℝ)*(major_s4_0) + (420943790753/125000000000 : ℝ)*(major_s4_1) + (420943790753/125000000000 : ℝ)*(major_s4_2) + (7774059/1000000000000 : ℝ)*(sp_s4_7) + (11151223/200000000000 : ℝ)*(sp_s4_8) + (4551002965651/1000000000000 : ℝ)*(sp_s4_14) + (4550959016309/1000000000000 : ℝ)*(sp_s4_15) + (91020215399/20000000000 : ℝ)*(sp_s4_16) + (2184043412403/1000000000000 : ℝ)*(sp_s4_20) + (7932001/200000000000 : ℝ)*(sp_s4_27) + (2184083072409/1000000000000 : ℝ)*(f.failure) + (568876846553/125000000000 : ℝ)*(f.sum) + (53852243133187707923/127199728950000000000000000000000 : ℝ)*base63 + (423560000953997/721230000000000000000000000 : ℝ)*base65 + (1821495720868941/1763650000000000000000000000 : ℝ)*base67 + (369851195098601/721230000000000000000000000 : ℝ)*base69 + (323798621007056207/1801422181250000000000000000000 : ℝ)*base71 + (1664805353743/9366406250000000000000000 : ℝ)*base73 + (282778850245987/220456250000000000000000000 : ℝ)*base75 + (835569214944223/1798350000000000000000000000 : ℝ)*base77 + (1612691771453529751/4228879970000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (27037/50000000000000000 : ℝ)*base87 + (27037/50000000000000000 : ℝ)*base89 + (27037/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59467/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59467/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (389397160234420972383/48082000000000000000000000 : ℝ) := by norm_num
    linear_combination (15840351003/100000000000 : ℝ)*(base7) + (19490430303/250000000000 : ℝ)*(base40) + (87217/500000000000 : ℝ)*(base59) + (33476836371/10000000000 : ℝ)*(major_s4_0) + (33476836371/10000000000 : ℝ)*(major_s4_1) + (33476836371/10000000000 : ℝ)*(major_s4_2) + (3498391/1000000000000 : ℝ)*(sp_s4_1) + (4132927/1000000000000 : ℝ)*(sp_s4_8) + (90044787/1000000000000 : ℝ)*(sp_s4_9) + (11163759/1000000000000 : ℝ)*(sp_s4_20) + (553244922399/125000000000 : ℝ)*(sp_s4_21) + (2212975873937/500000000000 : ℝ)*(sp_s4_22) + (1106467333601/250000000000 : ℝ)*(sp_s4_23) + (2329590533591/1000000000000 : ℝ)*(sp_s4_27) + (2171198187319/1000000000000 : ℝ)*(f.failure) + (553244922399/125000000000 : ℝ)*(f.sum) + (842014838202047151/4239990965000000000000000000000 : ℝ)*base62 + (58699638876009/240410000000000000000000000 : ℝ)*base64 + (91007175198971/352730000000000000000000000 : ℝ)*base66 + (107258090222721/240410000000000000000000000 : ℝ)*base68 + (665813433069745223/2882275490000000000000000000000 : ℝ)*base70 + (6073762708959/59945000000000000000000000 : ℝ)*base72 + (1443839681231/176365000000000000000000000 : ℝ)*base75 + (20269196185519/119890000000000000000000000 : ℝ)*base77 + (29931171222445789/422887997000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (16333/50000000000000000 : ℝ)*base86 + (16333/50000000000000000 : ℝ)*base88 + (16333/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((35967/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35967/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35273/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35273/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72123/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72123/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((57271/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57271/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14381/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14381/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59467/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59467/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306055_s4 p hpa hpb X hX hprev3

#print axioms solution
