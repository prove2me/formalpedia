-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305063_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:32:50.960435+00:00
-- url     : https://prove2.me/submissions/f94564a3-d8a7-4611-bd0c-e553ecee6e6d

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
theorem collision_support_c305063_s6_s6_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-65967623/400000000 : ℝ)*x 0 + (5452170089/10000000000 : ℝ)*x 1 + (5496585267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65967623/400000000 : ℝ)^67 ≤ (4684667377833/50000000000000 : ℝ)^51 := by
    have hnat : (65967623 : ℕ)^67*50000000000000^51 ≤ 4684667377833^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65967623 400000000 4684667377833 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452170089/10000000000 : ℝ)^67 ≤ (45073833952101/100000000000000 : ℝ)^51 := by
    have hnat : (5452170089 : ℕ)^67*100000000000000^51 ≤ 45073833952101^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452170089 10000000000 45073833952101 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496585267/10000000000 : ℝ)^67 ≤ (45556831271207/100000000000000 : ℝ)^51 := by
    have hnat : (5496585267 : ℕ)^67*100000000000000^51 ≤ 45556831271207^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496585267 10000000000 45556831271207 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65967623/400000000 : ℝ), (5452170089/10000000000 : ℝ), (5496585267/10000000000 : ℝ)] ![(4684667377833/50000000000000 : ℝ), (45073833952101/100000000000000 : ℝ), (45556831271207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65967623/400000000 : ℝ)|^67 ≤ (4684667377833/50000000000000 : ℝ)^51
        have hw : |(-65967623/400000000 : ℝ)|=(65967623/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452170089/10000000000 : ℝ)|^67 ≤ (45073833952101/100000000000000 : ℝ)^51
        have hw : |(5452170089/10000000000 : ℝ)|=(5452170089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496585267/10000000000 : ℝ)|^67 ≤ (45556831271207/100000000000000 : ℝ)^51
        have hw : |(5496585267/10000000000 : ℝ)|=(5496585267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5453606321/10000000000 : ℝ)*x 0 + (-207829841/1250000000 : ℝ)*x 1 + (274295977/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5453606321/10000000000 : ℝ)^67 ≤ (45089433150231/100000000000000 : ℝ)^51 := by
    have hnat : (5453606321 : ℕ)^67*100000000000000^51 ≤ 45089433150231^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453606321 10000000000 45089433150231 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207829841/1250000000 : ℝ)^67 ≤ (2367458298241/25000000000000 : ℝ)^51 := by
    have hnat : (207829841 : ℕ)^67*25000000000000^51 ≤ 2367458298241^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207829841 1250000000 2367458298241 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274295977/500000000 : ℝ)^67 ≤ (45440733639781/100000000000000 : ℝ)^51 := by
    have hnat : (274295977 : ℕ)^67*100000000000000^51 ≤ 45440733639781^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274295977 500000000 45440733639781 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5453606321/10000000000 : ℝ), (-207829841/1250000000 : ℝ), (274295977/500000000 : ℝ)] ![(45089433150231/100000000000000 : ℝ), (2367458298241/25000000000000 : ℝ), (45440733639781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5453606321/10000000000 : ℝ)|^67 ≤ (45089433150231/100000000000000 : ℝ)^51
        have hw : |(5453606321/10000000000 : ℝ)|=(5453606321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207829841/1250000000 : ℝ)|^67 ≤ (2367458298241/25000000000000 : ℝ)^51
        have hw : |(-207829841/1250000000 : ℝ)|=(207829841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274295977/500000000 : ℝ)|^67 ≤ (45440733639781/100000000000000 : ℝ)^51
        have hw : |(274295977/500000000 : ℝ)|=(274295977/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (685466959/1250000000 : ℝ)*x 0 + (684879903/1250000000 : ℝ)*x 1 + (-1628760371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685466959/1250000000 : ℝ)^67 ≤ (45416970720693/100000000000000 : ℝ)^51 := by
    have hnat : (685466959 : ℕ)^67*100000000000000^51 ≤ 45416970720693^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685466959 1250000000 45416970720693 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684879903/1250000000 : ℝ)^67 ≤ (567073477343/1250000000000 : ℝ)^51 := by
    have hnat : (684879903 : ℕ)^67*1250000000000^51 ≤ 567073477343^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684879903 1250000000 567073477343 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1628760371/10000000000 : ℝ)^67 ≤ (368686043013/4000000000000 : ℝ)^51 := by
    have hnat : (1628760371 : ℕ)^67*4000000000000^51 ≤ 368686043013^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1628760371 10000000000 368686043013 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685466959/1250000000 : ℝ), (684879903/1250000000 : ℝ), (-1628760371/10000000000 : ℝ)] ![(45416970720693/100000000000000 : ℝ), (567073477343/1250000000000 : ℝ), (368686043013/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685466959/1250000000 : ℝ)|^67 ≤ (45416970720693/100000000000000 : ℝ)^51
        have hw : |(685466959/1250000000 : ℝ)|=(685466959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684879903/1250000000 : ℝ)|^67 ≤ (567073477343/1250000000000 : ℝ)^51
        have hw : |(684879903/1250000000 : ℝ)|=(684879903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1628760371/10000000000 : ℝ)|^67 ≤ (368686043013/4000000000000 : ℝ)^51
        have hw : |(-1628760371/10000000000 : ℝ)|=(1628760371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4355504817/10000000000 : ℝ)*x 0 + (2170162997/5000000000 : ℝ)*x 1 + (4304000267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355504817/10000000000 : ℝ)^67 ≤ (2097373090651/6250000000000 : ℝ)^51 := by
    have hnat : (4355504817 : ℕ)^67*6250000000000^51 ≤ 2097373090651^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355504817 10000000000 2097373090651 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170162997/5000000000 : ℝ)^67 ≤ (1043887970693/3125000000000 : ℝ)^51 := by
    have hnat : (2170162997 : ℕ)^67*3125000000000^51 ≤ 1043887970693^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170162997 5000000000 1043887970693 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4304000267/10000000000 : ℝ)^67 ≤ (16518807740029/50000000000000 : ℝ)^51 := by
    have hnat : (4304000267 : ℕ)^67*50000000000000^51 ≤ 16518807740029^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304000267 10000000000 16518807740029 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355504817/10000000000 : ℝ), (2170162997/5000000000 : ℝ), (4304000267/10000000000 : ℝ)] ![(2097373090651/6250000000000 : ℝ), (1043887970693/3125000000000 : ℝ), (16518807740029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355504817/10000000000 : ℝ)|^67 ≤ (2097373090651/6250000000000 : ℝ)^51
        have hw : |(4355504817/10000000000 : ℝ)|=(4355504817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2170162997/5000000000 : ℝ)|^67 ≤ (1043887970693/3125000000000 : ℝ)^51
        have hw : |(2170162997/5000000000 : ℝ)|=(2170162997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4304000267/10000000000 : ℝ)|^67 ≤ (16518807740029/50000000000000 : ℝ)^51
        have hw : |(4304000267/10000000000 : ℝ)|=(4304000267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-371432233/2500000000 : ℝ)*x 0 + (1136778531/2500000000 : ℝ)*x 1 + (201864191/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (371432233/2500000000 : ℝ)^67 ≤ (8168755918333/100000000000000 : ℝ)^51 := by
    have hnat : (371432233 : ℕ)^67*100000000000000^51 ≤ 8168755918333^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371432233 2500000000 8168755918333 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136778531/2500000000 : ℝ)^67 ≤ (8877667519913/25000000000000 : ℝ)^51 := by
    have hnat : (1136778531 : ℕ)^67*25000000000000^51 ≤ 8877667519913^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136778531 2500000000 8877667519913 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201864191/312500000 : ℝ)^67 ≤ (28160286992369/50000000000000 : ℝ)^51 := by
    have hnat : (201864191 : ℕ)^67*50000000000000^51 ≤ 28160286992369^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201864191 312500000 28160286992369 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-371432233/2500000000 : ℝ), (1136778531/2500000000 : ℝ), (201864191/312500000 : ℝ)] ![(8168755918333/100000000000000 : ℝ), (8877667519913/25000000000000 : ℝ), (28160286992369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-371432233/2500000000 : ℝ)|^67 ≤ (8168755918333/100000000000000 : ℝ)^51
        have hw : |(-371432233/2500000000 : ℝ)|=(371432233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1136778531/2500000000 : ℝ)|^67 ≤ (8877667519913/25000000000000 : ℝ)^51
        have hw : |(1136778531/2500000000 : ℝ)|=(1136778531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201864191/312500000 : ℝ)|^67 ≤ (28160286992369/50000000000000 : ℝ)^51
        have hw : |(201864191/312500000 : ℝ)|=(201864191/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1248273003/2500000000 : ℝ)*x 0 + (-201094311/2500000000 : ℝ)*x 1 + (806105231/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1248273003/2500000000 : ℝ)^67 ≤ (40155072512797/100000000000000 : ℝ)^51 := by
    have hnat : (1248273003 : ℕ)^67*100000000000000^51 ≤ 40155072512797^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248273003 2500000000 40155072512797 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201094311/2500000000 : ℝ)^67 ≤ (3648166133861/100000000000000 : ℝ)^51 := by
    have hnat : (201094311 : ℕ)^67*100000000000000^51 ≤ 3648166133861^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201094311 2500000000 3648166133861 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806105231/1250000000 : ℝ)^67 ≤ (2809838067159/5000000000000 : ℝ)^51 := by
    have hnat : (806105231 : ℕ)^67*5000000000000^51 ≤ 2809838067159^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806105231 1250000000 2809838067159 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1248273003/2500000000 : ℝ), (-201094311/2500000000 : ℝ), (806105231/1250000000 : ℝ)] ![(40155072512797/100000000000000 : ℝ), (3648166133861/100000000000000 : ℝ), (2809838067159/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1248273003/2500000000 : ℝ)|^67 ≤ (40155072512797/100000000000000 : ℝ)^51
        have hw : |(1248273003/2500000000 : ℝ)|=(1248273003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201094311/2500000000 : ℝ)|^67 ≤ (3648166133861/100000000000000 : ℝ)^51
        have hw : |(-201094311/2500000000 : ℝ)|=(201094311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806105231/1250000000 : ℝ)|^67 ≤ (2809838067159/5000000000000 : ℝ)^51
        have hw : |(806105231/1250000000 : ℝ)|=(806105231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2389729663/5000000000 : ℝ)*x 0 + (6669606009/10000000000 : ℝ)*x 1 + (-94209923/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2389729663/5000000000 : ℝ)^67 ≤ (7582662272171/20000000000000 : ℝ)^51 := by
    have hnat : (2389729663 : ℕ)^67*20000000000000^51 ≤ 7582662272171^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2389729663 5000000000 7582662272171 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6669606009/10000000000 : ℝ)^67 ≤ (58737562810501/100000000000000 : ℝ)^51 := by
    have hnat : (6669606009 : ℕ)^67*100000000000000^51 ≤ 58737562810501^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6669606009 10000000000 58737562810501 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94209923/1250000000 : ℝ)^67 ≤ (1674562907403/50000000000000 : ℝ)^51 := by
    have hnat : (94209923 : ℕ)^67*50000000000000^51 ≤ 1674562907403^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94209923 1250000000 1674562907403 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2389729663/5000000000 : ℝ), (6669606009/10000000000 : ℝ), (-94209923/1250000000 : ℝ)] ![(7582662272171/20000000000000 : ℝ), (58737562810501/100000000000000 : ℝ), (1674562907403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2389729663/5000000000 : ℝ)|^67 ≤ (7582662272171/20000000000000 : ℝ)^51
        have hw : |(2389729663/5000000000 : ℝ)|=(2389729663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6669606009/10000000000 : ℝ)|^67 ≤ (58737562810501/100000000000000 : ℝ)^51
        have hw : |(6669606009/10000000000 : ℝ)|=(6669606009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94209923/1250000000 : ℝ)|^67 ≤ (1674562907403/50000000000000 : ℝ)^51
        have hw : |(-94209923/1250000000 : ℝ)|=(94209923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2239824497/5000000000 : ℝ)*x 0 + (5839450591/10000000000 : ℝ)*x 1 + (2461191563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2239824497/5000000000 : ℝ)^67 ≤ (2176257855351/6250000000000 : ℝ)^51 := by
    have hnat : (2239824497 : ℕ)^67*6250000000000^51 ≤ 2176257855351^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239824497 5000000000 2176257855351 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5839450591/10000000000 : ℝ)^67 ≤ (49326116641691/100000000000000 : ℝ)^51 := by
    have hnat : (5839450591 : ℕ)^67*100000000000000^51 ≤ 49326116641691^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5839450591 10000000000 49326116641691 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2461191563/10000000000 : ℝ)^67 ≤ (990859853859/6250000000000 : ℝ)^51 := by
    have hnat : (2461191563 : ℕ)^67*6250000000000^51 ≤ 990859853859^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2461191563 10000000000 990859853859 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2239824497/5000000000 : ℝ), (5839450591/10000000000 : ℝ), (2461191563/10000000000 : ℝ)] ![(2176257855351/6250000000000 : ℝ), (49326116641691/100000000000000 : ℝ), (990859853859/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2239824497/5000000000 : ℝ)|^67 ≤ (2176257855351/6250000000000 : ℝ)^51
        have hw : |(2239824497/5000000000 : ℝ)|=(2239824497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5839450591/10000000000 : ℝ)|^67 ≤ (49326116641691/100000000000000 : ℝ)^51
        have hw : |(5839450591/10000000000 : ℝ)|=(5839450591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2461191563/10000000000 : ℝ)|^67 ≤ (990859853859/6250000000000 : ℝ)^51
        have hw : |(2461191563/10000000000 : ℝ)|=(2461191563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-787036193/10000000000 : ℝ)*x 0 + (5003782869/10000000000 : ℝ)*x 1 + (1611991709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787036193/10000000000 : ℝ)^67 ≤ (3545194786469/100000000000000 : ℝ)^51 := by
    have hnat : (787036193 : ℕ)^67*100000000000000^51 ≤ 3545194786469^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787036193 10000000000 3545194786469 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5003782869/10000000000 : ℝ)^67 ≤ (20134030443573/50000000000000 : ℝ)^51 := by
    have hnat : (5003782869 : ℕ)^67*50000000000000^51 ≤ 20134030443573^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003782869 10000000000 20134030443573 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1611991709/2500000000 : ℝ)^67 ≤ (2247469772547/4000000000000 : ℝ)^51 := by
    have hnat : (1611991709 : ℕ)^67*4000000000000^51 ≤ 2247469772547^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1611991709 2500000000 2247469772547 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-787036193/10000000000 : ℝ), (5003782869/10000000000 : ℝ), (1611991709/2500000000 : ℝ)] ![(3545194786469/100000000000000 : ℝ), (20134030443573/50000000000000 : ℝ), (2247469772547/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-787036193/10000000000 : ℝ)|^67 ≤ (3545194786469/100000000000000 : ℝ)^51
        have hw : |(-787036193/10000000000 : ℝ)|=(787036193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5003782869/10000000000 : ℝ)|^67 ≤ (20134030443573/50000000000000 : ℝ)^51
        have hw : |(5003782869/10000000000 : ℝ)|=(5003782869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1611991709/2500000000 : ℝ)|^67 ≤ (2247469772547/4000000000000 : ℝ)^51
        have hw : |(1611991709/2500000000 : ℝ)|=(1611991709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4572406641/10000000000 : ℝ)*x 0 + (-742715711/5000000000 : ℝ)*x 1 + (6437155029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4572406641/10000000000 : ℝ)^67 ≤ (17885192821587/50000000000000 : ℝ)^51 := by
    have hnat : (4572406641 : ℕ)^67*50000000000000^51 ≤ 17885192821587^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572406641 10000000000 17885192821587 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (742715711/5000000000 : ℝ)^67 ≤ (8166607054527/100000000000000 : ℝ)^51 := by
    have hnat : (742715711 : ℕ)^67*100000000000000^51 ≤ 8166607054527^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742715711 5000000000 8166607054527 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6437155029/10000000000 : ℝ)^67 ≤ (28031503640733/50000000000000 : ℝ)^51 := by
    have hnat : (6437155029 : ℕ)^67*50000000000000^51 ≤ 28031503640733^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6437155029 10000000000 28031503640733 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4572406641/10000000000 : ℝ), (-742715711/5000000000 : ℝ), (6437155029/10000000000 : ℝ)] ![(17885192821587/50000000000000 : ℝ), (8166607054527/100000000000000 : ℝ), (28031503640733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4572406641/10000000000 : ℝ)|^67 ≤ (17885192821587/50000000000000 : ℝ)^51
        have hw : |(4572406641/10000000000 : ℝ)|=(4572406641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-742715711/5000000000 : ℝ)|^67 ≤ (8166607054527/100000000000000 : ℝ)^51
        have hw : |(-742715711/5000000000 : ℝ)|=(742715711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6437155029/10000000000 : ℝ)|^67 ≤ (28031503640733/50000000000000 : ℝ)^51
        have hw : |(6437155029/10000000000 : ℝ)|=(6437155029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6433978147/10000000000 : ℝ)*x 0 + (5030978009/10000000000 : ℝ)*x 1 + (-382683343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6433978147/10000000000 : ℝ)^67 ≤ (28013330729289/50000000000000 : ℝ)^51 := by
    have hnat : (6433978147 : ℕ)^67*50000000000000^51 ≤ 28013330729289^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6433978147 10000000000 28013330729289 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5030978009/10000000000 : ℝ)^67 ≤ (20277909581003/50000000000000 : ℝ)^51 := by
    have hnat : (5030978009 : ℕ)^67*50000000000000^51 ≤ 20277909581003^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030978009 10000000000 20277909581003 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (382683343/5000000000 : ℝ)^67 ≤ (1708759681189/50000000000000 : ℝ)^51 := by
    have hnat : (382683343 : ℕ)^67*50000000000000^51 ≤ 1708759681189^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382683343 5000000000 1708759681189 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6433978147/10000000000 : ℝ), (5030978009/10000000000 : ℝ), (-382683343/5000000000 : ℝ)] ![(28013330729289/50000000000000 : ℝ), (20277909581003/50000000000000 : ℝ), (1708759681189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6433978147/10000000000 : ℝ)|^67 ≤ (28013330729289/50000000000000 : ℝ)^51
        have hw : |(6433978147/10000000000 : ℝ)|=(6433978147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5030978009/10000000000 : ℝ)|^67 ≤ (20277909581003/50000000000000 : ℝ)^51
        have hw : |(5030978009/10000000000 : ℝ)|=(5030978009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-382683343/5000000000 : ℝ)|^67 ≤ (1708759681189/50000000000000 : ℝ)^51
        have hw : |(-382683343/5000000000 : ℝ)|=(382683343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1261627037/2000000000 : ℝ)*x 0 + (786658381/2000000000 : ℝ)*x 1 + (497050051/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1261627037/2000000000 : ℝ)^67 ≤ (27295737736081/50000000000000 : ℝ)^51 := by
    have hnat : (1261627037 : ℕ)^67*50000000000000^51 ≤ 27295737736081^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261627037 2000000000 27295737736081 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (786658381/2000000000 : ℝ)^67 ≤ (29350862081387/100000000000000 : ℝ)^51 := by
    have hnat : (786658381 : ℕ)^67*100000000000000^51 ≤ 29350862081387^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786658381 2000000000 29350862081387 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497050051/2000000000 : ℝ)^67 ≤ (16057662428759/100000000000000 : ℝ)^51 := by
    have hnat : (497050051 : ℕ)^67*100000000000000^51 ≤ 16057662428759^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497050051 2000000000 16057662428759 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1261627037/2000000000 : ℝ), (786658381/2000000000 : ℝ), (497050051/2000000000 : ℝ)] ![(27295737736081/50000000000000 : ℝ), (29350862081387/100000000000000 : ℝ), (16057662428759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1261627037/2000000000 : ℝ)|^67 ≤ (27295737736081/50000000000000 : ℝ)^51
        have hw : |(1261627037/2000000000 : ℝ)|=(1261627037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(786658381/2000000000 : ℝ)|^67 ≤ (29350862081387/100000000000000 : ℝ)^51
        have hw : |(786658381/2000000000 : ℝ)|=(786658381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(497050051/2000000000 : ℝ)|^67 ≤ (16057662428759/100000000000000 : ℝ)^51
        have hw : |(497050051/2000000000 : ℝ)|=(497050051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-728695123/10000000000 : ℝ)*x 0 + (6052466793/10000000000 : ℝ)*x 1 + (5453895007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (728695123/10000000000 : ℝ)^67 ≤ (1602018439179/50000000000000 : ℝ)^51 := by
    have hnat : (728695123 : ℕ)^67*50000000000000^51 ≤ 1602018439179^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728695123 10000000000 1602018439179 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6052466793/10000000000 : ℝ)^67 ≤ (10340678865611/20000000000000 : ℝ)^51 := by
    have hnat : (6052466793 : ℕ)^67*20000000000000^51 ≤ 10340678865611^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6052466793 10000000000 10340678865611 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453895007/10000000000 : ℝ)^67 ≤ (45092568781213/100000000000000 : ℝ)^51 := by
    have hnat : (5453895007 : ℕ)^67*100000000000000^51 ≤ 45092568781213^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453895007 10000000000 45092568781213 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-728695123/10000000000 : ℝ), (6052466793/10000000000 : ℝ), (5453895007/10000000000 : ℝ)] ![(1602018439179/50000000000000 : ℝ), (10340678865611/20000000000000 : ℝ), (45092568781213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-728695123/10000000000 : ℝ)|^67 ≤ (1602018439179/50000000000000 : ℝ)^51
        have hw : |(-728695123/10000000000 : ℝ)|=(728695123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6052466793/10000000000 : ℝ)|^67 ≤ (10340678865611/20000000000000 : ℝ)^51
        have hw : |(6052466793/10000000000 : ℝ)|=(6052466793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453895007/10000000000 : ℝ)|^67 ≤ (45092568781213/100000000000000 : ℝ)^51
        have hw : |(5453895007/10000000000 : ℝ)|=(5453895007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (807726647/1250000000 : ℝ)*x 0 + (-91042299/1250000000 : ℝ)*x 1 + (5021239559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (807726647/1250000000 : ℝ)^67 ≤ (14086326374897/25000000000000 : ℝ)^51 := by
    have hnat : (807726647 : ℕ)^67*25000000000000^51 ≤ 14086326374897^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807726647 1250000000 14086326374897 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91042299/1250000000 : ℝ)^67 ≤ (80049410509/2500000000000 : ℝ)^51 := by
    have hnat : (91042299 : ℕ)^67*2500000000000^51 ≤ 80049410509^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91042299 1250000000 80049410509 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5021239559/10000000000 : ℝ)^67 ≤ (40452718067153/100000000000000 : ℝ)^51 := by
    have hnat : (5021239559 : ℕ)^67*100000000000000^51 ≤ 40452718067153^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5021239559 10000000000 40452718067153 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(807726647/1250000000 : ℝ), (-91042299/1250000000 : ℝ), (5021239559/10000000000 : ℝ)] ![(14086326374897/25000000000000 : ℝ), (80049410509/2500000000000 : ℝ), (40452718067153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(807726647/1250000000 : ℝ)|^67 ≤ (14086326374897/25000000000000 : ℝ)^51
        have hw : |(807726647/1250000000 : ℝ)|=(807726647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91042299/1250000000 : ℝ)|^67 ≤ (80049410509/2500000000000 : ℝ)^51
        have hw : |(-91042299/1250000000 : ℝ)|=(91042299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5021239559/10000000000 : ℝ)|^67 ≤ (40452718067153/100000000000000 : ℝ)^51
        have hw : |(5021239559/10000000000 : ℝ)|=(5021239559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (70706597/156250000 : ℝ)*x 0 + (3250753251/5000000000 : ℝ)*x 1 + (-1450230827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70706597/156250000 : ℝ)^67 ≤ (441077987859/1250000000000 : ℝ)^51 := by
    have hnat : (70706597 : ℕ)^67*1250000000000^51 ≤ 441077987859^51*156250000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70706597 156250000 441077987859 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3250753251/5000000000 : ℝ)^67 ≤ (56800443548419/100000000000000 : ℝ)^51 := by
    have hnat : (3250753251 : ℕ)^67*100000000000000^51 ≤ 56800443548419^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3250753251 5000000000 56800443548419 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1450230827/10000000000 : ℝ)^67 ≤ (989164675923/12500000000000 : ℝ)^51 := by
    have hnat : (1450230827 : ℕ)^67*12500000000000^51 ≤ 989164675923^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1450230827 10000000000 989164675923 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(70706597/156250000 : ℝ), (3250753251/5000000000 : ℝ), (-1450230827/10000000000 : ℝ)] ![(441077987859/1250000000000 : ℝ), (56800443548419/100000000000000 : ℝ), (989164675923/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(70706597/156250000 : ℝ)|^67 ≤ (441077987859/1250000000000 : ℝ)^51
        have hw : |(70706597/156250000 : ℝ)|=(70706597/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3250753251/5000000000 : ℝ)|^67 ≤ (56800443548419/100000000000000 : ℝ)^51
        have hw : |(3250753251/5000000000 : ℝ)|=(3250753251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1450230827/10000000000 : ℝ)|^67 ≤ (989164675923/12500000000000 : ℝ)^51
        have hw : |(-1450230827/10000000000 : ℝ)|=(1450230827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s6_s6_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (129361301/200000000 : ℝ)*x 0 + (3243166083/10000000000 : ℝ)*x 1 + (75667187/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129361301/200000000 : ℝ)^67 ≤ (56416933705829/100000000000000 : ℝ)^51 := by
    have hnat : (129361301 : ℕ)^67*100000000000000^51 ≤ 56416933705829^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129361301 200000000 56416933705829 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3243166083/10000000000 : ℝ)^67 ≤ (2277968733283/10000000000000 : ℝ)^51 := by
    have hnat : (3243166083 : ℕ)^67*10000000000000^51 ≤ 2277968733283^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3243166083 10000000000 2277968733283 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75667187/250000000 : ℝ)^67 ≤ (10401689470621/50000000000000 : ℝ)^51 := by
    have hnat : (75667187 : ℕ)^67*50000000000000^51 ≤ 10401689470621^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75667187 250000000 10401689470621 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129361301/200000000 : ℝ), (3243166083/10000000000 : ℝ), (75667187/250000000 : ℝ)] ![(56416933705829/100000000000000 : ℝ), (2277968733283/10000000000000 : ℝ), (10401689470621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129361301/200000000 : ℝ)|^67 ≤ (56416933705829/100000000000000 : ℝ)^51
        have hw : |(129361301/200000000 : ℝ)|=(129361301/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3243166083/10000000000 : ℝ)|^67 ≤ (2277968733283/10000000000000 : ℝ)^51
        have hw : |(3243166083/10000000000 : ℝ)|=(3243166083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75667187/250000000 : ℝ)|^67 ≤ (10401689470621/50000000000000 : ℝ)^51
        have hw : |(75667187/250000000 : ℝ)|=(75667187/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305063_s6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((26183/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26183/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53271/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53271/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(50937/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(50937/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((19223/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19223/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9741/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9741/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7433/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7433/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (26183/50000 : ℝ) ^ (133/32 : ℝ) ≤ (1359343047203128687/20000000000000000000 : ℝ) := by
    have hpowers : (26183/50000 : ℝ)^133 ≤ (1359343047203128687/20000000000000000000 : ℝ)^32 := by
      have hnat : (26183 : ℕ)^133*20000000000000000000^32 ≤ 1359343047203128687^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26183 50000 1359343047203128687 20000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26183/50000 : ℝ)) (X := (1359343047203128687/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s6_corner0a : (21359343047203128687/20000000000000000000 : ℝ) ≤ (2539867618752007/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (21359343047203128687/20000000000000000000 : ℝ)^32 ≤ (2539867618752007/2500000000000000 : ℝ)^133 := by
      have hnat : (21359343047203128687 : ℕ)^32*2500000000000000^133 ≤ 2539867618752007^133*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21359343047203128687 20000000000000000000 2539867618752007 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2539867618752007/2500000000000000 : ℝ)) (X := (21359343047203128687/20000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s6_corner0b : (11359343047203128687/10000000000000000000 : ℝ) ≤ (5155705134206029/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (11359343047203128687/10000000000000000000 : ℝ)^32 ≤ (5155705134206029/5000000000000000 : ℝ)^133 := by
      have hnat : (11359343047203128687 : ℕ)^32*5000000000000000^133 ≤ 5155705134206029^133*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11359343047203128687 10000000000000000000 5155705134206029 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5155705134206029/5000000000000000 : ℝ)) (X := (11359343047203128687/10000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(39867618752007/1309150000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(15193979340403/523660000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (26183/50000 : ℝ)) (alpha := (39867618752007/1309150000000000 : ℝ)) (beta := (15193979340403/523660000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (26183/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(39867618752007/1309150000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(15193979340403/523660000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (53271/100000 : ℝ) ^ (133/32 : ℝ) ≤ (2919359536240549/40000000000000000 : ℝ) := by
    have hpowers : (53271/100000 : ℝ)^133 ≤ (2919359536240549/40000000000000000 : ℝ)^32 := by
      have hnat : (53271 : ℕ)^133*40000000000000000^32 ≤ 2919359536240549^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53271 100000 2919359536240549 40000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (53271/100000 : ℝ)) (X := (2919359536240549/40000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s6_corner1a : (42919359536240549/40000000000000000 : ℝ) ≤ (5085466340763417/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (42919359536240549/40000000000000000 : ℝ)^32 ≤ (5085466340763417/5000000000000000 : ℝ)^133 := by
      have hnat : (42919359536240549 : ℕ)^32*5000000000000000^133 ≤ 5085466340763417^133*40000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42919359536240549 40000000000000000 5085466340763417 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5085466340763417/5000000000000000 : ℝ)) (X := (42919359536240549/40000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s6_corner1b : (22919359536240549/20000000000000000 : ℝ) ≤ (516662561114341/500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (22919359536240549/20000000000000000 : ℝ)^32 ≤ (516662561114341/500000000000000 : ℝ)^133 := by
      have hnat : (22919359536240549 : ℕ)^32*500000000000000^133 ≤ 516662561114341^133*20000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22919359536240549 20000000000000000 516662561114341 500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (516662561114341/500000000000000 : ℝ)) (X := (22919359536240549/20000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(85466340763417/2663550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(81159270379993/2663550000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (53271/100000 : ℝ)) (alpha := (85466340763417/2663550000000000 : ℝ)) (beta := (81159270379993/2663550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (53271/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(85466340763417/2663550000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(81159270379993/2663550000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (50937/100000 : ℝ) ^ (133/32 : ℝ) ≤ (6058392625475301501/100000000000000000000 : ℝ) := by
    have hpowers : (50937/100000 : ℝ)^133 ≤ (6058392625475301501/100000000000000000000 : ℝ)^32 := by
      have hnat : (50937 : ℕ)^133*100000000000000000000^32 ≤ 6058392625475301501^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50937 100000 6058392625475301501 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (50937/100000 : ℝ)) (X := (6058392625475301501/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s6_corner2a : (106058392625475301501/100000000000000000000 : ℝ) ≤ (10142527064182289/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (106058392625475301501/100000000000000000000 : ℝ)^32 ≤ (10142527064182289/10000000000000000 : ℝ)^133 := by
      have hnat : (106058392625475301501 : ℕ)^32*10000000000000000^133 ≤ 10142527064182289^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106058392625475301501 100000000000000000000 10142527064182289 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10142527064182289/10000000000000000 : ℝ)) (X := (106058392625475301501/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s6_corner2b : (56058392625475301501/50000000000000000000 : ℝ) ≤ (5139499571727291/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (56058392625475301501/50000000000000000000 : ℝ)^32 ≤ (5139499571727291/5000000000000000 : ℝ)^133 := by
      have hnat : (56058392625475301501 : ℕ)^32*5000000000000000^133 ≤ 5139499571727291^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56058392625475301501 50000000000000000000 5139499571727291 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5139499571727291/5000000000000000 : ℝ)) (X := (56058392625475301501/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(142527064182289/5093700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(136472079272293/5093700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (50937/100000 : ℝ)) (alpha := (142527064182289/5093700000000000 : ℝ)) (beta := (136472079272293/5093700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (50937/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(142527064182289/5093700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(136472079272293/5093700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-65967623/400000000 : ℝ)*X 0 0+(5452170089/10000000000 : ℝ)*X 0 1+(5496585267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((5453606321/10000000000 : ℝ)*X 1 0+(-207829841/1250000000 : ℝ)*X 1 1+(274295977/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((685466959/1250000000 : ℝ)*X 2 0+(684879903/1250000000 : ℝ)*X 2 1+(-1628760371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((4355504817/10000000000 : ℝ)*X 0 0+(2170162997/5000000000 : ℝ)*X 0 1+(4304000267/10000000000 : ℝ)*X 0 2+(4355504817/10000000000 : ℝ)*X 1 0+(2170162997/5000000000 : ℝ)*X 1 1+(4304000267/10000000000 : ℝ)*X 1 2+(4355504817/10000000000 : ℝ)*X 2 0+(2170162997/5000000000 : ℝ)*X 2 1+(4304000267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-371432233/2500000000 : ℝ)*X 0 0+(1136778531/2500000000 : ℝ)*X 0 1+(201864191/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((1248273003/2500000000 : ℝ)*X 1 0+(-201094311/2500000000 : ℝ)*X 1 1+(806105231/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((2389729663/5000000000 : ℝ)*X 2 0+(6669606009/10000000000 : ℝ)*X 2 1+(-94209923/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((2239824497/5000000000 : ℝ)*X 0 0+(5839450591/10000000000 : ℝ)*X 0 1+(2461191563/10000000000 : ℝ)*X 0 2+(2239824497/5000000000 : ℝ)*X 1 0+(5839450591/10000000000 : ℝ)*X 1 1+(2461191563/10000000000 : ℝ)*X 1 2+(2239824497/5000000000 : ℝ)*X 2 0+(5839450591/10000000000 : ℝ)*X 2 1+(2461191563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-787036193/10000000000 : ℝ)*X 0 0+(5003782869/10000000000 : ℝ)*X 0 1+(1611991709/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((4572406641/10000000000 : ℝ)*X 1 0+(-742715711/5000000000 : ℝ)*X 1 1+(6437155029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((6433978147/10000000000 : ℝ)*X 2 0+(5030978009/10000000000 : ℝ)*X 2 1+(-382683343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((1261627037/2000000000 : ℝ)*X 0 0+(786658381/2000000000 : ℝ)*X 0 1+(497050051/2000000000 : ℝ)*X 0 2+(1261627037/2000000000 : ℝ)*X 1 0+(786658381/2000000000 : ℝ)*X 1 1+(497050051/2000000000 : ℝ)*X 1 2+(1261627037/2000000000 : ℝ)*X 2 0+(786658381/2000000000 : ℝ)*X 2 1+(497050051/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-728695123/10000000000 : ℝ)*X 0 0+(6052466793/10000000000 : ℝ)*X 0 1+(5453895007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((807726647/1250000000 : ℝ)*X 1 0+(-91042299/1250000000 : ℝ)*X 1 1+(5021239559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((70706597/156250000 : ℝ)*X 2 0+(3250753251/5000000000 : ℝ)*X 2 1+(-1450230827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((129361301/200000000 : ℝ)*X 0 0+(3243166083/10000000000 : ℝ)*X 0 1+(75667187/250000000 : ℝ)*X 0 2+(129361301/200000000 : ℝ)*X 1 0+(3243166083/10000000000 : ℝ)*X 1 1+(75667187/250000000 : ℝ)*X 1 2+(129361301/200000000 : ℝ)*X 2 0+(3243166083/10000000000 : ℝ)*X 2 1+(75667187/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((19223/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19223/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25766135571186999349579657/3768701287500000000000000000000 : ℝ) := by norm_num
    linear_combination (43971/50000000000 : ℝ)*(base50) + (65942305569/500000000000 : ℝ)*(base60) + (1003277986273/250000000000 : ℝ)*(major_s6_0) + (1003277986273/250000000000 : ℝ)*(major_s6_1) + (1003277986273/250000000000 : ℝ)*(major_s6_2) + (2439883/200000000000 : ℝ)*(sp_s6_0) + (2305653/250000000000 : ℝ)*(sp_s6_6) + (2701003964767/500000000000 : ℝ)*(sp_s6_7) + (1350499547539/250000000000 : ℝ)*(sp_s6_8) + (270099836267/50000000000 : ℝ)*(sp_s6_9) + (328021833897/125000000000 : ℝ)*(sp_s6_13) + (3517697/200000000000 : ℝ)*(sp_s6_14) + (39527277/1000000000000 : ℝ)*(sp_s6_15) + (40992093/1000000000000 : ℝ)*(sp_s6_23) + (656045973447/250000000000 : ℝ)*(f.failure) + (5402037717433/1000000000000 : ℝ)*(f.sum) + (771236271761435867/5653051931250000000000000000000 : ℝ)*base62 + (801675299464811/1273425000000000000000000000 : ℝ)*base64 + (2308286418851219/2663550000000000000000000000 : ℝ)*base66 + (1471917088893451/2546850000000000000000000000 : ℝ)*base68 + (5565773216826805093/16671043387500000000000000000000 : ℝ)*base71 + (93906622327741/261830000000000000000000000 : ℝ)*base72 + (38086021544203/83235937500000000000000000 : ℝ)*base74 + (232039790826353/654575000000000000000000000 : ℝ)*base76 + (13710379530618382373/69739729650000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (11/97656250000000 : ℝ)*base87 + (11/97656250000000 : ℝ)*base89 + (11/97656250000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9741/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9741/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (647458137538031725509754170241/39470362324245000000000000000000000 : ℝ) := by norm_num
    linear_combination (2847443/1000000000000 : ℝ)*(base39) + (353827/125000000000 : ℝ)*(base49) + (1180389/500000000000 : ℝ)*(base60) + (405714649297/100000000000 : ℝ)*(major_s6_0) + (405714649297/100000000000 : ℝ)*(major_s6_1) + (405714649297/100000000000 : ℝ)*(major_s6_2) + (12185533/1000000000000 : ℝ)*(sp_s6_2) + (4982809/125000000000 : ℝ)*(sp_s6_7) + (35596513/500000000000 : ℝ)*(sp_s6_8) + (2730634730641/500000000000 : ℝ)*(sp_s6_14) + (682654766341/125000000000 : ℝ)*(sp_s6_15) + (5461297138221/1000000000000 : ℝ)*(sp_s6_16) + (530572400953/200000000000 : ℝ)*(sp_s6_20) + (11618953/100000000000 : ℝ)*(sp_s6_27) + (1326489097147/500000000000 : ℝ)*(f.failure) + (2730654661877/500000000000 : ℝ)*(f.sum) + (1082305682632291729/1130610386250000000000000000000 : ℝ)*base62 + (4230705419527/63671250000000000000000000 : ℝ)*base64 + (479016332155819/532710000000000000000000000 : ℝ)*base66 + (77471226338389/63671250000000000000000000 : ℝ)*base68 + (642033465292736321/3334208677500000000000000000000 : ℝ)*base71 + (144733437079/209464000000000000000000 : ℝ)*base72 + (1686994761307/2130840000000000000000000 : ℝ)*base74 + (14265229542321/26183000000000000000000000 : ℝ)*base76 + (12030229922056667327/13947945930000000000000000000000 : ℝ)*base78 + (7/97656250000000 : ℝ)*base86 + (7/97656250000000 : ℝ)*base88 + (7/97656250000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7433/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7433/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (147858937131171054647518067/11623288275000000000000000000000 : ℝ) := by norm_num
    linear_combination (1274789/125000000000 : ℝ)*(base15) + (107226882119/500000000000 : ℝ)*(base40) + (944148823939/250000000000 : ℝ)*(major_s6_0) + (944148823939/250000000000 : ℝ)*(major_s6_1) + (944148823939/250000000000 : ℝ)*(major_s6_2) + (30015823/500000000000 : ℝ)*(sp_s6_0) + (57044203/1000000000000 : ℝ)*(sp_s6_1) + (10120543/500000000000 : ℝ)*(sp_s6_2) + (44184929/1000000000000 : ℝ)*(sp_s6_9) + (20189767/250000000000 : ℝ)*(sp_s6_20) + (5083601251707/1000000000000 : ℝ)*(sp_s6_21) + (5083594040839/1000000000000 : ℝ)*(sp_s6_22) + (2541798428669/500000000000 : ℝ)*(sp_s6_23) + (1234722154389/500000000000 : ℝ)*(sp_s6_27) + (1234762533923/500000000000 : ℝ)*(f.failure) + (5083661283353/1000000000000 : ℝ)*(f.sum) + (10844234246648418797/45224415450000000000000000000000 : ℝ)*base63 + (547938059925839/2546850000000000000000000000 : ℝ)*base65 + (446270753468803/2663550000000000000000000000 : ℝ)*base67 + (924338534985553/2546850000000000000000000000 : ℝ)*base68 + (2280156494370817603/8335521693750000000000000000000 : ℝ)*base70 + (58688436161451/261830000000000000000000000 : ℝ)*base73 + (409727538272801/1331775000000000000000000000 : ℝ)*base75 + (328180214867433/1309150000000000000000000000 : ℝ)*base76 + (16149052350513400027/34869864825000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (733/1562500000000000 : ℝ)*base86 + (733/1562500000000000 : ℝ)*base88 + (733/1562500000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((26183/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26183/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53271/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53271/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(50937/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(50937/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((19223/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19223/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9741/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9741/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7433/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7433/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305063_s6 p hpa hpb X hX hprev5

#print axioms solution
