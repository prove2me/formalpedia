-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313053_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:32:50.988709+00:00
-- url     : https://prove2.me/submissions/da4be5d9-7bd8-490c-afa8-d4e76f65acfe

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
theorem collision_support_c313053_s1_s1_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-340257189/2000000000 : ℝ)*x 0 + (104377061/200000000 : ℝ)*x 1 + (5435858791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340257189/2000000000 : ℝ)^37 ≤ (2087410906063/20000000000000 : ℝ)^29 := by
    have hnat : (340257189 : ℕ)^37*20000000000000^29 ≤ 2087410906063^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340257189 2000000000 2087410906063 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104377061/200000000 : ℝ)^37 ≤ (8723579797617/20000000000000 : ℝ)^29 := by
    have hnat : (104377061 : ℕ)^37*20000000000000^29 ≤ 8723579797617^29*200000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104377061 200000000 8723579797617 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435858791/10000000000 : ℝ)^37 ≤ (5743130808059/12500000000000 : ℝ)^29 := by
    have hnat : (5435858791 : ℕ)^37*12500000000000^29 ≤ 5743130808059^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435858791 10000000000 5743130808059 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-340257189/2000000000 : ℝ), (104377061/200000000 : ℝ), (5435858791/10000000000 : ℝ)] ![(2087410906063/20000000000000 : ℝ), (8723579797617/20000000000000 : ℝ), (5743130808059/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-340257189/2000000000 : ℝ)|^37 ≤ (2087410906063/20000000000000 : ℝ)^29
        have hw : |(-340257189/2000000000 : ℝ)|=(340257189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104377061/200000000 : ℝ)|^37 ≤ (8723579797617/20000000000000 : ℝ)^29
        have hw : |(104377061/200000000 : ℝ)|=(104377061/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435858791/10000000000 : ℝ)|^37 ≤ (5743130808059/12500000000000 : ℝ)^29
        have hw : |(5435858791/10000000000 : ℝ)|=(5435858791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4529304499/10000000000 : ℝ)*x 0 + (-511416281/5000000000 : ℝ)*x 1 + (81720071/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4529304499/10000000000 : ℝ)^37 ≤ (36403543675991/100000000000000 : ℝ)^29 := by
    have hnat : (4529304499 : ℕ)^37*100000000000000^29 ≤ 36403543675991^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529304499 10000000000 36403543675991 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (511416281/5000000000 : ℝ)^37 ≤ (545314666753/10000000000000 : ℝ)^29 := by
    have hnat : (511416281 : ℕ)^37*10000000000000^29 ≤ 545314666753^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511416281 5000000000 545314666753 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81720071/125000000 : ℝ)^37 ≤ (29071654820909/50000000000000 : ℝ)^29 := by
    have hnat : (81720071 : ℕ)^37*50000000000000^29 ≤ 29071654820909^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81720071 125000000 29071654820909 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4529304499/10000000000 : ℝ), (-511416281/5000000000 : ℝ), (81720071/125000000 : ℝ)] ![(36403543675991/100000000000000 : ℝ), (545314666753/10000000000000 : ℝ), (29071654820909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4529304499/10000000000 : ℝ)|^37 ≤ (36403543675991/100000000000000 : ℝ)^29
        have hw : |(4529304499/10000000000 : ℝ)|=(4529304499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-511416281/5000000000 : ℝ)|^37 ≤ (545314666753/10000000000000 : ℝ)^29
        have hw : |(-511416281/5000000000 : ℝ)|=(511416281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81720071/125000000 : ℝ)|^37 ≤ (29071654820909/50000000000000 : ℝ)^29
        have hw : |(81720071/125000000 : ℝ)|=(81720071/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2277324933/5000000000 : ℝ)*x 0 + (3280207373/5000000000 : ℝ)*x 1 + (-472854587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2277324933/5000000000 : ℝ)^37 ≤ (36663648903159/100000000000000 : ℝ)^29 := by
    have hnat : (2277324933 : ℕ)^37*100000000000000^29 ≤ 36663648903159^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277324933 5000000000 36663648903159 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3280207373/5000000000 : ℝ)^37 ≤ (29201125381337/50000000000000 : ℝ)^29 := by
    have hnat : (3280207373 : ℕ)^37*50000000000000^29 ≤ 29201125381337^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3280207373 5000000000 29201125381337 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472854587/5000000000 : ℝ)^37 ≤ (493410031609/10000000000000 : ℝ)^29 := by
    have hnat : (472854587 : ℕ)^37*10000000000000^29 ≤ 493410031609^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472854587 5000000000 493410031609 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2277324933/5000000000 : ℝ), (3280207373/5000000000 : ℝ), (-472854587/5000000000 : ℝ)] ![(36663648903159/100000000000000 : ℝ), (29201125381337/50000000000000 : ℝ), (493410031609/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2277324933/5000000000 : ℝ)|^37 ≤ (36663648903159/100000000000000 : ℝ)^29
        have hw : |(2277324933/5000000000 : ℝ)|=(2277324933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3280207373/5000000000 : ℝ)|^37 ≤ (29201125381337/50000000000000 : ℝ)^29
        have hw : |(3280207373/5000000000 : ℝ)|=(3280207373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-472854587/5000000000 : ℝ)|^37 ≤ (493410031609/10000000000000 : ℝ)^29
        have hw : |(-472854587/5000000000 : ℝ)|=(472854587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1852411781/10000000000 : ℝ)*x 0 + (918063313/2500000000 : ℝ)*x 1 + (1686322411/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1852411781/10000000000 : ℝ)^37 ≤ (2326826981873/20000000000000 : ℝ)^29 := by
    have hnat : (1852411781 : ℕ)^37*20000000000000^29 ≤ 2326826981873^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852411781 10000000000 2326826981873 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (918063313/2500000000 : ℝ)^37 ≤ (13927848752511/50000000000000 : ℝ)^29 := by
    have hnat : (918063313 : ℕ)^37*50000000000000^29 ≤ 13927848752511^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918063313 2500000000 13927848752511 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1686322411/2500000000 : ℝ)^37 ≤ (15127541894329/25000000000000 : ℝ)^29 := by
    have hnat : (1686322411 : ℕ)^37*25000000000000^29 ≤ 15127541894329^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686322411 2500000000 15127541894329 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1852411781/10000000000 : ℝ), (918063313/2500000000 : ℝ), (1686322411/2500000000 : ℝ)] ![(2326826981873/20000000000000 : ℝ), (13927848752511/50000000000000 : ℝ), (15127541894329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1852411781/10000000000 : ℝ)|^37 ≤ (2326826981873/20000000000000 : ℝ)^29
        have hw : |(-1852411781/10000000000 : ℝ)|=(1852411781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(918063313/2500000000 : ℝ)|^37 ≤ (13927848752511/50000000000000 : ℝ)^29
        have hw : |(918063313/2500000000 : ℝ)|=(918063313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1686322411/2500000000 : ℝ)|^37 ≤ (15127541894329/25000000000000 : ℝ)^29
        have hw : |(1686322411/2500000000 : ℝ)|=(1686322411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (657946667/2000000000 : ℝ)*x 0 + (-51772401/1250000000 : ℝ)*x 1 + (7903732259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657946667/2000000000 : ℝ)^37 ≤ (24208263956849/100000000000000 : ℝ)^29 := by
    have hnat : (657946667 : ℕ)^37*100000000000000^29 ≤ 24208263956849^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657946667 2000000000 24208263956849 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51772401/1250000000 : ℝ)^37 ≤ (430192667383/25000000000000 : ℝ)^29 := by
    have hnat : (51772401 : ℕ)^37*25000000000000^29 ≤ 430192667383^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51772401 1250000000 430192667383 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7903732259/10000000000 : ℝ)^37 ≤ (14814193072207/20000000000000 : ℝ)^29 := by
    have hnat : (7903732259 : ℕ)^37*20000000000000^29 ≤ 14814193072207^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7903732259 10000000000 14814193072207 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657946667/2000000000 : ℝ), (-51772401/1250000000 : ℝ), (7903732259/10000000000 : ℝ)] ![(24208263956849/100000000000000 : ℝ), (430192667383/25000000000000 : ℝ), (14814193072207/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657946667/2000000000 : ℝ)|^37 ≤ (24208263956849/100000000000000 : ℝ)^29
        have hw : |(657946667/2000000000 : ℝ)|=(657946667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51772401/1250000000 : ℝ)|^37 ≤ (430192667383/25000000000000 : ℝ)^29
        have hw : |(-51772401/1250000000 : ℝ)|=(51772401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7903732259/10000000000 : ℝ)|^37 ≤ (14814193072207/20000000000000 : ℝ)^29
        have hw : |(7903732259/10000000000 : ℝ)|=(7903732259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (165871767/500000000 : ℝ)*x 0 + (7958018733/10000000000 : ℝ)*x 1 + (-114803647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165871767/500000000 : ℝ)^37 ≤ (2446865197259/10000000000000 : ℝ)^29 := by
    have hnat : (165871767 : ℕ)^37*10000000000000^29 ≤ 2446865197259^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165871767 500000000 2446865197259 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7958018733/10000000000 : ℝ)^37 ≤ (74720678591151/100000000000000 : ℝ)^29 := by
    have hnat : (7958018733 : ℕ)^37*100000000000000^29 ≤ 74720678591151^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7958018733 10000000000 74720678591151 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114803647/5000000000 : ℝ)^37 ≤ (405334717557/50000000000000 : ℝ)^29 := by
    have hnat : (114803647 : ℕ)^37*50000000000000^29 ≤ 405334717557^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114803647 5000000000 405334717557 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165871767/500000000 : ℝ), (7958018733/10000000000 : ℝ), (-114803647/5000000000 : ℝ)] ![(2446865197259/10000000000000 : ℝ), (74720678591151/100000000000000 : ℝ), (405334717557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165871767/500000000 : ℝ)|^37 ≤ (2446865197259/10000000000000 : ℝ)^29
        have hw : |(165871767/500000000 : ℝ)|=(165871767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7958018733/10000000000 : ℝ)|^37 ≤ (74720678591151/100000000000000 : ℝ)^29
        have hw : |(7958018733/10000000000 : ℝ)|=(7958018733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114803647/5000000000 : ℝ)|^37 ≤ (405334717557/50000000000000 : ℝ)^29
        have hw : |(-114803647/5000000000 : ℝ)|=(114803647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5956549731/10000000000 : ℝ)*x 0 + (5507223631/10000000000 : ℝ)*x 1 + (401021341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5956549731/10000000000 : ℝ)^37 ≤ (6454080491063/12500000000000 : ℝ)^29 := by
    have hnat : (5956549731 : ℕ)^37*12500000000000^29 ≤ 6454080491063^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5956549731 10000000000 6454080491063 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5507223631/10000000000 : ℝ)^37 ≤ (46716024136237/100000000000000 : ℝ)^29 := by
    have hnat : (5507223631 : ℕ)^37*100000000000000^29 ≤ 46716024136237^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507223631 10000000000 46716024136237 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401021341/10000000000 : ℝ)^37 ≤ (412832981409/25000000000000 : ℝ)^29 := by
    have hnat : (401021341 : ℕ)^37*25000000000000^29 ≤ 412832981409^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401021341 10000000000 412832981409 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5956549731/10000000000 : ℝ), (5507223631/10000000000 : ℝ), (401021341/10000000000 : ℝ)] ![(6454080491063/12500000000000 : ℝ), (46716024136237/100000000000000 : ℝ), (412832981409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5956549731/10000000000 : ℝ)|^37 ≤ (6454080491063/12500000000000 : ℝ)^29
        have hw : |(5956549731/10000000000 : ℝ)|=(5956549731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5507223631/10000000000 : ℝ)|^37 ≤ (46716024136237/100000000000000 : ℝ)^29
        have hw : |(5507223631/10000000000 : ℝ)|=(5507223631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(401021341/10000000000 : ℝ)|^37 ≤ (412832981409/25000000000000 : ℝ)^29
        have hw : |(401021341/10000000000 : ℝ)|=(401021341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-142139157/1250000000 : ℝ)*x 0 + (3699423687/10000000000 : ℝ)*x 1 + (3594711379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (142139157/1250000000 : ℝ)^37 ≤ (249686910167/4000000000000 : ℝ)^29 := by
    have hnat : (142139157 : ℕ)^37*4000000000000^29 ≤ 249686910167^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142139157 1250000000 249686910167 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3699423687/10000000000 : ℝ)^37 ≤ (7029730140381/25000000000000 : ℝ)^29 := by
    have hnat : (3699423687 : ℕ)^37*25000000000000^29 ≤ 7029730140381^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3699423687 10000000000 7029730140381 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3594711379/5000000000 : ℝ)^37 ≤ (2625556266841/4000000000000 : ℝ)^29 := by
    have hnat : (3594711379 : ℕ)^37*4000000000000^29 ≤ 2625556266841^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3594711379 5000000000 2625556266841 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-142139157/1250000000 : ℝ), (3699423687/10000000000 : ℝ), (3594711379/5000000000 : ℝ)] ![(249686910167/4000000000000 : ℝ), (7029730140381/25000000000000 : ℝ), (2625556266841/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-142139157/1250000000 : ℝ)|^37 ≤ (249686910167/4000000000000 : ℝ)^29
        have hw : |(-142139157/1250000000 : ℝ)|=(142139157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3699423687/10000000000 : ℝ)|^37 ≤ (7029730140381/25000000000000 : ℝ)^29
        have hw : |(3699423687/10000000000 : ℝ)|=(3699423687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3594711379/5000000000 : ℝ)|^37 ≤ (2625556266841/4000000000000 : ℝ)^29
        have hw : |(3594711379/5000000000 : ℝ)|=(3594711379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2128245921/10000000000 : ℝ)*x 0 + (-1015433667/10000000000 : ℝ)*x 1 + (8453689901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128245921/10000000000 : ℝ)^37 ≤ (2777656333459/20000000000000 : ℝ)^29 := by
    have hnat : (2128245921 : ℕ)^37*20000000000000^29 ≤ 2777656333459^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128245921 10000000000 2777656333459 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015433667/10000000000 : ℝ)^37 ≤ (2701434279703/50000000000000 : ℝ)^29 := by
    have hnat : (1015433667 : ℕ)^37*50000000000000^29 ≤ 2701434279703^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015433667 10000000000 2701434279703 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8453689901/10000000000 : ℝ)^37 ≤ (40354424880079/50000000000000 : ℝ)^29 := by
    have hnat : (8453689901 : ℕ)^37*50000000000000^29 ≤ 40354424880079^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8453689901 10000000000 40354424880079 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128245921/10000000000 : ℝ), (-1015433667/10000000000 : ℝ), (8453689901/10000000000 : ℝ)] ![(2777656333459/20000000000000 : ℝ), (2701434279703/50000000000000 : ℝ), (40354424880079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128245921/10000000000 : ℝ)|^37 ≤ (2777656333459/20000000000000 : ℝ)^29
        have hw : |(2128245921/10000000000 : ℝ)|=(2128245921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1015433667/10000000000 : ℝ)|^37 ≤ (2701434279703/50000000000000 : ℝ)^29
        have hw : |(-1015433667/10000000000 : ℝ)|=(1015433667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8453689901/10000000000 : ℝ)|^37 ≤ (40354424880079/50000000000000 : ℝ)^29
        have hw : |(8453689901/10000000000 : ℝ)|=(8453689901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3162544481/5000000000 : ℝ)*x 0 + (5112923773/10000000000 : ℝ)*x 1 + (-10565897/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3162544481/5000000000 : ℝ)^37 ≤ (55742760160287/100000000000000 : ℝ)^29 := by
    have hnat : (3162544481 : ℕ)^37*100000000000000^29 ≤ 55742760160287^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3162544481 5000000000 55742760160287 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5112923773/10000000000 : ℝ)^37 ≤ (21245758358477/50000000000000 : ℝ)^29 := by
    have hnat : (5112923773 : ℕ)^37*50000000000000^29 ≤ 21245758358477^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5112923773 10000000000 21245758358477 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10565897/250000000 : ℝ)^37 ≤ (1765723115099/100000000000000 : ℝ)^29 := by
    have hnat : (10565897 : ℕ)^37*100000000000000^29 ≤ 1765723115099^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10565897 250000000 1765723115099 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3162544481/5000000000 : ℝ), (5112923773/10000000000 : ℝ), (-10565897/250000000 : ℝ)] ![(55742760160287/100000000000000 : ℝ), (21245758358477/50000000000000 : ℝ), (1765723115099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3162544481/5000000000 : ℝ)|^37 ≤ (55742760160287/100000000000000 : ℝ)^29
        have hw : |(3162544481/5000000000 : ℝ)|=(3162544481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5112923773/10000000000 : ℝ)|^37 ≤ (21245758358477/50000000000000 : ℝ)^29
        have hw : |(5112923773/10000000000 : ℝ)|=(5112923773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10565897/250000000 : ℝ)|^37 ≤ (1765723115099/100000000000000 : ℝ)^29
        have hw : |(-10565897/250000000 : ℝ)|=(10565897/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4529466651/5000000000 : ℝ)*x 0 + (1567496851/10000000000 : ℝ)*x 1 + (27279091/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4529466651/5000000000 : ℝ)^37 ≤ (17630565694849/20000000000000 : ℝ)^29 := by
    have hnat : (4529466651 : ℕ)^37*20000000000000^29 ≤ 17630565694849^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529466651 5000000000 17630565694849 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1567496851/10000000000 : ℝ)^37 ≤ (1880289502987/20000000000000 : ℝ)^29 := by
    have hnat : (1567496851 : ℕ)^37*20000000000000^29 ≤ 1880289502987^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1567496851 10000000000 1880289502987 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27279091/500000000 : ℝ)^37 ≤ (2445724004687/100000000000000 : ℝ)^29 := by
    have hnat : (27279091 : ℕ)^37*100000000000000^29 ≤ 2445724004687^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27279091 500000000 2445724004687 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4529466651/5000000000 : ℝ), (1567496851/10000000000 : ℝ), (27279091/500000000 : ℝ)] ![(17630565694849/20000000000000 : ℝ), (1880289502987/20000000000000 : ℝ), (2445724004687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4529466651/5000000000 : ℝ)|^37 ≤ (17630565694849/20000000000000 : ℝ)^29
        have hw : |(4529466651/5000000000 : ℝ)|=(4529466651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1567496851/10000000000 : ℝ)|^37 ≤ (1880289502987/20000000000000 : ℝ)^29
        have hw : |(1567496851/10000000000 : ℝ)|=(1567496851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27279091/500000000 : ℝ)|^37 ≤ (2445724004687/100000000000000 : ℝ)^29
        have hw : |(27279091/500000000 : ℝ)|=(27279091/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-552888471/5000000000 : ℝ)*x 0 + (6767976887/10000000000 : ℝ)*x 1 + (2107232847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552888471/5000000000 : ℝ)^37 ≤ (3011769147693/50000000000000 : ℝ)^29 := by
    have hnat : (552888471 : ℕ)^37*50000000000000^29 ≤ 3011769147693^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552888471 5000000000 3011769147693 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6767976887/10000000000 : ℝ)^37 ≤ (60769952815473/100000000000000 : ℝ)^29 := by
    have hnat : (6767976887 : ℕ)^37*100000000000000^29 ≤ 60769952815473^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6767976887 10000000000 60769952815473 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107232847/5000000000 : ℝ)^37 ≤ (33206508876323/100000000000000 : ℝ)^29 := by
    have hnat : (2107232847 : ℕ)^37*100000000000000^29 ≤ 33206508876323^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107232847 5000000000 33206508876323 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-552888471/5000000000 : ℝ), (6767976887/10000000000 : ℝ), (2107232847/5000000000 : ℝ)] ![(3011769147693/50000000000000 : ℝ), (60769952815473/100000000000000 : ℝ), (33206508876323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-552888471/5000000000 : ℝ)|^37 ≤ (3011769147693/50000000000000 : ℝ)^29
        have hw : |(-552888471/5000000000 : ℝ)|=(552888471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6767976887/10000000000 : ℝ)|^37 ≤ (60769952815473/100000000000000 : ℝ)^29
        have hw : |(6767976887/10000000000 : ℝ)|=(6767976887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2107232847/5000000000 : ℝ)|^37 ≤ (33206508876323/100000000000000 : ℝ)^29
        have hw : |(2107232847/5000000000 : ℝ)|=(2107232847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3146822463/5000000000 : ℝ)*x 0 + (-4401717/125000000 : ℝ)*x 1 + (647588997/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3146822463/5000000000 : ℝ)^37 ≤ (6923680288041/12500000000000 : ℝ)^29 := by
    have hnat : (3146822463 : ℕ)^37*12500000000000^29 ≤ 6923680288041^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3146822463 5000000000 6923680288041 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4401717/125000000 : ℝ)^37 ≤ (699479679713/50000000000000 : ℝ)^29 := by
    have hnat : (4401717 : ℕ)^37*50000000000000^29 ≤ 699479679713^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401717 125000000 699479679713 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647588997/1250000000 : ℝ)^37 ≤ (10802899580667/25000000000000 : ℝ)^29 := by
    have hnat : (647588997 : ℕ)^37*25000000000000^29 ≤ 10802899580667^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647588997 1250000000 10802899580667 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3146822463/5000000000 : ℝ), (-4401717/125000000 : ℝ), (647588997/1250000000 : ℝ)] ![(6923680288041/12500000000000 : ℝ), (699479679713/50000000000000 : ℝ), (10802899580667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3146822463/5000000000 : ℝ)|^37 ≤ (6923680288041/12500000000000 : ℝ)^29
        have hw : |(3146822463/5000000000 : ℝ)|=(3146822463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4401717/125000000 : ℝ)|^37 ≤ (699479679713/50000000000000 : ℝ)^29
        have hw : |(-4401717/125000000 : ℝ)|=(4401717/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647588997/1250000000 : ℝ)|^37 ≤ (10802899580667/25000000000000 : ℝ)^29
        have hw : |(647588997/1250000000 : ℝ)|=(647588997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (13374797/62500000 : ℝ)*x 0 + (1693554189/2000000000 : ℝ)*x 1 + (-195111353/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13374797/62500000 : ℝ)^37 ≤ (2797189679663/20000000000000 : ℝ)^29 := by
    have hnat : (13374797 : ℕ)^37*20000000000000^29 ≤ 2797189679663^29*62500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13374797 62500000 2797189679663 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1693554189/2000000000 : ℝ)^37 ≤ (10110051077591/12500000000000 : ℝ)^29 := by
    have hnat : (1693554189 : ℕ)^37*12500000000000^29 ≤ 10110051077591^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693554189 2000000000 10110051077591 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195111353/2000000000 : ℝ)^37 ≤ (5133642961137/100000000000000 : ℝ)^29 := by
    have hnat : (195111353 : ℕ)^37*100000000000000^29 ≤ 5133642961137^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195111353 2000000000 5133642961137 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13374797/62500000 : ℝ), (1693554189/2000000000 : ℝ), (-195111353/2000000000 : ℝ)] ![(2797189679663/20000000000000 : ℝ), (10110051077591/12500000000000 : ℝ), (5133642961137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13374797/62500000 : ℝ)|^37 ≤ (2797189679663/20000000000000 : ℝ)^29
        have hw : |(13374797/62500000 : ℝ)|=(13374797/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1693554189/2000000000 : ℝ)|^37 ≤ (10110051077591/12500000000000 : ℝ)^29
        have hw : |(1693554189/2000000000 : ℝ)|=(1693554189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195111353/2000000000 : ℝ)|^37 ≤ (5133642961137/100000000000000 : ℝ)^29
        have hw : |(-195111353/2000000000 : ℝ)|=(195111353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s1_s1_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (9160700001/10000000000 : ℝ)*x 0 + (136803917/1250000000 : ℝ)*x 1 + (900769997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9160700001/10000000000 : ℝ)^37 ≤ (17883652324737/20000000000000 : ℝ)^29 := by
    have hnat : (9160700001 : ℕ)^37*20000000000000^29 ≤ 17883652324737^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9160700001 10000000000 17883652324737 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136803917/1250000000 : ℝ)^37 ≤ (1486199411877/25000000000000 : ℝ)^29 := by
    have hnat : (136803917 : ℕ)^37*25000000000000^29 ≤ 1486199411877^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136803917 1250000000 1486199411877 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900769997/10000000000 : ℝ)^37 ≤ (4636940713163/100000000000000 : ℝ)^29 := by
    have hnat : (900769997 : ℕ)^37*100000000000000^29 ≤ 4636940713163^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900769997 10000000000 4636940713163 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9160700001/10000000000 : ℝ), (136803917/1250000000 : ℝ), (900769997/10000000000 : ℝ)] ![(17883652324737/20000000000000 : ℝ), (1486199411877/25000000000000 : ℝ), (4636940713163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9160700001/10000000000 : ℝ)|^37 ≤ (17883652324737/20000000000000 : ℝ)^29
        have hw : |(9160700001/10000000000 : ℝ)|=(9160700001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136803917/1250000000 : ℝ)|^37 ≤ (1486199411877/25000000000000 : ℝ)^29
        have hw : |(136803917/1250000000 : ℝ)|=(136803917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900769997/10000000000 : ℝ)|^37 ≤ (4636940713163/100000000000000 : ℝ)^29
        have hw : |(900769997/10000000000 : ℝ)|=(900769997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313053_s1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((1653/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1653/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83107/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83107/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41029/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41029/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12193/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12193/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6553/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6553/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32043/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32043/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (176973/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (1653/2000 : ℝ) ^ (73/16 : ℝ) ≤ (41919929076575179527/100000000000000000000 : ℝ) := by
    have hpowers : (1653/2000 : ℝ)^73 ≤ (41919929076575179527/100000000000000000000 : ℝ)^16 := by
      have hnat : (1653 : ℕ)^73*100000000000000000000^16 ≤ 41919929076575179527^16*2000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1653 2000 41919929076575179527 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1653/2000 : ℝ)) (X := (41919929076575179527/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (141919929076575179527/100000000000000000000 : ℝ) ≤ (2159506786952617/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (141919929076575179527/100000000000000000000 : ℝ)^16 ≤ (2159506786952617/2000000000000000 : ℝ)^73 := by
      have hnat : (141919929076575179527 : ℕ)^16*2000000000000000^73 ≤ 2159506786952617^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141919929076575179527 100000000000000000000 2159506786952617 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2159506786952617/2000000000000000 : ℝ)) (X := (141919929076575179527/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (91919929076575179527/50000000000000000000 : ℝ) ≤ (5713857240562681/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (91919929076575179527/50000000000000000000 : ℝ)^16 ≤ (5713857240562681/5000000000000000 : ℝ)^73 := by
      have hnat : (91919929076575179527 : ℕ)^16*5000000000000000^73 ≤ 5713857240562681^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91919929076575179527 50000000000000000000 5713857240562681 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5713857240562681/5000000000000000 : ℝ)) (X := (91919929076575179527/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(159506786952617/1653000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(210060182120759/2755000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1653/2000 : ℝ)) (alpha := (159506786952617/1653000000000000 : ℝ)) (beta := (210060182120759/2755000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1653/2000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(159506786952617/1653000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(210060182120759/2755000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (83107/100000 : ℝ) ^ (73/16 : ℝ) ≤ (5373491765698820629/12500000000000000000 : ℝ) := by
    have hpowers : (83107/100000 : ℝ)^73 ≤ (5373491765698820629/12500000000000000000 : ℝ)^16 := by
      have hnat : (83107 : ℕ)^73*12500000000000000000^16 ≤ 5373491765698820629^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83107 100000 5373491765698820629 12500000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83107/100000 : ℝ)) (X := (5373491765698820629/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (17873491765698820629/12500000000000000000 : ℝ) ≤ (5407645669306877/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (17873491765698820629/12500000000000000000 : ℝ)^16 ≤ (5407645669306877/5000000000000000 : ℝ)^73 := by
      have hnat : (17873491765698820629 : ℕ)^16*5000000000000000^73 ≤ 5407645669306877^73*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17873491765698820629 12500000000000000000 5407645669306877 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5407645669306877/5000000000000000 : ℝ)) (X := (17873491765698820629/12500000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (11623491765698820629/6250000000000000000 : ℝ) ≤ (11456685193210001/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (11623491765698820629/6250000000000000000 : ℝ)^16 ≤ (11456685193210001/10000000000000000 : ℝ)^73 := by
      have hnat : (11623491765698820629 : ℕ)^16*10000000000000000^73 ≤ 11456685193210001^73*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11623491765698820629 6250000000000000000 11456685193210001 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11456685193210001/10000000000000000 : ℝ)) (X := (11623491765698820629/6250000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(407645669306877/4155350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(641393854596247/8310700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (83107/100000 : ℝ)) (alpha := (407645669306877/4155350000000000 : ℝ)) (beta := (641393854596247/8310700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (83107/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(407645669306877/4155350000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(641393854596247/8310700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (41029/50000 : ℝ) ^ (73/16 : ℝ) ≤ (40567358744605114889/100000000000000000000 : ℝ) := by
    have hpowers : (41029/50000 : ℝ)^73 ≤ (40567358744605114889/100000000000000000000 : ℝ)^16 := by
      have hnat : (41029 : ℕ)^73*100000000000000000000^16 ≤ 40567358744605114889^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41029 50000 40567358744605114889 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41029/50000 : ℝ)) (X := (40567358744605114889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (140567358744605114889/100000000000000000000 : ℝ) ≤ (1077489477664957/1000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (140567358744605114889/100000000000000000000 : ℝ)^16 ≤ (1077489477664957/1000000000000000 : ℝ)^73 := by
      have hnat : (140567358744605114889 : ℕ)^16*1000000000000000^73 ≤ 1077489477664957^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        140567358744605114889 100000000000000000000 1077489477664957 1000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1077489477664957/1000000000000000 : ℝ)) (X := (140567358744605114889/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (90567358744605114889/50000000000000000000 : ℝ) ≤ (2847661253311161/2500000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (90567358744605114889/50000000000000000000 : ℝ)^16 ≤ (2847661253311161/2500000000000000 : ℝ)^73 := by
      have hnat : (90567358744605114889 : ℕ)^16*2500000000000000^73 ≤ 2847661253311161^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90567358744605114889 50000000000000000000 2847661253311161 2500000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2847661253311161/2500000000000000 : ℝ)) (X := (90567358744605114889/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(77489477664957/820580000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(307875118297537/4102900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (41029/50000 : ℝ)) (alpha := (77489477664957/820580000000000 : ℝ)) (beta := (307875118297537/4102900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (41029/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(77489477664957/820580000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(307875118297537/4102900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-340257189/2000000000 : ℝ)*X 0 0+(104377061/200000000 : ℝ)*X 0 1+(5435858791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4529304499/10000000000 : ℝ)*X 1 0+(-511416281/5000000000 : ℝ)*X 1 1+(81720071/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2277324933/5000000000 : ℝ)*X 2 0+(3280207373/5000000000 : ℝ)*X 2 1+(-472854587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1852411781/10000000000 : ℝ)*X 0 0+(918063313/2500000000 : ℝ)*X 0 1+(1686322411/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((657946667/2000000000 : ℝ)*X 1 0+(-51772401/1250000000 : ℝ)*X 1 1+(7903732259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((165871767/500000000 : ℝ)*X 2 0+(7958018733/10000000000 : ℝ)*X 2 1+(-114803647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((5956549731/10000000000 : ℝ)*X 0 0+(5507223631/10000000000 : ℝ)*X 0 1+(401021341/10000000000 : ℝ)*X 0 2+(5956549731/10000000000 : ℝ)*X 1 0+(5507223631/10000000000 : ℝ)*X 1 1+(401021341/10000000000 : ℝ)*X 1 2+(5956549731/10000000000 : ℝ)*X 2 0+(5507223631/10000000000 : ℝ)*X 2 1+(401021341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-142139157/1250000000 : ℝ)*X 0 0+(3699423687/10000000000 : ℝ)*X 0 1+(3594711379/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2128245921/10000000000 : ℝ)*X 1 0+(-1015433667/10000000000 : ℝ)*X 1 1+(8453689901/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3162544481/5000000000 : ℝ)*X 2 0+(5112923773/10000000000 : ℝ)*X 2 1+(-10565897/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((4529466651/5000000000 : ℝ)*X 0 0+(1567496851/10000000000 : ℝ)*X 0 1+(27279091/500000000 : ℝ)*X 0 2+(4529466651/5000000000 : ℝ)*X 1 0+(1567496851/10000000000 : ℝ)*X 1 1+(27279091/500000000 : ℝ)*X 1 2+(4529466651/5000000000 : ℝ)*X 2 0+(1567496851/10000000000 : ℝ)*X 2 1+(27279091/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-552888471/5000000000 : ℝ)*X 0 0+(6767976887/10000000000 : ℝ)*X 0 1+(2107232847/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3146822463/5000000000 : ℝ)*X 1 0+(-4401717/125000000 : ℝ)*X 1 1+(647588997/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((13374797/62500000 : ℝ)*X 2 0+(1693554189/2000000000 : ℝ)*X 2 1+(-195111353/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((9160700001/10000000000 : ℝ)*X 0 0+(136803917/1250000000 : ℝ)*X 0 1+(900769997/10000000000 : ℝ)*X 0 2+(9160700001/10000000000 : ℝ)*X 1 0+(136803917/1250000000 : ℝ)*X 1 1+(900769997/10000000000 : ℝ)*X 1 2+(9160700001/10000000000 : ℝ)*X 2 0+(136803917/1250000000 : ℝ)*X 2 1+(900769997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((12193/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12193/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2840830840444718872809976373709/587124438672812500000000000000000000 : ℝ) := by norm_num
    linear_combination (400456003401/1000000000000 : ℝ)*(base7) + (44691/1000000000000 : ℝ)*(base23) + (57523/500000000000 : ℝ)*(base49) + (4660915463/50000000000 : ℝ)*(base59) + (1380078135081/500000000000 : ℝ)*(major_s1_0) + (1380078135081/500000000000 : ℝ)*(major_s1_1) + (1380078135081/500000000000 : ℝ)*(major_s1_2) + (4385393/500000000000 : ℝ)*(sp_s1_0) + (3655509907229/1000000000000 : ℝ)*(sp_s1_7) + (3655542202839/1000000000000 : ℝ)*(sp_s1_8) + (3655542200513/1000000000000 : ℝ)*(sp_s1_9) + (2028991684699/1000000000000 : ℝ)*(sp_s1_13) + (5891797/250000000000 : ℝ)*(sp_s1_14) + (8473/200000000000 : ℝ)*(sp_s1_22) + (814267840649/500000000000 : ℝ)*(f.failure) + (913885561301/250000000000 : ℝ)*(f.sum) + (33427123976437349411/170489855150000000000000000000000 : ℝ)*base63 + (647447027952859/1025725000000000000000000000 : ℝ)*base65 + (412663456189609/2077675000000000000000000000 : ℝ)*base67 + (59997298745821/410290000000000000000000000 : ℝ)*base69 + (4674295282391829491/11303489500000000000000000000000 : ℝ)*base71 + (264729756978521/1377500000000000000000000000 : ℝ)*base72 + (1303534196535959/4155350000000000000000000000 : ℝ)*base75 + (25960981814241/275500000000000000000000000 : ℝ)*base76 + (34387511754599589847/114479892500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (22937/50000000000000000 : ℝ)*base86 + (22937/50000000000000000 : ℝ)*base88 + (22937/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6553/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6553/10000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5196669735330269821588369532701/469699550938250000000000000000000000 : ℝ) := by norm_num
    linear_combination (20580957561/31250000000 : ℝ)*(base7) + (8841/25000000000 : ℝ)*(base27) + (395547788207/200000000000 : ℝ)*(major_s1_0) + (395547788207/200000000000 : ℝ)*(major_s1_1) + (395547788207/200000000000 : ℝ)*(major_s1_2) + (9184977/500000000000 : ℝ)*(sp_s1_0) + (11918871/500000000000 : ℝ)*(sp_s1_2) + (45590811/500000000000 : ℝ)*(sp_s1_8) + (60001131753/25000000000 : ℝ)*(sp_s1_14) + (2399976675547/1000000000000 : ℝ)*(sp_s1_15) + (1200022009713/500000000000 : ℝ)*(sp_s1_16) + (22817824217/12500000000 : ℝ)*(sp_s1_20) + (2108547/500000000000 : ℝ)*(sp_s1_21) + (15370579/250000000000 : ℝ)*(sp_s1_27) + (291724282841/250000000000 : ℝ)*(f.failure) + (2400067857169/1000000000000 : ℝ)*(f.sum) + (16362548770344787801/68195942060000000000000000000000 : ℝ)*base62 + (20440090274709/820580000000000000000000000 : ℝ)*base65 + (11366266663603/1662140000000000000000000000 : ℝ)*base67 + (469857902290699/820580000000000000000000000 : ℝ)*base68 + (943330743864253559/13564187400000000000000000000000 : ℝ)*base70 + (340365002065587/551000000000000000000000000 : ℝ)*base72 + (65230639646401/831070000000000000000000000 : ℝ)*base74 + (2442148612241/330600000000000000000000000 : ℝ)*base76 + (4207808934133354659/45791957000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (2433/25000000000000000 : ℝ)*base86 + (2433/25000000000000000 : ℝ)*base88 + (2433/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32043/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32043/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22689224893911714400921941498831/2348497754691250000000000000000000000 : ℝ) := by norm_num
    linear_combination (39704478741/62500000000 : ℝ)*(base7) + (10489989/1000000000000 : ℝ)*(base27) + (196803/500000000000 : ℝ)*(base34) + (1398132479/20000000000 : ℝ)*(base40) + (1166999/500000000000 : ℝ)*(base43) + (490247241453/250000000000 : ℝ)*(major_s1_0) + (98049351271/50000000000 : ℝ)*(major_s1_1) + (980494679709/500000000000 : ℝ)*(major_s1_2) + (10679087/1000000000000 : ℝ)*(sp_s1_1) + (34553767/500000000000 : ℝ)*(sp_s1_9) + (1195102525811/500000000000 : ℝ)*(sp_s1_21) + (2390197100139/1000000000000 : ℝ)*(sp_s1_22) + (1195068168847/500000000000 : ℝ)*(sp_s1_23) + (1792275390609/1000000000000 : ℝ)*(sp_s1_27) + (1157014614347/1000000000000 : ℝ)*(f.failure) + (2390207779227/1000000000000 : ℝ)*(f.sum) + (6544768743663436823/8524492757500000000000000000000 : ℝ)*base62 + (144211232404257/2051450000000000000000000000 : ℝ)*base65 + (241432818443861/831070000000000000000000000 : ℝ)*base66 + (290473579102831/410290000000000000000000000 : ℝ)*base68 + (235381226251807839/2825872375000000000000000000000 : ℝ)*base71 + (37818327261387/172187500000000000000000000 : ℝ)*base72 + (30769499675863/33242800000000000000000000 : ℝ)*base74 + (41577563727267/137750000000000000000000000 : ℝ)*base77 + (1889407730409091017/7154993281250000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (29989/100000000000000000 : ℝ)*base87 + (29989/100000000000000000 : ℝ)*base89 + (29989/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((1653/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1653/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83107/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83107/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41029/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41029/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12193/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12193/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6553/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6553/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32043/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32043/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313053_s1 p hpa hpb X hX hprev0

#print axioms solution
