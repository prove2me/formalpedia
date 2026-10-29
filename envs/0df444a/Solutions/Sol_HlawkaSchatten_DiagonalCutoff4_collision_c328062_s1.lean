-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c328062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:23:16.092614+00:00
-- url     : https://prove2.me/submissions/cda581a6-bd26-46e6-9620-20d89f6121a8

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
theorem collision_support_c328062_s1_s1_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-179904013/1250000000 : ℝ)*x 0 + (987814277/2000000000 : ℝ)*x 1 + (-5419996911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179904013/1250000000 : ℝ)^93 ≤ (9620485428079/100000000000000 : ℝ)^77 := by
    have hnat : (179904013 : ℕ)^93*100000000000000^77 ≤ 9620485428079^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179904013 1250000000 9620485428079 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987814277/2000000000 : ℝ)^93 ≤ (42656693093557/100000000000000 : ℝ)^77 := by
    have hnat : (987814277 : ℕ)^93*100000000000000^77 ≤ 42656693093557^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987814277 2000000000 42656693093557 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419996911/10000000000 : ℝ)^93 ≤ (9544564292641/20000000000000 : ℝ)^77 := by
    have hnat : (5419996911 : ℕ)^93*20000000000000^77 ≤ 9544564292641^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419996911 10000000000 9544564292641 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-179904013/1250000000 : ℝ), (987814277/2000000000 : ℝ), (-5419996911/10000000000 : ℝ)] ![(9620485428079/100000000000000 : ℝ), (42656693093557/100000000000000 : ℝ), (9544564292641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-179904013/1250000000 : ℝ)|^93 ≤ (9620485428079/100000000000000 : ℝ)^77
        have hw : |(-179904013/1250000000 : ℝ)|=(179904013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(987814277/2000000000 : ℝ)|^93 ≤ (42656693093557/100000000000000 : ℝ)^77
        have hw : |(987814277/2000000000 : ℝ)|=(987814277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5419996911/10000000000 : ℝ)|^93 ≤ (9544564292641/20000000000000 : ℝ)^77
        have hw : |(-5419996911/10000000000 : ℝ)|=(5419996911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4940436523/10000000000 : ℝ)*x 0 + (-143849371/1000000000 : ℝ)*x 1 + (-1083843673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4940436523/10000000000 : ℝ)^93 ≤ (8534186704891/20000000000000 : ℝ)^77 := by
    have hnat : (4940436523 : ℕ)^93*20000000000000^77 ≤ 8534186704891^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4940436523 10000000000 8534186704891 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (143849371/1000000000 : ℝ)^93 ≤ (9614524369669/100000000000000 : ℝ)^77 := by
    have hnat : (143849371 : ℕ)^93*100000000000000^77 ≤ 9614524369669^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143849371 1000000000 9614524369669 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083843673/2000000000 : ℝ)^93 ≤ (23857271048499/50000000000000 : ℝ)^77 := by
    have hnat : (1083843673 : ℕ)^93*50000000000000^77 ≤ 23857271048499^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083843673 2000000000 23857271048499 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4940436523/10000000000 : ℝ), (-143849371/1000000000 : ℝ), (-1083843673/2000000000 : ℝ)] ![(8534186704891/20000000000000 : ℝ), (9614524369669/100000000000000 : ℝ), (23857271048499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4940436523/10000000000 : ℝ)|^93 ≤ (8534186704891/20000000000000 : ℝ)^77
        have hw : |(4940436523/10000000000 : ℝ)|=(4940436523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-143849371/1000000000 : ℝ)|^93 ≤ (9614524369669/100000000000000 : ℝ)^77
        have hw : |(-143849371/1000000000 : ℝ)|=(143849371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1083843673/2000000000 : ℝ)|^93 ≤ (23857271048499/50000000000000 : ℝ)^77
        have hw : |(-1083843673/2000000000 : ℝ)|=(1083843673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5004401331/10000000000 : ℝ)*x 0 + (250308363/500000000 : ℝ)*x 1 + (941124419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5004401331/10000000000 : ℝ)^93 ≤ (5417386977707/12500000000000 : ℝ)^77 := by
    have hnat : (5004401331 : ℕ)^93*12500000000000^77 ≤ 5417386977707^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5004401331 10000000000 5417386977707 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250308363/500000000 : ℝ)^93 ≤ (10839391904141/25000000000000 : ℝ)^77 := by
    have hnat : (250308363 : ℕ)^93*25000000000000^77 ≤ 10839391904141^77*500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250308363 500000000 10839391904141 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941124419/5000000000 : ℝ)^93 ≤ (13303336547863/100000000000000 : ℝ)^77 := by
    have hnat : (941124419 : ℕ)^93*100000000000000^77 ≤ 13303336547863^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941124419 5000000000 13303336547863 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5004401331/10000000000 : ℝ), (250308363/500000000 : ℝ), (941124419/5000000000 : ℝ)] ![(5417386977707/12500000000000 : ℝ), (10839391904141/25000000000000 : ℝ), (13303336547863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5004401331/10000000000 : ℝ)|^93 ≤ (5417386977707/12500000000000 : ℝ)^77
        have hw : |(5004401331/10000000000 : ℝ)|=(5004401331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(250308363/500000000 : ℝ)|^93 ≤ (10839391904141/25000000000000 : ℝ)^77
        have hw : |(250308363/500000000 : ℝ)|=(250308363/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(941124419/5000000000 : ℝ)|^93 ≤ (13303336547863/100000000000000 : ℝ)^77
        have hw : |(941124419/5000000000 : ℝ)|=(941124419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1385985049/10000000000 : ℝ)*x 0 + (121721289/250000000 : ℝ)*x 1 + (-5528812699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1385985049/10000000000 : ℝ)^93 ≤ (4596133799919/50000000000000 : ℝ)^77 := by
    have hnat : (1385985049 : ℕ)^93*50000000000000^77 ≤ 4596133799919^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385985049 10000000000 4596133799919 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121721289/250000000 : ℝ)^93 ≤ (838506047539/2000000000000 : ℝ)^77 := by
    have hnat : (121721289 : ℕ)^93*2000000000000^77 ≤ 838506047539^77*250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121721289 250000000 838506047539 2000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5528812699/10000000000 : ℝ)^93 ≤ (48882430006359/100000000000000 : ℝ)^77 := by
    have hnat : (5528812699 : ℕ)^93*100000000000000^77 ≤ 48882430006359^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528812699 10000000000 48882430006359 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1385985049/10000000000 : ℝ), (121721289/250000000 : ℝ), (-5528812699/10000000000 : ℝ)] ![(4596133799919/50000000000000 : ℝ), (838506047539/2000000000000 : ℝ), (48882430006359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1385985049/10000000000 : ℝ)|^93 ≤ (4596133799919/50000000000000 : ℝ)^77
        have hw : |(-1385985049/10000000000 : ℝ)|=(1385985049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121721289/250000000 : ℝ)|^93 ≤ (838506047539/2000000000000 : ℝ)^77
        have hw : |(121721289/250000000 : ℝ)|=(121721289/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5528812699/10000000000 : ℝ)|^93 ≤ (48882430006359/100000000000000 : ℝ)^77
        have hw : |(-5528812699/10000000000 : ℝ)|=(5528812699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (990716393/2000000000 : ℝ)*x 0 + (-665743259/5000000000 : ℝ)*x 1 + (-5486822129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (990716393/2000000000 : ℝ)^93 ≤ (42808101963047/100000000000000 : ℝ)^77 := by
    have hnat : (990716393 : ℕ)^93*100000000000000^77 ≤ 42808101963047^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990716393 2000000000 42808101963047 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (665743259/5000000000 : ℝ)^93 ≤ (8757512748197/100000000000000 : ℝ)^77 := by
    have hnat : (665743259 : ℕ)^93*100000000000000^77 ≤ 8757512748197^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665743259 5000000000 8757512748197 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486822129/10000000000 : ℝ)^93 ≤ (12108596315867/25000000000000 : ℝ)^77 := by
    have hnat : (5486822129 : ℕ)^93*25000000000000^77 ≤ 12108596315867^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486822129 10000000000 12108596315867 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(990716393/2000000000 : ℝ), (-665743259/5000000000 : ℝ), (-5486822129/10000000000 : ℝ)] ![(42808101963047/100000000000000 : ℝ), (8757512748197/100000000000000 : ℝ), (12108596315867/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(990716393/2000000000 : ℝ)|^93 ≤ (42808101963047/100000000000000 : ℝ)^77
        have hw : |(990716393/2000000000 : ℝ)|=(990716393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-665743259/5000000000 : ℝ)|^93 ≤ (8757512748197/100000000000000 : ℝ)^77
        have hw : |(-665743259/5000000000 : ℝ)|=(665743259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5486822129/10000000000 : ℝ)|^93 ≤ (12108596315867/25000000000000 : ℝ)^77
        have hw : |(-5486822129/10000000000 : ℝ)|=(5486822129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (199152163/400000000 : ℝ)*x 0 + (2576264933/5000000000 : ℝ)*x 1 + (346487631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199152163/400000000 : ℝ)^93 ≤ (43071498241021/100000000000000 : ℝ)^77 := by
    have hnat : (199152163 : ℕ)^93*100000000000000^77 ≤ 43071498241021^77*400000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199152163 400000000 43071498241021 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2576264933/5000000000 : ℝ)^93 ≤ (11223301608633/25000000000000 : ℝ)^77 := by
    have hnat : (2576264933 : ℕ)^93*25000000000000^77 ≤ 11223301608633^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576264933 5000000000 11223301608633 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (346487631/2000000000 : ℝ)^93 ≤ (3008823826789/25000000000000 : ℝ)^77 := by
    have hnat : (346487631 : ℕ)^93*25000000000000^77 ≤ 3008823826789^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346487631 2000000000 3008823826789 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(199152163/400000000 : ℝ), (2576264933/5000000000 : ℝ), (346487631/2000000000 : ℝ)] ![(43071498241021/100000000000000 : ℝ), (11223301608633/25000000000000 : ℝ), (3008823826789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(199152163/400000000 : ℝ)|^93 ≤ (43071498241021/100000000000000 : ℝ)^77
        have hw : |(199152163/400000000 : ℝ)|=(199152163/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2576264933/5000000000 : ℝ)|^93 ≤ (11223301608633/25000000000000 : ℝ)^77
        have hw : |(2576264933/5000000000 : ℝ)|=(2576264933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(346487631/2000000000 : ℝ)|^93 ≤ (3008823826789/25000000000000 : ℝ)^77
        have hw : |(346487631/2000000000 : ℝ)|=(346487631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5325454777/10000000000 : ℝ)*x 0 + (137052449/250000000 : ℝ)*x 1 + (-164561909/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5325454777/10000000000 : ℝ)^93 ≤ (72998810233/156250000000 : ℝ)^77 := by
    have hnat : (5325454777 : ℕ)^93*156250000000^77 ≤ 72998810233^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5325454777 10000000000 72998810233 156250000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137052449/250000000 : ℝ)^93 ≤ (48384022251071/100000000000000 : ℝ)^77 := by
    have hnat : (137052449 : ℕ)^93*100000000000000^77 ≤ 48384022251071^77*250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137052449 250000000 48384022251071 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164561909/2000000000 : ℝ)^93 ≤ (244836958917/5000000000000 : ℝ)^77 := by
    have hnat : (164561909 : ℕ)^93*5000000000000^77 ≤ 244836958917^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164561909 2000000000 244836958917 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5325454777/10000000000 : ℝ), (137052449/250000000 : ℝ), (-164561909/2000000000 : ℝ)] ![(72998810233/156250000000 : ℝ), (48384022251071/100000000000000 : ℝ), (244836958917/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5325454777/10000000000 : ℝ)|^93 ≤ (72998810233/156250000000 : ℝ)^77
        have hw : |(5325454777/10000000000 : ℝ)|=(5325454777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137052449/250000000 : ℝ)|^93 ≤ (48384022251071/100000000000000 : ℝ)^77
        have hw : |(137052449/250000000 : ℝ)|=(137052449/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-164561909/2000000000 : ℝ)|^93 ≤ (244836958917/5000000000000 : ℝ)^77
        have hw : |(-164561909/2000000000 : ℝ)|=(164561909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-131718319/1000000000 : ℝ)*x 0 + (1233495827/2500000000 : ℝ)*x 1 + (-68957869/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131718319/1000000000 : ℝ)^93 ≤ (864401507451/10000000000000 : ℝ)^77 := by
    have hnat : (131718319 : ℕ)^93*10000000000000^77 ≤ 864401507451^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131718319 1000000000 864401507451 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1233495827/2500000000 : ℝ)^93 ≤ (2130181202371/5000000000000 : ℝ)^77 := by
    have hnat : (1233495827 : ℕ)^93*5000000000000^77 ≤ 2130181202371^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233495827 2500000000 2130181202371 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68957869/125000000 : ℝ)^93 ≤ (48752360869003/100000000000000 : ℝ)^77 := by
    have hnat : (68957869 : ℕ)^93*100000000000000^77 ≤ 48752360869003^77*125000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68957869 125000000 48752360869003 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-131718319/1000000000 : ℝ), (1233495827/2500000000 : ℝ), (-68957869/125000000 : ℝ)] ![(864401507451/10000000000000 : ℝ), (2130181202371/5000000000000 : ℝ), (48752360869003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-131718319/1000000000 : ℝ)|^93 ≤ (864401507451/10000000000000 : ℝ)^77
        have hw : |(-131718319/1000000000 : ℝ)|=(131718319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1233495827/2500000000 : ℝ)|^93 ≤ (2130181202371/5000000000000 : ℝ)^77
        have hw : |(1233495827/2500000000 : ℝ)|=(1233495827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68957869/125000000 : ℝ)|^93 ≤ (48752360869003/100000000000000 : ℝ)^77
        have hw : |(-68957869/125000000 : ℝ)|=(68957869/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4890027987/10000000000 : ℝ)*x 0 + (-1404502667/10000000000 : ℝ)*x 1 + (-1098849289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4890027987/10000000000 : ℝ)^93 ≤ (42145640963481/100000000000000 : ℝ)^77 := by
    have hnat : (4890027987 : ℕ)^93*100000000000000^77 ≤ 42145640963481^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4890027987 10000000000 42145640963481 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1404502667/10000000000 : ℝ)^93 ≤ (4670403519417/50000000000000 : ℝ)^77 := by
    have hnat : (1404502667 : ℕ)^93*50000000000000^77 ≤ 4670403519417^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404502667 10000000000 4670403519417 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098849289/2000000000 : ℝ)^93 ≤ (48513551976001/100000000000000 : ℝ)^77 := by
    have hnat : (1098849289 : ℕ)^93*100000000000000^77 ≤ 48513551976001^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098849289 2000000000 48513551976001 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4890027987/10000000000 : ℝ), (-1404502667/10000000000 : ℝ), (-1098849289/2000000000 : ℝ)] ![(42145640963481/100000000000000 : ℝ), (4670403519417/50000000000000 : ℝ), (48513551976001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4890027987/10000000000 : ℝ)|^93 ≤ (42145640963481/100000000000000 : ℝ)^77
        have hw : |(4890027987/10000000000 : ℝ)|=(4890027987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1404502667/10000000000 : ℝ)|^93 ≤ (4670403519417/50000000000000 : ℝ)^77
        have hw : |(-1404502667/10000000000 : ℝ)|=(1404502667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1098849289/2000000000 : ℝ)|^93 ≤ (48513551976001/100000000000000 : ℝ)^77
        have hw : |(-1098849289/2000000000 : ℝ)|=(1098849289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_16 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (640881937/1250000000 : ℝ)*x 0 + (200043439/400000000 : ℝ)*x 1 + (1736610193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (640881937/1250000000 : ℝ)^93 ≤ (44625269643943/100000000000000 : ℝ)^77 := by
    have hnat : (640881937 : ℕ)^93*100000000000000^77 ≤ 44625269643943^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640881937 1250000000 44625269643943 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200043439/400000000 : ℝ)^93 ≤ (21652210261529/50000000000000 : ℝ)^77 := by
    have hnat : (200043439 : ℕ)^93*50000000000000^77 ≤ 21652210261529^77*400000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200043439 400000000 21652210261529 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1736610193/10000000000 : ℝ)^93 ≤ (6035154909187/50000000000000 : ℝ)^77 := by
    have hnat : (1736610193 : ℕ)^93*50000000000000^77 ≤ 6035154909187^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736610193 10000000000 6035154909187 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(640881937/1250000000 : ℝ), (200043439/400000000 : ℝ), (1736610193/10000000000 : ℝ)] ![(44625269643943/100000000000000 : ℝ), (21652210261529/50000000000000 : ℝ), (6035154909187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(640881937/1250000000 : ℝ)|^93 ≤ (44625269643943/100000000000000 : ℝ)^77
        have hw : |(640881937/1250000000 : ℝ)|=(640881937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200043439/400000000 : ℝ)|^93 ≤ (21652210261529/50000000000000 : ℝ)^77
        have hw : |(200043439/400000000 : ℝ)|=(200043439/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1736610193/10000000000 : ℝ)|^93 ≤ (6035154909187/50000000000000 : ℝ)^77
        have hw : |(1736610193/10000000000 : ℝ)|=(1736610193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1386053589/2500000000 : ℝ)*x 0 + (5261476459/10000000000 : ℝ)*x 1 + (-824774281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1386053589/2500000000 : ℝ)^93 ≤ (2452347262881/5000000000000 : ℝ)^77 := by
    have hnat : (1386053589 : ℕ)^93*5000000000000^77 ≤ 2452347262881^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386053589 2500000000 2452347262881 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261476459/10000000000 : ℝ)^93 ≤ (23021094891293/50000000000000 : ℝ)^77 := by
    have hnat : (5261476459 : ℕ)^93*50000000000000^77 ≤ 23021094891293^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261476459 10000000000 23021094891293 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (824774281/10000000000 : ℝ)^93 ≤ (4910864935601/100000000000000 : ℝ)^77 := by
    have hnat : (824774281 : ℕ)^93*100000000000000^77 ≤ 4910864935601^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824774281 10000000000 4910864935601 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1386053589/2500000000 : ℝ), (5261476459/10000000000 : ℝ), (-824774281/10000000000 : ℝ)] ![(2452347262881/5000000000000 : ℝ), (23021094891293/50000000000000 : ℝ), (4910864935601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1386053589/2500000000 : ℝ)|^93 ≤ (2452347262881/5000000000000 : ℝ)^77
        have hw : |(1386053589/2500000000 : ℝ)|=(1386053589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261476459/10000000000 : ℝ)|^93 ≤ (23021094891293/50000000000000 : ℝ)^77
        have hw : |(5261476459/10000000000 : ℝ)|=(5261476459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-824774281/10000000000 : ℝ)|^93 ≤ (4910864935601/100000000000000 : ℝ)^77
        have hw : |(-824774281/10000000000 : ℝ)|=(824774281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-640190143/5000000000 : ℝ)*x 0 + (4994620733/10000000000 : ℝ)*x 1 + (-5484536933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (640190143/5000000000 : ℝ)^93 ≤ (4176581674521/50000000000000 : ℝ)^77 := by
    have hnat : (640190143 : ℕ)^93*50000000000000^77 ≤ 4176581674521^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640190143 5000000000 4176581674521 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4994620733/10000000000 : ℝ)^93 ≤ (21618407158539/50000000000000 : ℝ)^77 := by
    have hnat : (4994620733 : ℕ)^93*50000000000000^77 ≤ 21618407158539^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4994620733 10000000000 21618407158539 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484536933/10000000000 : ℝ)^93 ≤ (48410022317951/100000000000000 : ℝ)^77 := by
    have hnat : (5484536933 : ℕ)^93*100000000000000^77 ≤ 48410022317951^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484536933 10000000000 48410022317951 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-640190143/5000000000 : ℝ), (4994620733/10000000000 : ℝ), (-5484536933/10000000000 : ℝ)] ![(4176581674521/50000000000000 : ℝ), (21618407158539/50000000000000 : ℝ), (48410022317951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-640190143/5000000000 : ℝ)|^93 ≤ (4176581674521/50000000000000 : ℝ)^77
        have hw : |(-640190143/5000000000 : ℝ)|=(640190143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4994620733/10000000000 : ℝ)|^93 ≤ (21618407158539/50000000000000 : ℝ)^77
        have hw : |(4994620733/10000000000 : ℝ)|=(4994620733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5484536933/10000000000 : ℝ)|^93 ≤ (48410022317951/100000000000000 : ℝ)^77
        have hw : |(-5484536933/10000000000 : ℝ)|=(5484536933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_22 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1019977591/2000000000 : ℝ)*x 0 + (-1383545959/10000000000 : ℝ)*x 1 + (-5303568657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019977591/2000000000 : ℝ)^93 ≤ (443398289453/1000000000000 : ℝ)^77 := by
    have hnat : (1019977591 : ℕ)^93*1000000000000^77 ≤ 443398289453^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019977591 2000000000 443398289453 1000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1383545959/10000000000 : ℝ)^93 ≤ (4586366495659/50000000000000 : ℝ)^77 := by
    have hnat : (1383545959 : ℕ)^93*50000000000000^77 ≤ 4586366495659^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383545959 10000000000 4586366495659 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5303568657/10000000000 : ℝ)^93 ≤ (46487438044931/100000000000000 : ℝ)^77 := by
    have hnat : (5303568657 : ℕ)^93*100000000000000^77 ≤ 46487438044931^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303568657 10000000000 46487438044931 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1019977591/2000000000 : ℝ), (-1383545959/10000000000 : ℝ), (-5303568657/10000000000 : ℝ)] ![(443398289453/1000000000000 : ℝ), (4586366495659/50000000000000 : ℝ), (46487438044931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1019977591/2000000000 : ℝ)|^93 ≤ (443398289453/1000000000000 : ℝ)^77
        have hw : |(1019977591/2000000000 : ℝ)|=(1019977591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1383545959/10000000000 : ℝ)|^93 ≤ (4586366495659/50000000000000 : ℝ)^77
        have hw : |(-1383545959/10000000000 : ℝ)|=(1383545959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5303568657/10000000000 : ℝ)|^93 ≤ (46487438044931/100000000000000 : ℝ)^77
        have hw : |(-5303568657/10000000000 : ℝ)|=(5303568657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_23 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (617668407/1250000000 : ℝ)*x 0 + (5061722259/10000000000 : ℝ)*x 1 + (945624149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (617668407/1250000000 : ℝ)^93 ≤ (1067010857159/2500000000000 : ℝ)^77 := by
    have hnat : (617668407 : ℕ)^93*2500000000000^77 ≤ 1067010857159^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617668407 1250000000 1067010857159 2500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5061722259/10000000000 : ℝ)^93 ≤ (10984841966279/25000000000000 : ℝ)^77 := by
    have hnat : (5061722259 : ℕ)^93*25000000000000^77 ≤ 10984841966279^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5061722259 10000000000 10984841966279 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945624149/5000000000 : ℝ)^93 ≤ (13380197830157/100000000000000 : ℝ)^77 := by
    have hnat : (945624149 : ℕ)^93*100000000000000^77 ≤ 13380197830157^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945624149 5000000000 13380197830157 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(617668407/1250000000 : ℝ), (5061722259/10000000000 : ℝ), (945624149/5000000000 : ℝ)] ![(1067010857159/2500000000000 : ℝ), (10984841966279/25000000000000 : ℝ), (13380197830157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(617668407/1250000000 : ℝ)|^93 ≤ (1067010857159/2500000000000 : ℝ)^77
        have hw : |(617668407/1250000000 : ℝ)|=(617668407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5061722259/10000000000 : ℝ)|^93 ≤ (10984841966279/25000000000000 : ℝ)^77
        have hw : |(5061722259/10000000000 : ℝ)|=(5061722259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(945624149/5000000000 : ℝ)|^93 ≤ (13380197830157/100000000000000 : ℝ)^77
        have hw : |(945624149/5000000000 : ℝ)|=(945624149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328062_s1_s1_27 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (139661617/250000000 : ℝ)*x 0 + (2595745459/5000000000 : ℝ)*x 1 + (-432234549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139661617/250000000 : ℝ)^93 ≤ (24749367957767/50000000000000 : ℝ)^77 := by
    have hnat : (139661617 : ℕ)^93*50000000000000^77 ≤ 24749367957767^77*250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139661617 250000000 24749367957767 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2595745459/5000000000 : ℝ)^93 ≤ (5662940886443/12500000000000 : ℝ)^77 := by
    have hnat : (2595745459 : ℕ)^93*12500000000000^77 ≤ 5662940886443^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595745459 5000000000 5662940886443 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432234549/5000000000 : ℝ)^93 ≤ (5197736975861/100000000000000 : ℝ)^77 := by
    have hnat : (432234549 : ℕ)^93*100000000000000^77 ≤ 5197736975861^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432234549 5000000000 5197736975861 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(139661617/250000000 : ℝ), (2595745459/5000000000 : ℝ), (-432234549/5000000000 : ℝ)] ![(24749367957767/50000000000000 : ℝ), (5662940886443/12500000000000 : ℝ), (5197736975861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(139661617/250000000 : ℝ)|^93 ≤ (24749367957767/50000000000000 : ℝ)^77
        have hw : |(139661617/250000000 : ℝ)|=(139661617/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2595745459/5000000000 : ℝ)|^93 ≤ (5662940886443/12500000000000 : ℝ)^77
        have hw : |(2595745459/5000000000 : ℝ)|=(2595745459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-432234549/5000000000 : ℝ)|^93 ≤ (5197736975861/100000000000000 : ℝ)^77
        have hw : |(-432234549/5000000000 : ℝ)|=(432234549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328062_s1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((62083/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62083/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(773/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(773/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1041/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1041/2000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22889/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22889/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22929/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22929/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-12639/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-12639/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s1_pow0 : (62083/100000 : ℝ) ^ (91/16 : ℝ) ≤ (830696183779494903/12500000000000000000 : ℝ) := by
    have hpowers : (62083/100000 : ℝ)^91 ≤ (830696183779494903/12500000000000000000 : ℝ)^16 := by
      have hnat : (62083 : ℕ)^91*12500000000000000000^16 ≤ 830696183779494903^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62083 100000 830696183779494903 12500000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62083/100000 : ℝ)) (X := (830696183779494903/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (13330696183779494903/12500000000000000000 : ℝ) ≤ (252844220821803/250000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (13330696183779494903/12500000000000000000 : ℝ)^16 ≤ (252844220821803/250000000000000 : ℝ)^91 := by
      have hnat : (13330696183779494903 : ℕ)^16*250000000000000^91 ≤ 252844220821803^91*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13330696183779494903 12500000000000000000 252844220821803 250000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252844220821803/250000000000000 : ℝ)) (X := (13330696183779494903/12500000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (7080696183779494903/6250000000000000000 : ℝ) ≤ (5110918566895409/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (7080696183779494903/6250000000000000000 : ℝ)^16 ≤ (5110918566895409/5000000000000000 : ℝ)^91 := by
      have hnat : (7080696183779494903 : ℕ)^16*5000000000000000^91 ≤ 5110918566895409^91*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7080696183779494903 6250000000000000000 5110918566895409 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5110918566895409/5000000000000000 : ℝ)) (X := (7080696183779494903/6250000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2844220821803/155207500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(54034150459349/3104150000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (62083/100000 : ℝ)) (alpha := (2844220821803/155207500000000 : ℝ)) (beta := (54034150459349/3104150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (62083/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2844220821803/155207500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(54034150459349/3104150000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (773/1250 : ℝ) ^ (91/16 : ℝ) ≤ (1624744896028715601/25000000000000000000 : ℝ) := by
    have hpowers : (773/1250 : ℝ)^91 ≤ (1624744896028715601/25000000000000000000 : ℝ)^16 := by
      have hnat : (773 : ℕ)^91*25000000000000000000^16 ≤ 1624744896028715601^16*1250^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        773 1250 1624744896028715601 25000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (773/1250 : ℝ)) (X := (1624744896028715601/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (26624744896028715601/25000000000000000000 : ℝ) ≤ (2527830789193401/2500000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (26624744896028715601/25000000000000000000 : ℝ)^16 ≤ (2527830789193401/2500000000000000 : ℝ)^91 := by
      have hnat : (26624744896028715601 : ℕ)^16*2500000000000000^91 ≤ 2527830789193401^91*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26624744896028715601 25000000000000000000 2527830789193401 2500000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527830789193401/2500000000000000 : ℝ)) (X := (26624744896028715601/25000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (14124744896028715601/12500000000000000000 : ℝ) ≤ (10217181173903283/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (14124744896028715601/12500000000000000000 : ℝ)^16 ≤ (10217181173903283/10000000000000000 : ℝ)^91 := by
      have hnat : (14124744896028715601 : ℕ)^16*10000000000000000^91 ≤ 10217181173903283^91*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14124744896028715601 12500000000000000000 10217181173903283 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10217181173903283/10000000000000000 : ℝ)) (X := (14124744896028715601/12500000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(27830789193401/1546000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(105858017129679/6184000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (773/1250 : ℝ)) (alpha := (27830789193401/1546000000000000 : ℝ)) (beta := (105858017129679/6184000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (773/1250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(27830789193401/1546000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(105858017129679/6184000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1041/2000 : ℝ) ^ (91/16 : ℝ) ≤ (60965330488875141/2500000000000000000 : ℝ) := by
    have hpowers : (1041/2000 : ℝ)^91 ≤ (60965330488875141/2500000000000000000 : ℝ)^16 := by
      have hnat : (1041 : ℕ)^91*2500000000000000000^16 ≤ 60965330488875141^16*2000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1041 2000 60965330488875141 2500000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1041/2000 : ℝ)) (X := (60965330488875141/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (2560965330488875141/2500000000000000000 : ℝ) ≤ (313826628722039/312500000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2560965330488875141/2500000000000000000 : ℝ)^16 ≤ (313826628722039/312500000000000 : ℝ)^91 := by
      have hnat : (2560965330488875141 : ℕ)^16*312500000000000^91 ≤ 313826628722039^91*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2560965330488875141 2500000000000000000 313826628722039 312500000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313826628722039/312500000000000 : ℝ)) (X := (2560965330488875141/2500000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1310965330488875141/1250000000000000000 : ℝ) ≤ (2016815867231707/2000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (1310965330488875141/1250000000000000000 : ℝ)^16 ≤ (2016815867231707/2000000000000000 : ℝ)^91 := by
      have hnat : (1310965330488875141 : ℕ)^16*2000000000000000^91 ≤ 2016815867231707^91*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1310965330488875141 1250000000000000000 2016815867231707 2000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2016815867231707/2000000000000000 : ℝ)) (X := (1310965330488875141/1250000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(442209574013/54218750000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(41627217053287/5205000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1041/2000 : ℝ)) (alpha := (442209574013/54218750000000 : ℝ)) (beta := (41627217053287/5205000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1041/2000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(442209574013/54218750000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(41627217053287/5205000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-179904013/1250000000 : ℝ)*X 0 0+(987814277/2000000000 : ℝ)*X 0 1+(-5419996911/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4940436523/10000000000 : ℝ)*X 1 0+(-143849371/1000000000 : ℝ)*X 1 1+(-1083843673/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5004401331/10000000000 : ℝ)*X 2 0+(250308363/500000000 : ℝ)*X 2 1+(941124419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1385985049/10000000000 : ℝ)*X 0 0+(121721289/250000000 : ℝ)*X 0 1+(-5528812699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((990716393/2000000000 : ℝ)*X 1 0+(-665743259/5000000000 : ℝ)*X 1 1+(-5486822129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((199152163/400000000 : ℝ)*X 2 0+(2576264933/5000000000 : ℝ)*X 2 1+(346487631/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((5325454777/10000000000 : ℝ)*X 0 0+(137052449/250000000 : ℝ)*X 0 1+(-164561909/2000000000 : ℝ)*X 0 2+(5325454777/10000000000 : ℝ)*X 1 0+(137052449/250000000 : ℝ)*X 1 1+(-164561909/2000000000 : ℝ)*X 1 2+(5325454777/10000000000 : ℝ)*X 2 0+(137052449/250000000 : ℝ)*X 2 1+(-164561909/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-131718319/1000000000 : ℝ)*X 0 0+(1233495827/2500000000 : ℝ)*X 0 1+(-68957869/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4890027987/10000000000 : ℝ)*X 1 0+(-1404502667/10000000000 : ℝ)*X 1 1+(-1098849289/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((640881937/1250000000 : ℝ)*X 2 0+(200043439/400000000 : ℝ)*X 2 1+(1736610193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1386053589/2500000000 : ℝ)*X 0 0+(5261476459/10000000000 : ℝ)*X 0 1+(-824774281/10000000000 : ℝ)*X 0 2+(1386053589/2500000000 : ℝ)*X 1 0+(5261476459/10000000000 : ℝ)*X 1 1+(-824774281/10000000000 : ℝ)*X 1 2+(1386053589/2500000000 : ℝ)*X 2 0+(5261476459/10000000000 : ℝ)*X 2 1+(-824774281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-640190143/5000000000 : ℝ)*X 0 0+(4994620733/10000000000 : ℝ)*X 0 1+(-5484536933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1019977591/2000000000 : ℝ)*X 1 0+(-1383545959/10000000000 : ℝ)*X 1 1+(-5303568657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((617668407/1250000000 : ℝ)*X 2 0+(5061722259/10000000000 : ℝ)*X 2 1+(945624149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((139661617/250000000 : ℝ)*X 0 0+(2595745459/5000000000 : ℝ)*X 0 1+(-432234549/5000000000 : ℝ)*X 0 2+(139661617/250000000 : ℝ)*X 1 0+(2595745459/5000000000 : ℝ)*X 1 1+(-432234549/5000000000 : ℝ)*X 1 2+(139661617/250000000 : ℝ)*X 2 0+(2595745459/5000000000 : ℝ)*X 2 1+(-432234549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((22889/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22889/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (31696677698992546225647241/1923464375000000000000000000000 : ℝ) := by norm_num
    linear_combination (3660438964637/1000000000000 : ℝ)*(base39) + (1717437346099/500000000000 : ℝ)*(base49) + (27236851899/125000000000 : ℝ)*(base60) + (9134218682603/250000000000 : ℝ)*(major_s1_0) + (9134218682603/250000000000 : ℝ)*(major_s1_1) + (9134218682603/250000000000 : ℝ)*(major_s1_2) + (630856363/1000000000000 : ℝ)*(sp_s1_0) + (2811687022467/50000000000 : ℝ)*(sp_s1_7) + (3514587910477/62500000000 : ℝ)*(sp_s1_8) + (56233624300239/1000000000000 : ℝ)*(sp_s1_9) + (16839209462109/1000000000000 : ℝ)*(sp_s1_13) + (163200017/1000000000000 : ℝ)*(sp_s1_14) + (140992261/125000000000 : ℝ)*(sp_s1_15) + (22755137/25000000000 : ℝ)*(sp_s1_23) + (16839209462109/1000000000000 : ℝ)*(f.failure) + (1405863362643/25000000000 : ℝ)*(f.sum) + (138504775935685037/670577500000000000000000000000 : ℝ)*base62 + (596010691103593/650625000000000000000000000 : ℝ)*base65 + (1296835128274763/1546000000000000000000000000 : ℝ)*base66 + (77047595508973/433750000000000000000000000 : ℝ)*base69 + (6099134408983295009/11540786250000000000000000000000 : ℝ)*base71 + (38873230124231/443450000000000000000000000 : ℝ)*base72 + (404175206205103/386500000000000000000000000 : ℝ)*base75 + (46952593910273/44345000000000000000000000 : ℝ)*base77 + (710462767218019033/13711474000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (3989/4000000000000000 : ℝ)*base86 + (3989/4000000000000000 : ℝ)*base88 + (3989/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22929/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22929/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (373939735959437856458368454877/83262925865000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1857517091989/500000000000 : ℝ)*(base39) + (1798270954979/500000000000 : ℝ)*(base49) + (2245671/1000000000000 : ℝ)*(base60) + (9385987603869/250000000000 : ℝ)*(major_s1_0) + (9385987603869/250000000000 : ℝ)*(major_s1_1) + (9385987603869/250000000000 : ℝ)*(major_s1_2) + (346401979/500000000000 : ℝ)*(sp_s1_1) + (327189471/1000000000000 : ℝ)*(sp_s1_8) + (57783971654897/1000000000000 : ℝ)*(sp_s1_14) + (11556705245633/200000000000 : ℝ)*(sp_s1_15) + (28892273110797/500000000000 : ℝ)*(sp_s1_16) + (17302914023159/1000000000000 : ℝ)*(sp_s1_20) + (574566697/1000000000000 : ℝ)*(sp_s1_21) + (43908917/100000000000 : ℝ)*(sp_s1_27) + (17303353112329/1000000000000 : ℝ)*(f.failure) + (28892273110797/500000000000 : ℝ)*(f.sum) + (306746044741420899/670577500000000000000000000000 : ℝ)*base63 + (104482288499949/433750000000000000000000000 : ℝ)*base64 + (913496471303949/1546000000000000000000000000 : ℝ)*base66 + (75777981599/105895996093750000000000 : ℝ)*base69 + (13210010254655727017/26928501250000000000000000000000 : ℝ)*base70 + (2235758337534781/3104150000000000000000000000 : ℝ)*base72 + (90567888966269/386500000000000000000000000 : ℝ)*base75 + (150988966507059/620830000000000000000000000 : ℝ)*base77 + (75051821985195811087/95980318000000000000000000000000 : ℝ)*base78 + (609/4000000000000000 : ℝ)*base86 + (609/4000000000000000 : ℝ)*base88 + (609/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-12639/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-12639/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5846389397332959218997166159/1040786573312500000000000000000000 : ℝ) := by norm_num
    linear_combination (2361637/1000000000000 : ℝ)*(base11) + (891619093393/250000000000 : ℝ)*(base39) + (2761615993711/1000000000000 : ℝ)*(base49) + (3649954385317/125000000000 : ℝ)*(major_s1_0) + (3649954385317/125000000000 : ℝ)*(major_s1_1) + (3649954385317/125000000000 : ℝ)*(major_s1_2) + (1245741/12500000000 : ℝ)*(sp_s1_0) + (25157483/250000000000 : ℝ)*(sp_s1_2) + (8210279/40000000000 : ℝ)*(sp_s1_9) + (8194133/500000000000 : ℝ)*(sp_s1_20) + (2808847676447/62500000000 : ℝ)*(sp_s1_21) + (44941664844069/1000000000000 : ℝ)*(sp_s1_22) + (44941358957161/1000000000000 : ℝ)*(sp_s1_23) + (2691517412061/200000000000 : ℝ)*(sp_s1_27) + (13457603448571/1000000000000 : ℝ)*(f.failure) + (44941664844069/1000000000000 : ℝ)*(f.sum) + (14384689595709893/335288750000000000000000000000 : ℝ)*base62 + (413110967194271/650625000000000000000000000 : ℝ)*base64 + (677571079046843/773000000000000000000000000 : ℝ)*base67 + (339408898838881/433750000000000000000000000 : ℝ)*base68 + (5684859447958993861/80785503750000000000000000000000 : ℝ)*base70 + (1373052703311199/3104150000000000000000000000 : ℝ)*base73 + (3470066231863/12078125000000000000000000 : ℝ)*base74 + (165771462617967/620830000000000000000000000 : ℝ)*base76 + (3258301420084855091/47990159000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (3709/4000000000000000 : ℝ)*base87 + (3709/4000000000000000 : ℝ)*base89 + (3709/4000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((62083/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62083/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(773/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(773/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1041/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1041/2000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22889/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22889/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22929/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22929/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-12639/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-12639/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c328062_s1 p hpa hpb X hX hprev0

#print axioms solution
