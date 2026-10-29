-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309083_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:06:13.718439+00:00
-- url     : https://prove2.me/submissions/c3df7280-b2b0-4689-b879-cc4c34e13985

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
theorem collision_support_c309083_s1_s1_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1973671131/10000000000 : ℝ)*x 0 + (249773301/500000000 : ℝ)*x 1 + (2798509737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1973671131/10000000000 : ℝ)^35 ≤ (305075496943/2500000000000 : ℝ)^27 := by
    have hnat : (1973671131 : ℕ)^35*2500000000000^27 ≤ 305075496943^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973671131 10000000000 305075496943 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249773301/500000000 : ℝ)^35 ≤ (40669159503903/100000000000000 : ℝ)^27 := by
    have hnat : (249773301 : ℕ)^35*100000000000000^27 ≤ 40669159503903^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249773301 500000000 40669159503903 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2798509737/5000000000 : ℝ)^35 ≤ (47127820612519/100000000000000 : ℝ)^27 := by
    have hnat : (2798509737 : ℕ)^35*100000000000000^27 ≤ 47127820612519^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2798509737 5000000000 47127820612519 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1973671131/10000000000 : ℝ), (249773301/500000000 : ℝ), (2798509737/5000000000 : ℝ)] ![(305075496943/2500000000000 : ℝ), (40669159503903/100000000000000 : ℝ), (47127820612519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1973671131/10000000000 : ℝ)|^35 ≤ (305075496943/2500000000000 : ℝ)^27
        have hw : |(-1973671131/10000000000 : ℝ)|=(1973671131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(249773301/500000000 : ℝ)|^35 ≤ (40669159503903/100000000000000 : ℝ)^27
        have hw : |(249773301/500000000 : ℝ)|=(249773301/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2798509737/5000000000 : ℝ)|^35 ≤ (47127820612519/100000000000000 : ℝ)^27
        have hw : |(2798509737/5000000000 : ℝ)|=(2798509737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (176980243/500000000 : ℝ)*x 0 + (6820608091/10000000000 : ℝ)*x 1 + (-130170727/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176980243/500000000 : ℝ)^35 ≤ (3252533425541/12500000000000 : ℝ)^27 := by
    have hnat : (176980243 : ℕ)^35*12500000000000^27 ≤ 3252533425541^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176980243 500000000 3252533425541 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6820608091/10000000000 : ℝ)^35 ≤ (60895541216339/100000000000000 : ℝ)^27 := by
    have hnat : (6820608091 : ℕ)^35*100000000000000^27 ≤ 60895541216339^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6820608091 10000000000 60895541216339 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130170727/625000000 : ℝ)^35 ≤ (261683827253/2000000000000 : ℝ)^27 := by
    have hnat : (130170727 : ℕ)^35*2000000000000^27 ≤ 261683827253^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130170727 625000000 261683827253 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(176980243/500000000 : ℝ), (6820608091/10000000000 : ℝ), (-130170727/625000000 : ℝ)] ![(3252533425541/12500000000000 : ℝ), (60895541216339/100000000000000 : ℝ), (261683827253/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(176980243/500000000 : ℝ)|^35 ≤ (3252533425541/12500000000000 : ℝ)^27
        have hw : |(176980243/500000000 : ℝ)|=(176980243/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6820608091/10000000000 : ℝ)|^35 ≤ (60895541216339/100000000000000 : ℝ)^27
        have hw : |(6820608091/10000000000 : ℝ)|=(6820608091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130170727/625000000 : ℝ)|^35 ≤ (261683827253/2000000000000 : ℝ)^27
        have hw : |(-130170727/625000000 : ℝ)|=(130170727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3097865889/10000000000 : ℝ)*x 0 + (1162096249/2500000000 : ℝ)*x 1 + (5032872229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3097865889/10000000000 : ℝ)^35 ≤ (21891037739107/100000000000000 : ℝ)^27 := by
    have hnat : (3097865889 : ℕ)^35*100000000000000^27 ≤ 21891037739107^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3097865889 10000000000 21891037739107 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1162096249/2500000000 : ℝ)^35 ≤ (9261150483559/25000000000000 : ℝ)^27 := by
    have hnat : (1162096249 : ℕ)^35*25000000000000^27 ≤ 9261150483559^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162096249 2500000000 9261150483559 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5032872229/10000000000 : ℝ)^35 ≤ (1026609008027/2500000000000 : ℝ)^27 := by
    have hnat : (5032872229 : ℕ)^35*2500000000000^27 ≤ 1026609008027^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032872229 10000000000 1026609008027 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3097865889/10000000000 : ℝ), (1162096249/2500000000 : ℝ), (5032872229/10000000000 : ℝ)] ![(21891037739107/100000000000000 : ℝ), (9261150483559/25000000000000 : ℝ), (1026609008027/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3097865889/10000000000 : ℝ)|^35 ≤ (21891037739107/100000000000000 : ℝ)^27
        have hw : |(3097865889/10000000000 : ℝ)|=(3097865889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1162096249/2500000000 : ℝ)|^35 ≤ (9261150483559/25000000000000 : ℝ)^27
        have hw : |(1162096249/2500000000 : ℝ)|=(1162096249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5032872229/10000000000 : ℝ)|^35 ≤ (1026609008027/2500000000000 : ℝ)^27
        have hw : |(5032872229/10000000000 : ℝ)|=(5032872229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2653136681/10000000000 : ℝ)*x 0 + (3849499739/10000000000 : ℝ)*x 1 + (766880041/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2653136681/10000000000 : ℝ)^35 ≤ (8953477347087/50000000000000 : ℝ)^27 := by
    have hnat : (2653136681 : ℕ)^35*50000000000000^27 ≤ 8953477347087^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653136681 10000000000 8953477347087 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3849499739/10000000000 : ℝ)^35 ≤ (1450544734379/5000000000000 : ℝ)^27 := by
    have hnat : (3849499739 : ℕ)^35*5000000000000^27 ≤ 1450544734379^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3849499739 10000000000 1450544734379 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (766880041/1250000000 : ℝ)^35 ≤ (13270537650541/25000000000000 : ℝ)^27 := by
    have hnat : (766880041 : ℕ)^35*25000000000000^27 ≤ 13270537650541^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766880041 1250000000 13270537650541 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2653136681/10000000000 : ℝ), (3849499739/10000000000 : ℝ), (766880041/1250000000 : ℝ)] ![(8953477347087/50000000000000 : ℝ), (1450544734379/5000000000000 : ℝ), (13270537650541/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2653136681/10000000000 : ℝ)|^35 ≤ (8953477347087/50000000000000 : ℝ)^27
        have hw : |(-2653136681/10000000000 : ℝ)|=(2653136681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3849499739/10000000000 : ℝ)|^35 ≤ (1450544734379/5000000000000 : ℝ)^27
        have hw : |(3849499739/10000000000 : ℝ)|=(3849499739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(766880041/1250000000 : ℝ)|^35 ≤ (13270537650541/25000000000000 : ℝ)^27
        have hw : |(766880041/1250000000 : ℝ)|=(766880041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5832080369/10000000000 : ℝ)*x 0 + (23012459/10000000000 : ℝ)*x 1 + (294059587/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5832080369/10000000000 : ℝ)^35 ≤ (24854662765647/50000000000000 : ℝ)^27 := by
    have hnat : (5832080369 : ℕ)^35*50000000000000^27 ≤ 24854662765647^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5832080369 10000000000 24854662765647 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23012459/10000000000 : ℝ)^35 ≤ (19023588701/50000000000000 : ℝ)^27 := by
    have hnat : (23012459 : ℕ)^35*50000000000000^27 ≤ 19023588701^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23012459 10000000000 19023588701 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (294059587/500000000 : ℝ)^35 ≤ (3140789205253/6250000000000 : ℝ)^27 := by
    have hnat : (294059587 : ℕ)^35*6250000000000^27 ≤ 3140789205253^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294059587 500000000 3140789205253 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5832080369/10000000000 : ℝ), (23012459/10000000000 : ℝ), (294059587/500000000 : ℝ)] ![(24854662765647/50000000000000 : ℝ), (19023588701/50000000000000 : ℝ), (3140789205253/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5832080369/10000000000 : ℝ)|^35 ≤ (24854662765647/50000000000000 : ℝ)^27
        have hw : |(5832080369/10000000000 : ℝ)|=(5832080369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(23012459/10000000000 : ℝ)|^35 ≤ (19023588701/50000000000000 : ℝ)^27
        have hw : |(23012459/10000000000 : ℝ)|=(23012459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(294059587/500000000 : ℝ)|^35 ≤ (3140789205253/6250000000000 : ℝ)^27
        have hw : |(294059587/500000000 : ℝ)|=(294059587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1667021817/10000000000 : ℝ)*x 0 + (2116871063/2500000000 : ℝ)*x 1 + (-1639335427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1667021817/10000000000 : ℝ)^35 ≤ (4902023309647/50000000000000 : ℝ)^27 := by
    have hnat : (1667021817 : ℕ)^35*50000000000000^27 ≤ 4902023309647^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1667021817 10000000000 4902023309647 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116871063/2500000000 : ℝ)^35 ≤ (1259413427207/1562500000000 : ℝ)^27 := by
    have hnat : (2116871063 : ℕ)^35*1562500000000^27 ≤ 1259413427207^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116871063 2500000000 1259413427207 1562500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1639335427/10000000000 : ℝ)^35 ≤ (9593494023363/100000000000000 : ℝ)^27 := by
    have hnat : (1639335427 : ℕ)^35*100000000000000^27 ≤ 9593494023363^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639335427 10000000000 9593494023363 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1667021817/10000000000 : ℝ), (2116871063/2500000000 : ℝ), (-1639335427/10000000000 : ℝ)] ![(4902023309647/50000000000000 : ℝ), (1259413427207/1562500000000 : ℝ), (9593494023363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1667021817/10000000000 : ℝ)|^35 ≤ (4902023309647/50000000000000 : ℝ)^27
        have hw : |(1667021817/10000000000 : ℝ)|=(1667021817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2116871063/2500000000 : ℝ)|^35 ≤ (1259413427207/1562500000000 : ℝ)^27
        have hw : |(2116871063/2500000000 : ℝ)|=(2116871063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1639335427/10000000000 : ℝ)|^35 ≤ (9593494023363/100000000000000 : ℝ)^27
        have hw : |(-1639335427/10000000000 : ℝ)|=(1639335427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (284017863/1000000000 : ℝ)*x 0 + (1449848051/2500000000 : ℝ)*x 1 + (4060759301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284017863/1000000000 : ℝ)^35 ≤ (19560231827503/100000000000000 : ℝ)^27 := by
    have hnat : (284017863 : ℕ)^35*100000000000000^27 ≤ 19560231827503^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284017863 1000000000 19560231827503 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1449848051/2500000000 : ℝ)^35 ≤ (12337114470939/25000000000000 : ℝ)^27 := by
    have hnat : (1449848051 : ℕ)^35*25000000000000^27 ≤ 12337114470939^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449848051 2500000000 12337114470939 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4060759301/10000000000 : ℝ)^35 ≤ (31091310275037/100000000000000 : ℝ)^27 := by
    have hnat : (4060759301 : ℕ)^35*100000000000000^27 ≤ 31091310275037^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4060759301 10000000000 31091310275037 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(284017863/1000000000 : ℝ), (1449848051/2500000000 : ℝ), (4060759301/10000000000 : ℝ)] ![(19560231827503/100000000000000 : ℝ), (12337114470939/25000000000000 : ℝ), (31091310275037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(284017863/1000000000 : ℝ)|^35 ≤ (19560231827503/100000000000000 : ℝ)^27
        have hw : |(284017863/1000000000 : ℝ)|=(284017863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1449848051/2500000000 : ℝ)|^35 ≤ (12337114470939/25000000000000 : ℝ)^27
        have hw : |(1449848051/2500000000 : ℝ)|=(1449848051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4060759301/10000000000 : ℝ)|^35 ≤ (31091310275037/100000000000000 : ℝ)^27
        have hw : |(4060759301/10000000000 : ℝ)|=(4060759301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-579276849/10000000000 : ℝ)*x 0 + (726262679/2500000000 : ℝ)*x 1 + (512758221/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (579276849/10000000000 : ℝ)^35 ≤ (1245385861953/50000000000000 : ℝ)^27 := by
    have hnat : (579276849 : ℕ)^35*50000000000000^27 ≤ 1245385861953^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579276849 10000000000 1245385861953 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (726262679/2500000000 : ℝ)^35 ≤ (10070665201971/50000000000000 : ℝ)^27 := by
    have hnat : (726262679 : ℕ)^35*50000000000000^27 ≤ 10070665201971^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726262679 2500000000 10070665201971 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512758221/625000000 : ℝ)^35 ≤ (38683948927063/50000000000000 : ℝ)^27 := by
    have hnat : (512758221 : ℕ)^35*50000000000000^27 ≤ 38683948927063^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512758221 625000000 38683948927063 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-579276849/10000000000 : ℝ), (726262679/2500000000 : ℝ), (512758221/625000000 : ℝ)] ![(1245385861953/50000000000000 : ℝ), (10070665201971/50000000000000 : ℝ), (38683948927063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-579276849/10000000000 : ℝ)|^35 ≤ (1245385861953/50000000000000 : ℝ)^27
        have hw : |(-579276849/10000000000 : ℝ)|=(579276849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(726262679/2500000000 : ℝ)|^35 ≤ (10070665201971/50000000000000 : ℝ)^27
        have hw : |(726262679/2500000000 : ℝ)|=(726262679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(512758221/625000000 : ℝ)|^35 ≤ (38683948927063/50000000000000 : ℝ)^27
        have hw : |(512758221/625000000 : ℝ)|=(512758221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8688362933/10000000000 : ℝ)*x 0 + (15053/2000000000 : ℝ)*x 1 + (2509621729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8688362933/10000000000 : ℝ)^35 ≤ (8333846482397/10000000000000 : ℝ)^27 := by
    have hnat : (8688362933 : ℕ)^35*10000000000000^27 ≤ 8333846482397^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8688362933 10000000000 8333846482397 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15053/2000000000 : ℝ)^35 ≤ (11416069/50000000000000 : ℝ)^27 := by
    have hnat : (15053 : ℕ)^35*50000000000000^27 ≤ 11416069^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15053 2000000000 11416069 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2509621729/10000000000 : ℝ)^35 ≤ (8330756164539/50000000000000 : ℝ)^27 := by
    have hnat : (2509621729 : ℕ)^35*50000000000000^27 ≤ 8330756164539^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509621729 10000000000 8330756164539 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8688362933/10000000000 : ℝ), (15053/2000000000 : ℝ), (2509621729/10000000000 : ℝ)] ![(8333846482397/10000000000000 : ℝ), (11416069/50000000000000 : ℝ), (8330756164539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8688362933/10000000000 : ℝ)|^35 ≤ (8333846482397/10000000000000 : ℝ)^27
        have hw : |(8688362933/10000000000 : ℝ)|=(8688362933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15053/2000000000 : ℝ)|^35 ≤ (11416069/50000000000000 : ℝ)^27
        have hw : |(15053/2000000000 : ℝ)|=(15053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2509621729/10000000000 : ℝ)|^35 ≤ (8330756164539/50000000000000 : ℝ)^27
        have hw : |(2509621729/10000000000 : ℝ)|=(2509621729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (441064217/1000000000 : ℝ)*x 0 + (1691134623/2500000000 : ℝ)*x 1 + (-25344167/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441064217/1000000000 : ℝ)^35 ≤ (17303702402931/50000000000000 : ℝ)^27 := by
    have hnat : (441064217 : ℕ)^35*50000000000000^27 ≤ 17303702402931^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441064217 1000000000 17303702402931 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1691134623/2500000000 : ℝ)^35 ≤ (60247408613473/100000000000000 : ℝ)^27 := by
    have hnat : (1691134623 : ℕ)^35*100000000000000^27 ≤ 60247408613473^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691134623 2500000000 60247408613473 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25344167/250000000 : ℝ)^35 ≤ (5145186576083/100000000000000 : ℝ)^27 := by
    have hnat : (25344167 : ℕ)^35*100000000000000^27 ≤ 5145186576083^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25344167 250000000 5145186576083 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(441064217/1000000000 : ℝ), (1691134623/2500000000 : ℝ), (-25344167/250000000 : ℝ)] ![(17303702402931/50000000000000 : ℝ), (60247408613473/100000000000000 : ℝ), (5145186576083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(441064217/1000000000 : ℝ)|^35 ≤ (17303702402931/50000000000000 : ℝ)^27
        have hw : |(441064217/1000000000 : ℝ)|=(441064217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1691134623/2500000000 : ℝ)|^35 ≤ (60247408613473/100000000000000 : ℝ)^27
        have hw : |(1691134623/2500000000 : ℝ)|=(1691134623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25344167/250000000 : ℝ)|^35 ≤ (5145186576083/100000000000000 : ℝ)^27
        have hw : |(-25344167/250000000 : ℝ)|=(25344167/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1436144957/5000000000 : ℝ)*x 0 + (338727157/1000000000 : ℝ)*x 1 + (1589024129/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1436144957/5000000000 : ℝ)^35 ≤ (9923693023113/50000000000000 : ℝ)^27 := by
    have hnat : (1436144957 : ℕ)^35*50000000000000^27 ≤ 9923693023113^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1436144957 5000000000 9923693023113 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338727157/1000000000 : ℝ)^35 ≤ (24577987463279/100000000000000 : ℝ)^27 := by
    have hnat : (338727157 : ℕ)^35*100000000000000^27 ≤ 24577987463279^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338727157 1000000000 24577987463279 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1589024129/2500000000 : ℝ)^35 ≤ (6946828308479/12500000000000 : ℝ)^27 := by
    have hnat : (1589024129 : ℕ)^35*12500000000000^27 ≤ 6946828308479^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589024129 2500000000 6946828308479 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1436144957/5000000000 : ℝ), (338727157/1000000000 : ℝ), (1589024129/2500000000 : ℝ)] ![(9923693023113/50000000000000 : ℝ), (24577987463279/100000000000000 : ℝ), (6946828308479/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1436144957/5000000000 : ℝ)|^35 ≤ (9923693023113/50000000000000 : ℝ)^27
        have hw : |(1436144957/5000000000 : ℝ)|=(1436144957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338727157/1000000000 : ℝ)|^35 ≤ (24577987463279/100000000000000 : ℝ)^27
        have hw : |(338727157/1000000000 : ℝ)|=(338727157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1589024129/2500000000 : ℝ)|^35 ≤ (6946828308479/12500000000000 : ℝ)^27
        have hw : |(1589024129/2500000000 : ℝ)|=(1589024129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-790420091/5000000000 : ℝ)*x 0 + (786391899/1250000000 : ℝ)*x 1 + (4547759317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (790420091/5000000000 : ℝ)^35 ≤ (183042287051/2000000000000 : ℝ)^27 := by
    have hnat : (790420091 : ℕ)^35*2000000000000^27 ≤ 183042287051^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790420091 5000000000 183042287051 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (786391899/1250000000 : ℝ)^35 ≤ (2193578408891/4000000000000 : ℝ)^27 := by
    have hnat : (786391899 : ℕ)^35*4000000000000^27 ≤ 2193578408891^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786391899 1250000000 2193578408891 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4547759317/10000000000 : ℝ)^35 ≤ (2250526587761/6250000000000 : ℝ)^27 := by
    have hnat : (4547759317 : ℕ)^35*6250000000000^27 ≤ 2250526587761^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547759317 10000000000 2250526587761 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-790420091/5000000000 : ℝ), (786391899/1250000000 : ℝ), (4547759317/10000000000 : ℝ)] ![(183042287051/2000000000000 : ℝ), (2193578408891/4000000000000 : ℝ), (2250526587761/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-790420091/5000000000 : ℝ)|^35 ≤ (183042287051/2000000000000 : ℝ)^27
        have hw : |(-790420091/5000000000 : ℝ)|=(790420091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(786391899/1250000000 : ℝ)|^35 ≤ (2193578408891/4000000000000 : ℝ)^27
        have hw : |(786391899/1250000000 : ℝ)|=(786391899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4547759317/10000000000 : ℝ)|^35 ≤ (2250526587761/6250000000000 : ℝ)^27
        have hw : |(4547759317/10000000000 : ℝ)|=(4547759317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (834433379/1000000000 : ℝ)*x 0 + (549091/2000000000 : ℝ)*x 1 + (74759261/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834433379/1000000000 : ℝ)^35 ≤ (79086127560817/100000000000000 : ℝ)^27 := by
    have hnat : (834433379 : ℕ)^35*100000000000000^27 ≤ 79086127560817^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834433379 1000000000 79086127560817 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549091/2000000000 : ℝ)^35 ≤ (483525009/20000000000000 : ℝ)^27 := by
    have hnat : (549091 : ℕ)^35*20000000000000^27 ≤ 483525009^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549091 2000000000 483525009 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74759261/250000000 : ℝ)^35 ≤ (2613931850593/12500000000000 : ℝ)^27 := by
    have hnat : (74759261 : ℕ)^35*12500000000000^27 ≤ 2613931850593^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74759261 250000000 2613931850593 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(834433379/1000000000 : ℝ), (549091/2000000000 : ℝ), (74759261/250000000 : ℝ)] ![(79086127560817/100000000000000 : ℝ), (483525009/20000000000000 : ℝ), (2613931850593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(834433379/1000000000 : ℝ)|^35 ≤ (79086127560817/100000000000000 : ℝ)^27
        have hw : |(834433379/1000000000 : ℝ)|=(834433379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549091/2000000000 : ℝ)|^35 ≤ (483525009/20000000000000 : ℝ)^27
        have hw : |(549091/2000000000 : ℝ)|=(549091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74759261/250000000 : ℝ)|^35 ≤ (2613931850593/12500000000000 : ℝ)^27
        have hw : |(74759261/250000000 : ℝ)|=(74759261/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (591516601/2500000000 : ℝ)*x 0 + (949756239/1250000000 : ℝ)*x 1 + (-1128580393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (591516601/2500000000 : ℝ)^35 ≤ (964791444979/6250000000000 : ℝ)^27 := by
    have hnat : (591516601 : ℕ)^35*6250000000000^27 ≤ 964791444979^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591516601 2500000000 964791444979 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (949756239/1250000000 : ℝ)^35 ≤ (35020684713901/50000000000000 : ℝ)^27 := by
    have hnat : (949756239 : ℕ)^35*50000000000000^27 ≤ 35020684713901^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949756239 1250000000 35020684713901 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128580393/5000000000 : ℝ)^35 ≤ (7260983717869/50000000000000 : ℝ)^27 := by
    have hnat : (1128580393 : ℕ)^35*50000000000000^27 ≤ 7260983717869^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128580393 5000000000 7260983717869 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(591516601/2500000000 : ℝ), (949756239/1250000000 : ℝ), (-1128580393/5000000000 : ℝ)] ![(964791444979/6250000000000 : ℝ), (35020684713901/50000000000000 : ℝ), (7260983717869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(591516601/2500000000 : ℝ)|^35 ≤ (964791444979/6250000000000 : ℝ)^27
        have hw : |(591516601/2500000000 : ℝ)|=(591516601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(949756239/1250000000 : ℝ)|^35 ≤ (35020684713901/50000000000000 : ℝ)^27
        have hw : |(949756239/1250000000 : ℝ)|=(949756239/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1128580393/5000000000 : ℝ)|^35 ≤ (7260983717869/50000000000000 : ℝ)^27
        have hw : |(-1128580393/5000000000 : ℝ)|=(1128580393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309083_s1_s1_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2893785867/5000000000 : ℝ)*x 0 + (3723247573/10000000000 : ℝ)*x 1 + (804515629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2893785867/5000000000 : ℝ)^35 ≤ (9843622304691/20000000000000 : ℝ)^27 := by
    have hnat : (2893785867 : ℕ)^35*20000000000000^27 ≤ 9843622304691^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2893785867 5000000000 9843622304691 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3723247573/10000000000 : ℝ)^35 ≤ (27783545614549/100000000000000 : ℝ)^27 := by
    have hnat : (3723247573 : ℕ)^35*100000000000000^27 ≤ 27783545614549^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3723247573 10000000000 27783545614549 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (804515629/2500000000 : ℝ)^35 ≤ (11499171422573/50000000000000 : ℝ)^27 := by
    have hnat : (804515629 : ℕ)^35*50000000000000^27 ≤ 11499171422573^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804515629 2500000000 11499171422573 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2893785867/5000000000 : ℝ), (3723247573/10000000000 : ℝ), (804515629/2500000000 : ℝ)] ![(9843622304691/20000000000000 : ℝ), (27783545614549/100000000000000 : ℝ), (11499171422573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2893785867/5000000000 : ℝ)|^35 ≤ (9843622304691/20000000000000 : ℝ)^27
        have hw : |(2893785867/5000000000 : ℝ)|=(2893785867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3723247573/10000000000 : ℝ)|^35 ≤ (27783545614549/100000000000000 : ℝ)^27
        have hw : |(3723247573/10000000000 : ℝ)|=(3723247573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(804515629/2500000000 : ℝ)|^35 ≤ (11499171422573/50000000000000 : ℝ)^27
        have hw : |(804515629/2500000000 : ℝ)|=(804515629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309083_s1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((39519/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39519/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((82627/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(82627/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43799/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43799/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((58687/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58687/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((56283/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(56283/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2067/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2067/3125 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (39519/50000 : ℝ) ^ (69/16 : ℝ) ≤ (18129570064873145629/50000000000000000000 : ℝ) := by
    have hpowers : (39519/50000 : ℝ)^69 ≤ (18129570064873145629/50000000000000000000 : ℝ)^16 := by
      have hnat : (39519 : ℕ)^69*50000000000000000000^16 ≤ 18129570064873145629^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39519 50000 18129570064873145629 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39519/50000 : ℝ)) (X := (18129570064873145629/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (68129570064873145629/50000000000000000000 : ℝ) ≤ (2685945890941337/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (68129570064873145629/50000000000000000000 : ℝ)^16 ≤ (2685945890941337/2500000000000000 : ℝ)^69 := by
      have hnat : (68129570064873145629 : ℕ)^16*2500000000000000^69 ≤ 2685945890941337^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68129570064873145629 50000000000000000000 2685945890941337 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2685945890941337/2500000000000000 : ℝ)) (X := (68129570064873145629/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (43129570064873145629/25000000000000000000 : ℝ) ≤ (5673986433849983/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (43129570064873145629/25000000000000000000 : ℝ)^16 ≤ (5673986433849983/5000000000000000 : ℝ)^69 := by
      have hnat : (43129570064873145629 : ℕ)^16*5000000000000000^69 ≤ 5673986433849983^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43129570064873145629 25000000000000000000 5673986433849983 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5673986433849983/5000000000000000 : ℝ)) (X := (43129570064873145629/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(185945890941337/1975950000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(302094651967309/3951900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (39519/50000 : ℝ)) (alpha := (185945890941337/1975950000000000 : ℝ)) (beta := (302094651967309/3951900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (39519/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(185945890941337/1975950000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(302094651967309/3951900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (82627/100000 : ℝ) ^ (69/16 : ℝ) ≤ (21956270050834797669/50000000000000000000 : ℝ) := by
    have hpowers : (82627/100000 : ℝ)^69 ≤ (21956270050834797669/50000000000000000000 : ℝ)^16 := by
      have hnat : (82627 : ℕ)^69*50000000000000000000^16 ≤ 21956270050834797669^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82627 100000 21956270050834797669 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (82627/100000 : ℝ)) (X := (21956270050834797669/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (71956270050834797669/50000000000000000000 : ℝ) ≤ (2176158628509141/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (71956270050834797669/50000000000000000000 : ℝ)^16 ≤ (2176158628509141/2000000000000000 : ℝ)^69 := by
      have hnat : (71956270050834797669 : ℕ)^16*2000000000000000^69 ≤ 2176158628509141^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71956270050834797669 50000000000000000000 2176158628509141 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2176158628509141/2000000000000000 : ℝ)) (X := (71956270050834797669/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (46956270050834797669/25000000000000000000 : ℝ) ≤ (1446735388057597/1250000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (46956270050834797669/25000000000000000000 : ℝ)^16 ≤ (1446735388057597/1250000000000000 : ℝ)^69 := by
      have hnat : (46956270050834797669 : ℕ)^16*1250000000000000^69 ≤ 1446735388057597^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46956270050834797669 25000000000000000000 1446735388057597 1250000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1446735388057597/1250000000000000 : ℝ)) (X := (46956270050834797669/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(176158628509141/1652540000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(693089961915071/8262700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (82627/100000 : ℝ)) (alpha := (176158628509141/1652540000000000 : ℝ)) (beta := (693089961915071/8262700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (82627/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(176158628509141/1652540000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(693089961915071/8262700000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (43799/50000 : ℝ) ^ (69/16 : ℝ) ≤ (14123625907180513737/25000000000000000000 : ℝ) := by
    have hpowers : (43799/50000 : ℝ)^69 ≤ (14123625907180513737/25000000000000000000 : ℝ)^16 := by
      have hnat : (43799 : ℕ)^69*25000000000000000000^16 ≤ 14123625907180513737^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43799 50000 14123625907180513737 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43799/50000 : ℝ)) (X := (14123625907180513737/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (39123625907180513737/25000000000000000000 : ℝ) ≤ (2218866808385097/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (39123625907180513737/25000000000000000000 : ℝ)^16 ≤ (2218866808385097/2000000000000000 : ℝ)^69 := by
      have hnat : (39123625907180513737 : ℕ)^16*2000000000000000^69 ≤ 2218866808385097^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39123625907180513737 25000000000000000000 2218866808385097 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2218866808385097/2000000000000000 : ℝ)) (X := (39123625907180513737/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (26623625907180513737/12500000000000000000 : ℝ) ≤ (11916282692351353/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (26623625907180513737/12500000000000000000 : ℝ)^16 ≤ (11916282692351353/10000000000000000 : ℝ)^69 := by
      have hnat : (26623625907180513737 : ℕ)^16*10000000000000000^69 ≤ 11916282692351353^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26623625907180513737 12500000000000000000 11916282692351353 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11916282692351353/10000000000000000 : ℝ)) (X := (26623625907180513737/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(218866808385097/1751960000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(29355308943781/312850000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (43799/50000 : ℝ)) (alpha := (218866808385097/1751960000000000 : ℝ)) (beta := (29355308943781/312850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (43799/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(218866808385097/1751960000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(29355308943781/312850000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1973671131/10000000000 : ℝ)*X 0 0+(249773301/500000000 : ℝ)*X 0 1+(2798509737/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((176980243/500000000 : ℝ)*X 2 0+(6820608091/10000000000 : ℝ)*X 2 1+(-130170727/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3097865889/10000000000 : ℝ)*X 0 0+(1162096249/2500000000 : ℝ)*X 0 1+(5032872229/10000000000 : ℝ)*X 0 2+(3097865889/10000000000 : ℝ)*X 1 0+(1162096249/2500000000 : ℝ)*X 1 1+(5032872229/10000000000 : ℝ)*X 1 2+(3097865889/10000000000 : ℝ)*X 2 0+(1162096249/2500000000 : ℝ)*X 2 1+(5032872229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2653136681/10000000000 : ℝ)*X 0 0+(3849499739/10000000000 : ℝ)*X 0 1+(766880041/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5832080369/10000000000 : ℝ)*X 1 0+(23012459/10000000000 : ℝ)*X 1 1+(294059587/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1667021817/10000000000 : ℝ)*X 2 0+(2116871063/2500000000 : ℝ)*X 2 1+(-1639335427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((284017863/1000000000 : ℝ)*X 0 0+(1449848051/2500000000 : ℝ)*X 0 1+(4060759301/10000000000 : ℝ)*X 0 2+(284017863/1000000000 : ℝ)*X 1 0+(1449848051/2500000000 : ℝ)*X 1 1+(4060759301/10000000000 : ℝ)*X 1 2+(284017863/1000000000 : ℝ)*X 2 0+(1449848051/2500000000 : ℝ)*X 2 1+(4060759301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-579276849/10000000000 : ℝ)*X 0 0+(726262679/2500000000 : ℝ)*X 0 1+(512758221/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((8688362933/10000000000 : ℝ)*X 1 0+(15053/2000000000 : ℝ)*X 1 1+(2509621729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((441064217/1000000000 : ℝ)*X 2 0+(1691134623/2500000000 : ℝ)*X 2 1+(-25344167/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1436144957/5000000000 : ℝ)*X 0 0+(338727157/1000000000 : ℝ)*X 0 1+(1589024129/2500000000 : ℝ)*X 0 2+(1436144957/5000000000 : ℝ)*X 1 0+(338727157/1000000000 : ℝ)*X 1 1+(1589024129/2500000000 : ℝ)*X 1 2+(1436144957/5000000000 : ℝ)*X 2 0+(338727157/1000000000 : ℝ)*X 2 1+(1589024129/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-790420091/5000000000 : ℝ)*X 0 0+(786391899/1250000000 : ℝ)*X 0 1+(4547759317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((834433379/1000000000 : ℝ)*X 1 0+(549091/2000000000 : ℝ)*X 1 1+(74759261/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((591516601/2500000000 : ℝ)*X 2 0+(949756239/1250000000 : ℝ)*X 2 1+(-1128580393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((2893785867/5000000000 : ℝ)*X 0 0+(3723247573/10000000000 : ℝ)*X 0 1+(804515629/2500000000 : ℝ)*X 0 2+(2893785867/5000000000 : ℝ)*X 1 0+(3723247573/10000000000 : ℝ)*X 1 1+(804515629/2500000000 : ℝ)*X 1 2+(2893785867/5000000000 : ℝ)*X 2 0+(3723247573/10000000000 : ℝ)*X 2 1+(804515629/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309083_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((58687/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58687/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4778501369344421472290363675547/317818821228860000000000000000000000 : ℝ) := by norm_num
    linear_combination (83746068493/125000000000 : ℝ)*(base7) + (6444113/500000000000 : ℝ)*(base23) + (418736517219/1000000000000 : ℝ)*(base49) + (214912373881/1000000000000 : ℝ)*(base60) + (2215701446283/1000000000000 : ℝ)*(major_s1_0) + (2215701446283/1000000000000 : ℝ)*(major_s1_1) + (2215701446283/1000000000000 : ℝ)*(major_s1_2) + (70158093/1000000000000 : ℝ)*(sp_s1_0) + (20271623/500000000000 : ℝ)*(sp_s1_6) + (2632059498391/1000000000000 : ℝ)*(sp_s1_7) + (52642922609/20000000000 : ℝ)*(sp_s1_8) + (164508327639/62500000000 : ℝ)*(sp_s1_9) + (2061289503679/1000000000000 : ℝ)*(sp_s1_13) + (3294793/200000000000 : ℝ)*(sp_s1_14) + (1391361498981/1000000000000 : ℝ)*(f.failure) + (52642922609/20000000000 : ℝ)*(f.sum) + (189340118644034070771/723795994600000000000000000000000 : ℝ)*base63 + (134263547592469/156425000000000000000000000 : ℝ)*base65 + (1808658373820021/1652540000000000000000000000 : ℝ)*base67 + (543687790197707/1751960000000000000000000000 : ℝ)*base69 + (164339464665855403/686862175000000000000000000000 : ℝ)*base71 + (166127181583553/439100000000000000000000000 : ℝ)*base73 + (6831218780049467/8262700000000000000000000000 : ℝ)*base75 + (85760488556919/219550000000000000000000000 : ℝ)*base77 + (109382442245772057/4535189462500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (72693/100000000000000000 : ℝ)*base86 + (72693/100000000000000000 : ℝ)*base88 + (72693/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((56283/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(56283/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1334126978618248545560582537703/113506721867450000000000000000000000 : ℝ) := by norm_num
    linear_combination (30250415443/125000000000 : ℝ)*(base7) + (23265927/1000000000000 : ℝ)*(base33) + (653176624291/1000000000000 : ℝ)*(base40) + (1161970609/3906250000 : ℝ)*(base49) + (513898801303/1000000000000 : ℝ)*(base60) + (2312526483521/1000000000000 : ℝ)*(major_s1_0) + (289068718681/125000000000 : ℝ)*(major_s1_1) + (289068718681/125000000000 : ℝ)*(major_s1_2) + (11984371/500000000000 : ℝ)*(sp_s1_2) + (756395302967/250000000000 : ℝ)*(sp_s1_14) + (1512666724927/500000000000 : ℝ)*(sp_s1_15) + (7563834943/2500000000 : ℝ)*(sp_s1_16) + (847090614609/500000000000 : ℝ)*(sp_s1_20) + (28062011/125000000000 : ℝ)*(sp_s1_22) + (726088952837/500000000000 : ℝ)*(f.failure) + (756395302967/250000000000 : ℝ)*(f.sum) + (46821898190267352897/90474499325000000000000000000000 : ℝ)*base63 + (889853970823/78212500000000000000000000 : ℝ)*base64 + (47659169866903/206567500000000000000000000 : ℝ)*base67 + (47229397872133/109497500000000000000000000 : ℝ)*base68 + (1385828527905702989/12363519150000000000000000000000 : ℝ)*base70 + (1157054867462071/3951900000000000000000000000 : ℝ)*base72 + (37047849217293/129104687500000000000000000 : ℝ)*base75 + (973963496324713/1975950000000000000000000000 : ℝ)*base76 + (5672398294484044657/326533641300000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (33739/50000000000000000 : ℝ)*base87 + (33739/50000000000000000 : ℝ)*base89 + (33739/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2067/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2067/3125 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (88031450821995787624644396873737/4767282318432900000000000000000000000 : ℝ) := by norm_num
    linear_combination (181834733343/250000000000 : ℝ)*(base7) + (5066887/500000000000 : ℝ)*(base11) + (96274510001/250000000000 : ℝ)*(base40) + (248043910871/1000000000000 : ℝ)*(base49) + (2474146696423/1000000000000 : ℝ)*(major_s1_0) + (2474146696423/1000000000000 : ℝ)*(major_s1_1) + (2474146696423/1000000000000 : ℝ)*(major_s1_2) + (14972631/125000000000 : ℝ)*(sp_s1_2) + (49631187/500000000000 : ℝ)*(sp_s1_9) + (3237881/1000000000000 : ℝ)*(sp_s1_15) + (2951805047033/1000000000000 : ℝ)*(sp_s1_21) + (2951811942927/1000000000000 : ℝ)*(sp_s1_22) + (590319227477/200000000000 : ℝ)*(sp_s1_23) + (1140496250369/500000000000 : ℝ)*(sp_s1_27) + (776826783683/500000000000 : ℝ)*(f.failure) + (368976897601/125000000000 : ℝ)*(f.sum) + (440461921356000991109/723795994600000000000000000000000 : ℝ)*base62 + (201858062435513/312850000000000000000000000 : ℝ)*base65 + (240072108427317/1652540000000000000000000000 : ℝ)*base67 + (418748534683989/1751960000000000000000000000 : ℝ)*base68 + (82404585227720909/772719946875000000000000000000 : ℝ)*base71 + (1086828467757323/3951900000000000000000000000 : ℝ)*base72 + (2629835238529933/8262700000000000000000000000 : ℝ)*base74 + (1613106932814601/1975950000000000000000000000 : ℝ)*base77 + (74552356126809775723/163266820650000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (16701/50000000000000000 : ℝ)*base87 + (16701/50000000000000000 : ℝ)*base89 + (16701/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((39519/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39519/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((82627/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(82627/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43799/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43799/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((58687/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58687/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((56283/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(56283/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2067/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2067/3125 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309083_s1 p hpa hpb X hX hprev0

#print axioms solution
