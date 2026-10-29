-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c321054_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:41:25.145419+00:00
-- url     : https://prove2.me/submissions/b9648487-3b0f-4466-b5b0-c20018612239

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
theorem collision_support_c321054_s2_s2_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-52141447/400000000 : ℝ)*x 0 + (1131889513/2500000000 : ℝ)*x 1 + (-1532004649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52141447/400000000 : ℝ)^83 ≤ (8013259342067/100000000000000 : ℝ)^67 := by
    have hnat : (52141447 : ℕ)^83*100000000000000^67 ≤ 8013259342067^67*400000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52141447 400000000 8013259342067 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131889513/2500000000 : ℝ)^83 ≤ (37469880043343/100000000000000 : ℝ)^67 := by
    have hnat : (1131889513 : ℕ)^83*100000000000000^67 ≤ 37469880043343^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131889513 2500000000 37469880043343 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1532004649/2500000000 : ℝ)^83 ≤ (27258430295837/50000000000000 : ℝ)^67 := by
    have hnat : (1532004649 : ℕ)^83*50000000000000^67 ≤ 27258430295837^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532004649 2500000000 27258430295837 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52141447/400000000 : ℝ), (1131889513/2500000000 : ℝ), (-1532004649/2500000000 : ℝ)] ![(8013259342067/100000000000000 : ℝ), (37469880043343/100000000000000 : ℝ), (27258430295837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52141447/400000000 : ℝ)|^83 ≤ (8013259342067/100000000000000 : ℝ)^67
        have hw : |(-52141447/400000000 : ℝ)|=(52141447/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131889513/2500000000 : ℝ)|^83 ≤ (37469880043343/100000000000000 : ℝ)^67
        have hw : |(1131889513/2500000000 : ℝ)|=(1131889513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1532004649/2500000000 : ℝ)|^83 ≤ (27258430295837/50000000000000 : ℝ)^67
        have hw : |(-1532004649/2500000000 : ℝ)|=(1532004649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (542343583/1000000000 : ℝ)*x 0 + (-1104481811/5000000000 : ℝ)*x 1 + (-569191417/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542343583/1000000000 : ℝ)^83 ≤ (2928853769109/6250000000000 : ℝ)^67 := by
    have hnat : (542343583 : ℕ)^83*6250000000000^67 ≤ 2928853769109^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542343583 1000000000 2928853769109 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104481811/5000000000 : ℝ)^83 ≤ (3080398287109/20000000000000 : ℝ)^67 := by
    have hnat : (1104481811 : ℕ)^83*20000000000000^67 ≤ 3080398287109^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104481811 5000000000 3080398287109 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569191417/1250000000 : ℝ)^83 ≤ (9434087059387/25000000000000 : ℝ)^67 := by
    have hnat : (569191417 : ℕ)^83*25000000000000^67 ≤ 9434087059387^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569191417 1250000000 9434087059387 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542343583/1000000000 : ℝ), (-1104481811/5000000000 : ℝ), (-569191417/1250000000 : ℝ)] ![(2928853769109/6250000000000 : ℝ), (3080398287109/20000000000000 : ℝ), (9434087059387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542343583/1000000000 : ℝ)|^83 ≤ (2928853769109/6250000000000 : ℝ)^67
        have hw : |(542343583/1000000000 : ℝ)|=(542343583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1104481811/5000000000 : ℝ)|^83 ≤ (3080398287109/20000000000000 : ℝ)^67
        have hw : |(-1104481811/5000000000 : ℝ)|=(1104481811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-569191417/1250000000 : ℝ)|^83 ≤ (9434087059387/25000000000000 : ℝ)^67
        have hw : |(-569191417/1250000000 : ℝ)|=(569191417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5011003443/10000000000 : ℝ)*x 0 + (1000734579/2000000000 : ℝ)*x 1 + (1087039919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5011003443/10000000000 : ℝ)^83 ≤ (42487866935471/100000000000000 : ℝ)^67 := by
    have hnat : (5011003443 : ℕ)^83*100000000000000^67 ≤ 42487866935471^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011003443 10000000000 42487866935471 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000734579/2000000000 : ℝ)^83 ≤ (42410882298861/100000000000000 : ℝ)^67 := by
    have hnat : (1000734579 : ℕ)^83*100000000000000^67 ≤ 42410882298861^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000734579 2000000000 42410882298861 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087039919/5000000000 : ℝ)^83 ≤ (3020250147749/20000000000000 : ℝ)^67 := by
    have hnat : (1087039919 : ℕ)^83*20000000000000^67 ≤ 3020250147749^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087039919 5000000000 3020250147749 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5011003443/10000000000 : ℝ), (1000734579/2000000000 : ℝ), (1087039919/5000000000 : ℝ)] ![(42487866935471/100000000000000 : ℝ), (42410882298861/100000000000000 : ℝ), (3020250147749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5011003443/10000000000 : ℝ)|^83 ≤ (42487866935471/100000000000000 : ℝ)^67
        have hw : |(5011003443/10000000000 : ℝ)|=(5011003443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000734579/2000000000 : ℝ)|^83 ≤ (42410882298861/100000000000000 : ℝ)^67
        have hw : |(1000734579/2000000000 : ℝ)|=(1000734579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087039919/5000000000 : ℝ)|^83 ≤ (3020250147749/20000000000000 : ℝ)^67
        have hw : |(1087039919/5000000000 : ℝ)|=(1087039919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_6 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5097674893/10000000000 : ℝ)*x 0 + (127286021/250000000 : ℝ)*x 1 + (-489528019/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5097674893/10000000000 : ℝ)^83 ≤ (10850028077441/25000000000000 : ℝ)^67 := by
    have hnat : (5097674893 : ℕ)^83*25000000000000^67 ≤ 10850028077441^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097674893 10000000000 10850028077441 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127286021/250000000 : ℝ)^83 ≤ (10833593101711/25000000000000 : ℝ)^67 := by
    have hnat : (127286021 : ℕ)^83*25000000000000^67 ≤ 10833593101711^67*250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127286021 250000000 10833593101711 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (489528019/2500000000 : ℝ)^83 ≤ (13265515270639/100000000000000 : ℝ)^67 := by
    have hnat : (489528019 : ℕ)^83*100000000000000^67 ≤ 13265515270639^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489528019 2500000000 13265515270639 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5097674893/10000000000 : ℝ), (127286021/250000000 : ℝ), (-489528019/2500000000 : ℝ)] ![(10850028077441/25000000000000 : ℝ), (10833593101711/25000000000000 : ℝ), (13265515270639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5097674893/10000000000 : ℝ)|^83 ≤ (10850028077441/25000000000000 : ℝ)^67
        have hw : |(5097674893/10000000000 : ℝ)|=(5097674893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(127286021/250000000 : ℝ)|^83 ≤ (10833593101711/25000000000000 : ℝ)^67
        have hw : |(127286021/250000000 : ℝ)|=(127286021/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-489528019/2500000000 : ℝ)|^83 ≤ (13265515270639/100000000000000 : ℝ)^67
        have hw : |(-489528019/2500000000 : ℝ)|=(489528019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_7 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-6357057/50000000 : ℝ)*x 0 + (54739011/125000000 : ℝ)*x 1 + (-6287201481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6357057/50000000 : ℝ)^83 ≤ (388467131699/5000000000000 : ℝ)^67 := by
    have hnat : (6357057 : ℕ)^83*5000000000000^67 ≤ 388467131699^67*50000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6357057 50000000 388467131699 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54739011/125000000 : ℝ)^83 ≤ (17977032210721/50000000000000 : ℝ)^67 := by
    have hnat : (54739011 : ℕ)^83*50000000000000^67 ≤ 17977032210721^67*125000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54739011 125000000 17977032210721 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6287201481/10000000000 : ℝ)^83 ≤ (5627659292941/10000000000000 : ℝ)^67 := by
    have hnat : (6287201481 : ℕ)^83*10000000000000^67 ≤ 5627659292941^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6287201481 10000000000 5627659292941 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6357057/50000000 : ℝ), (54739011/125000000 : ℝ), (-6287201481/10000000000 : ℝ)] ![(388467131699/5000000000000 : ℝ), (17977032210721/50000000000000 : ℝ), (5627659292941/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6357057/50000000 : ℝ)|^83 ≤ (388467131699/5000000000000 : ℝ)^67
        have hw : |(-6357057/50000000 : ℝ)|=(6357057/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54739011/125000000 : ℝ)|^83 ≤ (17977032210721/50000000000000 : ℝ)^67
        have hw : |(54739011/125000000 : ℝ)|=(54739011/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6287201481/10000000000 : ℝ)|^83 ≤ (5627659292941/10000000000000 : ℝ)^67
        have hw : |(-6287201481/10000000000 : ℝ)|=(6287201481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_8 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2676894983/5000000000 : ℝ)*x 0 + (-468130977/2500000000 : ℝ)*x 1 + (-4900636903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676894983/5000000000 : ℝ)^83 ≤ (46117317197189/100000000000000 : ℝ)^67 := by
    have hnat : (2676894983 : ℕ)^83*100000000000000^67 ≤ 46117317197189^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676894983 5000000000 46117317197189 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468130977/2500000000 : ℝ)^83 ≤ (12551010241603/100000000000000 : ℝ)^67 := by
    have hnat : (468130977 : ℕ)^83*100000000000000^67 ≤ 12551010241603^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468130977 2500000000 12551010241603 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4900636903/10000000000 : ℝ)^83 ≤ (20665836274617/50000000000000 : ℝ)^67 := by
    have hnat : (4900636903 : ℕ)^83*50000000000000^67 ≤ 20665836274617^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4900636903 10000000000 20665836274617 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676894983/5000000000 : ℝ), (-468130977/2500000000 : ℝ), (-4900636903/10000000000 : ℝ)] ![(46117317197189/100000000000000 : ℝ), (12551010241603/100000000000000 : ℝ), (20665836274617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676894983/5000000000 : ℝ)|^83 ≤ (46117317197189/100000000000000 : ℝ)^67
        have hw : |(2676894983/5000000000 : ℝ)|=(2676894983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-468130977/2500000000 : ℝ)|^83 ≤ (12551010241603/100000000000000 : ℝ)^67
        have hw : |(-468130977/2500000000 : ℝ)|=(468130977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4900636903/10000000000 : ℝ)|^83 ≤ (20665836274617/50000000000000 : ℝ)^67
        have hw : |(-4900636903/10000000000 : ℝ)|=(4900636903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_9 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1229616243/2500000000 : ℝ)*x 0 + (670988499/1250000000 : ℝ)*x 1 + (91591289/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1229616243/2500000000 : ℝ)^83 ≤ (41518021298747/100000000000000 : ℝ)^67 := by
    have hnat : (1229616243 : ℕ)^83*100000000000000^67 ≤ 41518021298747^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229616243 2500000000 41518021298747 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (670988499/1250000000 : ℝ)^83 ≤ (46268018360541/100000000000000 : ℝ)^67 := by
    have hnat : (670988499 : ℕ)^83*100000000000000^67 ≤ 46268018360541^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670988499 1250000000 46268018360541 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91591289/500000000 : ℝ)^83 ≤ (3053490082047/25000000000000 : ℝ)^67 := by
    have hnat : (91591289 : ℕ)^83*25000000000000^67 ≤ 3053490082047^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91591289 500000000 3053490082047 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1229616243/2500000000 : ℝ), (670988499/1250000000 : ℝ), (91591289/500000000 : ℝ)] ![(41518021298747/100000000000000 : ℝ), (46268018360541/100000000000000 : ℝ), (3053490082047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1229616243/2500000000 : ℝ)|^83 ≤ (41518021298747/100000000000000 : ℝ)^67
        have hw : |(1229616243/2500000000 : ℝ)|=(1229616243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(670988499/1250000000 : ℝ)|^83 ≤ (46268018360541/100000000000000 : ℝ)^67
        have hw : |(670988499/1250000000 : ℝ)|=(670988499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(91591289/500000000 : ℝ)|^83 ≤ (3053490082047/25000000000000 : ℝ)^67
        have hw : |(91591289/500000000 : ℝ)|=(91591289/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_13 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1013657357/2000000000 : ℝ)*x 0 + (2726923463/5000000000 : ℝ)*x 1 + (-761842591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013657357/2000000000 : ℝ)^83 ≤ (10772593639153/25000000000000 : ℝ)^67 := by
    have hnat : (1013657357 : ℕ)^83*25000000000000^67 ≤ 10772593639153^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013657357 2000000000 10772593639153 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726923463/5000000000 : ℝ)^83 ≤ (47187398581173/100000000000000 : ℝ)^67 := by
    have hnat : (2726923463 : ℕ)^83*100000000000000^67 ≤ 47187398581173^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726923463 5000000000 47187398581173 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (761842591/5000000000 : ℝ)^83 ≤ (243055671101/2500000000000 : ℝ)^67 := by
    have hnat : (761842591 : ℕ)^83*2500000000000^67 ≤ 243055671101^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      761842591 5000000000 243055671101 2500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1013657357/2000000000 : ℝ), (2726923463/5000000000 : ℝ), (-761842591/5000000000 : ℝ)] ![(10772593639153/25000000000000 : ℝ), (47187398581173/100000000000000 : ℝ), (243055671101/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1013657357/2000000000 : ℝ)|^83 ≤ (10772593639153/25000000000000 : ℝ)^67
        have hw : |(1013657357/2000000000 : ℝ)|=(1013657357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726923463/5000000000 : ℝ)|^83 ≤ (47187398581173/100000000000000 : ℝ)^67
        have hw : |(2726923463/5000000000 : ℝ)|=(2726923463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-761842591/5000000000 : ℝ)|^83 ≤ (243055671101/2500000000000 : ℝ)^67
        have hw : |(-761842591/5000000000 : ℝ)|=(761842591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_14 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056314673/10000000000 : ℝ)*x 0 + (4556395837/10000000000 : ℝ)*x 1 + (-783443897/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056314673/10000000000 : ℝ)^83 ≤ (6175460204837/100000000000000 : ℝ)^67 := by
    have hnat : (1056314673 : ℕ)^83*100000000000000^67 ≤ 6175460204837^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056314673 10000000000 6175460204837 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4556395837/10000000000 : ℝ)^83 ≤ (9441439583081/25000000000000 : ℝ)^67 := by
    have hnat : (4556395837 : ℕ)^83*25000000000000^67 ≤ 9441439583081^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556395837 10000000000 9441439583081 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (783443897/1250000000 : ℝ)^83 ≤ (3503673840411/6250000000000 : ℝ)^67 := by
    have hnat : (783443897 : ℕ)^83*6250000000000^67 ≤ 3503673840411^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783443897 1250000000 3503673840411 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056314673/10000000000 : ℝ), (4556395837/10000000000 : ℝ), (-783443897/1250000000 : ℝ)] ![(6175460204837/100000000000000 : ℝ), (9441439583081/25000000000000 : ℝ), (3503673840411/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056314673/10000000000 : ℝ)|^83 ≤ (6175460204837/100000000000000 : ℝ)^67
        have hw : |(-1056314673/10000000000 : ℝ)|=(1056314673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4556395837/10000000000 : ℝ)|^83 ≤ (9441439583081/25000000000000 : ℝ)^67
        have hw : |(4556395837/10000000000 : ℝ)|=(4556395837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-783443897/1250000000 : ℝ)|^83 ≤ (3503673840411/6250000000000 : ℝ)^67
        have hw : |(-783443897/1250000000 : ℝ)|=(783443897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_15 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (81006981/156250000 : ℝ)*x 0 + (-1035780501/5000000000 : ℝ)*x 1 + (-1228198859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81006981/156250000 : ℝ)^83 ≤ (22158566447361/50000000000000 : ℝ)^67 := by
    have hnat : (81006981 : ℕ)^83*50000000000000^67 ≤ 22158566447361^67*156250000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81006981 156250000 22158566447361 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035780501/5000000000 : ℝ)^83 ≤ (1422412440369/10000000000000 : ℝ)^67 := by
    have hnat : (1035780501 : ℕ)^83*10000000000000^67 ≤ 1422412440369^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035780501 5000000000 1422412440369 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1228198859/2500000000 : ℝ)^83 ≤ (41458742680051/100000000000000 : ℝ)^67 := by
    have hnat : (1228198859 : ℕ)^83*100000000000000^67 ≤ 41458742680051^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228198859 2500000000 41458742680051 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81006981/156250000 : ℝ), (-1035780501/5000000000 : ℝ), (-1228198859/2500000000 : ℝ)] ![(22158566447361/50000000000000 : ℝ), (1422412440369/10000000000000 : ℝ), (41458742680051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81006981/156250000 : ℝ)|^83 ≤ (22158566447361/50000000000000 : ℝ)^67
        have hw : |(81006981/156250000 : ℝ)|=(81006981/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035780501/5000000000 : ℝ)|^83 ≤ (1422412440369/10000000000000 : ℝ)^67
        have hw : |(-1035780501/5000000000 : ℝ)|=(1035780501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1228198859/2500000000 : ℝ)|^83 ≤ (41458742680051/100000000000000 : ℝ)^67
        have hw : |(-1228198859/2500000000 : ℝ)|=(1228198859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_16 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (336475763/625000000 : ℝ)*x 0 + (4912019053/10000000000 : ℝ)*x 1 + (227458401/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336475763/625000000 : ℝ)^83 ≤ (9287152469067/20000000000000 : ℝ)^67 := by
    have hnat : (336475763 : ℕ)^83*20000000000000^67 ≤ 9287152469067^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336475763 625000000 9287152469067 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4912019053/10000000000 : ℝ)^83 ≤ (41450626371333/100000000000000 : ℝ)^67 := by
    have hnat : (4912019053 : ℕ)^83*100000000000000^67 ≤ 41450626371333^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4912019053 10000000000 41450626371333 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227458401/1250000000 : ℝ)^83 ≤ (6056805636147/50000000000000 : ℝ)^67 := by
    have hnat : (227458401 : ℕ)^83*50000000000000^67 ≤ 6056805636147^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227458401 1250000000 6056805636147 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336475763/625000000 : ℝ), (4912019053/10000000000 : ℝ), (227458401/1250000000 : ℝ)] ![(9287152469067/20000000000000 : ℝ), (41450626371333/100000000000000 : ℝ), (6056805636147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336475763/625000000 : ℝ)|^83 ≤ (9287152469067/20000000000000 : ℝ)^67
        have hw : |(336475763/625000000 : ℝ)|=(336475763/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4912019053/10000000000 : ℝ)|^83 ≤ (41450626371333/100000000000000 : ℝ)^67
        have hw : |(4912019053/10000000000 : ℝ)|=(4912019053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227458401/1250000000 : ℝ)|^83 ≤ (6056805636147/50000000000000 : ℝ)^67
        have hw : |(227458401/1250000000 : ℝ)|=(227458401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_20 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5440314739/10000000000 : ℝ)*x 0 + (252023107/500000000 : ℝ)*x 1 + (-1578843237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5440314739/10000000000 : ℝ)^83 ≤ (9408479876303/20000000000000 : ℝ)^67 := by
    have hnat : (5440314739 : ℕ)^83*20000000000000^67 ≤ 9408479876303^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440314739 10000000000 9408479876303 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252023107/500000000 : ℝ)^83 ≤ (42797509989013/100000000000000 : ℝ)^67 := by
    have hnat : (252023107 : ℕ)^83*100000000000000^67 ≤ 42797509989013^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252023107 500000000 42797509989013 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1578843237/10000000000 : ℝ)^83 ≤ (2032018121383/20000000000000 : ℝ)^67 := by
    have hnat : (1578843237 : ℕ)^83*20000000000000^67 ≤ 2032018121383^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578843237 10000000000 2032018121383 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5440314739/10000000000 : ℝ), (252023107/500000000 : ℝ), (-1578843237/10000000000 : ℝ)] ![(9408479876303/20000000000000 : ℝ), (42797509989013/100000000000000 : ℝ), (2032018121383/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5440314739/10000000000 : ℝ)|^83 ≤ (9408479876303/20000000000000 : ℝ)^67
        have hw : |(5440314739/10000000000 : ℝ)|=(5440314739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(252023107/500000000 : ℝ)|^83 ≤ (42797509989013/100000000000000 : ℝ)^67
        have hw : |(252023107/500000000 : ℝ)|=(252023107/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1578843237/10000000000 : ℝ)|^83 ≤ (2032018121383/20000000000000 : ℝ)^67
        have hw : |(-1578843237/10000000000 : ℝ)|=(1578843237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_21 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-225452741/2500000000 : ℝ)*x 0 + (194818431/400000000 : ℝ)*x 1 + (-6072582127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225452741/2500000000 : ℝ)^83 ≤ (5076809377727/100000000000000 : ℝ)^67 := by
    have hnat : (225452741 : ℕ)^83*100000000000000^67 ≤ 5076809377727^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225452741 2500000000 5076809377727 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194818431/400000000 : ℝ)^83 ≤ (256353900697/625000000000 : ℝ)^67 := by
    have hnat : (194818431 : ℕ)^83*625000000000^67 ≤ 256353900697^67*400000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194818431 400000000 256353900697 625000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6072582127/10000000000 : ℝ)^83 ≤ (53906566496613/100000000000000 : ℝ)^67 := by
    have hnat : (6072582127 : ℕ)^83*100000000000000^67 ≤ 53906566496613^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6072582127 10000000000 53906566496613 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-225452741/2500000000 : ℝ), (194818431/400000000 : ℝ), (-6072582127/10000000000 : ℝ)] ![(5076809377727/100000000000000 : ℝ), (256353900697/625000000000 : ℝ), (53906566496613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-225452741/2500000000 : ℝ)|^83 ≤ (5076809377727/100000000000000 : ℝ)^67
        have hw : |(-225452741/2500000000 : ℝ)|=(225452741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(194818431/400000000 : ℝ)|^83 ≤ (256353900697/625000000000 : ℝ)^67
        have hw : |(194818431/400000000 : ℝ)|=(194818431/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6072582127/10000000000 : ℝ)|^83 ≤ (53906566496613/100000000000000 : ℝ)^67
        have hw : |(-6072582127/10000000000 : ℝ)|=(6072582127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_22 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5830011287/10000000000 : ℝ)*x 0 + (-1870918833/10000000000 : ℝ)*x 1 + (-2202154569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5830011287/10000000000 : ℝ)^83 ≤ (51251885617871/100000000000000 : ℝ)^67 := by
    have hnat : (5830011287 : ℕ)^83*100000000000000^67 ≤ 51251885617871^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5830011287 10000000000 51251885617871 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870918833/10000000000 : ℝ)^83 ≤ (12537684067861/100000000000000 : ℝ)^67 := by
    have hnat : (1870918833 : ℕ)^83*100000000000000^67 ≤ 12537684067861^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870918833 10000000000 12537684067861 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202154569/5000000000 : ℝ)^83 ≤ (36210430296711/100000000000000 : ℝ)^67 := by
    have hnat : (2202154569 : ℕ)^83*100000000000000^67 ≤ 36210430296711^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202154569 5000000000 36210430296711 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5830011287/10000000000 : ℝ), (-1870918833/10000000000 : ℝ), (-2202154569/5000000000 : ℝ)] ![(51251885617871/100000000000000 : ℝ), (12537684067861/100000000000000 : ℝ), (36210430296711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5830011287/10000000000 : ℝ)|^83 ≤ (51251885617871/100000000000000 : ℝ)^67
        have hw : |(5830011287/10000000000 : ℝ)|=(5830011287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1870918833/10000000000 : ℝ)|^83 ≤ (12537684067861/100000000000000 : ℝ)^67
        have hw : |(-1870918833/10000000000 : ℝ)|=(1870918833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2202154569/5000000000 : ℝ)|^83 ≤ (36210430296711/100000000000000 : ℝ)^67
        have hw : |(-2202154569/5000000000 : ℝ)|=(2202154569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_23 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4993937879/10000000000 : ℝ)*x 0 + (39892341/80000000 : ℝ)*x 1 + (2215703071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4993937879/10000000000 : ℝ)^83 ≤ (4230868782677/10000000000000 : ℝ)^67 := by
    have hnat : (4993937879 : ℕ)^83*10000000000000^67 ≤ 4230868782677^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993937879 10000000000 4230868782677 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39892341/80000000 : ℝ)^83 ≤ (10557771766513/25000000000000 : ℝ)^67 := by
    have hnat : (39892341 : ℕ)^83*25000000000000^67 ≤ 10557771766513^67*80000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39892341 80000000 10557771766513 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2215703071/10000000000 : ℝ)^83 ≤ (3092045018239/20000000000000 : ℝ)^67 := by
    have hnat : (2215703071 : ℕ)^83*20000000000000^67 ≤ 3092045018239^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215703071 10000000000 3092045018239 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4993937879/10000000000 : ℝ), (39892341/80000000 : ℝ), (2215703071/10000000000 : ℝ)] ![(4230868782677/10000000000000 : ℝ), (10557771766513/25000000000000 : ℝ), (3092045018239/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4993937879/10000000000 : ℝ)|^83 ≤ (4230868782677/10000000000000 : ℝ)^67
        have hw : |(4993937879/10000000000 : ℝ)|=(4993937879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39892341/80000000 : ℝ)|^83 ≤ (10557771766513/25000000000000 : ℝ)^67
        have hw : |(39892341/80000000 : ℝ)|=(39892341/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2215703071/10000000000 : ℝ)|^83 ≤ (3092045018239/20000000000000 : ℝ)^67
        have hw : |(2215703071/10000000000 : ℝ)|=(2215703071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s2_s2_27 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2577860187/5000000000 : ℝ)*x 0 + (5149654769/10000000000 : ℝ)*x 1 + (-452619051/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2577860187/5000000000 : ℝ)^83 ≤ (44013138167669/100000000000000 : ℝ)^67 := by
    have hnat : (2577860187 : ℕ)^83*100000000000000^67 ≤ 44013138167669^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577860187 5000000000 44013138167669 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149654769/10000000000 : ℝ)^83 ≤ (21974500530457/50000000000000 : ℝ)^67 := by
    have hnat : (5149654769 : ℕ)^83*50000000000000^67 ≤ 21974500530457^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149654769 10000000000 21974500530457 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452619051/2500000000 : ℝ)^83 ≤ (3009465190089/25000000000000 : ℝ)^67 := by
    have hnat : (452619051 : ℕ)^83*25000000000000^67 ≤ 3009465190089^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452619051 2500000000 3009465190089 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2577860187/5000000000 : ℝ), (5149654769/10000000000 : ℝ), (-452619051/2500000000 : ℝ)] ![(44013138167669/100000000000000 : ℝ), (21974500530457/50000000000000 : ℝ), (3009465190089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2577860187/5000000000 : ℝ)|^83 ≤ (44013138167669/100000000000000 : ℝ)^67
        have hw : |(2577860187/5000000000 : ℝ)|=(2577860187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149654769/10000000000 : ℝ)|^83 ≤ (21974500530457/50000000000000 : ℝ)^67
        have hw : |(5149654769/10000000000 : ℝ)|=(5149654769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-452619051/2500000000 : ℝ)|^83 ≤ (3009465190089/25000000000000 : ℝ)^67
        have hw : |(-452619051/2500000000 : ℝ)|=(452619051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c321054_s2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((843/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(843/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44457/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44457/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31831/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31831/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5443/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5443/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11549/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11549/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-14349/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-14349/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80491/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80491/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (843/2000 : ℝ) ^ (81/16 : ℝ) ≤ (252097035773910019/20000000000000000000 : ℝ) := by
    have hpowers : (843/2000 : ℝ)^81 ≤ (252097035773910019/20000000000000000000 : ℝ)^16 := by
      have hnat : (843 : ℕ)^81*20000000000000000000^16 ≤ 252097035773910019^16*2000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        843 2000 252097035773910019 20000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (843/2000 : ℝ)) (X := (252097035773910019/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (20252097035773910019/20000000000000000000 : ℝ) ≤ (10024773493904221/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (20252097035773910019/20000000000000000000 : ℝ)^16 ≤ (10024773493904221/10000000000000000 : ℝ)^81 := by
      have hnat : (20252097035773910019 : ℕ)^16*10000000000000000^81 ≤ 10024773493904221^81*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20252097035773910019 20000000000000000000 10024773493904221 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024773493904221/10000000000000000 : ℝ)) (X := (20252097035773910019/20000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (10252097035773910019/10000000000000000000 : ℝ) ≤ (2512325186516091/2500000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (10252097035773910019/10000000000000000000 : ℝ)^16 ≤ (2512325186516091/2500000000000000 : ℝ)^81 := by
      have hnat : (10252097035773910019 : ℕ)^16*2500000000000000^81 ≤ 2512325186516091^81*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10252097035773910019 10000000000000000000 2512325186516091 2500000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2512325186516091/2500000000000000 : ℝ)) (X := (10252097035773910019/10000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(8257831301407/1405000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(24527252160143/4215000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (843/2000 : ℝ)) (alpha := (8257831301407/1405000000000000 : ℝ)) (beta := (24527252160143/4215000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (843/2000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(8257831301407/1405000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(24527252160143/4215000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (44457/100000 : ℝ) ^ (81/16 : ℝ) ≤ (825404871339545657/50000000000000000000 : ℝ) := by
    have hpowers : (44457/100000 : ℝ)^81 ≤ (825404871339545657/50000000000000000000 : ℝ)^16 := by
      have hnat : (44457 : ℕ)^81*50000000000000000000^16 ≤ 825404871339545657^16*100000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44457 100000 825404871339545657 50000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44457/100000 : ℝ)) (X := (825404871339545657/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (50825404871339545657/50000000000000000000 : ℝ) ≤ (80259157747383/80000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (50825404871339545657/50000000000000000000 : ℝ)^16 ≤ (80259157747383/80000000000000 : ℝ)^81 := by
      have hnat : (50825404871339545657 : ℕ)^16*80000000000000^81 ≤ 80259157747383^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50825404871339545657 50000000000000000000 80259157747383 80000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80259157747383/80000000000000 : ℝ)) (X := (50825404871339545657/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (25825404871339545657/25000000000000000000 : ℝ) ≤ (10064369978833721/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (25825404871339545657/25000000000000000000 : ℝ)^16 ≤ (10064369978833721/10000000000000000 : ℝ)^81 := by
      have hnat : (25825404871339545657 : ℕ)^16*10000000000000000^81 ≤ 10064369978833721^81*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25825404871339545657 25000000000000000000 10064369978833721 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10064369978833721/10000000000000000 : ℝ)) (X := (25825404871339545657/25000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(259157747383/35565600000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(219008632951/30450000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (44457/100000 : ℝ)) (alpha := (259157747383/35565600000000 : ℝ)) (beta := (219008632951/30450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (44457/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(259157747383/35565600000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(219008632951/30450000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (31831/100000 : ℝ) ^ (81/16 : ℝ) ≤ (38026781444560781/12500000000000000000 : ℝ) := by
    have hpowers : (31831/100000 : ℝ)^81 ≤ (38026781444560781/12500000000000000000 : ℝ)^16 := by
      have hnat : (31831 : ℕ)^81*12500000000000000000^16 ≤ 38026781444560781^16*100000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31831 100000 38026781444560781 12500000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31831/100000 : ℝ)) (X := (38026781444560781/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (12538026781444560781/12500000000000000000 : ℝ) ≤ (1000600184890927/1000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (12538026781444560781/12500000000000000000 : ℝ)^16 ≤ (1000600184890927/1000000000000000 : ℝ)^81 := by
      have hnat : (12538026781444560781 : ℕ)^16*1000000000000000^81 ≤ 1000600184890927^81*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12538026781444560781 12500000000000000000 1000600184890927 1000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000600184890927/1000000000000000 : ℝ)) (X := (12538026781444560781/12500000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (6288026781444560781/6250000000000000000 : ℝ) ≤ (5005994554060091/5000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (6288026781444560781/6250000000000000000 : ℝ)^16 ≤ (5005994554060091/5000000000000000 : ℝ)^81 := by
      have hnat : (6288026781444560781 : ℕ)^16*5000000000000000^81 ≤ 5005994554060091^81*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6288026781444560781 6250000000000000000 5005994554060091 5000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005994554060091/5000000000000000 : ℝ)) (X := (6288026781444560781/6250000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(600184890927/318310000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(187101850341/99471875000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (31831/100000 : ℝ)) (alpha := (600184890927/318310000000000 : ℝ)) (beta := (187101850341/99471875000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (31831/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(600184890927/318310000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(187101850341/99471875000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-52141447/400000000 : ℝ)*X 0 0+(1131889513/2500000000 : ℝ)*X 0 1+(-1532004649/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((542343583/1000000000 : ℝ)*X 1 0+(-1104481811/5000000000 : ℝ)*X 1 1+(-569191417/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5011003443/10000000000 : ℝ)*X 2 0+(1000734579/2000000000 : ℝ)*X 2 1+(1087039919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((5097674893/10000000000 : ℝ)*X 0 0+(127286021/250000000 : ℝ)*X 0 1+(-489528019/2500000000 : ℝ)*X 0 2+(5097674893/10000000000 : ℝ)*X 1 0+(127286021/250000000 : ℝ)*X 1 1+(-489528019/2500000000 : ℝ)*X 1 2+(5097674893/10000000000 : ℝ)*X 2 0+(127286021/250000000 : ℝ)*X 2 1+(-489528019/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-6357057/50000000 : ℝ)*X 0 0+(54739011/125000000 : ℝ)*X 0 1+(-6287201481/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2676894983/5000000000 : ℝ)*X 1 0+(-468130977/2500000000 : ℝ)*X 1 1+(-4900636903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1229616243/2500000000 : ℝ)*X 2 0+(670988499/1250000000 : ℝ)*X 2 1+(91591289/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1013657357/2000000000 : ℝ)*X 0 0+(2726923463/5000000000 : ℝ)*X 0 1+(-761842591/5000000000 : ℝ)*X 0 2+(1013657357/2000000000 : ℝ)*X 1 0+(2726923463/5000000000 : ℝ)*X 1 1+(-761842591/5000000000 : ℝ)*X 1 2+(1013657357/2000000000 : ℝ)*X 2 0+(2726923463/5000000000 : ℝ)*X 2 1+(-761842591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1056314673/10000000000 : ℝ)*X 0 0+(4556395837/10000000000 : ℝ)*X 0 1+(-783443897/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((81006981/156250000 : ℝ)*X 1 0+(-1035780501/5000000000 : ℝ)*X 1 1+(-1228198859/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((336475763/625000000 : ℝ)*X 2 0+(4912019053/10000000000 : ℝ)*X 2 1+(227458401/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((5440314739/10000000000 : ℝ)*X 0 0+(252023107/500000000 : ℝ)*X 0 1+(-1578843237/10000000000 : ℝ)*X 0 2+(5440314739/10000000000 : ℝ)*X 1 0+(252023107/500000000 : ℝ)*X 1 1+(-1578843237/10000000000 : ℝ)*X 1 2+(5440314739/10000000000 : ℝ)*X 2 0+(252023107/500000000 : ℝ)*X 2 1+(-1578843237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-225452741/2500000000 : ℝ)*X 0 0+(194818431/400000000 : ℝ)*X 0 1+(-6072582127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5830011287/10000000000 : ℝ)*X 1 0+(-1870918833/10000000000 : ℝ)*X 1 1+(-2202154569/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4993937879/10000000000 : ℝ)*X 2 0+(39892341/80000000 : ℝ)*X 2 1+(2215703071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2577860187/5000000000 : ℝ)*X 0 0+(5149654769/10000000000 : ℝ)*X 0 1+(-452619051/2500000000 : ℝ)*X 0 2+(2577860187/5000000000 : ℝ)*X 1 0+(5149654769/10000000000 : ℝ)*X 1 1+(-452619051/2500000000 : ℝ)*X 1 2+(2577860187/5000000000 : ℝ)*X 2 0+(5149654769/10000000000 : ℝ)*X 2 1+(-452619051/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((5443/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5443/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (257247108482576255540182219/23585179450000000000000000000000 : ℝ) := by norm_num
    linear_combination (2651119242279/1000000000000 : ℝ)*(base39) + (4754001/1000000000000 : ℝ)*(base50) + (963696881827/1000000000000 : ℝ)*(base60) + (865431679631/62500000000 : ℝ)*(major_s2_0) + (865431679631/62500000000 : ℝ)*(major_s2_1) + (865431679631/62500000000 : ℝ)*(major_s2_2) + (50308311/200000000000 : ℝ)*(sp_s2_0) + (10209537374731/500000000000 : ℝ)*(sp_s2_7) + (5104769825543/250000000000 : ℝ)*(sp_s2_8) + (2041928117659/100000000000 : ℝ)*(sp_s2_9) + (7274368997487/1000000000000 : ℝ)*(sp_s2_13) + (114823967/1000000000000 : ℝ)*(sp_s2_14) + (90453203/250000000000 : ℝ)*(sp_s2_15) + (159938393/1000000000000 : ℝ)*(sp_s2_23) + (7274368997487/1000000000000 : ℝ)*(f.failure) + (2552430139373/125000000000 : ℝ)*(f.sum) + (2887556196396072149/14151107670000000000000000000000 : ℝ)*base62 + (1091562190584179/1591550000000000000000000000 : ℝ)*base64 + (986082068491/7612500000000000000000000 : ℝ)*base67 + (100272600295713/318310000000000000000000000 : ℝ)*base68 + (988154429385806321/5590319375000000000000000000000 : ℝ)*base70 + (270984667283591/526875000000000000000000000 : ℝ)*base73 + (88541743852927/222285000000000000000000000 : ℝ)*base74 + (1385873334893/351250000000000000000000000 : ℝ)*base77 + (40772925895513829/213911250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (2839/6250000000000000 : ℝ)*base87 + (2839/6250000000000000 : ℝ)*base89 + (2839/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11549/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11549/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2205694140580059686760592883673/331371771272500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1289584787177/500000000000 : ℝ)*(base39) + (2950849/1000000000000 : ℝ)*(base40) + (334503859243/500000000000 : ℝ)*(base60) + (13809419957099/1000000000000 : ℝ)*(major_s2_0) + (13809419957099/1000000000000 : ℝ)*(major_s2_1) + (13809419957099/1000000000000 : ℝ)*(major_s2_2) + (814451/250000000000 : ℝ)*(sp_s2_6) + (21322557/125000000000 : ℝ)*(sp_s2_7) + (154514943/1000000000000 : ℝ)*(sp_s2_8) + (5090997897267/250000000000 : ℝ)*(sp_s2_14) + (20364007654581/1000000000000 : ℝ)*(sp_s2_15) + (5091033342367/250000000000 : ℝ)*(sp_s2_16) + (1813668067029/250000000000 : ℝ)*(sp_s2_20) + (3600007/125000000000 : ℝ)*(sp_s2_23) + (45341722037/6250000000 : ℝ)*(f.failure) + (5091040542381/250000000000 : ℝ)*(f.sum) + (12270950797076986891/28302215340000000000000000000000 : ℝ)*base62 + (85885647043691/397887500000000000000000000 : ℝ)*base65 + (4335676666351/30450000000000000000000000 : ℝ)*base67 + (36697250997581/63662000000000000000000000 : ℝ)*base68 + (19662897048703883883/44722555000000000000000000000000 : ℝ)*base71 + (1579710647413343/4215000000000000000000000000 : ℝ)*base72 + (151788009407371/889140000000000000000000000 : ℝ)*base74 + (127945490423707/1405000000000000000000000000 : ℝ)*base76 + (448712750965638029/855645000000000000000000000000 : ℝ)*base78 + (149/625000000000000 : ℝ)*base87 + (149/625000000000000 : ℝ)*base89 + (149/625000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-14349/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-14349/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (510865219479251432509195404067/47338824467500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2016077054343/1000000000000 : ℝ)*(base39) + (1317877/250000000000 : ℝ)*(base50) + (113536348261/1000000000000 : ℝ)*(base60) + (8652612570053/1000000000000 : ℝ)*(major_s2_0) + (8652612570053/1000000000000 : ℝ)*(major_s2_1) + (8652612570053/1000000000000 : ℝ)*(major_s2_2) + (30211091/500000000000 : ℝ)*(sp_s2_1) + (106064699/500000000000 : ℝ)*(sp_s2_2) + (17751983/125000000000 : ℝ)*(sp_s2_13) + (59191939/200000000000 : ℝ)*(sp_s2_20) + (12759636221969/1000000000000 : ℝ)*(sp_s2_21) + (3189893949947/250000000000 : ℝ)*(sp_s2_22) + (12759424092571/1000000000000 : ℝ)*(sp_s2_23) + (1136286836337/250000000000 : ℝ)*(sp_s2_27) + (4545585320907/1000000000000 : ℝ)*(f.failure) + (12759636221969/1000000000000 : ℝ)*(f.sum) + (5080636154159462401/5660443068000000000000000000000 : ℝ)*base63 + (580513996052237/1591550000000000000000000000 : ℝ)*base64 + (13760938253407/30450000000000000000000000 : ℝ)*base67 + (4928205497609/39788750000000000000000000 : ℝ)*base68 + (6918090712277643699/44722555000000000000000000000000 : ℝ)*base70 + (1972284014694079/4215000000000000000000000000 : ℝ)*base73 + (81231590033479/177828000000000000000000000 : ℝ)*base75 + (41095730394071/1405000000000000000000000000 : ℝ)*base77 + (375958985644489237/855645000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (671/6250000000000000 : ℝ)*base86 + (671/6250000000000000 : ℝ)*base88 + (671/6250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((843/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(843/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44457/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44457/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31831/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31831/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5443/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5443/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11549/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11549/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-14349/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-14349/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c321054_s2 p hpa hpb X hX hprev1

#print axioms solution
