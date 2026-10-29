-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316057_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:07:18.607081+00:00
-- url     : https://prove2.me/submissions/314c126c-2943-4d61-96ac-179928db331f

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
theorem collision_support_c316057_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3203874483/10000000000 : ℝ)*x 0 + (-3196955609/10000000000 : ℝ)*x 1 + (6004534769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3203874483/10000000000 : ℝ)^77 ≤ (23769311743227/100000000000000 : ℝ)^61 := by
    have hnat : (3203874483 : ℕ)^77*100000000000000^61 ≤ 23769311743227^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3203874483 10000000000 23769311743227 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3196955609/10000000000 : ℝ)^77 ≤ (11852267855501/50000000000000 : ℝ)^61 := by
    have hnat : (3196955609 : ℕ)^77*50000000000000^61 ≤ 11852267855501^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3196955609 10000000000 11852267855501 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6004534769/10000000000 : ℝ)^77 ≤ (52526152536641/100000000000000 : ℝ)^61 := by
    have hnat : (6004534769 : ℕ)^77*100000000000000^61 ≤ 52526152536641^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6004534769 10000000000 52526152536641 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3203874483/10000000000 : ℝ), (-3196955609/10000000000 : ℝ), (6004534769/10000000000 : ℝ)] ![(23769311743227/100000000000000 : ℝ), (11852267855501/50000000000000 : ℝ), (52526152536641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3203874483/10000000000 : ℝ)|^77 ≤ (23769311743227/100000000000000 : ℝ)^61
        have hw : |(3203874483/10000000000 : ℝ)|=(3203874483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3196955609/10000000000 : ℝ)|^77 ≤ (11852267855501/50000000000000 : ℝ)^61
        have hw : |(-3196955609/10000000000 : ℝ)|=(3196955609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6004534769/10000000000 : ℝ)|^77 ≤ (52526152536641/100000000000000 : ℝ)^61
        have hw : |(6004534769/10000000000 : ℝ)|=(6004534769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2832981971/5000000000 : ℝ)*x 0 + (354782367/625000000 : ℝ)*x 1 + (-495669947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2832981971/5000000000 : ℝ)^77 ≤ (3050975755297/6250000000000 : ℝ)^61 := by
    have hnat : (2832981971 : ℕ)^77*6250000000000^61 ≤ 3050975755297^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832981971 5000000000 3050975755297 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354782367/625000000 : ℝ)^77 ≤ (48930418475353/100000000000000 : ℝ)^61 := by
    have hnat : (354782367 : ℕ)^77*100000000000000^61 ≤ 48930418475353^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354782367 625000000 48930418475353 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495669947/10000000000 : ℝ)^77 ≤ (2253969426601/100000000000000 : ℝ)^61 := by
    have hnat : (495669947 : ℕ)^77*100000000000000^61 ≤ 2253969426601^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495669947 10000000000 2253969426601 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2832981971/5000000000 : ℝ), (354782367/625000000 : ℝ), (-495669947/10000000000 : ℝ)] ![(3050975755297/6250000000000 : ℝ), (48930418475353/100000000000000 : ℝ), (2253969426601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2832981971/5000000000 : ℝ)|^77 ≤ (3050975755297/6250000000000 : ℝ)^61
        have hw : |(2832981971/5000000000 : ℝ)|=(2832981971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(354782367/625000000 : ℝ)|^77 ≤ (48930418475353/100000000000000 : ℝ)^61
        have hw : |(354782367/625000000 : ℝ)|=(354782367/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-495669947/10000000000 : ℝ)|^77 ≤ (2253969426601/100000000000000 : ℝ)^61
        have hw : |(-495669947/10000000000 : ℝ)|=(495669947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4532698053/10000000000 : ℝ)*x 0 + (227057053/500000000 : ℝ)*x 1 + (433252857/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4532698053/10000000000 : ℝ)^77 ≤ (18415811866147/50000000000000 : ℝ)^61 := by
    have hnat : (4532698053 : ℕ)^77*50000000000000^61 ≤ 18415811866147^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532698053 10000000000 18415811866147 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227057053/500000000 : ℝ)^77 ≤ (36918245720243/100000000000000 : ℝ)^61 := by
    have hnat : (227057053 : ℕ)^77*100000000000000^61 ≤ 36918245720243^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227057053 500000000 36918245720243 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433252857/1250000000 : ℝ)^77 ≤ (26250130538531/100000000000000 : ℝ)^61 := by
    have hnat : (433252857 : ℕ)^77*100000000000000^61 ≤ 26250130538531^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433252857 1250000000 26250130538531 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4532698053/10000000000 : ℝ), (227057053/500000000 : ℝ), (433252857/1250000000 : ℝ)] ![(18415811866147/50000000000000 : ℝ), (36918245720243/100000000000000 : ℝ), (26250130538531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4532698053/10000000000 : ℝ)|^77 ≤ (18415811866147/50000000000000 : ℝ)^61
        have hw : |(4532698053/10000000000 : ℝ)|=(4532698053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(227057053/500000000 : ℝ)|^77 ≤ (36918245720243/100000000000000 : ℝ)^61
        have hw : |(227057053/500000000 : ℝ)|=(227057053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(433252857/1250000000 : ℝ)|^77 ≤ (26250130538531/100000000000000 : ℝ)^61
        have hw : |(433252857/1250000000 : ℝ)|=(433252857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-121583177/400000000 : ℝ)*x 0 + (10819177/39062500 : ℝ)*x 1 + (649337667/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121583177/400000000 : ℝ)^77 ≤ (11120594987071/50000000000000 : ℝ)^61 := by
    have hnat : (121583177 : ℕ)^77*50000000000000^61 ≤ 11120594987071^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121583177 400000000 11120594987071 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10819177/39062500 : ℝ)^77 ≤ (9889114969143/50000000000000 : ℝ)^61 := by
    have hnat : (10819177 : ℕ)^77*50000000000000^61 ≤ 9889114969143^61*39062500^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10819177 39062500 9889114969143 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649337667/1000000000 : ℝ)^77 ≤ (57980580073673/100000000000000 : ℝ)^61 := by
    have hnat : (649337667 : ℕ)^77*100000000000000^61 ≤ 57980580073673^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649337667 1000000000 57980580073673 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121583177/400000000 : ℝ), (10819177/39062500 : ℝ), (649337667/1000000000 : ℝ)] ![(11120594987071/50000000000000 : ℝ), (9889114969143/50000000000000 : ℝ), (57980580073673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121583177/400000000 : ℝ)|^77 ≤ (11120594987071/50000000000000 : ℝ)^61
        have hw : |(-121583177/400000000 : ℝ)|=(121583177/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10819177/39062500 : ℝ)|^77 ≤ (9889114969143/50000000000000 : ℝ)^61
        have hw : |(10819177/39062500 : ℝ)|=(10819177/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(649337667/1000000000 : ℝ)|^77 ≤ (57980580073673/100000000000000 : ℝ)^61
        have hw : |(649337667/1000000000 : ℝ)|=(649337667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (606746599/2000000000 : ℝ)*x 0 + (-2764381959/10000000000 : ℝ)*x 1 + (52019393/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (606746599/2000000000 : ℝ)^77 ≤ (22187203302939/100000000000000 : ℝ)^61 := by
    have hnat : (606746599 : ℕ)^77*100000000000000^61 ≤ 22187203302939^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606746599 2000000000 22187203302939 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2764381959/10000000000 : ℝ)^77 ≤ (19730221676997/100000000000000 : ℝ)^61 := by
    have hnat : (2764381959 : ℕ)^77*100000000000000^61 ≤ 19730221676997^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2764381959 10000000000 19730221676997 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52019393/80000000 : ℝ)^77 ≤ (1815080469031/3125000000000 : ℝ)^61 := by
    have hnat : (52019393 : ℕ)^77*3125000000000^61 ≤ 1815080469031^61*80000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52019393 80000000 1815080469031 3125000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(606746599/2000000000 : ℝ), (-2764381959/10000000000 : ℝ), (52019393/80000000 : ℝ)] ![(22187203302939/100000000000000 : ℝ), (19730221676997/100000000000000 : ℝ), (1815080469031/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(606746599/2000000000 : ℝ)|^77 ≤ (22187203302939/100000000000000 : ℝ)^61
        have hw : |(606746599/2000000000 : ℝ)|=(606746599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2764381959/10000000000 : ℝ)|^77 ≤ (19730221676997/100000000000000 : ℝ)^61
        have hw : |(-2764381959/10000000000 : ℝ)|=(2764381959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52019393/80000000 : ℝ)|^77 ≤ (1815080469031/3125000000000 : ℝ)^61
        have hw : |(52019393/80000000 : ℝ)|=(52019393/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2642502137/5000000000 : ℝ)*x 0 + (624641259/1000000000 : ℝ)*x 1 + (-34970713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642502137/5000000000 : ℝ)^77 ≤ (22354836749623/50000000000000 : ℝ)^61 := by
    have hnat : (2642502137 : ℕ)^77*50000000000000^61 ≤ 22354836749623^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642502137 5000000000 22354836749623 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624641259/1000000000 : ℝ)^77 ≤ (13802749451681/25000000000000 : ℝ)^61 := by
    have hnat : (624641259 : ℕ)^77*25000000000000^61 ≤ 13802749451681^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624641259 1000000000 13802749451681 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34970713/10000000000 : ℝ)^77 ≤ (15865736959/20000000000000 : ℝ)^61 := by
    have hnat : (34970713 : ℕ)^77*20000000000000^61 ≤ 15865736959^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34970713 10000000000 15865736959 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642502137/5000000000 : ℝ), (624641259/1000000000 : ℝ), (-34970713/10000000000 : ℝ)] ![(22354836749623/50000000000000 : ℝ), (13802749451681/25000000000000 : ℝ), (15865736959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642502137/5000000000 : ℝ)|^77 ≤ (22354836749623/50000000000000 : ℝ)^61
        have hw : |(2642502137/5000000000 : ℝ)|=(2642502137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624641259/1000000000 : ℝ)|^77 ≤ (13802749451681/25000000000000 : ℝ)^61
        have hw : |(624641259/1000000000 : ℝ)|=(624641259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34970713/10000000000 : ℝ)|^77 ≤ (15865736959/20000000000000 : ℝ)^61
        have hw : |(-34970713/10000000000 : ℝ)|=(34970713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_12 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2313355753/5000000000 : ℝ)*x 0 + (2734184071/5000000000 : ℝ)*x 1 + (2286262339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2313355753/5000000000 : ℝ)^77 ≤ (37798539758411/100000000000000 : ℝ)^61 := by
    have hnat : (2313355753 : ℕ)^77*100000000000000^61 ≤ 37798539758411^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313355753 5000000000 37798539758411 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734184071/5000000000 : ℝ)^77 ≤ (5834573741117/12500000000000 : ℝ)^61 := by
    have hnat : (2734184071 : ℕ)^77*12500000000000^61 ≤ 5834573741117^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734184071 5000000000 5834573741117 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2286262339/10000000000 : ℝ)^77 ≤ (15524870291699/100000000000000 : ℝ)^61 := by
    have hnat : (2286262339 : ℕ)^77*100000000000000^61 ≤ 15524870291699^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286262339 10000000000 15524870291699 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2313355753/5000000000 : ℝ), (2734184071/5000000000 : ℝ), (2286262339/10000000000 : ℝ)] ![(37798539758411/100000000000000 : ℝ), (5834573741117/12500000000000 : ℝ), (15524870291699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2313355753/5000000000 : ℝ)|^77 ≤ (37798539758411/100000000000000 : ℝ)^61
        have hw : |(2313355753/5000000000 : ℝ)|=(2313355753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734184071/5000000000 : ℝ)|^77 ≤ (5834573741117/12500000000000 : ℝ)^61
        have hw : |(2734184071/5000000000 : ℝ)|=(2734184071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2286262339/10000000000 : ℝ)|^77 ≤ (15524870291699/100000000000000 : ℝ)^61
        have hw : |(2286262339/10000000000 : ℝ)|=(2286262339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1388304287/5000000000 : ℝ)*x 0 + (3032840867/10000000000 : ℝ)*x 1 + (3246688891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1388304287/5000000000 : ℝ)^77 ≤ (19840439698247/100000000000000 : ℝ)^61 := by
    have hnat : (1388304287 : ℕ)^77*100000000000000^61 ≤ 19840439698247^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388304287 5000000000 19840439698247 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3032840867/10000000000 : ℝ)^77 ≤ (2772370959851/12500000000000 : ℝ)^61 := by
    have hnat : (3032840867 : ℕ)^77*12500000000000^61 ≤ 2772370959851^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3032840867 10000000000 2772370959851 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3246688891/5000000000 : ℝ)^77 ≤ (2319223704293/4000000000000 : ℝ)^61 := by
    have hnat : (3246688891 : ℕ)^77*4000000000000^61 ≤ 2319223704293^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3246688891 5000000000 2319223704293 4000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1388304287/5000000000 : ℝ), (3032840867/10000000000 : ℝ), (3246688891/5000000000 : ℝ)] ![(19840439698247/100000000000000 : ℝ), (2772370959851/12500000000000 : ℝ), (2319223704293/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1388304287/5000000000 : ℝ)|^77 ≤ (19840439698247/100000000000000 : ℝ)^61
        have hw : |(-1388304287/5000000000 : ℝ)|=(1388304287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3032840867/10000000000 : ℝ)|^77 ≤ (2772370959851/12500000000000 : ℝ)^61
        have hw : |(3032840867/10000000000 : ℝ)|=(3032840867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3246688891/5000000000 : ℝ)|^77 ≤ (2319223704293/4000000000000 : ℝ)^61
        have hw : |(3246688891/5000000000 : ℝ)|=(3246688891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (110850721/400000000 : ℝ)*x 0 + (-3027007479/10000000000 : ℝ)*x 1 + (1625606277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110850721/400000000 : ℝ)^77 ≤ (9896140551521/50000000000000 : ℝ)^61 := by
    have hnat : (110850721 : ℕ)^77*50000000000000^61 ≤ 9896140551521^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110850721 400000000 9896140551521 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3027007479/10000000000 : ℝ)^77 ≤ (1382820799207/6250000000000 : ℝ)^61 := by
    have hnat : (3027007479 : ℕ)^77*6250000000000^61 ≤ 1382820799207^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3027007479 10000000000 1382820799207 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1625606277/2500000000 : ℝ)^77 ≤ (58082586092697/100000000000000 : ℝ)^61 := by
    have hnat : (1625606277 : ℕ)^77*100000000000000^61 ≤ 58082586092697^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625606277 2500000000 58082586092697 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(110850721/400000000 : ℝ), (-3027007479/10000000000 : ℝ), (1625606277/2500000000 : ℝ)] ![(9896140551521/50000000000000 : ℝ), (1382820799207/6250000000000 : ℝ), (58082586092697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(110850721/400000000 : ℝ)|^77 ≤ (9896140551521/50000000000000 : ℝ)^61
        have hw : |(110850721/400000000 : ℝ)|=(110850721/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3027007479/10000000000 : ℝ)|^77 ≤ (1382820799207/6250000000000 : ℝ)^61
        have hw : |(-3027007479/10000000000 : ℝ)|=(3027007479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1625606277/2500000000 : ℝ)|^77 ≤ (58082586092697/100000000000000 : ℝ)^61
        have hw : |(1625606277/2500000000 : ℝ)|=(1625606277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6236155183/10000000000 : ℝ)*x 0 + (5295716483/10000000000 : ℝ)*x 1 + (-17484821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6236155183/10000000000 : ℝ)^77 ≤ (860884036933/1562500000000 : ℝ)^61 := by
    have hnat : (6236155183 : ℕ)^77*1562500000000^61 ≤ 860884036933^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6236155183 10000000000 860884036933 1562500000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5295716483/10000000000 : ℝ)^77 ≤ (22412048002739/50000000000000 : ℝ)^61 := by
    have hnat : (5295716483 : ℕ)^77*50000000000000^61 ≤ 22412048002739^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295716483 10000000000 22412048002739 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17484821/5000000000 : ℝ)^77 ≤ (79325618073/100000000000000 : ℝ)^61 := by
    have hnat : (17484821 : ℕ)^77*100000000000000^61 ≤ 79325618073^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17484821 5000000000 79325618073 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6236155183/10000000000 : ℝ), (5295716483/10000000000 : ℝ), (-17484821/5000000000 : ℝ)] ![(860884036933/1562500000000 : ℝ), (22412048002739/50000000000000 : ℝ), (79325618073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6236155183/10000000000 : ℝ)|^77 ≤ (860884036933/1562500000000 : ℝ)^61
        have hw : |(6236155183/10000000000 : ℝ)|=(6236155183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5295716483/10000000000 : ℝ)|^77 ≤ (22412048002739/50000000000000 : ℝ)^61
        have hw : |(5295716483/10000000000 : ℝ)|=(5295716483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17484821/5000000000 : ℝ)|^77 ≤ (79325618073/100000000000000 : ℝ)^61
        have hw : |(-17484821/5000000000 : ℝ)|=(17484821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_18 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1091877903/2000000000 : ℝ)*x 0 + (4636090379/10000000000 : ℝ)*x 1 + (2286259457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091877903/2000000000 : ℝ)^77 ≤ (5822483675927/12500000000000 : ℝ)^61 := by
    have hnat : (1091877903 : ℕ)^77*12500000000000^61 ≤ 5822483675927^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091877903 2000000000 5822483675927 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4636090379/10000000000 : ℝ)^77 ≤ (947382124547/2500000000000 : ℝ)^61 := by
    have hnat : (4636090379 : ℕ)^77*2500000000000^61 ≤ 947382124547^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4636090379 10000000000 947382124547 2500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2286259457/10000000000 : ℝ)^77 ≤ (155248455883/1000000000000 : ℝ)^61 := by
    have hnat : (2286259457 : ℕ)^77*1000000000000^61 ≤ 155248455883^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286259457 10000000000 155248455883 1000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091877903/2000000000 : ℝ), (4636090379/10000000000 : ℝ), (2286259457/10000000000 : ℝ)] ![(5822483675927/12500000000000 : ℝ), (947382124547/2500000000000 : ℝ), (155248455883/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091877903/2000000000 : ℝ)|^77 ≤ (5822483675927/12500000000000 : ℝ)^61
        have hw : |(1091877903/2000000000 : ℝ)|=(1091877903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4636090379/10000000000 : ℝ)|^77 ≤ (947382124547/2500000000000 : ℝ)^61
        have hw : |(4636090379/10000000000 : ℝ)|=(4636090379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2286259457/10000000000 : ℝ)|^77 ≤ (155248455883/1000000000000 : ℝ)^61
        have hw : |(2286259457/10000000000 : ℝ)|=(2286259457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_19 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-718993777/2000000000 : ℝ)*x 0 + (1426464689/5000000000 : ℝ)*x 1 + (595500921/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (718993777/2000000000 : ℝ)^77 ≤ (3436102955783/12500000000000 : ℝ)^61 := by
    have hnat : (718993777 : ℕ)^77*12500000000000^61 ≤ 3436102955783^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718993777 2000000000 3436102955783 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426464689/5000000000 : ℝ)^77 ≤ (10265652033893/50000000000000 : ℝ)^61 := by
    have hnat : (1426464689 : ℕ)^77*50000000000000^61 ≤ 10265652033893^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426464689 5000000000 10265652033893 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (595500921/1000000000 : ℝ)^77 ≤ (25989936135809/50000000000000 : ℝ)^61 := by
    have hnat : (595500921 : ℕ)^77*50000000000000^61 ≤ 25989936135809^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595500921 1000000000 25989936135809 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-718993777/2000000000 : ℝ), (1426464689/5000000000 : ℝ), (595500921/1000000000 : ℝ)] ![(3436102955783/12500000000000 : ℝ), (10265652033893/50000000000000 : ℝ), (25989936135809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-718993777/2000000000 : ℝ)|^77 ≤ (3436102955783/12500000000000 : ℝ)^61
        have hw : |(-718993777/2000000000 : ℝ)|=(718993777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1426464689/5000000000 : ℝ)|^77 ≤ (10265652033893/50000000000000 : ℝ)^61
        have hw : |(1426464689/5000000000 : ℝ)|=(1426464689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(595500921/1000000000 : ℝ)|^77 ≤ (25989936135809/50000000000000 : ℝ)^61
        have hw : |(595500921/1000000000 : ℝ)|=(595500921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (713695401/2500000000 : ℝ)*x 0 + (-1791445839/5000000000 : ℝ)*x 1 + (23856221/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (713695401/2500000000 : ℝ)^77 ≤ (642129108771/3125000000000 : ℝ)^61 := by
    have hnat : (713695401 : ℕ)^77*3125000000000^61 ≤ 642129108771^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713695401 2500000000 642129108771 3125000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1791445839/5000000000 : ℝ)^77 ≤ (13686152306263/50000000000000 : ℝ)^61 := by
    have hnat : (1791445839 : ℕ)^77*50000000000000^61 ≤ 13686152306263^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791445839 5000000000 13686152306263 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23856221/40000000 : ℝ)^77 ≤ (52079563889539/100000000000000 : ℝ)^61 := by
    have hnat : (23856221 : ℕ)^77*100000000000000^61 ≤ 52079563889539^61*40000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23856221 40000000 52079563889539 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(713695401/2500000000 : ℝ), (-1791445839/5000000000 : ℝ), (23856221/40000000 : ℝ)] ![(642129108771/3125000000000 : ℝ), (13686152306263/50000000000000 : ℝ), (52079563889539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(713695401/2500000000 : ℝ)|^77 ≤ (642129108771/3125000000000 : ℝ)^61
        have hw : |(713695401/2500000000 : ℝ)|=(713695401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1791445839/5000000000 : ℝ)|^77 ≤ (13686152306263/50000000000000 : ℝ)^61
        have hw : |(-1791445839/5000000000 : ℝ)|=(1791445839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(23856221/40000000 : ℝ)|^77 ≤ (52079563889539/100000000000000 : ℝ)^61
        have hw : |(23856221/40000000 : ℝ)|=(23856221/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5869194281/10000000000 : ℝ)*x 0 + (5496638307/10000000000 : ℝ)*x 1 + (-447748223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5869194281/10000000000 : ℝ)^77 ≤ (51036133010557/100000000000000 : ℝ)^61 := by
    have hnat : (5869194281 : ℕ)^77*100000000000000^61 ≤ 51036133010557^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5869194281 10000000000 51036133010557 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496638307/10000000000 : ℝ)^77 ≤ (23490698342313/50000000000000 : ℝ)^61 := by
    have hnat : (5496638307 : ℕ)^77*50000000000000^61 ≤ 23490698342313^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496638307 10000000000 23490698342313 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447748223/10000000000 : ℝ)^77 ≤ (991235149503/50000000000000 : ℝ)^61 := by
    have hnat : (447748223 : ℕ)^77*50000000000000^61 ≤ 991235149503^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447748223 10000000000 991235149503 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5869194281/10000000000 : ℝ), (5496638307/10000000000 : ℝ), (-447748223/10000000000 : ℝ)] ![(51036133010557/100000000000000 : ℝ), (23490698342313/50000000000000 : ℝ), (991235149503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5869194281/10000000000 : ℝ)|^77 ≤ (51036133010557/100000000000000 : ℝ)^61
        have hw : |(5869194281/10000000000 : ℝ)|=(5869194281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496638307/10000000000 : ℝ)|^77 ≤ (23490698342313/50000000000000 : ℝ)^61
        have hw : |(5496638307/10000000000 : ℝ)|=(5496638307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-447748223/10000000000 : ℝ)|^77 ≤ (991235149503/50000000000000 : ℝ)^61
        have hw : |(-447748223/10000000000 : ℝ)|=(447748223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316057_s1_s1_25 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (819591359/2000000000 : ℝ)*x 0 + (2540810073/5000000000 : ℝ)*x 1 + (333683971/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819591359/2000000000 : ℝ)^77 ≤ (32429907000403/100000000000000 : ℝ)^61 := by
    have hnat : (819591359 : ℕ)^77*100000000000000^61 ≤ 32429907000403^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819591359 2000000000 32429907000403 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540810073/5000000000 : ℝ)^77 ≤ (42548869012981/100000000000000 : ℝ)^61 := by
    have hnat : (2540810073 : ℕ)^77*100000000000000^61 ≤ 42548869012981^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540810073 5000000000 42548869012981 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333683971/1000000000 : ℝ)^77 ≤ (25021223975631/100000000000000 : ℝ)^61 := by
    have hnat : (333683971 : ℕ)^77*100000000000000^61 ≤ 25021223975631^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333683971 1000000000 25021223975631 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(819591359/2000000000 : ℝ), (2540810073/5000000000 : ℝ), (333683971/1000000000 : ℝ)] ![(32429907000403/100000000000000 : ℝ), (42548869012981/100000000000000 : ℝ), (25021223975631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(819591359/2000000000 : ℝ)|^77 ≤ (32429907000403/100000000000000 : ℝ)^61
        have hw : |(819591359/2000000000 : ℝ)|=(819591359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2540810073/5000000000 : ℝ)|^77 ≤ (42548869012981/100000000000000 : ℝ)^61
        have hw : |(2540810073/5000000000 : ℝ)|=(2540810073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(333683971/1000000000 : ℝ)|^77 ≤ (25021223975631/100000000000000 : ℝ)^61
        have hw : |(333683971/1000000000 : ℝ)|=(333683971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316057_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((15697/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15697/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(77849/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(77849/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7733/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7733/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((41747/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41747/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41689/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(41689/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(511/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(511/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  have s1_pow0 : (15697/20000 : ℝ) ^ (19/4 : ℝ) ≤ (31640012572133181997/100000000000000000000 : ℝ) := by
    have hpowers : (15697/20000 : ℝ)^19 ≤ (31640012572133181997/100000000000000000000 : ℝ)^4 := by
      have hnat : (15697 : ℕ)^19*100000000000000000000^4 ≤ 31640012572133181997^4*20000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15697 20000 31640012572133181997 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15697/20000 : ℝ)) (X := (31640012572133181997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (131640012572133181997/100000000000000000000 : ℝ) ≤ (10595813313767773/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (131640012572133181997/100000000000000000000 : ℝ)^4 ≤ (10595813313767773/10000000000000000 : ℝ)^19 := by
      have hnat : (131640012572133181997 : ℕ)^4*10000000000000000^19 ≤ 10595813313767773^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131640012572133181997 100000000000000000000 10595813313767773 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10595813313767773/10000000000000000 : ℝ)) (X := (131640012572133181997/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (81640012572133181997/50000000000000000000 : ℝ) ≤ (1108735650991241/1000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (81640012572133181997/50000000000000000000 : ℝ)^4 ≤ (1108735650991241/1000000000000000 : ℝ)^19 := by
      have hnat : (81640012572133181997 : ℕ)^4*1000000000000000^19 ≤ 1108735650991241^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81640012572133181997 50000000000000000000 1108735650991241 1000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1108735650991241/1000000000000000 : ℝ)) (X := (81640012572133181997/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(595813313767773/7848500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(491543196144637/7848500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (15697/20000 : ℝ)) (alpha := (595813313767773/7848500000000000 : ℝ)) (beta := (491543196144637/7848500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15697/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(595813313767773/7848500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(491543196144637/7848500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (77849/100000 : ℝ) ^ (19/4 : ℝ) ≤ (15220255260068304281/50000000000000000000 : ℝ) := by
    have hpowers : (77849/100000 : ℝ)^19 ≤ (15220255260068304281/50000000000000000000 : ℝ)^4 := by
      have hnat : (77849 : ℕ)^19*50000000000000000000^4 ≤ 15220255260068304281^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77849 100000 15220255260068304281 50000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77849/100000 : ℝ)) (X := (15220255260068304281/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (65220255260068304281/50000000000000000000 : ℝ) ≤ (10575413717787261/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (65220255260068304281/50000000000000000000 : ℝ)^4 ≤ (10575413717787261/10000000000000000 : ℝ)^19 := by
      have hnat : (65220255260068304281 : ℕ)^4*10000000000000000^19 ≤ 10575413717787261^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65220255260068304281 50000000000000000000 10575413717787261 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10575413717787261/10000000000000000 : ℝ)) (X := (65220255260068304281/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (40220255260068304281/25000000000000000000 : ℝ) ≤ (5526430363294303/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (40220255260068304281/25000000000000000000 : ℝ)^4 ≤ (5526430363294303/5000000000000000 : ℝ)^19 := by
      have hnat : (40220255260068304281 : ℕ)^4*5000000000000000^19 ≤ 5526430363294303^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40220255260068304281 25000000000000000000 5526430363294303 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5526430363294303/5000000000000000 : ℝ)) (X := (40220255260068304281/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(575413717787261/7784900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(95489401760269/1556980000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (77849/100000 : ℝ)) (alpha := (575413717787261/7784900000000000 : ℝ)) (beta := (95489401760269/1556980000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (77849/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(575413717787261/7784900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(95489401760269/1556980000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (7733/20000 : ℝ) ^ (19/4 : ℝ) ≤ (1095873862929225601/100000000000000000000 : ℝ) := by
    have hpowers : (7733/20000 : ℝ)^19 ≤ (1095873862929225601/100000000000000000000 : ℝ)^4 := by
      have hnat : (7733 : ℕ)^19*100000000000000000000^4 ≤ 1095873862929225601^4*20000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7733 20000 1095873862929225601 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7733/20000 : ℝ)) (X := (1095873862929225601/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101095873862929225601/100000000000000000000 : ℝ) ≤ (5011485937529489/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (101095873862929225601/100000000000000000000 : ℝ)^4 ≤ (5011485937529489/5000000000000000 : ℝ)^19 := by
      have hnat : (101095873862929225601 : ℕ)^4*5000000000000000^19 ≤ 5011485937529489^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101095873862929225601 100000000000000000000 5011485937529489 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011485937529489/5000000000000000 : ℝ)) (X := (101095873862929225601/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51095873862929225601/50000000000000000000 : ℝ) ≤ (1255718499209337/1250000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (51095873862929225601/50000000000000000000 : ℝ)^4 ≤ (1255718499209337/1250000000000000 : ℝ)^19 := by
      have hnat : (51095873862929225601 : ℕ)^4*1250000000000000^19 ≤ 1255718499209337^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51095873862929225601 50000000000000000000 1255718499209337 1250000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1255718499209337/1250000000000000 : ℝ)) (X := (51095873862929225601/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(11485937529489/1933250000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(11388059307859/1933250000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (7733/20000 : ℝ)) (alpha := (11485937529489/1933250000000000 : ℝ)) (beta := (11388059307859/1933250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (7733/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(11485937529489/1933250000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(11388059307859/1933250000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((3203874483/10000000000 : ℝ)*X 1 0+(-3196955609/10000000000 : ℝ)*X 1 1+(6004534769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2832981971/5000000000 : ℝ)*X 2 0+(354782367/625000000 : ℝ)*X 2 1+(-495669947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4532698053/10000000000 : ℝ)*X 0 0+(227057053/500000000 : ℝ)*X 0 1+(433252857/1250000000 : ℝ)*X 0 2+(4532698053/10000000000 : ℝ)*X 1 0+(227057053/500000000 : ℝ)*X 1 1+(433252857/1250000000 : ℝ)*X 1 2+(4532698053/10000000000 : ℝ)*X 2 0+(227057053/500000000 : ℝ)*X 2 1+(433252857/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-121583177/400000000 : ℝ)*X 0 0+(10819177/39062500 : ℝ)*X 0 1+(649337667/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((606746599/2000000000 : ℝ)*X 1 0+(-2764381959/10000000000 : ℝ)*X 1 1+(52019393/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2642502137/5000000000 : ℝ)*X 2 0+(624641259/1000000000 : ℝ)*X 2 1+(-34970713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((2313355753/5000000000 : ℝ)*X 0 0+(2734184071/5000000000 : ℝ)*X 0 1+(2286262339/10000000000 : ℝ)*X 0 2+(2313355753/5000000000 : ℝ)*X 1 0+(2734184071/5000000000 : ℝ)*X 1 1+(2286262339/10000000000 : ℝ)*X 1 2+(2313355753/5000000000 : ℝ)*X 2 0+(2734184071/5000000000 : ℝ)*X 2 1+(2286262339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-1388304287/5000000000 : ℝ)*X 0 0+(3032840867/10000000000 : ℝ)*X 0 1+(3246688891/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((110850721/400000000 : ℝ)*X 1 0+(-3027007479/10000000000 : ℝ)*X 1 1+(1625606277/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((6236155183/10000000000 : ℝ)*X 2 0+(5295716483/10000000000 : ℝ)*X 2 1+(-17484821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((1091877903/2000000000 : ℝ)*X 0 0+(4636090379/10000000000 : ℝ)*X 0 1+(2286259457/10000000000 : ℝ)*X 0 2+(1091877903/2000000000 : ℝ)*X 1 0+(4636090379/10000000000 : ℝ)*X 1 1+(2286259457/10000000000 : ℝ)*X 1 2+(1091877903/2000000000 : ℝ)*X 2 0+(4636090379/10000000000 : ℝ)*X 2 1+(2286259457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-718993777/2000000000 : ℝ)*X 0 0+(1426464689/5000000000 : ℝ)*X 0 1+(595500921/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((713695401/2500000000 : ℝ)*X 1 0+(-1791445839/5000000000 : ℝ)*X 1 1+(23856221/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((5869194281/10000000000 : ℝ)*X 2 0+(5496638307/10000000000 : ℝ)*X 2 1+(-447748223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((819591359/2000000000 : ℝ)*X 0 0+(2540810073/5000000000 : ℝ)*X 0 1+(333683971/1000000000 : ℝ)*X 0 2+(819591359/2000000000 : ℝ)*X 1 0+(2540810073/5000000000 : ℝ)*X 1 1+(333683971/1000000000 : ℝ)*X 1 2+(819591359/2000000000 : ℝ)*X 2 0+(2540810073/5000000000 : ℝ)*X 2 1+(333683971/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316057_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((41747/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41747/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15718450080925353493519268037/1718126028718000000000000000000000 : ℝ) := by norm_num
    linear_combination (2034621/250000000000 : ℝ)*(base23) + (188991/1000000000000 : ℝ)*(base39) + (410363069727/100000000000 : ℝ)*(base59) + (37597073937/20000000000 : ℝ)*(base60) + (1544707029779/200000000000 : ℝ)*(major_s1_0) + (1544707029779/200000000000 : ℝ)*(major_s1_1) + (1544707029779/200000000000 : ℝ)*(major_s1_2) + (20947267/500000000000 : ℝ)*(sp_s1_2) + (2772453675079/250000000000 : ℝ)*(sp_s1_7) + (693104422571/62500000000 : ℝ)*(sp_s1_8) + (5544882333649/500000000000 : ℝ)*(sp_s1_9) + (544654172921/125000000000 : ℝ)*(sp_s1_12) + (143939179/1000000000000 : ℝ)*(sp_s1_14) + (2395571/125000000000 : ℝ)*(sp_s1_25) + (136164142123/31250000000 : ℝ)*(f.failure) + (2772453675079/250000000000 : ℝ)*(f.sum) + (17562198678898234737/60200631700000000000000000000000 : ℝ)*base63 + (174183662752201/386650000000000000000000000 : ℝ)*base64 + (675523085232141/1556980000000000000000000000 : ℝ)*base66 + (26749092126837/193325000000000000000000000 : ℝ)*base69 + (345883462133476383/1103499100000000000000000000000 : ℝ)*base70 + (228423209441857/1569700000000000000000000000 : ℝ)*base72 + (52865193663077/311396000000000000000000000 : ℝ)*base74 + (865772875572273/1569700000000000000000000000 : ℝ)*base76 + (18596038867159902149/61099787650000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (33/390625000000000 : ℝ)*base86 + (33/390625000000000 : ℝ)*base88 + (33/390625000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41689/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(41689/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4620191429975972736140129889/290223991337500000000000000000000 : ℝ) := by norm_num
    linear_combination (3064419/200000000000 : ℝ)*(base21) + (2051290144331/500000000000 : ℝ)*(base59) + (1112608388827/500000000000 : ℝ)*(base60) + (1544460344871/200000000000 : ℝ)*(major_s1_0) + (1544460344871/200000000000 : ℝ)*(major_s1_1) + (1544460344871/200000000000 : ℝ)*(major_s1_2) + (881631/1000000000000 : ℝ)*(sp_s1_1) + (14839789/500000000000 : ℝ)*(sp_s1_6) + (239658481/1000000000000 : ℝ)*(sp_s1_7) + (5543900887751/500000000000 : ℝ)*(sp_s1_13) + (346501267261/31250000000 : ℝ)*(sp_s1_14) + (2771984893233/250000000000 : ℝ)*(sp_s1_15) + (4356527028679/1000000000000 : ℝ)*(sp_s1_18) + (17307791/200000000000 : ℝ)*(sp_s1_21) + (4356556708257/1000000000000 : ℝ)*(f.failure) + (11088041433983/1000000000000 : ℝ)*(f.sum) + (181481242279115491/1627044100000000000000000000000 : ℝ)*base62 + (152180139597/2612500000000000000000000 : ℝ)*base65 + (149706133436639/311396000000000000000000000 : ℝ)*base66 + (5608868554327/10450000000000000000000000 : ℝ)*base68 + (14733671356271719/29824300000000000000000000000 : ℝ)*base71 + (760290984545393/1569700000000000000000000000 : ℝ)*base72 + (542043028947791/1556980000000000000000000000 : ℝ)*base75 + (204133933010857/1569700000000000000000000000 : ℝ)*base76 + (784199125441998831/61099787650000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (11049/100000000000000000 : ℝ)*base87 + (11049/100000000000000000 : ℝ)*base89 + (11049/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(511/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(511/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (370852782396644022187791747/27772630750000000000000000000000 : ℝ) := by norm_num
    linear_combination (3414887/1000000000000 : ℝ)*(base40) + (295579/100000000000 : ℝ)*(base50) + (52729892349/62500000000 : ℝ)*(base59) + (354141079633/125000000000 : ℝ)*(major_s1_0) + (354141079633/125000000000 : ℝ)*(major_s1_1) + (354141079633/125000000000 : ℝ)*(major_s1_2) + (6202011/500000000000 : ℝ)*(sp_s1_1) + (8161721/200000000000 : ℝ)*(sp_s1_9) + (13303949/125000000000 : ℝ)*(sp_s1_12) + (67146273/1000000000000 : ℝ)*(sp_s1_15) + (4067935895063/1000000000000 : ℝ)*(sp_s1_19) + (4067923491041/1000000000000 : ℝ)*(sp_s1_20) + (813565588037/200000000000 : ℝ)*(sp_s1_21) + (199776312051/125000000000 : ℝ)*(sp_s1_25) + (1598316927999/1000000000000 : ℝ)*(f.failure) + (4067935895063/1000000000000 : ℝ)*(f.sum) + (1915522710629673641/13681961750000000000000000000000 : ℝ)*base63 + (7389775748133/87875000000000000000000000 : ℝ)*base64 + (165309179046797/389245000000000000000000000 : ℝ)*base66 + (12258857364293/87875000000000000000000000 : ℝ)*base68 + (2475826398211103/7837351562500000000000000000 : ℝ)*base71 + (47850015204589/89187500000000000000000000 : ℝ)*base72 + (188947485906741/1946225000000000000000000000 : ℝ)*base75 + (3910592048761/22296875000000000000000000 : ℝ)*base77 + (12293539951259118647/13886315375000000000000000000000 : ℝ)*base78 + (81257/100000000000000000 : ℝ)*base86 + (81257/100000000000000000 : ℝ)*base88 + (81257/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((15697/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15697/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(77849/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(77849/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7733/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7733/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((41747/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41747/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41689/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(41689/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(511/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(511/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316057_s1 p hpa hpb X hX hprev0

#print axioms solution
