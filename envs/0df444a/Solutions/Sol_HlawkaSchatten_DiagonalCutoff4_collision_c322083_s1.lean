-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c322083_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:48:04.216637+00:00
-- url     : https://prove2.me/submissions/8667cfee-0973-4758-aa13-d49b7205fb15

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
theorem collision_support_c322083_s1_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-28845963/125000000 : ℝ)*x 0 + (2356855153/5000000000 : ℝ)*x 1 + (5187854567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28845963/125000000 : ℝ)^83 ≤ (4064783629177/25000000000000 : ℝ)^67 := by
    have hnat : (28845963 : ℕ)^83*25000000000000^67 ≤ 4064783629177^67*125000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28845963 125000000 4064783629177 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2356855153/5000000000 : ℝ)^83 ≤ (615431926077/1562500000000 : ℝ)^67 := by
    have hnat : (2356855153 : ℕ)^83*1562500000000^67 ≤ 615431926077^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356855153 5000000000 615431926077 1562500000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5187854567/10000000000 : ℝ)^83 ≤ (4435322220109/10000000000000 : ℝ)^67 := by
    have hnat : (5187854567 : ℕ)^83*10000000000000^67 ≤ 4435322220109^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187854567 10000000000 4435322220109 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-28845963/125000000 : ℝ), (2356855153/5000000000 : ℝ), (5187854567/10000000000 : ℝ)] ![(4064783629177/25000000000000 : ℝ), (615431926077/1562500000000 : ℝ), (4435322220109/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-28845963/125000000 : ℝ)|^83 ≤ (4064783629177/25000000000000 : ℝ)^67
        have hw : |(-28845963/125000000 : ℝ)|=(28845963/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2356855153/5000000000 : ℝ)|^83 ≤ (615431926077/1562500000000 : ℝ)^67
        have hw : |(2356855153/5000000000 : ℝ)|=(2356855153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5187854567/10000000000 : ℝ)|^83 ≤ (4435322220109/10000000000000 : ℝ)^67
        have hw : |(5187854567/10000000000 : ℝ)|=(5187854567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1323855251/2000000000 : ℝ)*x 0 + (-920741867/10000000000 : ℝ)*x 1 + (853240091/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323855251/2000000000 : ℝ)^83 ≤ (2999086488631/5000000000000 : ℝ)^67 := by
    have hnat : (1323855251 : ℕ)^83*5000000000000^67 ≤ 2999086488631^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323855251 2000000000 2999086488631 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (920741867/10000000000 : ℝ)^83 ≤ (2604580830879/50000000000000 : ℝ)^67 := by
    have hnat : (920741867 : ℕ)^83*50000000000000^67 ≤ 2604580830879^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920741867 10000000000 2604580830879 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (853240091/2000000000 : ℝ)^83 ≤ (34809108552537/100000000000000 : ℝ)^67 := by
    have hnat : (853240091 : ℕ)^83*100000000000000^67 ≤ 34809108552537^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853240091 2000000000 34809108552537 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323855251/2000000000 : ℝ), (-920741867/10000000000 : ℝ), (853240091/2000000000 : ℝ)] ![(2999086488631/5000000000000 : ℝ), (2604580830879/50000000000000 : ℝ), (34809108552537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323855251/2000000000 : ℝ)|^83 ≤ (2999086488631/5000000000000 : ℝ)^67
        have hw : |(1323855251/2000000000 : ℝ)|=(1323855251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-920741867/10000000000 : ℝ)|^83 ≤ (2604580830879/50000000000000 : ℝ)^67
        have hw : |(-920741867/10000000000 : ℝ)|=(920741867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(853240091/2000000000 : ℝ)|^83 ≤ (34809108552537/100000000000000 : ℝ)^67
        have hw : |(853240091/2000000000 : ℝ)|=(853240091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3530128437/10000000000 : ℝ)*x 0 + (3134222661/5000000000 : ℝ)*x 1 + (-2323996379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3530128437/10000000000 : ℝ)^83 ≤ (27529617664231/100000000000000 : ℝ)^67 := by
    have hnat : (3530128437 : ℕ)^83*100000000000000^67 ≤ 27529617664231^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3530128437 10000000000 27529617664231 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3134222661/5000000000 : ℝ)^83 ≤ (56068688965027/100000000000000 : ℝ)^67 := by
    have hnat : (3134222661 : ℕ)^83*100000000000000^67 ≤ 56068688965027^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134222661 5000000000 56068688965027 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2323996379/10000000000 : ℝ)^83 ≤ (16401693356499/100000000000000 : ℝ)^67 := by
    have hnat : (2323996379 : ℕ)^83*100000000000000^67 ≤ 16401693356499^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323996379 10000000000 16401693356499 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3530128437/10000000000 : ℝ), (3134222661/5000000000 : ℝ), (-2323996379/10000000000 : ℝ)] ![(27529617664231/100000000000000 : ℝ), (56068688965027/100000000000000 : ℝ), (16401693356499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3530128437/10000000000 : ℝ)|^83 ≤ (27529617664231/100000000000000 : ℝ)^67
        have hw : |(3530128437/10000000000 : ℝ)|=(3530128437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3134222661/5000000000 : ℝ)|^83 ≤ (56068688965027/100000000000000 : ℝ)^67
        have hw : |(3134222661/5000000000 : ℝ)|=(3134222661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2323996379/10000000000 : ℝ)|^83 ≤ (16401693356499/100000000000000 : ℝ)^67
        have hw : |(-2323996379/10000000000 : ℝ)|=(2323996379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2368608773/10000000000 : ℝ)*x 0 + (36570159/78125000 : ℝ)*x 1 + (258471891/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2368608773/10000000000 : ℝ)^83 ≤ (2099078209239/12500000000000 : ℝ)^67 := by
    have hnat : (2368608773 : ℕ)^83*12500000000000^67 ≤ 2099078209239^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2368608773 10000000000 2099078209239 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36570159/78125000 : ℝ)^83 ≤ (9762280698761/25000000000000 : ℝ)^67 := by
    have hnat : (36570159 : ℕ)^83*25000000000000^67 ≤ 9762280698761^67*78125000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36570159 78125000 9762280698761 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258471891/500000000 : ℝ)^83 ≤ (44158251522941/100000000000000 : ℝ)^67 := by
    have hnat : (258471891 : ℕ)^83*100000000000000^67 ≤ 44158251522941^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258471891 500000000 44158251522941 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2368608773/10000000000 : ℝ), (36570159/78125000 : ℝ), (258471891/500000000 : ℝ)] ![(2099078209239/12500000000000 : ℝ), (9762280698761/25000000000000 : ℝ), (44158251522941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2368608773/10000000000 : ℝ)|^83 ≤ (2099078209239/12500000000000 : ℝ)^67
        have hw : |(-2368608773/10000000000 : ℝ)|=(2368608773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36570159/78125000 : ℝ)|^83 ≤ (9762280698761/25000000000000 : ℝ)^67
        have hw : |(36570159/78125000 : ℝ)|=(36570159/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258471891/500000000 : ℝ)|^83 ≤ (44158251522941/100000000000000 : ℝ)^67
        have hw : |(258471891/500000000 : ℝ)|=(258471891/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1305372353/2000000000 : ℝ)*x 0 + (-429586877/10000000000 : ℝ)*x 1 + (467894209/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305372353/2000000000 : ℝ)^83 ≤ (58946051973237/100000000000000 : ℝ)^67 := by
    have hnat : (1305372353 : ℕ)^83*100000000000000^67 ≤ 58946051973237^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305372353 2000000000 58946051973237 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429586877/10000000000 : ℝ)^83 ≤ (506471992387/25000000000000 : ℝ)^67 := by
    have hnat : (429586877 : ℕ)^83*25000000000000^67 ≤ 506471992387^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429586877 10000000000 506471992387 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467894209/1000000000 : ℝ)^83 ≤ (1561122401597/4000000000000 : ℝ)^67 := by
    have hnat : (467894209 : ℕ)^83*4000000000000^67 ≤ 1561122401597^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467894209 1000000000 1561122401597 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1305372353/2000000000 : ℝ), (-429586877/10000000000 : ℝ), (467894209/1000000000 : ℝ)] ![(58946051973237/100000000000000 : ℝ), (506471992387/25000000000000 : ℝ), (1561122401597/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1305372353/2000000000 : ℝ)|^83 ≤ (58946051973237/100000000000000 : ℝ)^67
        have hw : |(1305372353/2000000000 : ℝ)|=(1305372353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429586877/10000000000 : ℝ)|^83 ≤ (506471992387/25000000000000 : ℝ)^67
        have hw : |(-429586877/10000000000 : ℝ)|=(429586877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(467894209/1000000000 : ℝ)|^83 ≤ (1561122401597/4000000000000 : ℝ)^67
        have hw : |(467894209/1000000000 : ℝ)|=(467894209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (329329217/1000000000 : ℝ)*x 0 + (6779459737/10000000000 : ℝ)*x 1 + (-960496333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329329217/1000000000 : ℝ)^83 ≤ (2526024091483/10000000000000 : ℝ)^67 := by
    have hnat : (329329217 : ℕ)^83*10000000000000^67 ≤ 2526024091483^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329329217 1000000000 2526024091483 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6779459737/10000000000 : ℝ)^83 ≤ (61785058827523/100000000000000 : ℝ)^67 := by
    have hnat : (6779459737 : ℕ)^83*100000000000000^67 ≤ 61785058827523^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6779459737 10000000000 61785058827523 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (960496333/5000000000 : ℝ)^83 ≤ (6477350118161/50000000000000 : ℝ)^67 := by
    have hnat : (960496333 : ℕ)^83*50000000000000^67 ≤ 6477350118161^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960496333 5000000000 6477350118161 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329329217/1000000000 : ℝ), (6779459737/10000000000 : ℝ), (-960496333/5000000000 : ℝ)] ![(2526024091483/10000000000000 : ℝ), (61785058827523/100000000000000 : ℝ), (6477350118161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329329217/1000000000 : ℝ)|^83 ≤ (2526024091483/10000000000000 : ℝ)^67
        have hw : |(329329217/1000000000 : ℝ)|=(329329217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6779459737/10000000000 : ℝ)|^83 ≤ (61785058827523/100000000000000 : ℝ)^67
        have hw : |(6779459737/10000000000 : ℝ)|=(6779459737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-960496333/5000000000 : ℝ)|^83 ≤ (6477350118161/50000000000000 : ℝ)^67
        have hw : |(-960496333/5000000000 : ℝ)|=(960496333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1369033969/5000000000 : ℝ)*x 0 + (2297450187/5000000000 : ℝ)*x 1 + (4939950283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1369033969/5000000000 : ℝ)^83 ≤ (4019134468203/20000000000000 : ℝ)^67 := by
    have hnat : (1369033969 : ℕ)^83*20000000000000^67 ≤ 4019134468203^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369033969 5000000000 4019134468203 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2297450187/5000000000 : ℝ)^83 ≤ (19080757855209/50000000000000 : ℝ)^67 := by
    have hnat : (2297450187 : ℕ)^83*50000000000000^67 ≤ 19080757855209^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297450187 5000000000 19080757855209 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4939950283/10000000000 : ℝ)^83 ≤ (41742811932539/100000000000000 : ℝ)^67 := by
    have hnat : (4939950283 : ℕ)^83*100000000000000^67 ≤ 41742811932539^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4939950283 10000000000 41742811932539 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1369033969/5000000000 : ℝ), (2297450187/5000000000 : ℝ), (4939950283/10000000000 : ℝ)] ![(4019134468203/20000000000000 : ℝ), (19080757855209/50000000000000 : ℝ), (41742811932539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1369033969/5000000000 : ℝ)|^83 ≤ (4019134468203/20000000000000 : ℝ)^67
        have hw : |(1369033969/5000000000 : ℝ)|=(1369033969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2297450187/5000000000 : ℝ)|^83 ≤ (19080757855209/50000000000000 : ℝ)^67
        have hw : |(2297450187/5000000000 : ℝ)|=(2297450187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4939950283/10000000000 : ℝ)|^83 ≤ (41742811932539/100000000000000 : ℝ)^67
        have hw : |(4939950283/10000000000 : ℝ)|=(4939950283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-37994819/200000000 : ℝ)*x 0 + (267532643/625000000 : ℝ)*x 1 + (2961600027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37994819/200000000 : ℝ)^83 ≤ (3194348574881/25000000000000 : ℝ)^67 := by
    have hnat : (37994819 : ℕ)^83*25000000000000^67 ≤ 3194348574881^67*200000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37994819 200000000 3194348574881 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267532643/625000000 : ℝ)^83 ≤ (17476964092163/50000000000000 : ℝ)^67 := by
    have hnat : (267532643 : ℕ)^83*50000000000000^67 ≤ 17476964092163^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267532643 625000000 17476964092163 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2961600027/5000000000 : ℝ)^83 ≤ (52268677498957/100000000000000 : ℝ)^67 := by
    have hnat : (2961600027 : ℕ)^83*100000000000000^67 ≤ 52268677498957^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2961600027 5000000000 52268677498957 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37994819/200000000 : ℝ), (267532643/625000000 : ℝ), (2961600027/5000000000 : ℝ)] ![(3194348574881/25000000000000 : ℝ), (17476964092163/50000000000000 : ℝ), (52268677498957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37994819/200000000 : ℝ)|^83 ≤ (3194348574881/25000000000000 : ℝ)^67
        have hw : |(-37994819/200000000 : ℝ)|=(37994819/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(267532643/625000000 : ℝ)|^83 ≤ (17476964092163/50000000000000 : ℝ)^67
        have hw : |(267532643/625000000 : ℝ)|=(267532643/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2961600027/5000000000 : ℝ)|^83 ≤ (52268677498957/100000000000000 : ℝ)^67
        have hw : |(2961600027/5000000000 : ℝ)|=(2961600027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (443865591/625000000 : ℝ)*x 0 + (-431676629/5000000000 : ℝ)*x 1 + (469712189/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443865591/625000000 : ℝ)^83 ≤ (65445242267089/100000000000000 : ℝ)^67 := by
    have hnat : (443865591 : ℕ)^83*100000000000000^67 ≤ 65445242267089^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443865591 625000000 65445242267089 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431676629/5000000000 : ℝ)^83 ≤ (1202497026899/25000000000000 : ℝ)^67 := by
    have hnat : (431676629 : ℕ)^83*25000000000000^67 ≤ 1202497026899^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431676629 5000000000 1202497026899 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469712189/1250000000 : ℝ)^83 ≤ (2974476960939/10000000000000 : ℝ)^67 := by
    have hnat : (469712189 : ℕ)^83*10000000000000^67 ≤ 2974476960939^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469712189 1250000000 2974476960939 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(443865591/625000000 : ℝ), (-431676629/5000000000 : ℝ), (469712189/1250000000 : ℝ)] ![(65445242267089/100000000000000 : ℝ), (1202497026899/25000000000000 : ℝ), (2974476960939/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(443865591/625000000 : ℝ)|^83 ≤ (65445242267089/100000000000000 : ℝ)^67
        have hw : |(443865591/625000000 : ℝ)|=(443865591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-431676629/5000000000 : ℝ)|^83 ≤ (1202497026899/25000000000000 : ℝ)^67
        have hw : |(-431676629/5000000000 : ℝ)|=(431676629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(469712189/1250000000 : ℝ)|^83 ≤ (2974476960939/10000000000000 : ℝ)^67
        have hw : |(469712189/1250000000 : ℝ)|=(469712189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (44546011/125000000 : ℝ)*x 0 + (1636446153/2500000000 : ℝ)*x 1 + (-1924982147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44546011/125000000 : ℝ)^83 ≤ (27854127989107/100000000000000 : ℝ)^67 := by
    have hnat : (44546011 : ℕ)^83*100000000000000^67 ≤ 27854127989107^67*125000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44546011 125000000 27854127989107 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1636446153/2500000000 : ℝ)^83 ≤ (59157834576087/100000000000000 : ℝ)^67 := by
    have hnat : (1636446153 : ℕ)^83*100000000000000^67 ≤ 59157834576087^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636446153 2500000000 59157834576087 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1924982147/10000000000 : ℝ)^83 ≤ (12988037425207/100000000000000 : ℝ)^67 := by
    have hnat : (1924982147 : ℕ)^83*100000000000000^67 ≤ 12988037425207^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924982147 10000000000 12988037425207 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44546011/125000000 : ℝ), (1636446153/2500000000 : ℝ), (-1924982147/10000000000 : ℝ)] ![(27854127989107/100000000000000 : ℝ), (59157834576087/100000000000000 : ℝ), (12988037425207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44546011/125000000 : ℝ)|^83 ≤ (27854127989107/100000000000000 : ℝ)^67
        have hw : |(44546011/125000000 : ℝ)|=(44546011/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1636446153/2500000000 : ℝ)|^83 ≤ (59157834576087/100000000000000 : ℝ)^67
        have hw : |(1636446153/2500000000 : ℝ)|=(1636446153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1924982147/10000000000 : ℝ)|^83 ≤ (12988037425207/100000000000000 : ℝ)^67
        have hw : |(-1924982147/10000000000 : ℝ)|=(1924982147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1331918823/5000000000 : ℝ)*x 0 + (166984821/400000000 : ℝ)*x 1 + (5407505959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1331918823/5000000000 : ℝ)^83 ≤ (19422967058421/100000000000000 : ℝ)^67 := by
    have hnat : (1331918823 : ℕ)^83*100000000000000^67 ≤ 19422967058421^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331918823 5000000000 19422967058421 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166984821/400000000 : ℝ)^83 ≤ (6777165249517/20000000000000 : ℝ)^67 := by
    have hnat : (166984821 : ℕ)^83*20000000000000^67 ≤ 6777165249517^67*400000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166984821 400000000 6777165249517 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407505959/10000000000 : ℝ)^83 ≤ (5836400834163/12500000000000 : ℝ)^67 := by
    have hnat : (5407505959 : ℕ)^83*12500000000000^67 ≤ 5836400834163^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407505959 10000000000 5836400834163 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1331918823/5000000000 : ℝ), (166984821/400000000 : ℝ), (5407505959/10000000000 : ℝ)] ![(19422967058421/100000000000000 : ℝ), (6777165249517/20000000000000 : ℝ), (5836400834163/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1331918823/5000000000 : ℝ)|^83 ≤ (19422967058421/100000000000000 : ℝ)^67
        have hw : |(1331918823/5000000000 : ℝ)|=(1331918823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166984821/400000000 : ℝ)|^83 ≤ (6777165249517/20000000000000 : ℝ)^67
        have hw : |(166984821/400000000 : ℝ)|=(166984821/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407505959/10000000000 : ℝ)|^83 ≤ (5836400834163/12500000000000 : ℝ)^67
        have hw : |(5407505959/10000000000 : ℝ)|=(5407505959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-968045307/5000000000 : ℝ)*x 0 + (2554527391/5000000000 : ℝ)*x 1 + (1019511691/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (968045307/5000000000 : ℝ)^83 ≤ (6540474834627/50000000000000 : ℝ)^67 := by
    have hnat : (968045307 : ℕ)^83*50000000000000^67 ≤ 6540474834627^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968045307 5000000000 6540474834627 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2554527391/5000000000 : ℝ)^83 ≤ (43520166055627/100000000000000 : ℝ)^67 := by
    have hnat : (2554527391 : ℕ)^83*100000000000000^67 ≤ 43520166055627^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2554527391 5000000000 43520166055627 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019511691/2000000000 : ℝ)^83 ≤ (8679776852229/20000000000000 : ℝ)^67 := by
    have hnat : (1019511691 : ℕ)^83*20000000000000^67 ≤ 8679776852229^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019511691 2000000000 8679776852229 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-968045307/5000000000 : ℝ), (2554527391/5000000000 : ℝ), (1019511691/2000000000 : ℝ)] ![(6540474834627/50000000000000 : ℝ), (43520166055627/100000000000000 : ℝ), (8679776852229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-968045307/5000000000 : ℝ)|^83 ≤ (6540474834627/50000000000000 : ℝ)^67
        have hw : |(-968045307/5000000000 : ℝ)|=(968045307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2554527391/5000000000 : ℝ)|^83 ≤ (43520166055627/100000000000000 : ℝ)^67
        have hw : |(2554527391/5000000000 : ℝ)|=(2554527391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1019511691/2000000000 : ℝ)|^83 ≤ (8679776852229/20000000000000 : ℝ)^67
        have hw : |(1019511691/2000000000 : ℝ)|=(1019511691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3542115807/5000000000 : ℝ)*x 0 + (-84512449/2000000000 : ℝ)*x 1 + (1015846573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3542115807/5000000000 : ℝ)^83 ≤ (32622089235739/50000000000000 : ℝ)^67 := by
    have hnat : (3542115807 : ℕ)^83*50000000000000^67 ≤ 32622089235739^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3542115807 5000000000 32622089235739 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84512449/2000000000 : ℝ)^83 ≤ (496232487389/25000000000000 : ℝ)^67 := by
    have hnat : (84512449 : ℕ)^83*25000000000000^67 ≤ 496232487389^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84512449 2000000000 496232487389 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015846573/2500000000 : ℝ)^83 ≤ (32770891575691/100000000000000 : ℝ)^67 := by
    have hnat : (1015846573 : ℕ)^83*100000000000000^67 ≤ 32770891575691^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015846573 2500000000 32770891575691 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3542115807/5000000000 : ℝ), (-84512449/2000000000 : ℝ), (1015846573/2500000000 : ℝ)] ![(32622089235739/50000000000000 : ℝ), (496232487389/25000000000000 : ℝ), (32770891575691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3542115807/5000000000 : ℝ)|^83 ≤ (32622089235739/50000000000000 : ℝ)^67
        have hw : |(3542115807/5000000000 : ℝ)|=(3542115807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84512449/2000000000 : ℝ)|^83 ≤ (496232487389/25000000000000 : ℝ)^67
        have hw : |(-84512449/2000000000 : ℝ)|=(84512449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1015846573/2500000000 : ℝ)|^83 ≤ (32770891575691/100000000000000 : ℝ)^67
        have hw : |(1015846573/2500000000 : ℝ)|=(1015846573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1707229543/5000000000 : ℝ)*x 0 + (6342947947/10000000000 : ℝ)*x 1 + (-2356693447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1707229543/5000000000 : ℝ)^83 ≤ (26416568350727/100000000000000 : ℝ)^67 := by
    have hnat : (1707229543 : ℕ)^83*100000000000000^67 ≤ 26416568350727^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707229543 5000000000 26416568350727 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6342947947/10000000000 : ℝ)^83 ≤ (28447695938627/50000000000000 : ℝ)^67 := by
    have hnat : (6342947947 : ℕ)^83*50000000000000^67 ≤ 28447695938627^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6342947947 10000000000 28447695938627 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2356693447/10000000000 : ℝ)^83 ≤ (8344019877407/50000000000000 : ℝ)^67 := by
    have hnat : (2356693447 : ℕ)^83*50000000000000^67 ≤ 8344019877407^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356693447 10000000000 8344019877407 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1707229543/5000000000 : ℝ), (6342947947/10000000000 : ℝ), (-2356693447/10000000000 : ℝ)] ![(26416568350727/100000000000000 : ℝ), (28447695938627/50000000000000 : ℝ), (8344019877407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1707229543/5000000000 : ℝ)|^83 ≤ (26416568350727/100000000000000 : ℝ)^67
        have hw : |(1707229543/5000000000 : ℝ)|=(1707229543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6342947947/10000000000 : ℝ)|^83 ≤ (28447695938627/50000000000000 : ℝ)^67
        have hw : |(6342947947/10000000000 : ℝ)|=(6342947947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2356693447/10000000000 : ℝ)|^83 ≤ (8344019877407/50000000000000 : ℝ)^67
        have hw : |(-2356693447/10000000000 : ℝ)|=(2356693447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322083_s1_s1_27 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (189812867/625000000 : ℝ)*x 0 + (4639111259/10000000000 : ℝ)*x 1 + (4631164809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189812867/625000000 : ℝ)^83 ≤ (5712031151177/25000000000000 : ℝ)^67 := by
    have hnat : (189812867 : ℕ)^83*25000000000000^67 ≤ 5712031151177^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189812867 625000000 5712031151177 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4639111259/10000000000 : ℝ)^83 ≤ (7723380297331/20000000000000 : ℝ)^67 := by
    have hnat : (4639111259 : ℕ)^83*20000000000000^67 ≤ 7723380297331^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4639111259 10000000000 7723380297331 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4631164809/10000000000 : ℝ)^83 ≤ (38534973891417/100000000000000 : ℝ)^67 := by
    have hnat : (4631164809 : ℕ)^83*100000000000000^67 ≤ 38534973891417^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4631164809 10000000000 38534973891417 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(189812867/625000000 : ℝ), (4639111259/10000000000 : ℝ), (4631164809/10000000000 : ℝ)] ![(5712031151177/25000000000000 : ℝ), (7723380297331/20000000000000 : ℝ), (38534973891417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(189812867/625000000 : ℝ)|^83 ≤ (5712031151177/25000000000000 : ℝ)^67
        have hw : |(189812867/625000000 : ℝ)|=(189812867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4639111259/10000000000 : ℝ)|^83 ≤ (7723380297331/20000000000000 : ℝ)^67
        have hw : |(4639111259/10000000000 : ℝ)|=(4639111259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4631164809/10000000000 : ℝ)|^83 ≤ (38534973891417/100000000000000 : ℝ)^67
        have hw : |(4631164809/10000000000 : ℝ)|=(4631164809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322083_s1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((15351/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15351/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1853/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(1853/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13329/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13329/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18169/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18169/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((9467/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(9467/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19337/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19337/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (15351/25000 : ℝ) ^ (41/8 : ℝ) ≤ (8213114888741818349/100000000000000000000 : ℝ) := by
    have hpowers : (15351/25000 : ℝ)^41 ≤ (8213114888741818349/100000000000000000000 : ℝ)^8 := by
      have hnat : (15351 : ℕ)^41*100000000000000000000^8 ≤ 8213114888741818349^8*25000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15351 25000 8213114888741818349 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15351/25000 : ℝ)) (X := (8213114888741818349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (108213114888741818349/100000000000000000000 : ℝ) ≤ (10155206539593233/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (108213114888741818349/100000000000000000000 : ℝ)^8 ≤ (10155206539593233/10000000000000000 : ℝ)^41 := by
      have hnat : (108213114888741818349 : ℕ)^8*10000000000000000^41 ≤ 10155206539593233^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108213114888741818349 100000000000000000000 10155206539593233 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10155206539593233/10000000000000000 : ℝ)) (X := (108213114888741818349/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (58213114888741818349/50000000000000000000 : ℝ) ≤ (1030120352063339/1000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (58213114888741818349/50000000000000000000 : ℝ)^8 ≤ (1030120352063339/1000000000000000 : ℝ)^41 := by
      have hnat : (58213114888741818349 : ℕ)^8*1000000000000000^41 ≤ 1030120352063339^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58213114888741818349 50000000000000000000 1030120352063339 1000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1030120352063339/1000000000000000 : ℝ)) (X := (58213114888741818349/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(155206539593233/6140400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(48665660346719/2046800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (15351/25000 : ℝ)) (alpha := (155206539593233/6140400000000000 : ℝ)) (beta := (48665660346719/2046800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15351/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(155206539593233/6140400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(48665660346719/2046800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1853/3125 : ℝ) ^ (41/8 : ℝ) ≤ (6866812086691752591/100000000000000000000 : ℝ) := by
    have hpowers : (1853/3125 : ℝ)^41 ≤ (6866812086691752591/100000000000000000000 : ℝ)^8 := by
      have hnat : (1853 : ℕ)^41*100000000000000000000^8 ≤ 6866812086691752591^8*3125^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1853 3125 6866812086691752591 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1853/3125 : ℝ)) (X := (6866812086691752591/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (106866812086691752591/100000000000000000000 : ℝ) ≤ (10130429860674987/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (106866812086691752591/100000000000000000000 : ℝ)^8 ≤ (10130429860674987/10000000000000000 : ℝ)^41 := by
      have hnat : (106866812086691752591 : ℕ)^8*10000000000000000^41 ≤ 10130429860674987^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106866812086691752591 100000000000000000000 10130429860674987 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10130429860674987/10000000000000000 : ℝ)) (X := (106866812086691752591/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (56866812086691752591/50000000000000000000 : ℝ) ≤ (10254279410371107/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (56866812086691752591/50000000000000000000 : ℝ)^8 ≤ (10254279410371107/10000000000000000 : ℝ)^41 := by
      have hnat : (56866812086691752591 : ℕ)^8*10000000000000000^41 ≤ 10254279410371107^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56866812086691752591 50000000000000000000 10254279410371107 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10254279410371107/10000000000000000 : ℝ)) (X := (56866812086691752591/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(130429860674987/5929600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(3096238742403/148240000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1853/3125 : ℝ)) (alpha := (130429860674987/5929600000000000 : ℝ)) (beta := (3096238742403/148240000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1853/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(130429860674987/5929600000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(3096238742403/148240000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13329/20000 : ℝ) ^ (41/8 : ℝ) ≤ (12497087425660949943/100000000000000000000 : ℝ) := by
    have hpowers : (13329/20000 : ℝ)^41 ≤ (12497087425660949943/100000000000000000000 : ℝ)^8 := by
      have hnat : (13329 : ℕ)^41*100000000000000000000^8 ≤ 12497087425660949943^8*20000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13329 20000 12497087425660949943 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13329/20000 : ℝ)) (X := (12497087425660949943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (112497087425660949943/100000000000000000000 : ℝ) ≤ (5116215044173257/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (112497087425660949943/100000000000000000000 : ℝ)^8 ≤ (5116215044173257/5000000000000000 : ℝ)^41 := by
      have hnat : (112497087425660949943 : ℕ)^8*5000000000000000^41 ≤ 5116215044173257^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112497087425660949943 100000000000000000000 5116215044173257 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5116215044173257/5000000000000000 : ℝ)) (X := (112497087425660949943/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (62497087425660949943/50000000000000000000 : ℝ) ≤ (652807806290501/625000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (62497087425660949943/50000000000000000000 : ℝ)^8 ≤ (652807806290501/625000000000000 : ℝ)^41 := by
      have hnat : (62497087425660949943 : ℕ)^8*625000000000000^41 ≤ 652807806290501^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62497087425660949943 50000000000000000000 652807806290501 625000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (652807806290501/625000000000000 : ℝ)) (X := (62497087425660949943/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(116215044173257/3332250000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(106247406150751/3332250000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (13329/20000 : ℝ)) (alpha := (116215044173257/3332250000000000 : ℝ)) (beta := (106247406150751/3332250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (13329/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(116215044173257/3332250000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(106247406150751/3332250000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-28845963/125000000 : ℝ)*X 0 0+(2356855153/5000000000 : ℝ)*X 0 1+(5187854567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1323855251/2000000000 : ℝ)*X 1 0+(-920741867/10000000000 : ℝ)*X 1 1+(853240091/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3530128437/10000000000 : ℝ)*X 2 0+(3134222661/5000000000 : ℝ)*X 2 1+(-2323996379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2368608773/10000000000 : ℝ)*X 0 0+(36570159/78125000 : ℝ)*X 0 1+(258471891/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1305372353/2000000000 : ℝ)*X 1 0+(-429586877/10000000000 : ℝ)*X 1 1+(467894209/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((329329217/1000000000 : ℝ)*X 2 0+(6779459737/10000000000 : ℝ)*X 2 1+(-960496333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1369033969/5000000000 : ℝ)*X 0 0+(2297450187/5000000000 : ℝ)*X 0 1+(4939950283/10000000000 : ℝ)*X 0 2+(1369033969/5000000000 : ℝ)*X 1 0+(2297450187/5000000000 : ℝ)*X 1 1+(4939950283/10000000000 : ℝ)*X 1 2+(1369033969/5000000000 : ℝ)*X 2 0+(2297450187/5000000000 : ℝ)*X 2 1+(4939950283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-37994819/200000000 : ℝ)*X 0 0+(267532643/625000000 : ℝ)*X 0 1+(2961600027/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((443865591/625000000 : ℝ)*X 1 0+(-431676629/5000000000 : ℝ)*X 1 1+(469712189/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((44546011/125000000 : ℝ)*X 2 0+(1636446153/2500000000 : ℝ)*X 2 1+(-1924982147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1331918823/5000000000 : ℝ)*X 0 0+(166984821/400000000 : ℝ)*X 0 1+(5407505959/10000000000 : ℝ)*X 0 2+(1331918823/5000000000 : ℝ)*X 1 0+(166984821/400000000 : ℝ)*X 1 1+(5407505959/10000000000 : ℝ)*X 1 2+(1331918823/5000000000 : ℝ)*X 2 0+(166984821/400000000 : ℝ)*X 2 1+(5407505959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-968045307/5000000000 : ℝ)*X 0 0+(2554527391/5000000000 : ℝ)*X 0 1+(1019511691/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3542115807/5000000000 : ℝ)*X 1 0+(-84512449/2000000000 : ℝ)*X 1 1+(1015846573/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1707229543/5000000000 : ℝ)*X 2 0+(6342947947/10000000000 : ℝ)*X 2 1+(-2356693447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((189812867/625000000 : ℝ)*X 0 0+(4639111259/10000000000 : ℝ)*X 0 1+(4631164809/10000000000 : ℝ)*X 0 2+(189812867/625000000 : ℝ)*X 1 0+(4639111259/10000000000 : ℝ)*X 1 1+(4631164809/10000000000 : ℝ)*X 1 2+(189812867/625000000 : ℝ)*X 2 0+(4639111259/10000000000 : ℝ)*X 2 1+(4631164809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322083_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((18169/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18169/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (506657780894023792457849087/65863032000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2598401/500000000000 : ℝ)*(base19) + (520883467227/1000000000000 : ℝ)*(base40) + (2261186550239/1000000000000 : ℝ)*(base49) + (350277745773/500000000000 : ℝ)*(base60) + (6995144146607/1000000000000 : ℝ)*(major_s1_0) + (6995144146607/1000000000000 : ℝ)*(major_s1_1) + (6995144146607/1000000000000 : ℝ)*(major_s1_2) + (511407873/1000000000000 : ℝ)*(sp_s1_0) + (43227257/1000000000000 : ℝ)*(sp_s1_1) + (2591289874573/250000000000 : ℝ)*(sp_s1_7) + (10365622482107/1000000000000 : ℝ)*(sp_s1_8) + (2073134181233/200000000000 : ℝ)*(sp_s1_9) + (226537920053/62500000000 : ℝ)*(sp_s1_13) + (2025499/250000000000 : ℝ)*(sp_s1_20) + (906153705711/250000000000 : ℝ)*(f.failure) + (2073134181233/200000000000 : ℝ)*(f.sum) + (25901369527664898851/49397274000000000000000000000000 : ℝ)*base63 + (123519527640707/3332250000000000000000000000 : ℝ)*base65 + (2656876279615269/5929600000000000000000000000 : ℝ)*base67 + (1627905017897249/3332250000000000000000000000 : ℝ)*base69 + (73181869262917005583/136408986000000000000000000000000 : ℝ)*base70 + (107563732224407/2046800000000000000000000000 : ℝ)*base72 + (81095653570019/148240000000000000000000000 : ℝ)*base75 + (1810690033966151/6140400000000000000000000000 : ℝ)*base77 + (55427414280973141/356961920000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (911/2500000000000000 : ℝ)*base86 + (911/2500000000000000 : ℝ)*base88 + (911/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((9467/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(9467/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5836653781325162027727022473/413016096500000000000000000000000 : ℝ) := by norm_num
    linear_combination (274797943283/200000000000 : ℝ)*(base40) + (2302918303217/1000000000000 : ℝ)*(base49) + (572155231443/500000000000 : ℝ)*(base60) + (7357470084603/1000000000000 : ℝ)*(major_s1_0) + (7357470084603/1000000000000 : ℝ)*(major_s1_1) + (7357470084603/1000000000000 : ℝ)*(major_s1_2) + (370371539/1000000000000 : ℝ)*(sp_s1_1) + (160147477/250000000000 : ℝ)*(sp_s1_2) + (552438471/1000000000000 : ℝ)*(sp_s1_7) + (436080992921/40000000000 : ℝ)*(sp_s1_14) + (2180425523643/200000000000 : ℝ)*(sp_s1_15) + (2725484167897/250000000000 : ℝ)*(sp_s1_16) + (381235819711/100000000000 : ℝ)*(sp_s1_20) + (79271741/1000000000000 : ℝ)*(sp_s1_22) + (381235819711/100000000000 : ℝ)*(f.failure) + (1362822157687/125000000000 : ℝ)*(f.sum) + (2164699363458653969/5488586000000000000000000000000 : ℝ)*base62 + (144575001178767/370250000000000000000000000 : ℝ)*base65 + (328477401147561/5929600000000000000000000000 : ℝ)*base67 + (27984214968561/92562500000000000000000000 : ℝ)*base69 + (10994737497530517277/15156554000000000000000000000000 : ℝ)*base71 + (236941064072397/2046800000000000000000000000 : ℝ)*base73 + (16249791204913/148240000000000000000000000 : ℝ)*base74 + (725321220488073/2046800000000000000000000000 : ℝ)*base77 + (78650756171492391/356961920000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (411/1000000000000000 : ℝ)*base86 + (411/1000000000000000 : ℝ)*base88 + (411/1000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19337/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19337/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10967363462482951257102983/823287900000000000000000000000 : ℝ) := by norm_num
    linear_combination (562369317031/500000000000 : ℝ)*(base40) + (458204075971/200000000000 : ℝ)*(base49) + (1698431/200000000000 : ℝ)*(base50) + (249754499367/1000000000000 : ℝ)*(base60) + (725511534679/100000000000 : ℝ)*(major_s1_0) + (725511534679/100000000000 : ℝ)*(major_s1_1) + (725511534679/100000000000 : ℝ)*(major_s1_2) + (21742419/62500000000 : ℝ)*(sp_s1_2) + (65213817/500000000000 : ℝ)*(sp_s1_15) + (249386167/1000000000000 : ℝ)*(sp_s1_16) + (10750904346889/1000000000000 : ℝ)*(sp_s1_21) + (2150154783851/200000000000 : ℝ)*(sp_s1_22) + (10750307082017/1000000000000 : ℝ)*(sp_s1_23) + (3759321906207/1000000000000 : ℝ)*(sp_s1_27) + (3759321906207/1000000000000 : ℝ)*(f.failure) + (10750904346889/1000000000000 : ℝ)*(f.sum) + (2987633115515720227/4939727400000000000000000000000 : ℝ)*base63 + (30325028473763/666450000000000000000000000 : ℝ)*base65 + (65187868985721/118592000000000000000000000 : ℝ)*base67 + (121540058201549/166612500000000000000000000 : ℝ)*base69 + (350343698905079711/13640898600000000000000000000000 : ℝ)*base70 + (58525314075693/204680000000000000000000000 : ℝ)*base73 + (58993654725327/74120000000000000000000000 : ℝ)*base75 + (751233271187191/614040000000000000000000000 : ℝ)*base77 + (5099983417190559/178480960000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (11107/10000000000000000 : ℝ)*base86 + (11107/10000000000000000 : ℝ)*base88 + (11107/10000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((15351/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15351/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1853/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(1853/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13329/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13329/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18169/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18169/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((9467/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(9467/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19337/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19337/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c322083_s1 p hpa hpb X hX hprev0

#print axioms solution
