-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309054_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:02:32.977741+00:00
-- url     : https://prove2.me/submissions/055e352f-fbd3-460a-ab89-bf07b884f91b

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
theorem collision_support_c309054_s1_s1_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-167202343/10000000000 : ℝ)*x 0 + (2288188103/5000000000 : ℝ)*x 1 + (-7018880941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167202343/10000000000 : ℝ)^35 ≤ (4975029387/1000000000000 : ℝ)^27 := by
    have hnat : (167202343 : ℕ)^35*1000000000000^27 ≤ 4975029387^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167202343 10000000000 4975029387 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2288188103/5000000000 : ℝ)^35 ≤ (290419349639/800000000000 : ℝ)^27 := by
    have hnat : (2288188103 : ℕ)^35*800000000000^27 ≤ 290419349639^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288188103 5000000000 290419349639 800000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7018880941/10000000000 : ℝ)^35 ≤ (31600039170381/50000000000000 : ℝ)^27 := by
    have hnat : (7018880941 : ℕ)^35*50000000000000^27 ≤ 31600039170381^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7018880941 10000000000 31600039170381 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-167202343/10000000000 : ℝ), (2288188103/5000000000 : ℝ), (-7018880941/10000000000 : ℝ)] ![(4975029387/1000000000000 : ℝ), (290419349639/800000000000 : ℝ), (31600039170381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-167202343/10000000000 : ℝ)|^35 ≤ (4975029387/1000000000000 : ℝ)^27
        have hw : |(-167202343/10000000000 : ℝ)|=(167202343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2288188103/5000000000 : ℝ)|^35 ≤ (290419349639/800000000000 : ℝ)^27
        have hw : |(2288188103/5000000000 : ℝ)|=(2288188103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7018880941/10000000000 : ℝ)|^35 ≤ (31600039170381/50000000000000 : ℝ)^27
        have hw : |(-7018880941/10000000000 : ℝ)|=(7018880941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (92059857/156250000 : ℝ)*x 0 + (-387652637/2500000000 : ℝ)*x 1 + (-624841203/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92059857/156250000 : ℝ)^35 ≤ (10074100323923/20000000000000 : ℝ)^27 := by
    have hnat : (92059857 : ℕ)^35*20000000000000^27 ≤ 10074100323923^27*156250000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92059857 156250000 10074100323923 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387652637/2500000000 : ℝ)^35 ≤ (2231473330847/25000000000000 : ℝ)^27 := by
    have hnat : (387652637 : ℕ)^35*25000000000000^27 ≤ 2231473330847^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387652637 2500000000 2231473330847 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624841203/1250000000 : ℝ)^35 ≤ (40703605040171/100000000000000 : ℝ)^27 := by
    have hnat : (624841203 : ℕ)^35*100000000000000^27 ≤ 40703605040171^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624841203 1250000000 40703605040171 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(92059857/156250000 : ℝ), (-387652637/2500000000 : ℝ), (-624841203/1250000000 : ℝ)] ![(10074100323923/20000000000000 : ℝ), (2231473330847/25000000000000 : ℝ), (40703605040171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(92059857/156250000 : ℝ)|^35 ≤ (10074100323923/20000000000000 : ℝ)^27
        have hw : |(92059857/156250000 : ℝ)|=(92059857/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-387652637/2500000000 : ℝ)|^35 ≤ (2231473330847/25000000000000 : ℝ)^27
        have hw : |(-387652637/2500000000 : ℝ)|=(387652637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-624841203/1250000000 : ℝ)|^35 ≤ (40703605040171/100000000000000 : ℝ)^27
        have hw : |(-624841203/1250000000 : ℝ)|=(624841203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1388804009/2500000000 : ℝ)*x 0 + (34397347/62500000 : ℝ)*x 1 + (1316222293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1388804009/2500000000 : ℝ)^35 ≤ (9334408144149/20000000000000 : ℝ)^27 := by
    have hnat : (1388804009 : ℕ)^35*20000000000000^27 ≤ 9334408144149^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388804009 2500000000 9334408144149 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34397347/62500000 : ℝ)^35 ≤ (23055204988657/50000000000000 : ℝ)^27 := by
    have hnat : (34397347 : ℕ)^35*50000000000000^27 ≤ 23055204988657^27*62500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34397347 62500000 23055204988657 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316222293/10000000000 : ℝ)^35 ≤ (3608774644923/50000000000000 : ℝ)^27 := by
    have hnat : (1316222293 : ℕ)^35*50000000000000^27 ≤ 3608774644923^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316222293 10000000000 3608774644923 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1388804009/2500000000 : ℝ), (34397347/62500000 : ℝ), (1316222293/10000000000 : ℝ)] ![(9334408144149/20000000000000 : ℝ), (23055204988657/50000000000000 : ℝ), (3608774644923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1388804009/2500000000 : ℝ)|^35 ≤ (9334408144149/20000000000000 : ℝ)^27
        have hw : |(1388804009/2500000000 : ℝ)|=(1388804009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34397347/62500000 : ℝ)|^35 ≤ (23055204988657/50000000000000 : ℝ)^27
        have hw : |(34397347/62500000 : ℝ)|=(34397347/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316222293/10000000000 : ℝ)|^35 ≤ (3608774644923/50000000000000 : ℝ)^27
        have hw : |(1316222293/10000000000 : ℝ)|=(1316222293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (218642389/400000000 : ℝ)*x 0 + (2714502433/5000000000 : ℝ)*x 1 + (-194974179/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218642389/400000000 : ℝ)^35 ≤ (11425843457007/25000000000000 : ℝ)^27 := by
    have hnat : (218642389 : ℕ)^35*25000000000000^27 ≤ 11425843457007^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218642389 400000000 11425843457007 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714502433/5000000000 : ℝ)^35 ≤ (2831384401831/6250000000000 : ℝ)^27 := by
    have hnat : (2714502433 : ℕ)^35*6250000000000^27 ≤ 2831384401831^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714502433 5000000000 2831384401831 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194974179/1250000000 : ℝ)^35 ≤ (2248618930499/25000000000000 : ℝ)^27 := by
    have hnat : (194974179 : ℕ)^35*25000000000000^27 ≤ 2248618930499^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194974179 1250000000 2248618930499 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218642389/400000000 : ℝ), (2714502433/5000000000 : ℝ), (-194974179/1250000000 : ℝ)] ![(11425843457007/25000000000000 : ℝ), (2831384401831/6250000000000 : ℝ), (2248618930499/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218642389/400000000 : ℝ)|^35 ≤ (11425843457007/25000000000000 : ℝ)^27
        have hw : |(218642389/400000000 : ℝ)|=(218642389/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714502433/5000000000 : ℝ)|^35 ≤ (2831384401831/6250000000000 : ℝ)^27
        have hw : |(2714502433/5000000000 : ℝ)|=(2714502433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194974179/1250000000 : ℝ)|^35 ≤ (2248618930499/25000000000000 : ℝ)^27
        have hw : |(-194974179/1250000000 : ℝ)|=(194974179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-24544811/2000000000 : ℝ)*x 0 + (2096799127/10000000000 : ℝ)*x 1 + (-8938986059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24544811/2000000000 : ℝ)^35 ≤ (333185922587/100000000000000 : ℝ)^27 := by
    have hnat : (24544811 : ℕ)^35*100000000000000^27 ≤ 333185922587^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24544811 2000000000 333185922587 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2096799127/10000000000 : ℝ)^35 ≤ (527954649713/4000000000000 : ℝ)^27 := by
    have hnat : (2096799127 : ℕ)^35*4000000000000^27 ≤ 527954649713^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096799127 10000000000 527954649713 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8938986059/10000000000 : ℝ)^35 ≤ (43233973910039/50000000000000 : ℝ)^27 := by
    have hnat : (8938986059 : ℕ)^35*50000000000000^27 ≤ 43233973910039^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8938986059 10000000000 43233973910039 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24544811/2000000000 : ℝ), (2096799127/10000000000 : ℝ), (-8938986059/10000000000 : ℝ)] ![(333185922587/100000000000000 : ℝ), (527954649713/4000000000000 : ℝ), (43233973910039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24544811/2000000000 : ℝ)|^35 ≤ (333185922587/100000000000000 : ℝ)^27
        have hw : |(-24544811/2000000000 : ℝ)|=(24544811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2096799127/10000000000 : ℝ)|^35 ≤ (527954649713/4000000000000 : ℝ)^27
        have hw : |(2096799127/10000000000 : ℝ)|=(2096799127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8938986059/10000000000 : ℝ)|^35 ≤ (43233973910039/50000000000000 : ℝ)^27
        have hw : |(-8938986059/10000000000 : ℝ)|=(8938986059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (982619943/2500000000 : ℝ)*x 0 + (-3163721/39062500 : ℝ)*x 1 + (-7287197291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (982619943/2500000000 : ℝ)^35 ≤ (14902231064419/50000000000000 : ℝ)^27 := by
    have hnat : (982619943 : ℕ)^35*50000000000000^27 ≤ 14902231064419^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982619943 2500000000 14902231064419 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3163721/39062500 : ℝ)^35 ≤ (3846027693183/100000000000000 : ℝ)^27 := by
    have hnat : (3163721 : ℕ)^35*100000000000000^27 ≤ 3846027693183^27*39062500^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3163721 39062500 3846027693183 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7287197291/10000000000 : ℝ)^35 ≤ (66349510167769/100000000000000 : ℝ)^27 := by
    have hnat : (7287197291 : ℕ)^35*100000000000000^27 ≤ 66349510167769^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7287197291 10000000000 66349510167769 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(982619943/2500000000 : ℝ), (-3163721/39062500 : ℝ), (-7287197291/10000000000 : ℝ)] ![(14902231064419/50000000000000 : ℝ), (3846027693183/100000000000000 : ℝ), (66349510167769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(982619943/2500000000 : ℝ)|^35 ≤ (14902231064419/50000000000000 : ℝ)^27
        have hw : |(982619943/2500000000 : ℝ)|=(982619943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3163721/39062500 : ℝ)|^35 ≤ (3846027693183/100000000000000 : ℝ)^27
        have hw : |(-3163721/39062500 : ℝ)|=(3163721/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7287197291/10000000000 : ℝ)|^35 ≤ (66349510167769/100000000000000 : ℝ)^27
        have hw : |(-7287197291/10000000000 : ℝ)|=(7287197291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3358107097/10000000000 : ℝ)*x 0 + (7939950223/10000000000 : ℝ)*x 1 + (400173129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3358107097/10000000000 : ℝ)^35 ≤ (972160792929/4000000000000 : ℝ)^27 := by
    have hnat : (3358107097 : ℕ)^35*4000000000000^27 ≤ 972160792929^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3358107097 10000000000 972160792929 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7939950223/10000000000 : ℝ)^35 ≤ (74153927660551/100000000000000 : ℝ)^27 := by
    have hnat : (7939950223 : ℕ)^35*100000000000000^27 ≤ 74153927660551^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7939950223 10000000000 74153927660551 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400173129/10000000000 : ℝ)^35 ≤ (1542052499287/100000000000000 : ℝ)^27 := by
    have hnat : (400173129 : ℕ)^35*100000000000000^27 ≤ 1542052499287^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400173129 10000000000 1542052499287 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3358107097/10000000000 : ℝ), (7939950223/10000000000 : ℝ), (400173129/10000000000 : ℝ)] ![(972160792929/4000000000000 : ℝ), (74153927660551/100000000000000 : ℝ), (1542052499287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3358107097/10000000000 : ℝ)|^35 ≤ (972160792929/4000000000000 : ℝ)^27
        have hw : |(3358107097/10000000000 : ℝ)|=(3358107097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7939950223/10000000000 : ℝ)|^35 ≤ (74153927660551/100000000000000 : ℝ)^27
        have hw : |(7939950223/10000000000 : ℝ)|=(7939950223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(400173129/10000000000 : ℝ)|^35 ≤ (1542052499287/100000000000000 : ℝ)^27
        have hw : |(400173129/10000000000 : ℝ)|=(400173129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (921863177/2500000000 : ℝ)*x 0 + (1523712547/2000000000 : ℝ)*x 1 + (-540281411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (921863177/2500000000 : ℝ)^35 ≤ (13718894553981/50000000000000 : ℝ)^27 := by
    have hnat : (921863177 : ℕ)^35*50000000000000^27 ≤ 13718894553981^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921863177 2500000000 13718894553981 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1523712547/2000000000 : ℝ)^35 ≤ (17571647338363/25000000000000 : ℝ)^27 := by
    have hnat : (1523712547 : ℕ)^35*25000000000000^27 ≤ 17571647338363^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523712547 2000000000 17571647338363 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540281411/10000000000 : ℝ)^35 ≤ (1137810762071/50000000000000 : ℝ)^27 := by
    have hnat : (540281411 : ℕ)^35*50000000000000^27 ≤ 1137810762071^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540281411 10000000000 1137810762071 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(921863177/2500000000 : ℝ), (1523712547/2000000000 : ℝ), (-540281411/10000000000 : ℝ)] ![(13718894553981/50000000000000 : ℝ), (17571647338363/25000000000000 : ℝ), (1137810762071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(921863177/2500000000 : ℝ)|^35 ≤ (13718894553981/50000000000000 : ℝ)^27
        have hw : |(921863177/2500000000 : ℝ)|=(921863177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1523712547/2000000000 : ℝ)|^35 ≤ (17571647338363/25000000000000 : ℝ)^27
        have hw : |(1523712547/2000000000 : ℝ)|=(1523712547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-540281411/10000000000 : ℝ)|^35 ≤ (1137810762071/50000000000000 : ℝ)^27
        have hw : |(-540281411/10000000000 : ℝ)|=(540281411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (545543/2000000000 : ℝ)*x 0 + (2270574867/10000000000 : ℝ)*x 1 + (-8850790513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545543/2000000000 : ℝ)^35 ≤ (239739411/10000000000000 : ℝ)^27 := by
    have hnat : (545543 : ℕ)^35*10000000000000^27 ≤ 239739411^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545543 2000000000 239739411 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270574867/10000000000 : ℝ)^35 ≤ (457310610569/3125000000000 : ℝ)^27 := by
    have hnat : (2270574867 : ℕ)^35*3125000000000^27 ≤ 457310610569^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270574867 10000000000 457310610569 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8850790513/10000000000 : ℝ)^35 ≤ (85363663055567/100000000000000 : ℝ)^27 := by
    have hnat : (8850790513 : ℕ)^35*100000000000000^27 ≤ 85363663055567^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8850790513 10000000000 85363663055567 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545543/2000000000 : ℝ), (2270574867/10000000000 : ℝ), (-8850790513/10000000000 : ℝ)] ![(239739411/10000000000000 : ℝ), (457310610569/3125000000000 : ℝ), (85363663055567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545543/2000000000 : ℝ)|^35 ≤ (239739411/10000000000000 : ℝ)^27
        have hw : |(545543/2000000000 : ℝ)|=(545543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2270574867/10000000000 : ℝ)|^35 ≤ (457310610569/3125000000000 : ℝ)^27
        have hw : |(2270574867/10000000000 : ℝ)|=(2270574867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8850790513/10000000000 : ℝ)|^35 ≤ (85363663055567/100000000000000 : ℝ)^27
        have hw : |(-8850790513/10000000000 : ℝ)|=(8850790513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (802816289/2500000000 : ℝ)*x 0 + (-2069814719/10000000000 : ℝ)*x 1 + (-1773654563/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (802816289/2500000000 : ℝ)^35 ≤ (4587078137263/20000000000000 : ℝ)^27 := by
    have hnat : (802816289 : ℕ)^35*20000000000000^27 ≤ 4587078137263^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802816289 2500000000 4587078137263 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069814719/10000000000 : ℝ)^35 ≤ (12979097635999/100000000000000 : ℝ)^27 := by
    have hnat : (2069814719 : ℕ)^35*100000000000000^27 ≤ 12979097635999^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069814719 10000000000 12979097635999 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1773654563/2500000000 : ℝ)^35 ≤ (32042755832153/50000000000000 : ℝ)^27 := by
    have hnat : (1773654563 : ℕ)^35*50000000000000^27 ≤ 32042755832153^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773654563 2500000000 32042755832153 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(802816289/2500000000 : ℝ), (-2069814719/10000000000 : ℝ), (-1773654563/2500000000 : ℝ)] ![(4587078137263/20000000000000 : ℝ), (12979097635999/100000000000000 : ℝ), (32042755832153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(802816289/2500000000 : ℝ)|^35 ≤ (4587078137263/20000000000000 : ℝ)^27
        have hw : |(802816289/2500000000 : ℝ)|=(802816289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069814719/10000000000 : ℝ)|^35 ≤ (12979097635999/100000000000000 : ℝ)^27
        have hw : |(-2069814719/10000000000 : ℝ)|=(2069814719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1773654563/2500000000 : ℝ)|^35 ≤ (32042755832153/50000000000000 : ℝ)^27
        have hw : |(-1773654563/2500000000 : ℝ)|=(1773654563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (788016387/1000000000 : ℝ)*x 0 + (2999443267/10000000000 : ℝ)*x 1 + (539271617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (788016387/1000000000 : ℝ)^35 ≤ (18357732403499/25000000000000 : ℝ)^27 := by
    have hnat : (788016387 : ℕ)^35*25000000000000^27 ≤ 18357732403499^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788016387 1000000000 18357732403499 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2999443267/10000000000 : ℝ)^35 ≤ (839749444551/4000000000000 : ℝ)^27 := by
    have hnat : (2999443267 : ℕ)^35*4000000000000^27 ≤ 839749444551^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999443267 10000000000 839749444551 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539271617/5000000000 : ℝ)^35 ≤ (5575334254107/100000000000000 : ℝ)^27 := by
    have hnat : (539271617 : ℕ)^35*100000000000000^27 ≤ 5575334254107^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539271617 5000000000 5575334254107 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(788016387/1000000000 : ℝ), (2999443267/10000000000 : ℝ), (539271617/5000000000 : ℝ)] ![(18357732403499/25000000000000 : ℝ), (839749444551/4000000000000 : ℝ), (5575334254107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(788016387/1000000000 : ℝ)|^35 ≤ (18357732403499/25000000000000 : ℝ)^27
        have hw : |(788016387/1000000000 : ℝ)|=(788016387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2999443267/10000000000 : ℝ)|^35 ≤ (839749444551/4000000000000 : ℝ)^27
        have hw : |(2999443267/10000000000 : ℝ)|=(2999443267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539271617/5000000000 : ℝ)|^35 ≤ (5575334254107/100000000000000 : ℝ)^27
        have hw : |(539271617/5000000000 : ℝ)|=(539271617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (726114939/1000000000 : ℝ)*x 0 + (186599133/500000000 : ℝ)*x 1 + (-1154521629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (726114939/1000000000 : ℝ)^35 ≤ (33021118735999/50000000000000 : ℝ)^27 := by
    have hnat : (726114939 : ℕ)^35*50000000000000^27 ≤ 33021118735999^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726114939 1000000000 33021118735999 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186599133/500000000 : ℝ)^35 ≤ (222944569473/800000000000 : ℝ)^27 := by
    have hnat : (186599133 : ℕ)^35*800000000000^27 ≤ 222944569473^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186599133 500000000 222944569473 800000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1154521629/10000000000 : ℝ)^35 ≤ (6089691336351/100000000000000 : ℝ)^27 := by
    have hnat : (1154521629 : ℕ)^35*100000000000000^27 ≤ 6089691336351^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154521629 10000000000 6089691336351 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(726114939/1000000000 : ℝ), (186599133/500000000 : ℝ), (-1154521629/10000000000 : ℝ)] ![(33021118735999/50000000000000 : ℝ), (222944569473/800000000000 : ℝ), (6089691336351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(726114939/1000000000 : ℝ)|^35 ≤ (33021118735999/50000000000000 : ℝ)^27
        have hw : |(726114939/1000000000 : ℝ)|=(726114939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186599133/500000000 : ℝ)|^35 ≤ (222944569473/800000000000 : ℝ)^27
        have hw : |(186599133/500000000 : ℝ)|=(186599133/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1154521629/10000000000 : ℝ)|^35 ≤ (6089691336351/100000000000000 : ℝ)^27
        have hw : |(-1154521629/10000000000 : ℝ)|=(1154521629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2464159/1000000000 : ℝ)*x 0 + (6349306423/10000000000 : ℝ)*x 1 + (-5351052467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2464159/1000000000 : ℝ)^35 ≤ (41574767737/100000000000000 : ℝ)^27 := by
    have hnat : (2464159 : ℕ)^35*100000000000000^27 ≤ 41574767737^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2464159 1000000000 41574767737 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6349306423/10000000000 : ℝ)^35 ≤ (13874419617851/25000000000000 : ℝ)^27 := by
    have hnat : (6349306423 : ℕ)^35*25000000000000^27 ≤ 13874419617851^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6349306423 10000000000 13874419617851 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5351052467/10000000000 : ℝ)^35 ≤ (44460746751759/100000000000000 : ℝ)^27 := by
    have hnat : (5351052467 : ℕ)^35*100000000000000^27 ≤ 44460746751759^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351052467 10000000000 44460746751759 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2464159/1000000000 : ℝ), (6349306423/10000000000 : ℝ), (-5351052467/10000000000 : ℝ)] ![(41574767737/100000000000000 : ℝ), (13874419617851/25000000000000 : ℝ), (44460746751759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2464159/1000000000 : ℝ)|^35 ≤ (41574767737/100000000000000 : ℝ)^27
        have hw : |(2464159/1000000000 : ℝ)|=(2464159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6349306423/10000000000 : ℝ)|^35 ≤ (13874419617851/25000000000000 : ℝ)^27
        have hw : |(6349306423/10000000000 : ℝ)|=(6349306423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5351052467/10000000000 : ℝ)|^35 ≤ (44460746751759/100000000000000 : ℝ)^27
        have hw : |(-5351052467/10000000000 : ℝ)|=(5351052467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1588774143/2000000000 : ℝ)*x 0 + (-829367347/5000000000 : ℝ)*x 1 + (-2439165361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1588774143/2000000000 : ℝ)^35 ≤ (74201394792923/100000000000000 : ℝ)^27 := by
    have hnat : (1588774143 : ℕ)^35*100000000000000^27 ≤ 74201394792923^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588774143 2000000000 74201394792923 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (829367347/5000000000 : ℝ)^35 ≤ (1948182858101/20000000000000 : ℝ)^27 := by
    have hnat : (829367347 : ℕ)^35*20000000000000^27 ≤ 1948182858101^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829367347 5000000000 1948182858101 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2439165361/10000000000 : ℝ)^35 ≤ (1605769090677/10000000000000 : ℝ)^27 := by
    have hnat : (2439165361 : ℕ)^35*10000000000000^27 ≤ 1605769090677^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439165361 10000000000 1605769090677 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1588774143/2000000000 : ℝ), (-829367347/5000000000 : ℝ), (-2439165361/10000000000 : ℝ)] ![(74201394792923/100000000000000 : ℝ), (1948182858101/20000000000000 : ℝ), (1605769090677/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1588774143/2000000000 : ℝ)|^35 ≤ (74201394792923/100000000000000 : ℝ)^27
        have hw : |(1588774143/2000000000 : ℝ)|=(1588774143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-829367347/5000000000 : ℝ)|^35 ≤ (1948182858101/20000000000000 : ℝ)^27
        have hw : |(-829367347/5000000000 : ℝ)|=(829367347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2439165361/10000000000 : ℝ)|^35 ≤ (1605769090677/10000000000000 : ℝ)^27
        have hw : |(-2439165361/10000000000 : ℝ)|=(2439165361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3184179553/10000000000 : ℝ)*x 0 + (6779399739/10000000000 : ℝ)*x 1 + (2536827133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3184179553/10000000000 : ℝ)^35 ≤ (22684936285543/100000000000000 : ℝ)^27 := by
    have hnat : (3184179553 : ℕ)^35*100000000000000^27 ≤ 22684936285543^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3184179553 10000000000 22684936285543 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6779399739/10000000000 : ℝ)^35 ≤ (60419041689743/100000000000000 : ℝ)^27 := by
    have hnat : (6779399739 : ℕ)^35*100000000000000^27 ≤ 60419041689743^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6779399739 10000000000 60419041689743 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2536827133/10000000000 : ℝ)^35 ≤ (844801100173/5000000000000 : ℝ)^27 := by
    have hnat : (2536827133 : ℕ)^35*5000000000000^27 ≤ 844801100173^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536827133 10000000000 844801100173 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3184179553/10000000000 : ℝ), (6779399739/10000000000 : ℝ), (2536827133/10000000000 : ℝ)] ![(22684936285543/100000000000000 : ℝ), (60419041689743/100000000000000 : ℝ), (844801100173/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3184179553/10000000000 : ℝ)|^35 ≤ (22684936285543/100000000000000 : ℝ)^27
        have hw : |(3184179553/10000000000 : ℝ)|=(3184179553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6779399739/10000000000 : ℝ)|^35 ≤ (60419041689743/100000000000000 : ℝ)^27
        have hw : |(6779399739/10000000000 : ℝ)|=(6779399739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2536827133/10000000000 : ℝ)|^35 ≤ (844801100173/5000000000000 : ℝ)^27
        have hw : |(2536827133/10000000000 : ℝ)|=(2536827133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s1_s1_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (904766943/1250000000 : ℝ)*x 0 + (141824757/400000000 : ℝ)*x 1 + (-1445748097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904766943/1250000000 : ℝ)^35 ≤ (13154205485817/20000000000000 : ℝ)^27 := by
    have hnat : (904766943 : ℕ)^35*20000000000000^27 ≤ 13154205485817^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904766943 1250000000 13154205485817 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141824757/400000000 : ℝ)^35 ≤ (1303879584369/5000000000000 : ℝ)^27 := by
    have hnat : (141824757 : ℕ)^35*5000000000000^27 ≤ 1303879584369^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141824757 400000000 1303879584369 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1445748097/10000000000 : ℝ)^35 ≤ (8151380875929/100000000000000 : ℝ)^27 := by
    have hnat : (1445748097 : ℕ)^35*100000000000000^27 ≤ 8151380875929^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445748097 10000000000 8151380875929 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(904766943/1250000000 : ℝ), (141824757/400000000 : ℝ), (-1445748097/10000000000 : ℝ)] ![(13154205485817/20000000000000 : ℝ), (1303879584369/5000000000000 : ℝ), (8151380875929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(904766943/1250000000 : ℝ)|^35 ≤ (13154205485817/20000000000000 : ℝ)^27
        have hw : |(904766943/1250000000 : ℝ)|=(904766943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141824757/400000000 : ℝ)|^35 ≤ (1303879584369/5000000000000 : ℝ)^27
        have hw : |(141824757/400000000 : ℝ)|=(141824757/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1445748097/10000000000 : ℝ)|^35 ≤ (8151380875929/100000000000000 : ℝ)^27
        have hw : |(-1445748097/10000000000 : ℝ)|=(1445748097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309054_s1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((87879/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(87879/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22599/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22599/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-80289/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-80289/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18249/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18249/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(77471/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(77471/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64251/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64251/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  have s1_pow0 : (87879/100000 : ℝ) ^ (69/16 : ℝ) ≤ (3580012461279851801/6250000000000000000 : ℝ) := by
    have hpowers : (87879/100000 : ℝ)^69 ≤ (3580012461279851801/6250000000000000000 : ℝ)^16 := by
      have hnat : (87879 : ℕ)^69*6250000000000000000^16 ≤ 3580012461279851801^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87879 100000 3580012461279851801 6250000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (87879/100000 : ℝ)) (X := (3580012461279851801/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (9830012461279851801/6250000000000000000 : ℝ) ≤ (1110722519320529/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (9830012461279851801/6250000000000000000 : ℝ)^16 ≤ (1110722519320529/1000000000000000 : ℝ)^69 := by
      have hnat : (9830012461279851801 : ℕ)^16*1000000000000000^69 ≤ 1110722519320529^69*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9830012461279851801 6250000000000000000 1110722519320529 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1110722519320529/1000000000000000 : ℝ)) (X := (9830012461279851801/6250000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (6705012461279851801/3125000000000000000 : ℝ) ≤ (11936611500496343/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (6705012461279851801/3125000000000000000 : ℝ)^16 ≤ (11936611500496343/10000000000000000 : ℝ)^69 := by
      have hnat : (6705012461279851801 : ℕ)^16*10000000000000000^69 ≤ 11936611500496343^69*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6705012461279851801 3125000000000000000 11936611500496343 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11936611500496343/10000000000000000 : ℝ)) (X := (6705012461279851801/3125000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(110722519320529/878790000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(276462102430351/2929300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (87879/100000 : ℝ)) (alpha := (110722519320529/878790000000000 : ℝ)) (beta := (276462102430351/2929300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (87879/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(110722519320529/878790000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(276462102430351/2929300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (22599/25000 : ℝ) ^ (69/16 : ℝ) ≤ (32349195716410811371/50000000000000000000 : ℝ) := by
    have hpowers : (22599/25000 : ℝ)^69 ≤ (32349195716410811371/50000000000000000000 : ℝ)^16 := by
      have hnat : (22599 : ℕ)^69*50000000000000000000^16 ≤ 32349195716410811371^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22599 25000 32349195716410811371 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22599/25000 : ℝ)) (X := (32349195716410811371/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (82349195716410811371/50000000000000000000 : ℝ) ≤ (11226562734222283/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (82349195716410811371/50000000000000000000 : ℝ)^16 ≤ (11226562734222283/10000000000000000 : ℝ)^69 := by
      have hnat : (82349195716410811371 : ℕ)^16*10000000000000000^69 ≤ 11226562734222283^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82349195716410811371 50000000000000000000 11226562734222283 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11226562734222283/10000000000000000 : ℝ)) (X := (82349195716410811371/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (57349195716410811371/25000000000000000000 : ℝ) ≤ (3030780332669887/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (57349195716410811371/25000000000000000000 : ℝ)^16 ≤ (3030780332669887/2500000000000000 : ℝ)^69 := by
      have hnat : (57349195716410811371 : ℕ)^16*2500000000000000^69 ≤ 3030780332669887^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57349195716410811371 25000000000000000000 3030780332669887 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3030780332669887/2500000000000000 : ℝ)) (X := (57349195716410811371/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(408854244740761/3013200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(19923524365717/200880000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (22599/25000 : ℝ)) (alpha := (408854244740761/3013200000000000 : ℝ)) (beta := (19923524365717/200880000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (22599/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(408854244740761/3013200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(19923524365717/200880000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (80289/100000 : ℝ) ^ (69/16 : ℝ) ≤ (155199101201051243/400000000000000000 : ℝ) := by
    have hpowers : (80289/100000 : ℝ)^69 ≤ (155199101201051243/400000000000000000 : ℝ)^16 := by
      have hnat : (80289 : ℕ)^69*400000000000000000^16 ≤ 155199101201051243^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80289 100000 155199101201051243 400000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (80289/100000 : ℝ)) (X := (155199101201051243/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (555199101201051243/400000000000000000 : ℝ) ≤ (10789906571249113/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (555199101201051243/400000000000000000 : ℝ)^16 ≤ (10789906571249113/10000000000000000 : ℝ)^69 := by
      have hnat : (555199101201051243 : ℕ)^16*10000000000000000^69 ≤ 10789906571249113^69*400000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        555199101201051243 400000000000000000 10789906571249113 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10789906571249113/10000000000000000 : ℝ)) (X := (555199101201051243/400000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (355199101201051243/200000000000000000 : ℝ) ≤ (5712307732521661/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (355199101201051243/200000000000000000 : ℝ)^16 ≤ (5712307732521661/5000000000000000 : ℝ)^69 := by
      have hnat : (355199101201051243 : ℕ)^16*5000000000000000^69 ≤ 5712307732521661^69*200000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        355199101201051243 200000000000000000 5712307732521661 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5712307732521661/5000000000000000 : ℝ)) (X := (355199101201051243/200000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(87767396805457/892100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(634708893794209/8028900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (80289/100000 : ℝ)) (alpha := (87767396805457/892100000000000 : ℝ)) (beta := (634708893794209/8028900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (80289/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(87767396805457/892100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(634708893794209/8028900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-167202343/10000000000 : ℝ)*X 0 0+(2288188103/5000000000 : ℝ)*X 0 1+(-7018880941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((92059857/156250000 : ℝ)*X 1 0+(-387652637/2500000000 : ℝ)*X 1 1+(-624841203/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1388804009/2500000000 : ℝ)*X 2 0+(34397347/62500000 : ℝ)*X 2 1+(1316222293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((218642389/400000000 : ℝ)*X 0 0+(2714502433/5000000000 : ℝ)*X 0 1+(-194974179/1250000000 : ℝ)*X 0 2+(218642389/400000000 : ℝ)*X 1 0+(2714502433/5000000000 : ℝ)*X 1 1+(-194974179/1250000000 : ℝ)*X 1 2+(218642389/400000000 : ℝ)*X 2 0+(2714502433/5000000000 : ℝ)*X 2 1+(-194974179/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-24544811/2000000000 : ℝ)*X 0 0+(2096799127/10000000000 : ℝ)*X 0 1+(-8938986059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((982619943/2500000000 : ℝ)*X 1 0+(-3163721/39062500 : ℝ)*X 1 1+(-7287197291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3358107097/10000000000 : ℝ)*X 2 0+(7939950223/10000000000 : ℝ)*X 2 1+(400173129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((921863177/2500000000 : ℝ)*X 0 0+(1523712547/2000000000 : ℝ)*X 0 1+(-540281411/10000000000 : ℝ)*X 0 2+(921863177/2500000000 : ℝ)*X 1 0+(1523712547/2000000000 : ℝ)*X 1 1+(-540281411/10000000000 : ℝ)*X 1 2+(921863177/2500000000 : ℝ)*X 2 0+(1523712547/2000000000 : ℝ)*X 2 1+(-540281411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((545543/2000000000 : ℝ)*X 0 0+(2270574867/10000000000 : ℝ)*X 0 1+(-8850790513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((802816289/2500000000 : ℝ)*X 1 0+(-2069814719/10000000000 : ℝ)*X 1 1+(-1773654563/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((788016387/1000000000 : ℝ)*X 2 0+(2999443267/10000000000 : ℝ)*X 2 1+(539271617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((726114939/1000000000 : ℝ)*X 0 0+(186599133/500000000 : ℝ)*X 0 1+(-1154521629/10000000000 : ℝ)*X 0 2+(726114939/1000000000 : ℝ)*X 1 0+(186599133/500000000 : ℝ)*X 1 1+(-1154521629/10000000000 : ℝ)*X 1 2+(726114939/1000000000 : ℝ)*X 2 0+(186599133/500000000 : ℝ)*X 2 1+(-1154521629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((2464159/1000000000 : ℝ)*X 0 0+(6349306423/10000000000 : ℝ)*X 0 1+(-5351052467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1588774143/2000000000 : ℝ)*X 1 0+(-829367347/5000000000 : ℝ)*X 1 1+(-2439165361/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3184179553/10000000000 : ℝ)*X 2 0+(6779399739/10000000000 : ℝ)*X 2 1+(2536827133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((904766943/1250000000 : ℝ)*X 0 0+(141824757/400000000 : ℝ)*X 0 1+(-1445748097/10000000000 : ℝ)*X 0 2+(904766943/1250000000 : ℝ)*X 1 0+(141824757/400000000 : ℝ)*X 1 1+(-1445748097/10000000000 : ℝ)*X 1 2+(904766943/1250000000 : ℝ)*X 2 0+(141824757/400000000 : ℝ)*X 2 1+(-1445748097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((18249/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18249/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8394754643732177271402613241/795371738040000000000000000000000 : ℝ) := by norm_num
    linear_combination (986519023/1600000000 : ℝ)*(base7) + (74093/125000000000 : ℝ)*(base39) + (48922387811/250000000000 : ℝ)*(base60) + (1874810135823/1000000000000 : ℝ)*(major_s1_0) + (1874810135823/1000000000000 : ℝ)*(major_s1_1) + (1874810135823/1000000000000 : ℝ)*(major_s1_2) + (17060909/1000000000000 : ℝ)*(sp_s1_1) + (13573479/1000000000000 : ℝ)*(sp_s1_6) + (1098259200453/500000000000 : ℝ)*(sp_s1_7) + (137307492749/62500000000 : ℝ)*(sp_s1_8) + (219693101593/100000000000 : ℝ)*(sp_s1_9) + (1793857804739/1000000000000 : ℝ)*(sp_s1_13) + (418543987/1000000000000 : ℝ)*(sp_s1_14) + (5928963/1000000000000 : ℝ)*(sp_s1_23) + (1177296988843/1000000000000 : ℝ)*(f.failure) + (2196936944893/1000000000000 : ℝ)*(f.sum) + (157916899027134001/358410096000000000000000000000 : ℝ)*base63 + (368143679915431/2676300000000000000000000000 : ℝ)*base64 + (2951177137787/13392000000000000000000000 : ℝ)*base67 + (248420330640041/892100000000000000000000000 : ℝ)*base69 + (569405516230717447/7126986900000000000000000000000 : ℝ)*base71 + (97410214489683/2929300000000000000000000000 : ℝ)*base73 + (3416809823261/1004400000000000000000000000 : ℝ)*base75 + (18716313076171/292930000000000000000000000 : ℝ)*base77 + (3199327309996488181/9807296400000000000000000000000 : ℝ)*base78 + (18779/100000000000000000 : ℝ)*base86 + (18779/100000000000000000 : ℝ)*base88 + (18779/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(77471/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(77471/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (539231012148682915060227133/34987026600000000000000000000000 : ℝ) := by norm_num
    linear_combination (217004471517/250000000000 : ℝ)*(base7) + (450321/1000000000000 : ℝ)*(base39) + (65387033343/1000000000000 : ℝ)*(base60) + (1958194867439/1000000000000 : ℝ)*(major_s1_0) + (1958194867439/1000000000000 : ℝ)*(major_s1_1) + (1958194867439/1000000000000 : ℝ)*(major_s1_2) + (1656079/250000000000 : ℝ)*(sp_s1_0) + (1053559/100000000000 : ℝ)*(sp_s1_1) + (47619259/1000000000000 : ℝ)*(sp_s1_8) + (431650489899/200000000000 : ℝ)*(sp_s1_14) + (2158200918961/1000000000000 : ℝ)*(sp_s1_15) + (2158259073811/1000000000000 : ℝ)*(sp_s1_16) + (1048820643913/500000000000 : ℝ)*(sp_s1_20) + (8868117/250000000000 : ℝ)*(sp_s1_27) + (614829437113/500000000000 : ℝ)*(f.failure) + (2158259073811/1000000000000 : ℝ)*(f.sum) + (93259632417426727/173424240000000000000000000000 : ℝ)*base62 + (372127701556939/8028900000000000000000000000 : ℝ)*base64 + (1118310169319/1296000000000000000000000 : ℝ)*base67 + (582440432501737/892100000000000000000000000 : ℝ)*base68 + (7688003975725256353/21380960700000000000000000000000 : ℝ)*base71 + (1251568026271481/2929300000000000000000000000 : ℝ)*base72 + (77121995898631/97200000000000000000000000 : ℝ)*base74 + (125835779923633/219697500000000000000000000 : ℝ)*base76 + (458108135678496289/949093200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (16089/50000000000000000 : ℝ)*base86 + (16089/50000000000000000 : ℝ)*base88 + (16089/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64251/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64251/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8568407580000105489519739907/745661004412500000000000000000000 : ℝ) := by norm_num
    linear_combination (103484494747/125000000000 : ℝ)*(base7) + (1364359/500000000000 : ℝ)*(base27) + (55787897091/250000000000 : ℝ)*(base39) + (898020748841/500000000000 : ℝ)*(major_s1_0) + (898020748841/500000000000 : ℝ)*(major_s1_1) + (898020748841/500000000000 : ℝ)*(major_s1_2) + (3737213/1000000000000 : ℝ)*(sp_s1_1) + (3212937/250000000000 : ℝ)*(sp_s1_2) + (20831291/1000000000000 : ℝ)*(sp_s1_9) + (129571153/1000000000000 : ℝ)*(sp_s1_20) + (245027240049/125000000000 : ℝ)*(sp_s1_21) + (1960214183179/1000000000000 : ℝ)*(sp_s1_22) + (980092118677/500000000000 : ℝ)*(sp_s1_23) + (391115492399/200000000000 : ℝ)*(sp_s1_27) + (1127833803891/1000000000000 : ℝ)*(f.failure) + (245027240049/125000000000 : ℝ)*(f.sum) + (530447866476544721/2688075720000000000000000000000 : ℝ)*base63 + (1173632895657337/2007225000000000000000000000 : ℝ)*base65 + (50867928776093/100440000000000000000000000 : ℝ)*base66 + (159999817230571/223025000000000000000000000 : ℝ)*base69 + (94206544736400521/5345240175000000000000000000000 : ℝ)*base71 + (328761744573607/732325000000000000000000000 : ℝ)*base72 + (224497283065781/1506600000000000000000000000 : ℝ)*base75 + (1894460523841/109848750000000000000000000 : ℝ)*base76 + (2781147678168727381/14710944600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (30077/100000000000000000 : ℝ)*base87 + (30077/100000000000000000 : ℝ)*base89 + (30077/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((87879/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(87879/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22599/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22599/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-80289/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-80289/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18249/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18249/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(77471/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(77471/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64251/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64251/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309054_s1 p hpa hpb X hX hprev0

#print axioms solution
