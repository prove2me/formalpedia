-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:27:04.583397+00:00
-- url     : https://prove2.me/submissions/71777747-2301-42eb-9a64-e540e1edfaf5

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
theorem collision_support_c310055_s2_s2_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1651272899/10000000000 : ℝ)*x 0 + (5845231607/10000000000 : ℝ)*x 1 + (987714317/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1651272899/10000000000 : ℝ)^71 ≤ (391142708041/4000000000000 : ℝ)^55 := by
    have hnat : (1651272899 : ℕ)^71*4000000000000^55 ≤ 391142708041^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1651272899 10000000000 391142708041 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5845231607/10000000000 : ℝ)^71 ≤ (9999820887681/20000000000000 : ℝ)^55 := by
    have hnat : (5845231607 : ℕ)^71*20000000000000^55 ≤ 9999820887681^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5845231607 10000000000 9999820887681 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987714317/2000000000 : ℝ)^71 ≤ (20111163921171/50000000000000 : ℝ)^55 := by
    have hnat : (987714317 : ℕ)^71*50000000000000^55 ≤ 20111163921171^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987714317 2000000000 20111163921171 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1651272899/10000000000 : ℝ), (5845231607/10000000000 : ℝ), (987714317/2000000000 : ℝ)] ![(391142708041/4000000000000 : ℝ), (9999820887681/20000000000000 : ℝ), (20111163921171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1651272899/10000000000 : ℝ)|^71 ≤ (391142708041/4000000000000 : ℝ)^55
        have hw : |(-1651272899/10000000000 : ℝ)|=(1651272899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5845231607/10000000000 : ℝ)|^71 ≤ (9999820887681/20000000000000 : ℝ)^55
        have hw : |(5845231607/10000000000 : ℝ)|=(5845231607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(987714317/2000000000 : ℝ)|^71 ≤ (20111163921171/50000000000000 : ℝ)^55
        have hw : |(987714317/2000000000 : ℝ)|=(987714317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2427986753/5000000000 : ℝ)*x 0 + (-120850261/2000000000 : ℝ)*x 1 + (6555164531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2427986753/5000000000 : ℝ)^71 ≤ (39356025628773/100000000000000 : ℝ)^55 := by
    have hnat : (2427986753 : ℕ)^71*100000000000000^55 ≤ 39356025628773^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2427986753 5000000000 39356025628773 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120850261/2000000000 : ℝ)^71 ≤ (2670931291649/100000000000000 : ℝ)^55 := by
    have hnat : (120850261 : ℕ)^71*100000000000000^55 ≤ 2670931291649^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120850261 2000000000 2670931291649 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6555164531/10000000000 : ℝ)^71 ≤ (36233151919/62500000000 : ℝ)^55 := by
    have hnat : (6555164531 : ℕ)^71*62500000000^55 ≤ 36233151919^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6555164531 10000000000 36233151919 62500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2427986753/5000000000 : ℝ), (-120850261/2000000000 : ℝ), (6555164531/10000000000 : ℝ)] ![(39356025628773/100000000000000 : ℝ), (2670931291649/100000000000000 : ℝ), (36233151919/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2427986753/5000000000 : ℝ)|^71 ≤ (39356025628773/100000000000000 : ℝ)^55
        have hw : |(2427986753/5000000000 : ℝ)|=(2427986753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120850261/2000000000 : ℝ)|^71 ≤ (2670931291649/100000000000000 : ℝ)^55
        have hw : |(-120850261/2000000000 : ℝ)|=(120850261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6555164531/10000000000 : ℝ)|^71 ≤ (36233151919/62500000000 : ℝ)^55
        have hw : |(6555164531/10000000000 : ℝ)|=(6555164531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (483034217/1000000000 : ℝ)*x 0 + (5971637093/10000000000 : ℝ)*x 1 + (-202047711/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (483034217/1000000000 : ℝ)^71 ≤ (39088066934777/100000000000000 : ℝ)^55 := by
    have hnat : (483034217 : ℕ)^71*100000000000000^55 ≤ 39088066934777^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483034217 1000000000 39088066934777 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5971637093/10000000000 : ℝ)^71 ≤ (51399269128391/100000000000000 : ℝ)^55 := by
    have hnat : (5971637093 : ℕ)^71*100000000000000^55 ≤ 51399269128391^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5971637093 10000000000 51399269128391 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202047711/1250000000 : ℝ)^71 ≤ (4756331959217/50000000000000 : ℝ)^55 := by
    have hnat : (202047711 : ℕ)^71*50000000000000^55 ≤ 4756331959217^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202047711 1250000000 4756331959217 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(483034217/1000000000 : ℝ), (5971637093/10000000000 : ℝ), (-202047711/1250000000 : ℝ)] ![(39088066934777/100000000000000 : ℝ), (51399269128391/100000000000000 : ℝ), (4756331959217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(483034217/1000000000 : ℝ)|^71 ≤ (39088066934777/100000000000000 : ℝ)^55
        have hw : |(483034217/1000000000 : ℝ)|=(483034217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5971637093/10000000000 : ℝ)|^71 ≤ (51399269128391/100000000000000 : ℝ)^55
        have hw : |(5971637093/10000000000 : ℝ)|=(5971637093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-202047711/1250000000 : ℝ)|^71 ≤ (4756331959217/50000000000000 : ℝ)^55
        have hw : |(-202047711/1250000000 : ℝ)|=(202047711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6355993913/10000000000 : ℝ)*x 0 + (967732521/2500000000 : ℝ)*x 1 + (572680841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6355993913/10000000000 : ℝ)^71 ≤ (55709306937169/100000000000000 : ℝ)^55 := by
    have hnat : (6355993913 : ℕ)^71*100000000000000^55 ≤ 55709306937169^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6355993913 10000000000 55709306937169 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (967732521/2500000000 : ℝ)^71 ≤ (7342552618761/25000000000000 : ℝ)^55 := by
    have hnat : (967732521 : ℕ)^71*25000000000000^55 ≤ 7342552618761^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967732521 2500000000 7342552618761 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572680841/2500000000 : ℝ)^71 ≤ (1492048256473/10000000000000 : ℝ)^55 := by
    have hnat : (572680841 : ℕ)^71*10000000000000^55 ≤ 1492048256473^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572680841 2500000000 1492048256473 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6355993913/10000000000 : ℝ), (967732521/2500000000 : ℝ), (572680841/2500000000 : ℝ)] ![(55709306937169/100000000000000 : ℝ), (7342552618761/25000000000000 : ℝ), (1492048256473/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6355993913/10000000000 : ℝ)|^71 ≤ (55709306937169/100000000000000 : ℝ)^55
        have hw : |(6355993913/10000000000 : ℝ)|=(6355993913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(967732521/2500000000 : ℝ)|^71 ≤ (7342552618761/25000000000000 : ℝ)^55
        have hw : |(967732521/2500000000 : ℝ)|=(967732521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(572680841/2500000000 : ℝ)|^71 ≤ (1492048256473/10000000000000 : ℝ)^55
        have hw : |(572680841/2500000000 : ℝ)|=(572680841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-77891159/500000000 : ℝ)*x 0 + (4216053331/10000000000 : ℝ)*x 1 + (6569463849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77891159/500000000 : ℝ)^71 ≤ (9070147595459/100000000000000 : ℝ)^55 := by
    have hnat : (77891159 : ℕ)^71*100000000000000^55 ≤ 9070147595459^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77891159 500000000 9070147595459 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4216053331/10000000000 : ℝ)^71 ≤ (512398553669/1562500000000 : ℝ)^55 := by
    have hnat : (4216053331 : ℕ)^71*1562500000000^55 ≤ 512398553669^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216053331 10000000000 512398553669 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6569463849/10000000000 : ℝ)^71 ≤ (58136344952401/100000000000000 : ℝ)^55 := by
    have hnat : (6569463849 : ℕ)^71*100000000000000^55 ≤ 58136344952401^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6569463849 10000000000 58136344952401 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77891159/500000000 : ℝ), (4216053331/10000000000 : ℝ), (6569463849/10000000000 : ℝ)] ![(9070147595459/100000000000000 : ℝ), (512398553669/1562500000000 : ℝ), (58136344952401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77891159/500000000 : ℝ)|^71 ≤ (9070147595459/100000000000000 : ℝ)^55
        have hw : |(-77891159/500000000 : ℝ)|=(77891159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4216053331/10000000000 : ℝ)|^71 ≤ (512398553669/1562500000000 : ℝ)^55
        have hw : |(4216053331/10000000000 : ℝ)|=(4216053331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6569463849/10000000000 : ℝ)|^71 ≤ (58136344952401/100000000000000 : ℝ)^55
        have hw : |(6569463849/10000000000 : ℝ)|=(6569463849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (772577131/2000000000 : ℝ)*x 0 + (-68299/10000000000 : ℝ)*x 1 + (3822642543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (772577131/2000000000 : ℝ)^71 ≤ (7322860553783/25000000000000 : ℝ)^55 := by
    have hnat : (772577131 : ℕ)^71*25000000000000^55 ≤ 7322860553783^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772577131 2000000000 7322860553783 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68299/10000000000 : ℝ)^71 ≤ (107317/500000000000 : ℝ)^55 := by
    have hnat : (68299 : ℕ)^71*500000000000^55 ≤ 107317^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68299 10000000000 107317 500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3822642543/5000000000 : ℝ)^71 ≤ (70708536306903/100000000000000 : ℝ)^55 := by
    have hnat : (3822642543 : ℕ)^71*100000000000000^55 ≤ 70708536306903^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3822642543 5000000000 70708536306903 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(772577131/2000000000 : ℝ), (-68299/10000000000 : ℝ), (3822642543/5000000000 : ℝ)] ![(7322860553783/25000000000000 : ℝ), (107317/500000000000 : ℝ), (70708536306903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(772577131/2000000000 : ℝ)|^71 ≤ (7322860553783/25000000000000 : ℝ)^55
        have hw : |(772577131/2000000000 : ℝ)|=(772577131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-68299/10000000000 : ℝ)|^71 ≤ (107317/500000000000 : ℝ)^55
        have hw : |(-68299/10000000000 : ℝ)|=(68299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3822642543/5000000000 : ℝ)|^71 ≤ (70708536306903/100000000000000 : ℝ)^55
        have hw : |(3822642543/5000000000 : ℝ)|=(3822642543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3834190551/10000000000 : ℝ)*x 0 + (7361847089/10000000000 : ℝ)*x 1 + (-384506187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3834190551/10000000000 : ℝ)^71 ≤ (1450542938923/5000000000000 : ℝ)^55 := by
    have hnat : (3834190551 : ℕ)^71*5000000000000^55 ≤ 1450542938923^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3834190551 10000000000 1450542938923 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7361847089/10000000000 : ℝ)^71 ≤ (3367146758257/5000000000000 : ℝ)^55 := by
    have hnat : (7361847089 : ℕ)^71*5000000000000^55 ≤ 3367146758257^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7361847089 10000000000 3367146758257 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (384506187/5000000000 : ℝ)^71 ≤ (1823103016119/50000000000000 : ℝ)^55 := by
    have hnat : (384506187 : ℕ)^71*50000000000000^55 ≤ 1823103016119^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384506187 5000000000 1823103016119 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3834190551/10000000000 : ℝ), (7361847089/10000000000 : ℝ), (-384506187/5000000000 : ℝ)] ![(1450542938923/5000000000000 : ℝ), (3367146758257/5000000000000 : ℝ), (1823103016119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3834190551/10000000000 : ℝ)|^71 ≤ (1450542938923/5000000000000 : ℝ)^55
        have hw : |(3834190551/10000000000 : ℝ)|=(3834190551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7361847089/10000000000 : ℝ)|^71 ≤ (3367146758257/5000000000000 : ℝ)^55
        have hw : |(7361847089/10000000000 : ℝ)|=(7361847089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-384506187/5000000000 : ℝ)|^71 ≤ (1823103016119/50000000000000 : ℝ)^55
        have hw : |(-384506187/5000000000 : ℝ)|=(384506187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1099135073/2500000000 : ℝ)*x 0 + (659445331/1000000000 : ℝ)*x 1 + (1269057709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099135073/2500000000 : ℝ)^71 ≤ (34616951515921/100000000000000 : ℝ)^55 := by
    have hnat : (1099135073 : ℕ)^71*100000000000000^55 ≤ 34616951515921^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099135073 2500000000 34616951515921 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659445331/1000000000 : ℝ)^71 ≤ (29210989625137/50000000000000 : ℝ)^55 := by
    have hnat : (659445331 : ℕ)^71*50000000000000^55 ≤ 29210989625137^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659445331 1000000000 29210989625137 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269057709/10000000000 : ℝ)^71 ≤ (6961069221367/100000000000000 : ℝ)^55 := by
    have hnat : (1269057709 : ℕ)^71*100000000000000^55 ≤ 6961069221367^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269057709 10000000000 6961069221367 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099135073/2500000000 : ℝ), (659445331/1000000000 : ℝ), (1269057709/10000000000 : ℝ)] ![(34616951515921/100000000000000 : ℝ), (29210989625137/50000000000000 : ℝ), (6961069221367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099135073/2500000000 : ℝ)|^71 ≤ (34616951515921/100000000000000 : ℝ)^55
        have hw : |(1099135073/2500000000 : ℝ)|=(1099135073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659445331/1000000000 : ℝ)|^71 ≤ (29210989625137/50000000000000 : ℝ)^55
        have hw : |(659445331/1000000000 : ℝ)|=(659445331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269057709/10000000000 : ℝ)|^71 ≤ (6961069221367/100000000000000 : ℝ)^55
        have hw : |(1269057709/10000000000 : ℝ)|=(1269057709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-493917077/10000000000 : ℝ)*x 0 + (929561947/2000000000 : ℝ)*x 1 + (424815791/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (493917077/10000000000 : ℝ)^71 ≤ (1029428366391/50000000000000 : ℝ)^55 := by
    have hnat : (493917077 : ℕ)^71*50000000000000^55 ≤ 1029428366391^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493917077 10000000000 1029428366391 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (929561947/2000000000 : ℝ)^71 ≤ (7438371320613/20000000000000 : ℝ)^55 := by
    have hnat : (929561947 : ℕ)^71*20000000000000^55 ≤ 7438371320613^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929561947 2000000000 7438371320613 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424815791/625000000 : ℝ)^71 ≤ (3796830415259/6250000000000 : ℝ)^55 := by
    have hnat : (424815791 : ℕ)^71*6250000000000^55 ≤ 3796830415259^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424815791 625000000 3796830415259 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-493917077/10000000000 : ℝ), (929561947/2000000000 : ℝ), (424815791/625000000 : ℝ)] ![(1029428366391/50000000000000 : ℝ), (7438371320613/20000000000000 : ℝ), (3796830415259/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-493917077/10000000000 : ℝ)|^71 ≤ (1029428366391/50000000000000 : ℝ)^55
        have hw : |(-493917077/10000000000 : ℝ)|=(493917077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(929561947/2000000000 : ℝ)|^71 ≤ (7438371320613/20000000000000 : ℝ)^55
        have hw : |(929561947/2000000000 : ℝ)|=(929561947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424815791/625000000 : ℝ)|^71 ≤ (3796830415259/6250000000000 : ℝ)^55
        have hw : |(424815791/625000000 : ℝ)|=(424815791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3396646707/10000000000 : ℝ)*x 0 + (-57792413/1250000000 : ℝ)*x 1 + (3930701887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3396646707/10000000000 : ℝ)^71 ≤ (24810108801663/100000000000000 : ℝ)^55 := by
    have hnat : (3396646707 : ℕ)^71*100000000000000^55 ≤ 24810108801663^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3396646707 10000000000 24810108801663 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57792413/1250000000 : ℝ)^71 ≤ (1890539602241/100000000000000 : ℝ)^55 := by
    have hnat : (57792413 : ℕ)^71*100000000000000^55 ≤ 1890539602241^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57792413 1250000000 1890539602241 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3930701887/5000000000 : ℝ)^71 ≤ (1465987031663/2000000000000 : ℝ)^55 := by
    have hnat : (3930701887 : ℕ)^71*2000000000000^55 ≤ 1465987031663^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3930701887 5000000000 1465987031663 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3396646707/10000000000 : ℝ), (-57792413/1250000000 : ℝ), (3930701887/5000000000 : ℝ)] ![(24810108801663/100000000000000 : ℝ), (1890539602241/100000000000000 : ℝ), (1465987031663/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3396646707/10000000000 : ℝ)|^71 ≤ (24810108801663/100000000000000 : ℝ)^55
        have hw : |(3396646707/10000000000 : ℝ)|=(3396646707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-57792413/1250000000 : ℝ)|^71 ≤ (1890539602241/100000000000000 : ℝ)^55
        have hw : |(-57792413/1250000000 : ℝ)|=(57792413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3930701887/5000000000 : ℝ)|^71 ≤ (1465987031663/2000000000000 : ℝ)^55
        have hw : |(3930701887/5000000000 : ℝ)|=(3930701887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (417818117/625000000 : ℝ)*x 0 + (4787815773/10000000000 : ℝ)*x 1 + (-18527333/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417818117/625000000 : ℝ)^71 ≤ (7432576232871/12500000000000 : ℝ)^55 := by
    have hnat : (417818117 : ℕ)^71*12500000000000^55 ≤ 7432576232871^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417818117 625000000 7432576232871 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4787815773/10000000000 : ℝ)^71 ≤ (7728878812459/20000000000000 : ℝ)^55 := by
    have hnat : (4787815773 : ℕ)^71*20000000000000^55 ≤ 7728878812459^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787815773 10000000000 7728878812459 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18527333/400000000 : ℝ)^71 ≤ (189499605319/10000000000000 : ℝ)^55 := by
    have hnat : (18527333 : ℕ)^71*10000000000000^55 ≤ 189499605319^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18527333 400000000 189499605319 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417818117/625000000 : ℝ), (4787815773/10000000000 : ℝ), (-18527333/400000000 : ℝ)] ![(7432576232871/12500000000000 : ℝ), (7728878812459/20000000000000 : ℝ), (189499605319/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417818117/625000000 : ℝ)|^71 ≤ (7432576232871/12500000000000 : ℝ)^55
        have hw : |(417818117/625000000 : ℝ)|=(417818117/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4787815773/10000000000 : ℝ)|^71 ≤ (7728878812459/20000000000000 : ℝ)^55
        have hw : |(4787815773/10000000000 : ℝ)|=(4787815773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18527333/400000000 : ℝ)|^71 ≤ (189499605319/10000000000000 : ℝ)^55
        have hw : |(-18527333/400000000 : ℝ)|=(18527333/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2053181947/2500000000 : ℝ)*x 0 + (1351468003/5000000000 : ℝ)*x 1 + (164318153/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2053181947/2500000000 : ℝ)^71 ≤ (77555221729409/100000000000000 : ℝ)^55 := by
    have hnat : (2053181947 : ℕ)^71*100000000000000^55 ≤ 77555221729409^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053181947 2500000000 77555221729409 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351468003/5000000000 : ℝ)^71 ≤ (9236801834537/50000000000000 : ℝ)^55 := by
    have hnat : (1351468003 : ℕ)^71*50000000000000^55 ≤ 9236801834537^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351468003 5000000000 9236801834537 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164318153/2000000000 : ℝ)^71 ≤ (1985587297109/50000000000000 : ℝ)^55 := by
    have hnat : (164318153 : ℕ)^71*50000000000000^55 ≤ 1985587297109^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164318153 2000000000 1985587297109 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2053181947/2500000000 : ℝ), (1351468003/5000000000 : ℝ), (164318153/2000000000 : ℝ)] ![(77555221729409/100000000000000 : ℝ), (9236801834537/50000000000000 : ℝ), (1985587297109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2053181947/2500000000 : ℝ)|^71 ≤ (77555221729409/100000000000000 : ℝ)^55
        have hw : |(2053181947/2500000000 : ℝ)|=(2053181947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351468003/5000000000 : ℝ)|^71 ≤ (9236801834537/50000000000000 : ℝ)^55
        have hw : |(1351468003/5000000000 : ℝ)|=(1351468003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164318153/2000000000 : ℝ)|^71 ≤ (1985587297109/50000000000000 : ℝ)^55
        have hw : |(164318153/2000000000 : ℝ)|=(164318153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-78466697/1000000000 : ℝ)*x 0 + (3570986489/5000000000 : ℝ)*x 1 + (2043315369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (78466697/1000000000 : ℝ)^71 ≤ (116947063059/3125000000000 : ℝ)^55 := by
    have hnat : (78466697 : ℕ)^71*3125000000000^55 ≤ 116947063059^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78466697 1000000000 116947063059 3125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3570986489/5000000000 : ℝ)^71 ≤ (64757874967323/100000000000000 : ℝ)^55 := by
    have hnat : (3570986489 : ℕ)^71*100000000000000^55 ≤ 64757874967323^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3570986489 5000000000 64757874967323 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2043315369/5000000000 : ℝ)^71 ≤ (15749909499221/50000000000000 : ℝ)^55 := by
    have hnat : (2043315369 : ℕ)^71*50000000000000^55 ≤ 15749909499221^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043315369 5000000000 15749909499221 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-78466697/1000000000 : ℝ), (3570986489/5000000000 : ℝ), (2043315369/5000000000 : ℝ)] ![(116947063059/3125000000000 : ℝ), (64757874967323/100000000000000 : ℝ), (15749909499221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-78466697/1000000000 : ℝ)|^71 ≤ (116947063059/3125000000000 : ℝ)^55
        have hw : |(-78466697/1000000000 : ℝ)|=(78466697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3570986489/5000000000 : ℝ)|^71 ≤ (64757874967323/100000000000000 : ℝ)^55
        have hw : |(3570986489/5000000000 : ℝ)|=(3570986489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2043315369/5000000000 : ℝ)|^71 ≤ (15749909499221/50000000000000 : ℝ)^55
        have hw : |(2043315369/5000000000 : ℝ)|=(2043315369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6744912757/10000000000 : ℝ)*x 0 + (-4391279/2000000000 : ℝ)*x 1 + (122493703/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6744912757/10000000000 : ℝ)^71 ≤ (30074194386933/50000000000000 : ℝ)^55 := by
    have hnat : (6744912757 : ℕ)^71*50000000000000^55 ≤ 30074194386933^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6744912757 10000000000 30074194386933 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4391279/2000000000 : ℝ)^71 ≤ (36999595211/100000000000000 : ℝ)^55 := by
    have hnat : (4391279 : ℕ)^71*100000000000000^55 ≤ 36999595211^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391279 2000000000 36999595211 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122493703/250000000 : ℝ)^71 ≤ (39814611619183/100000000000000 : ℝ)^55 := by
    have hnat : (122493703 : ℕ)^71*100000000000000^55 ≤ 39814611619183^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122493703 250000000 39814611619183 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6744912757/10000000000 : ℝ), (-4391279/2000000000 : ℝ), (122493703/250000000 : ℝ)] ![(30074194386933/50000000000000 : ℝ), (36999595211/100000000000000 : ℝ), (39814611619183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6744912757/10000000000 : ℝ)|^71 ≤ (30074194386933/50000000000000 : ℝ)^55
        have hw : |(6744912757/10000000000 : ℝ)|=(6744912757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4391279/2000000000 : ℝ)|^71 ≤ (36999595211/100000000000000 : ℝ)^55
        have hw : |(-4391279/2000000000 : ℝ)|=(4391279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(122493703/250000000 : ℝ)|^71 ≤ (39814611619183/100000000000000 : ℝ)^55
        have hw : |(122493703/250000000 : ℝ)|=(122493703/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3030885059/10000000000 : ℝ)*x 0 + (948381219/1250000000 : ℝ)*x 1 + (-298150701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3030885059/10000000000 : ℝ)^71 ≤ (10708368702009/50000000000000 : ℝ)^55 := by
    have hnat : (3030885059 : ℕ)^71*50000000000000^55 ≤ 10708368702009^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3030885059 10000000000 10708368702009 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948381219/1250000000 : ℝ)^71 ≤ (70014026985269/100000000000000 : ℝ)^55 := by
    have hnat : (948381219 : ℕ)^71*100000000000000^55 ≤ 70014026985269^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948381219 1250000000 70014026985269 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (298150701/2000000000 : ℝ)^71 ≤ (1713847119461/20000000000000 : ℝ)^55 := by
    have hnat : (298150701 : ℕ)^71*20000000000000^55 ≤ 1713847119461^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298150701 2000000000 1713847119461 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3030885059/10000000000 : ℝ), (948381219/1250000000 : ℝ), (-298150701/2000000000 : ℝ)] ![(10708368702009/50000000000000 : ℝ), (70014026985269/100000000000000 : ℝ), (1713847119461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3030885059/10000000000 : ℝ)|^71 ≤ (10708368702009/50000000000000 : ℝ)^55
        have hw : |(3030885059/10000000000 : ℝ)|=(3030885059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(948381219/1250000000 : ℝ)|^71 ≤ (70014026985269/100000000000000 : ℝ)^55
        have hw : |(948381219/1250000000 : ℝ)|=(948381219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-298150701/2000000000 : ℝ)|^71 ≤ (1713847119461/20000000000000 : ℝ)^55
        have hw : |(-298150701/2000000000 : ℝ)|=(298150701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s2_s2_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1005626777/1250000000 : ℝ)*x 0 + (2197240851/10000000000 : ℝ)*x 1 + (1724768473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005626777/1250000000 : ℝ)^71 ≤ (75516822457723/100000000000000 : ℝ)^55 := by
    have hnat : (1005626777 : ℕ)^71*100000000000000^55 ≤ 75516822457723^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005626777 1250000000 75516822457723 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197240851/10000000000 : ℝ)^71 ≤ (14139169296449/100000000000000 : ℝ)^55 := by
    have hnat : (2197240851 : ℕ)^71*100000000000000^55 ≤ 14139169296449^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197240851 10000000000 14139169296449 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1724768473/10000000000 : ℝ)^71 ≤ (517200411631/5000000000000 : ℝ)^55 := by
    have hnat : (1724768473 : ℕ)^71*5000000000000^55 ≤ 517200411631^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724768473 10000000000 517200411631 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1005626777/1250000000 : ℝ), (2197240851/10000000000 : ℝ), (1724768473/10000000000 : ℝ)] ![(75516822457723/100000000000000 : ℝ), (14139169296449/100000000000000 : ℝ), (517200411631/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1005626777/1250000000 : ℝ)|^71 ≤ (75516822457723/100000000000000 : ℝ)^55
        have hw : |(1005626777/1250000000 : ℝ)|=(1005626777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2197240851/10000000000 : ℝ)|^71 ≤ (14139169296449/100000000000000 : ℝ)^55
        have hw : |(2197240851/10000000000 : ℝ)|=(2197240851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1724768473/10000000000 : ℝ)|^71 ≤ (517200411631/5000000000000 : ℝ)^55
        have hw : |(1724768473/10000000000 : ℝ)|=(1724768473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310055_s2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((38651/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38651/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9341/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9341/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37943/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(37943/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((62057/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62057/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30651/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30651/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12519/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12519/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (18111/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (38651/50000 : ℝ) ^ (35/8 : ℝ) ≤ (16210800073730771159/50000000000000000000 : ℝ) := by
    have hpowers : (38651/50000 : ℝ)^35 ≤ (16210800073730771159/50000000000000000000 : ℝ)^8 := by
      have hnat : (38651 : ℕ)^35*50000000000000000000^8 ≤ 16210800073730771159^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38651 50000 16210800073730771159 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38651/50000 : ℝ)) (X := (16210800073730771159/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (66210800073730771159/50000000000000000000 : ℝ) ≤ (2132584753613259/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (66210800073730771159/50000000000000000000 : ℝ)^8 ≤ (2132584753613259/2000000000000000 : ℝ)^35 := by
      have hnat : (66210800073730771159 : ℕ)^8*2000000000000000^35 ≤ 2132584753613259^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66210800073730771159 50000000000000000000 2132584753613259 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2132584753613259/2000000000000000 : ℝ)) (X := (66210800073730771159/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (41210800073730771159/25000000000000000000 : ℝ) ≤ (5605137121696799/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (41210800073730771159/25000000000000000000 : ℝ)^8 ≤ (5605137121696799/5000000000000000 : ℝ)^35 := by
      have hnat : (41210800073730771159 : ℕ)^8*5000000000000000^35 ≤ 5605137121696799^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41210800073730771159 25000000000000000000 5605137121696799 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5605137121696799/5000000000000000 : ℝ)) (X := (41210800073730771159/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(132584753613259/1546040000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(547350475327303/7730200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (38651/50000 : ℝ)) (alpha := (132584753613259/1546040000000000 : ℝ)) (beta := (547350475327303/7730200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (38651/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(132584753613259/1546040000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(547350475327303/7730200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (9341/12500 : ℝ) ^ (35/8 : ℝ) ≤ (5591388792411747447/20000000000000000000 : ℝ) := by
    have hpowers : (9341/12500 : ℝ)^35 ≤ (5591388792411747447/20000000000000000000 : ℝ)^8 := by
      have hnat : (9341 : ℕ)^35*20000000000000000000^8 ≤ 5591388792411747447^8*12500^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9341 12500 5591388792411747447 20000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9341/12500 : ℝ)) (X := (5591388792411747447/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (25591388792411747447/20000000000000000000 : ℝ) ≤ (5289830344579611/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25591388792411747447/20000000000000000000 : ℝ)^8 ≤ (5289830344579611/5000000000000000 : ℝ)^35 := by
      have hnat : (25591388792411747447 : ℕ)^8*5000000000000000^35 ≤ 5289830344579611^35*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25591388792411747447 20000000000000000000 5289830344579611 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5289830344579611/5000000000000000 : ℝ)) (X := (25591388792411747447/20000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (15591388792411747447/10000000000000000000 : ℝ) ≤ (11068479234018001/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (15591388792411747447/10000000000000000000 : ℝ)^8 ≤ (11068479234018001/10000000000000000 : ℝ)^35 := by
      have hnat : (15591388792411747447 : ℕ)^8*10000000000000000^35 ≤ 11068479234018001^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15591388792411747447 10000000000000000000 11068479234018001 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11068479234018001/10000000000000000 : ℝ)) (X := (15591388792411747447/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(289830344579611/3736400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(488818544858779/7472800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (9341/12500 : ℝ)) (alpha := (289830344579611/3736400000000000 : ℝ)) (beta := (488818544858779/7472800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (9341/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(289830344579611/3736400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(488818544858779/7472800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (37943/50000 : ℝ) ^ (35/8 : ℝ) ≤ (5980496832123940427/20000000000000000000 : ℝ) := by
    have hpowers : (37943/50000 : ℝ)^35 ≤ (5980496832123940427/20000000000000000000 : ℝ)^8 := by
      have hnat : (37943 : ℕ)^35*20000000000000000000^8 ≤ 5980496832123940427^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37943 50000 5980496832123940427 20000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37943/50000 : ℝ)) (X := (5980496832123940427/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (25980496832123940427/20000000000000000000 : ℝ) ≤ (1327026871942321/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25980496832123940427/20000000000000000000 : ℝ)^8 ≤ (1327026871942321/1250000000000000 : ℝ)^35 := by
      have hnat : (25980496832123940427 : ℕ)^8*1250000000000000^35 ≤ 1327026871942321^35*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25980496832123940427 20000000000000000000 1327026871942321 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1327026871942321/1250000000000000 : ℝ)) (X := (25980496832123940427/20000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (15980496832123940427/10000000000000000000 : ℝ) ≤ (2782754727400169/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (15980496832123940427/10000000000000000000 : ℝ)^8 ≤ (2782754727400169/2500000000000000 : ℝ)^35 := by
      have hnat : (15980496832123940427 : ℕ)^8*2500000000000000^35 ≤ 2782754727400169^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15980496832123940427 10000000000000000000 2782754727400169 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2782754727400169/2500000000000000 : ℝ)) (X := (15980496832123940427/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(77026871942321/948575000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(128700983515527/1897150000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (37943/50000 : ℝ)) (alpha := (77026871942321/948575000000000 : ℝ)) (beta := (128700983515527/1897150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (37943/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(77026871942321/948575000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(128700983515527/1897150000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1651272899/10000000000 : ℝ)*X 0 0+(5845231607/10000000000 : ℝ)*X 0 1+(987714317/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((2427986753/5000000000 : ℝ)*X 1 0+(-120850261/2000000000 : ℝ)*X 1 1+(6555164531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((483034217/1000000000 : ℝ)*X 2 0+(5971637093/10000000000 : ℝ)*X 2 1+(-202047711/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((6355993913/10000000000 : ℝ)*X 0 0+(967732521/2500000000 : ℝ)*X 0 1+(572680841/2500000000 : ℝ)*X 0 2+(6355993913/10000000000 : ℝ)*X 1 0+(967732521/2500000000 : ℝ)*X 1 1+(572680841/2500000000 : ℝ)*X 1 2+(6355993913/10000000000 : ℝ)*X 2 0+(967732521/2500000000 : ℝ)*X 2 1+(572680841/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-77891159/500000000 : ℝ)*X 0 0+(4216053331/10000000000 : ℝ)*X 0 1+(6569463849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((772577131/2000000000 : ℝ)*X 1 0+(-68299/10000000000 : ℝ)*X 1 1+(3822642543/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((3834190551/10000000000 : ℝ)*X 2 0+(7361847089/10000000000 : ℝ)*X 2 1+(-384506187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1099135073/2500000000 : ℝ)*X 0 0+(659445331/1000000000 : ℝ)*X 0 1+(1269057709/10000000000 : ℝ)*X 0 2+(1099135073/2500000000 : ℝ)*X 1 0+(659445331/1000000000 : ℝ)*X 1 1+(1269057709/10000000000 : ℝ)*X 1 2+(1099135073/2500000000 : ℝ)*X 2 0+(659445331/1000000000 : ℝ)*X 2 1+(1269057709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-493917077/10000000000 : ℝ)*X 0 0+(929561947/2000000000 : ℝ)*X 0 1+(424815791/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((3396646707/10000000000 : ℝ)*X 1 0+(-57792413/1250000000 : ℝ)*X 1 1+(3930701887/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((417818117/625000000 : ℝ)*X 2 0+(4787815773/10000000000 : ℝ)*X 2 1+(-18527333/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((2053181947/2500000000 : ℝ)*X 0 0+(1351468003/5000000000 : ℝ)*X 0 1+(164318153/2000000000 : ℝ)*X 0 2+(2053181947/2500000000 : ℝ)*X 1 0+(1351468003/5000000000 : ℝ)*X 1 1+(164318153/2000000000 : ℝ)*X 1 2+(2053181947/2500000000 : ℝ)*X 2 0+(1351468003/5000000000 : ℝ)*X 2 1+(164318153/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-78466697/1000000000 : ℝ)*X 0 0+(3570986489/5000000000 : ℝ)*X 0 1+(2043315369/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((6744912757/10000000000 : ℝ)*X 1 0+(-4391279/2000000000 : ℝ)*X 1 1+(122493703/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((3030885059/10000000000 : ℝ)*X 2 0+(948381219/1250000000 : ℝ)*X 2 1+(-298150701/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1005626777/1250000000 : ℝ)*X 0 0+(2197240851/10000000000 : ℝ)*X 0 1+(1724768473/10000000000 : ℝ)*X 0 2+(1005626777/1250000000 : ℝ)*X 1 0+(2197240851/10000000000 : ℝ)*X 1 1+(1724768473/10000000000 : ℝ)*X 1 2+(1005626777/1250000000 : ℝ)*X 2 0+(2197240851/10000000000 : ℝ)*X 2 1+(1724768473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((62057/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62057/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (538103936603687435534268397563/136989024355130000000000000000000000 : ℝ) := by norm_num
    linear_combination (503956572393/1000000000000 : ℝ)*(base7) + (376889/1000000000000 : ℝ)*(base49) + (304923/500000000000 : ℝ)*(base60) + (65720424519/25000000000 : ℝ)*(major_s2_0) + (65720424519/25000000000 : ℝ)*(major_s2_1) + (65720424519/25000000000 : ℝ)*(major_s2_2) + (4071883/1000000000000 : ℝ)*(sp_s2_0) + (316457/200000000000 : ℝ)*(sp_s2_6) + (332857490393/100000000000 : ℝ)*(sp_s2_7) + (3328591401327/1000000000000 : ℝ)*(sp_s2_8) + (1664292628837/500000000000 : ℝ)*(sp_s2_9) + (266094707273/125000000000 : ℝ)*(sp_s2_13) + (6212757/500000000000 : ℝ)*(sp_s2_14) + (6143653/1000000000000 : ℝ)*(sp_s2_23) + (406200667019/250000000000 : ℝ)*(f.failure) + (3328591401327/1000000000000 : ℝ)*(f.sum) + (604107001129800237/3544255630000000000000000000000 : ℝ)*base63 + (102413144510779/379430000000000000000000000 : ℝ)*base64 + (115235499557289/186820000000000000000000000 : ℝ)*base67 + (18811889358531/37943000000000000000000000 : ℝ)*base69 + (8772059473445775117/14665348930000000000000000000000 : ℝ)*base70 + (11936581517187/48313750000000000000000000 : ℝ)*base73 + (2461672966543/18682000000000000000000000 : ℝ)*base75 + (246566203421/3019609375000000000000000 : ℝ)*base77 + (2260542098615300987/7220779820000000000000000000000 : ℝ)*base79 + (5067/25000000000000000 : ℝ)*base87 + (5067/25000000000000000 : ℝ)*base89 + (5067/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30651/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30651/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18642940057935434032317657/2835404504000000000000000000000 : ℝ) := by norm_num
    linear_combination (398353543397/1000000000000 : ℝ)*(base7) + (769603/200000000000 : ℝ)*(base27) + (77019/1000000000000 : ℝ)*(base59) + (2355717529699/1000000000000 : ℝ)*(major_s2_0) + (2355717529699/1000000000000 : ℝ)*(major_s2_1) + (2355717529699/1000000000000 : ℝ)*(major_s2_2) + (2042449/250000000000 : ℝ)*(sp_s2_0) + (7752039/1000000000000 : ℝ)*(sp_s2_2) + (36694867/500000000000 : ℝ)*(sp_s2_8) + (47108306047/15625000000 : ℝ)*(sp_s2_14) + (301486636707/100000000000 : ℝ)*(sp_s2_15) + (602986400953/200000000000 : ℝ)*(sp_s2_16) + (115896093193/62500000000 : ℝ)*(sp_s2_20) + (4820263/250000000000 : ℝ)*(sp_s2_27) + (728003538379/500000000000 : ℝ)*(f.failure) + (753734939201/250000000000 : ℝ)*(f.sum) + (68102469039042899369/141770225200000000000000000000000 : ℝ)*base62 + (296116435016507/1897150000000000000000000000 : ℝ)*base64 + (1725419017663759/7472800000000000000000000000 : ℝ)*base67 + (98261945449491/948575000000000000000000000 : ℝ)*base68 + (159560436244270532633/293306978600000000000000000000000 : ℝ)*base70 + (2784836722907397/7730200000000000000000000000 : ℝ)*base73 + (231261953813951/3736400000000000000000000000 : ℝ)*base74 + (364596766776833/1546040000000000000000000000 : ℝ)*base77 + (13398167838689290583/288831192800000000000000000000000 : ℝ)*base78 + (3547/50000000000000000 : ℝ)*base87 + (3547/50000000000000000 : ℝ)*base89 + (3547/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12519/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12519/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (47558491630617859966728281786691/5479560974205200000000000000000000000 : ℝ) := by norm_num
    linear_combination (287810095383/500000000000 : ℝ)*(base7) + (84597/500000000000 : ℝ)*(base34) + (40551117229/500000000000 : ℝ)*(base40) + (69429/250000000000 : ℝ)*(base59) + (2215521345647/1000000000000 : ℝ)*(major_s2_0) + (2215521514841/1000000000000 : ℝ)*(major_s2_1) + (2215521514841/1000000000000 : ℝ)*(major_s2_2) + (4145073/1000000000000 : ℝ)*(sp_s2_1) + (55775091/1000000000000 : ℝ)*(sp_s2_9) + (20868341/1000000000000 : ℝ)*(sp_s2_20) + (339272806589/125000000000 : ℝ)*(sp_s2_21) + (2714178476833/1000000000000 : ℝ)*(sp_s2_22) + (542825369363/200000000000 : ℝ)*(sp_s2_23) + (60779836211/31250000000 : ℝ)*(sp_s2_27) + (1369355605521/1000000000000 : ℝ)*(f.failure) + (1357091310953/500000000000 : ℝ)*(f.sum) + (83513963919405374709/141770225200000000000000000000000 : ℝ)*base63 + (825173754371397/1897150000000000000000000000 : ℝ)*base65 + (1242981547417101/7472800000000000000000000000 : ℝ)*base67 + (808462246469737/1897150000000000000000000000 : ℝ)*base69 + (28567120802562517557/293306978600000000000000000000000 : ℝ)*base70 + (4254106257642361/7730200000000000000000000000 : ℝ)*base73 + (1706691490554611/3736400000000000000000000000 : ℝ)*base75 + (75043492633307/309208000000000000000000000 : ℝ)*base76 + (1140710072376372607/2310649542400000000000000000000 : ℝ)*base79 + (40847/100000000000000000 : ℝ)*base86 + (40847/100000000000000000 : ℝ)*base88 + (40847/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((38651/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38651/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9341/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9341/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37943/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(37943/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((62057/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62057/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30651/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30651/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12519/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12519/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310055_s2 p hpa hpb X hX hprev1

#print axioms solution
