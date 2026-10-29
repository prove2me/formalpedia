-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310086_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:15.152262+00:00
-- url     : https://prove2.me/submissions/275d4c16-36fe-4a6e-9c5a-fbbee4ee0659

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
theorem collision_support_c310086_s2_s2_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-655756029/10000000000 : ℝ)*x 0 + (-1484251689/2500000000 : ℝ)*x 1 + (2740620257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655756029/10000000000 : ℝ)^71 ≤ (1484198103829/50000000000000 : ℝ)^55 := by
    have hnat : (655756029 : ℕ)^71*50000000000000^55 ≤ 1484198103829^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655756029 10000000000 1484198103829 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1484251689/2500000000 : ℝ)^71 ≤ (25507405554969/50000000000000 : ℝ)^55 := by
    have hnat : (1484251689 : ℕ)^71*50000000000000^55 ≤ 25507405554969^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1484251689 2500000000 25507405554969 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2740620257/5000000000 : ℝ)^71 ≤ (46016792664669/100000000000000 : ℝ)^55 := by
    have hnat : (2740620257 : ℕ)^71*100000000000000^55 ≤ 46016792664669^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740620257 5000000000 46016792664669 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-655756029/10000000000 : ℝ), (-1484251689/2500000000 : ℝ), (2740620257/5000000000 : ℝ)] ![(1484198103829/50000000000000 : ℝ), (25507405554969/50000000000000 : ℝ), (46016792664669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-655756029/10000000000 : ℝ)|^71 ≤ (1484198103829/50000000000000 : ℝ)^55
        have hw : |(-655756029/10000000000 : ℝ)|=(655756029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1484251689/2500000000 : ℝ)|^71 ≤ (25507405554969/50000000000000 : ℝ)^55
        have hw : |(-1484251689/2500000000 : ℝ)|=(1484251689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2740620257/5000000000 : ℝ)|^71 ≤ (46016792664669/100000000000000 : ℝ)^55
        have hw : |(2740620257/5000000000 : ℝ)|=(2740620257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (241693659/400000000 : ℝ)*x 0 + (3388469157/10000000000 : ℝ)*x 1 + (802939541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (241693659/400000000 : ℝ)^71 ≤ (26093112826329/50000000000000 : ℝ)^55 := by
    have hnat : (241693659 : ℕ)^71*50000000000000^55 ≤ 26093112826329^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241693659 400000000 26093112826329 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3388469157/10000000000 : ℝ)^71 ≤ (12366514111941/50000000000000 : ℝ)^55 := by
    have hnat : (3388469157 : ℕ)^71*50000000000000^55 ≤ 12366514111941^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3388469157 10000000000 12366514111941 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (802939541/2500000000 : ℝ)^71 ≤ (11540373055919/50000000000000 : ℝ)^55 := by
    have hnat : (802939541 : ℕ)^71*50000000000000^55 ≤ 11540373055919^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802939541 2500000000 11540373055919 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(241693659/400000000 : ℝ), (3388469157/10000000000 : ℝ), (802939541/2500000000 : ℝ)] ![(26093112826329/50000000000000 : ℝ), (12366514111941/50000000000000 : ℝ), (11540373055919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(241693659/400000000 : ℝ)|^71 ≤ (26093112826329/50000000000000 : ℝ)^55
        have hw : |(241693659/400000000 : ℝ)|=(241693659/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3388469157/10000000000 : ℝ)|^71 ≤ (12366514111941/50000000000000 : ℝ)^55
        have hw : |(3388469157/10000000000 : ℝ)|=(3388469157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(802939541/2500000000 : ℝ)|^71 ≤ (11540373055919/50000000000000 : ℝ)^55
        have hw : |(802939541/2500000000 : ℝ)|=(802939541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1140491597/2000000000 : ℝ)*x 0 + (-901197563/2500000000 : ℝ)*x 1 + (-3393646207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1140491597/2000000000 : ℝ)^71 ≤ (48428201382149/100000000000000 : ℝ)^55 := by
    have hnat : (1140491597 : ℕ)^71*100000000000000^55 ≤ 48428201382149^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140491597 2000000000 48428201382149 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901197563/2500000000 : ℝ)^71 ≤ (5357995681851/20000000000000 : ℝ)^55 := by
    have hnat : (901197563 : ℕ)^71*20000000000000^55 ≤ 5357995681851^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901197563 2500000000 5357995681851 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3393646207/10000000000 : ℝ)^71 ≤ (24781820181523/100000000000000 : ℝ)^55 := by
    have hnat : (3393646207 : ℕ)^71*100000000000000^55 ≤ 24781820181523^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3393646207 10000000000 24781820181523 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1140491597/2000000000 : ℝ), (-901197563/2500000000 : ℝ), (-3393646207/10000000000 : ℝ)] ![(48428201382149/100000000000000 : ℝ), (5357995681851/20000000000000 : ℝ), (24781820181523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1140491597/2000000000 : ℝ)|^71 ≤ (48428201382149/100000000000000 : ℝ)^55
        have hw : |(1140491597/2000000000 : ℝ)|=(1140491597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-901197563/2500000000 : ℝ)|^71 ≤ (5357995681851/20000000000000 : ℝ)^55
        have hw : |(-901197563/2500000000 : ℝ)|=(901197563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3393646207/10000000000 : ℝ)|^71 ≤ (24781820181523/100000000000000 : ℝ)^55
        have hw : |(-3393646207/10000000000 : ℝ)|=(3393646207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1102595619/2500000000 : ℝ)*x 0 + (-3216524341/10000000000 : ℝ)*x 1 + (511787039/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102595619/2500000000 : ℝ)^71 ≤ (8689427674331/25000000000000 : ℝ)^55 := by
    have hnat : (1102595619 : ℕ)^71*25000000000000^55 ≤ 8689427674331^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102595619 2500000000 8689427674331 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3216524341/10000000000 : ℝ)^71 ≤ (5781242744643/25000000000000 : ℝ)^55 := by
    have hnat : (3216524341 : ℕ)^71*25000000000000^55 ≤ 5781242744643^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3216524341 10000000000 5781242744643 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511787039/1000000000 : ℝ)^71 ≤ (1684692732359/4000000000000 : ℝ)^55 := by
    have hnat : (511787039 : ℕ)^71*4000000000000^55 ≤ 1684692732359^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511787039 1000000000 1684692732359 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102595619/2500000000 : ℝ), (-3216524341/10000000000 : ℝ), (511787039/1000000000 : ℝ)] ![(8689427674331/25000000000000 : ℝ), (5781242744643/25000000000000 : ℝ), (1684692732359/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102595619/2500000000 : ℝ)|^71 ≤ (8689427674331/25000000000000 : ℝ)^55
        have hw : |(1102595619/2500000000 : ℝ)|=(1102595619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3216524341/10000000000 : ℝ)|^71 ≤ (5781242744643/25000000000000 : ℝ)^55
        have hw : |(-3216524341/10000000000 : ℝ)|=(3216524341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(511787039/1000000000 : ℝ)|^71 ≤ (1684692732359/4000000000000 : ℝ)^55
        have hw : |(511787039/1000000000 : ℝ)|=(511787039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-393656059/10000000000 : ℝ)*x 0 + (-6942496021/10000000000 : ℝ)*x 1 + (4535063169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393656059/10000000000 : ℝ)^71 ≤ (76805742321/5000000000000 : ℝ)^55 := by
    have hnat : (393656059 : ℕ)^71*5000000000000^55 ≤ 76805742321^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393656059 10000000000 76805742321 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6942496021/10000000000 : ℝ)^71 ≤ (31216276770197/50000000000000 : ℝ)^55 := by
    have hnat : (6942496021 : ℕ)^71*50000000000000^55 ≤ 31216276770197^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6942496021 10000000000 31216276770197 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4535063169/10000000000 : ℝ)^71 ≤ (36031331605471/100000000000000 : ℝ)^55 := by
    have hnat : (4535063169 : ℕ)^71*100000000000000^55 ≤ 36031331605471^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535063169 10000000000 36031331605471 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393656059/10000000000 : ℝ), (-6942496021/10000000000 : ℝ), (4535063169/10000000000 : ℝ)] ![(76805742321/5000000000000 : ℝ), (31216276770197/50000000000000 : ℝ), (36031331605471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393656059/10000000000 : ℝ)|^71 ≤ (76805742321/5000000000000 : ℝ)^55
        have hw : |(-393656059/10000000000 : ℝ)|=(393656059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6942496021/10000000000 : ℝ)|^71 ≤ (31216276770197/50000000000000 : ℝ)^55
        have hw : |(-6942496021/10000000000 : ℝ)|=(6942496021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4535063169/10000000000 : ℝ)|^71 ≤ (36031331605471/100000000000000 : ℝ)^55
        have hw : |(4535063169/10000000000 : ℝ)|=(4535063169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5978509887/10000000000 : ℝ)*x 0 + (3360021793/10000000000 : ℝ)*x 1 + (663343681/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5978509887/10000000000 : ℝ)^71 ≤ (5147564658633/10000000000000 : ℝ)^55 := by
    have hnat : (5978509887 : ℕ)^71*10000000000000^55 ≤ 5147564658633^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5978509887 10000000000 5147564658633 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3360021793/10000000000 : ℝ)^71 ≤ (24465308894191/100000000000000 : ℝ)^55 := by
    have hnat : (3360021793 : ℕ)^71*100000000000000^55 ≤ 24465308894191^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3360021793 10000000000 24465308894191 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (663343681/2000000000 : ℝ)^71 ≤ (4811808900907/20000000000000 : ℝ)^55 := by
    have hnat : (663343681 : ℕ)^71*20000000000000^55 ≤ 4811808900907^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663343681 2000000000 4811808900907 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5978509887/10000000000 : ℝ), (3360021793/10000000000 : ℝ), (663343681/2000000000 : ℝ)] ![(5147564658633/10000000000000 : ℝ), (24465308894191/100000000000000 : ℝ), (4811808900907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5978509887/10000000000 : ℝ)|^71 ≤ (5147564658633/10000000000000 : ℝ)^55
        have hw : |(5978509887/10000000000 : ℝ)|=(5978509887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3360021793/10000000000 : ℝ)|^71 ≤ (24465308894191/100000000000000 : ℝ)^55
        have hw : |(3360021793/10000000000 : ℝ)|=(3360021793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(663343681/2000000000 : ℝ)|^71 ≤ (4811808900907/20000000000000 : ℝ)^55
        have hw : |(663343681/2000000000 : ℝ)|=(663343681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2956982173/5000000000 : ℝ)*x 0 + (-3411249667/10000000000 : ℝ)*x 1 + (-668329781/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2956982173/5000000000 : ℝ)^71 ≤ (10151872113213/20000000000000 : ℝ)^55 := by
    have hnat : (2956982173 : ℕ)^71*20000000000000^55 ≤ 10151872113213^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956982173 5000000000 10151872113213 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3411249667/10000000000 : ℝ)^71 ≤ (12473944383147/50000000000000 : ℝ)^55 := by
    have hnat : (3411249667 : ℕ)^71*50000000000000^55 ≤ 12473944383147^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3411249667 10000000000 12473944383147 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (668329781/2000000000 : ℝ)^71 ≤ (3036593832337/12500000000000 : ℝ)^55 := by
    have hnat : (668329781 : ℕ)^71*12500000000000^55 ≤ 3036593832337^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668329781 2000000000 3036593832337 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2956982173/5000000000 : ℝ), (-3411249667/10000000000 : ℝ), (-668329781/2000000000 : ℝ)] ![(10151872113213/20000000000000 : ℝ), (12473944383147/50000000000000 : ℝ), (3036593832337/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2956982173/5000000000 : ℝ)|^71 ≤ (10151872113213/20000000000000 : ℝ)^55
        have hw : |(2956982173/5000000000 : ℝ)|=(2956982173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3411249667/10000000000 : ℝ)|^71 ≤ (12473944383147/50000000000000 : ℝ)^55
        have hw : |(-3411249667/10000000000 : ℝ)|=(3411249667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-668329781/2000000000 : ℝ)|^71 ≤ (3036593832337/12500000000000 : ℝ)^55
        have hw : |(-668329781/2000000000 : ℝ)|=(668329781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3190898423/10000000000 : ℝ)*x 0 + (-42413393/250000000 : ℝ)*x 1 + (3665828021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3190898423/10000000000 : ℝ)^71 ≤ (572185389179/2500000000000 : ℝ)^55 := by
    have hnat : (3190898423 : ℕ)^71*2500000000000^55 ≤ 572185389179^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3190898423 10000000000 572185389179 2500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42413393/250000000 : ℝ)^71 ≤ (10125952435741/100000000000000 : ℝ)^55 := by
    have hnat : (42413393 : ℕ)^71*100000000000000^55 ≤ 10125952435741^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42413393 250000000 10125952435741 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3665828021/5000000000 : ℝ)^71 ≤ (66986631990707/100000000000000 : ℝ)^55 := by
    have hnat : (3665828021 : ℕ)^71*100000000000000^55 ≤ 66986631990707^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665828021 5000000000 66986631990707 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3190898423/10000000000 : ℝ), (-42413393/250000000 : ℝ), (3665828021/5000000000 : ℝ)] ![(572185389179/2500000000000 : ℝ), (10125952435741/100000000000000 : ℝ), (66986631990707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3190898423/10000000000 : ℝ)|^71 ≤ (572185389179/2500000000000 : ℝ)^55
        have hw : |(3190898423/10000000000 : ℝ)|=(3190898423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42413393/250000000 : ℝ)|^71 ≤ (10125952435741/100000000000000 : ℝ)^55
        have hw : |(-42413393/250000000 : ℝ)|=(42413393/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3665828021/5000000000 : ℝ)|^71 ≤ (66986631990707/100000000000000 : ℝ)^55
        have hw : |(3665828021/5000000000 : ℝ)|=(3665828021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-10127493/2000000000 : ℝ)*x 0 + (-2829959747/5000000000 : ℝ)*x 1 + (6019242337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10127493/2000000000 : ℝ)^71 ≤ (54406649769/50000000000000 : ℝ)^55 := by
    have hnat : (10127493 : ℕ)^71*50000000000000^55 ≤ 54406649769^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10127493 2000000000 54406649769 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2829959747/5000000000 : ℝ)^71 ≤ (47962356138371/100000000000000 : ℝ)^55 := by
    have hnat : (2829959747 : ℕ)^71*100000000000000^55 ≤ 47962356138371^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829959747 5000000000 47962356138371 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6019242337/10000000000 : ℝ)^71 ≤ (6491103818879/12500000000000 : ℝ)^55 := by
    have hnat : (6019242337 : ℕ)^71*12500000000000^55 ≤ 6491103818879^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6019242337 10000000000 6491103818879 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10127493/2000000000 : ℝ), (-2829959747/5000000000 : ℝ), (6019242337/10000000000 : ℝ)] ![(54406649769/50000000000000 : ℝ), (47962356138371/100000000000000 : ℝ), (6491103818879/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10127493/2000000000 : ℝ)|^71 ≤ (54406649769/50000000000000 : ℝ)^55
        have hw : |(-10127493/2000000000 : ℝ)|=(10127493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2829959747/5000000000 : ℝ)|^71 ≤ (47962356138371/100000000000000 : ℝ)^55
        have hw : |(-2829959747/5000000000 : ℝ)|=(2829959747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6019242337/10000000000 : ℝ)|^71 ≤ (6491103818879/12500000000000 : ℝ)^55
        have hw : |(6019242337/10000000000 : ℝ)|=(6019242337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6701166137/10000000000 : ℝ)*x 0 + (3132851433/10000000000 : ℝ)*x 1 + (1324742301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6701166137/10000000000 : ℝ)^71 ≤ (59645262163649/100000000000000 : ℝ)^55 := by
    have hnat : (6701166137 : ℕ)^71*100000000000000^55 ≤ 59645262163649^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6701166137 10000000000 59645262163649 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3132851433/10000000000 : ℝ)^71 ≤ (22351367827461/100000000000000 : ℝ)^55 := by
    have hnat : (3132851433 : ℕ)^71*100000000000000^55 ≤ 22351367827461^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3132851433 10000000000 22351367827461 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1324742301/5000000000 : ℝ)^71 ≤ (18003370001417/100000000000000 : ℝ)^55 := by
    have hnat : (1324742301 : ℕ)^71*100000000000000^55 ≤ 18003370001417^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324742301 5000000000 18003370001417 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6701166137/10000000000 : ℝ), (3132851433/10000000000 : ℝ), (1324742301/5000000000 : ℝ)] ![(59645262163649/100000000000000 : ℝ), (22351367827461/100000000000000 : ℝ), (18003370001417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6701166137/10000000000 : ℝ)|^71 ≤ (59645262163649/100000000000000 : ℝ)^55
        have hw : |(6701166137/10000000000 : ℝ)|=(6701166137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3132851433/10000000000 : ℝ)|^71 ≤ (22351367827461/100000000000000 : ℝ)^55
        have hw : |(3132851433/10000000000 : ℝ)|=(3132851433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1324742301/5000000000 : ℝ)|^71 ≤ (18003370001417/100000000000000 : ℝ)^55
        have hw : |(1324742301/5000000000 : ℝ)|=(1324742301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (778362123/1250000000 : ℝ)*x 0 + (-353563507/1000000000 : ℝ)*x 1 + (-2831833841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (778362123/1250000000 : ℝ)^71 ≤ (27126480294993/50000000000000 : ℝ)^55 := by
    have hnat : (778362123 : ℕ)^71*50000000000000^55 ≤ 27126480294993^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778362123 1250000000 27126480294993 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (353563507/1000000000 : ℝ)^71 ≤ (26128381252089/100000000000000 : ℝ)^55 := by
    have hnat : (353563507 : ℕ)^71*100000000000000^55 ≤ 26128381252089^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353563507 1000000000 26128381252089 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2831833841/10000000000 : ℝ)^71 ≤ (19618658145497/100000000000000 : ℝ)^55 := by
    have hnat : (2831833841 : ℕ)^71*100000000000000^55 ≤ 19618658145497^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831833841 10000000000 19618658145497 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(778362123/1250000000 : ℝ), (-353563507/1000000000 : ℝ), (-2831833841/10000000000 : ℝ)] ![(27126480294993/50000000000000 : ℝ), (26128381252089/100000000000000 : ℝ), (19618658145497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(778362123/1250000000 : ℝ)|^71 ≤ (27126480294993/50000000000000 : ℝ)^55
        have hw : |(778362123/1250000000 : ℝ)|=(778362123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-353563507/1000000000 : ℝ)|^71 ≤ (26128381252089/100000000000000 : ℝ)^55
        have hw : |(-353563507/1000000000 : ℝ)|=(353563507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2831833841/10000000000 : ℝ)|^71 ≤ (19618658145497/100000000000000 : ℝ)^55
        have hw : |(-2831833841/10000000000 : ℝ)|=(2831833841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1670020981/5000000000 : ℝ)*x 0 + (-2502213621/10000000000 : ℝ)*x 1 + (6644956673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1670020981/5000000000 : ℝ)^71 ≤ (1213883567167/5000000000000 : ℝ)^55 := by
    have hnat : (1670020981 : ℕ)^71*5000000000000^55 ≤ 1213883567167^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1670020981 5000000000 1213883567167 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2502213621/10000000000 : ℝ)^71 ≤ (16722125456501/100000000000000 : ℝ)^55 := by
    have hnat : (2502213621 : ℕ)^71*100000000000000^55 ≤ 16722125456501^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502213621 10000000000 16722125456501 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6644956673/10000000000 : ℝ)^71 ≤ (460939087447/781250000000 : ℝ)^55 := by
    have hnat : (6644956673 : ℕ)^71*781250000000^55 ≤ 460939087447^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6644956673 10000000000 460939087447 781250000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1670020981/5000000000 : ℝ), (-2502213621/10000000000 : ℝ), (6644956673/10000000000 : ℝ)] ![(1213883567167/5000000000000 : ℝ), (16722125456501/100000000000000 : ℝ), (460939087447/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1670020981/5000000000 : ℝ)|^71 ≤ (1213883567167/5000000000000 : ℝ)^55
        have hw : |(1670020981/5000000000 : ℝ)|=(1670020981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2502213621/10000000000 : ℝ)|^71 ≤ (16722125456501/100000000000000 : ℝ)^55
        have hw : |(-2502213621/10000000000 : ℝ)|=(2502213621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6644956673/10000000000 : ℝ)|^71 ≤ (460939087447/781250000000 : ℝ)^55
        have hw : |(6644956673/10000000000 : ℝ)|=(6644956673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5245729/2000000000 : ℝ)*x 0 + (-3255017731/5000000000 : ℝ)*x 1 + (5153397181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245729/2000000000 : ℝ)^71 ≤ (5818141759/12500000000000 : ℝ)^55 := by
    have hnat : (5245729 : ℕ)^71*12500000000000^55 ≤ 5818141759^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245729 2000000000 5818141759 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3255017731/5000000000 : ℝ)^71 ≤ (287291688433/500000000000 : ℝ)^55 := by
    have hnat : (3255017731 : ℕ)^71*500000000000^55 ≤ 287291688433^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3255017731 5000000000 287291688433 500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5153397181/10000000000 : ℝ)^71 ≤ (42495117165457/100000000000000 : ℝ)^55 := by
    have hnat : (5153397181 : ℕ)^71*100000000000000^55 ≤ 42495117165457^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153397181 10000000000 42495117165457 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5245729/2000000000 : ℝ), (-3255017731/5000000000 : ℝ), (5153397181/10000000000 : ℝ)] ![(5818141759/12500000000000 : ℝ), (287291688433/500000000000 : ℝ), (42495117165457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5245729/2000000000 : ℝ)|^71 ≤ (5818141759/12500000000000 : ℝ)^55
        have hw : |(-5245729/2000000000 : ℝ)|=(5245729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3255017731/5000000000 : ℝ)|^71 ≤ (287291688433/500000000000 : ℝ)^55
        have hw : |(-3255017731/5000000000 : ℝ)|=(3255017731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5153397181/10000000000 : ℝ)|^71 ≤ (42495117165457/100000000000000 : ℝ)^55
        have hw : |(5153397181/10000000000 : ℝ)|=(5153397181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3362786941/5000000000 : ℝ)*x 0 + (2981308667/10000000000 : ℝ)*x 1 + (2774626937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3362786941/5000000000 : ℝ)^71 ≤ (59925856376679/100000000000000 : ℝ)^55 := by
    have hnat : (3362786941 : ℕ)^71*100000000000000^55 ≤ 59925856376679^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3362786941 5000000000 59925856376679 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2981308667/10000000000 : ℝ)^71 ≤ (10482796341601/50000000000000 : ℝ)^55 := by
    have hnat : (2981308667 : ℕ)^71*50000000000000^55 ≤ 10482796341601^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2981308667 10000000000 10482796341601 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2774626937/10000000000 : ℝ)^71 ≤ (19108550925231/100000000000000 : ℝ)^55 := by
    have hnat : (2774626937 : ℕ)^71*100000000000000^55 ≤ 19108550925231^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2774626937 10000000000 19108550925231 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3362786941/5000000000 : ℝ), (2981308667/10000000000 : ℝ), (2774626937/10000000000 : ℝ)] ![(59925856376679/100000000000000 : ℝ), (10482796341601/50000000000000 : ℝ), (19108550925231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3362786941/5000000000 : ℝ)|^71 ≤ (59925856376679/100000000000000 : ℝ)^55
        have hw : |(3362786941/5000000000 : ℝ)|=(3362786941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2981308667/10000000000 : ℝ)|^71 ≤ (10482796341601/50000000000000 : ℝ)^55
        have hw : |(2981308667/10000000000 : ℝ)|=(2981308667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2774626937/10000000000 : ℝ)|^71 ≤ (19108550925231/100000000000000 : ℝ)^55
        have hw : |(2774626937/10000000000 : ℝ)|=(2774626937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2740083251/5000000000 : ℝ)*x 0 + (-3789959333/10000000000 : ℝ)*x 1 + (-865163407/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2740083251/5000000000 : ℝ)^71 ≤ (1437661040101/3125000000000 : ℝ)^55 := by
    have hnat : (2740083251 : ℕ)^71*3125000000000^55 ≤ 1437661040101^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740083251 5000000000 1437661040101 3125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3789959333/10000000000 : ℝ)^71 ≤ (14289779066659/50000000000000 : ℝ)^55 := by
    have hnat : (3789959333 : ℕ)^71*50000000000000^55 ≤ 14289779066659^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3789959333 10000000000 14289779066659 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (865163407/2500000000 : ℝ)^71 ≤ (25415288569203/100000000000000 : ℝ)^55 := by
    have hnat : (865163407 : ℕ)^71*100000000000000^55 ≤ 25415288569203^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865163407 2500000000 25415288569203 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2740083251/5000000000 : ℝ), (-3789959333/10000000000 : ℝ), (-865163407/2500000000 : ℝ)] ![(1437661040101/3125000000000 : ℝ), (14289779066659/50000000000000 : ℝ), (25415288569203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2740083251/5000000000 : ℝ)|^71 ≤ (1437661040101/3125000000000 : ℝ)^55
        have hw : |(2740083251/5000000000 : ℝ)|=(2740083251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3789959333/10000000000 : ℝ)|^71 ≤ (14289779066659/50000000000000 : ℝ)^55
        have hw : |(-3789959333/10000000000 : ℝ)|=(3789959333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-865163407/2500000000 : ℝ)|^71 ≤ (25415288569203/100000000000000 : ℝ)^55
        have hw : |(-865163407/2500000000 : ℝ)|=(865163407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310086_s2_s2_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5009634863/10000000000 : ℝ)*x 0 + (-83233111/312500000 : ℝ)*x 1 + (5003181611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5009634863/10000000000 : ℝ)^71 ≤ (4097103452651/10000000000000 : ℝ)^55 := by
    have hnat : (5009634863 : ℕ)^71*10000000000000^55 ≤ 4097103452651^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5009634863 10000000000 4097103452651 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83233111/312500000 : ℝ)^71 ≤ (3625209843027/20000000000000 : ℝ)^55 := by
    have hnat : (83233111 : ℕ)^71*20000000000000^55 ≤ 3625209843027^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83233111 312500000 3625209843027 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5003181611/10000000000 : ℝ)^71 ≤ (40902916236811/100000000000000 : ℝ)^55 := by
    have hnat : (5003181611 : ℕ)^71*100000000000000^55 ≤ 40902916236811^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003181611 10000000000 40902916236811 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5009634863/10000000000 : ℝ), (-83233111/312500000 : ℝ), (5003181611/10000000000 : ℝ)] ![(4097103452651/10000000000000 : ℝ), (3625209843027/20000000000000 : ℝ), (40902916236811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5009634863/10000000000 : ℝ)|^71 ≤ (4097103452651/10000000000000 : ℝ)^55
        have hw : |(5009634863/10000000000 : ℝ)|=(5009634863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83233111/312500000 : ℝ)|^71 ≤ (3625209843027/20000000000000 : ℝ)^55
        have hw : |(-83233111/312500000 : ℝ)|=(83233111/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5003181611/10000000000 : ℝ)|^71 ≤ (40902916236811/100000000000000 : ℝ)^55
        have hw : |(5003181611/10000000000 : ℝ)|=(5003181611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310086_s2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((28259/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28259/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-37731/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-37731/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74177/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74177/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2407/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2407/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-43543/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-43543/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35829/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35829/100000 : ℝ)*X 1 2) := by
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
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (28259/50000 : ℝ) ^ (35/8 : ℝ) ≤ (8237912690248902593/100000000000000000000 : ℝ) := by
    have hpowers : (28259/50000 : ℝ)^35 ≤ (8237912690248902593/100000000000000000000 : ℝ)^8 := by
      have hnat : (28259 : ℕ)^35*100000000000000000000^8 ≤ 8237912690248902593^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28259 50000 8237912690248902593 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28259/50000 : ℝ)) (X := (8237912690248902593/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (108237912690248902593/100000000000000000000 : ℝ) ≤ (5091293747797383/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (108237912690248902593/100000000000000000000 : ℝ)^8 ≤ (5091293747797383/5000000000000000 : ℝ)^35 := by
      have hnat : (108237912690248902593 : ℕ)^8*5000000000000000^35 ≤ 5091293747797383^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108237912690248902593 100000000000000000000 5091293747797383 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5091293747797383/5000000000000000 : ℝ)) (X := (108237912690248902593/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (58237912690248902593/50000000000000000000 : ℝ) ≤ (10354749826014787/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (58237912690248902593/50000000000000000000 : ℝ)^8 ≤ (10354749826014787/10000000000000000 : ℝ)^35 := by
      have hnat : (58237912690248902593 : ℕ)^8*10000000000000000^35 ≤ 10354749826014787^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58237912690248902593 50000000000000000000 10354749826014787 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10354749826014787/10000000000000000 : ℝ)) (X := (58237912690248902593/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(91293747797383/2825900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(172162330420021/5651800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (28259/50000 : ℝ)) (alpha := (91293747797383/2825900000000000 : ℝ)) (beta := (172162330420021/5651800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (28259/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(91293747797383/2825900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(172162330420021/5651800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (37731/50000 : ℝ) ^ (35/8 : ℝ) ≤ (14589196247772720531/50000000000000000000 : ℝ) := by
    have hpowers : (37731/50000 : ℝ)^35 ≤ (14589196247772720531/50000000000000000000 : ℝ)^8 := by
      have hnat : (37731 : ℕ)^35*50000000000000000000^8 ≤ 14589196247772720531^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37731 50000 14589196247772720531 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37731/50000 : ℝ)) (X := (14589196247772720531/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (64589196247772720531/50000000000000000000 : ℝ) ≤ (2650664962409739/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (64589196247772720531/50000000000000000000 : ℝ)^8 ≤ (2650664962409739/2500000000000000 : ℝ)^35 := by
      have hnat : (64589196247772720531 : ℕ)^8*2500000000000000^35 ≤ 2650664962409739^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64589196247772720531 50000000000000000000 2650664962409739 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2650664962409739/2500000000000000 : ℝ)) (X := (64589196247772720531/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (39589196247772720531/25000000000000000000 : ℝ) ≤ (2221576311356627/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (39589196247772720531/25000000000000000000 : ℝ)^8 ≤ (2221576311356627/2000000000000000 : ℝ)^35 := by
      have hnat : (39589196247772720531 : ℕ)^8*2000000000000000^35 ≤ 2221576311356627^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39589196247772720531 25000000000000000000 2221576311356627 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2221576311356627/2000000000000000 : ℝ)) (X := (39589196247772720531/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(150664962409739/1886550000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(505221707144179/7546200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (37731/50000 : ℝ)) (alpha := (150664962409739/1886550000000000 : ℝ)) (beta := (505221707144179/7546200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (37731/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(150664962409739/1886550000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(505221707144179/7546200000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (74177/100000 : ℝ) ^ (35/8 : ℝ) ≤ (3383280819325437403/12500000000000000000 : ℝ) := by
    have hpowers : (74177/100000 : ℝ)^35 ≤ (3383280819325437403/12500000000000000000 : ℝ)^8 := by
      have hnat : (74177 : ℕ)^35*12500000000000000000^8 ≤ 3383280819325437403^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74177 100000 3383280819325437403 12500000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74177/100000 : ℝ)) (X := (3383280819325437403/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (15883280819325437403/12500000000000000000 : ℝ) ≤ (5281391182971489/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (15883280819325437403/12500000000000000000 : ℝ)^8 ≤ (5281391182971489/5000000000000000 : ℝ)^35 := by
      have hnat : (15883280819325437403 : ℕ)^8*5000000000000000^35 ≤ 5281391182971489^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15883280819325437403 12500000000000000000 5281391182971489 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5281391182971489/5000000000000000 : ℝ)) (X := (15883280819325437403/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (9633280819325437403/6250000000000000000 : ℝ) ≤ (2207889032261949/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (9633280819325437403/6250000000000000000 : ℝ)^8 ≤ (2207889032261949/2000000000000000 : ℝ)^35 := by
      have hnat : (9633280819325437403 : ℕ)^8*2000000000000000^35 ≤ 2207889032261949^35*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9633280819325437403 6250000000000000000 2207889032261949 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2207889032261949/2000000000000000 : ℝ)) (X := (9633280819325437403/6250000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(281391182971489/3708850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(476662795366767/7417700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (74177/100000 : ℝ)) (alpha := (281391182971489/3708850000000000 : ℝ)) (beta := (476662795366767/7417700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (74177/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(281391182971489/3708850000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(476662795366767/7417700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-655756029/10000000000 : ℝ)*X 0 0+(-1484251689/2500000000 : ℝ)*X 0 1+(2740620257/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((241693659/400000000 : ℝ)*X 1 0+(3388469157/10000000000 : ℝ)*X 1 1+(802939541/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1140491597/2000000000 : ℝ)*X 2 0+(-901197563/2500000000 : ℝ)*X 2 1+(-3393646207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((1102595619/2500000000 : ℝ)*X 0 0+(-3216524341/10000000000 : ℝ)*X 0 1+(511787039/1000000000 : ℝ)*X 0 2+(1102595619/2500000000 : ℝ)*X 1 0+(-3216524341/10000000000 : ℝ)*X 1 1+(511787039/1000000000 : ℝ)*X 1 2+(1102595619/2500000000 : ℝ)*X 2 0+(-3216524341/10000000000 : ℝ)*X 2 1+(511787039/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-393656059/10000000000 : ℝ)*X 0 0+(-6942496021/10000000000 : ℝ)*X 0 1+(4535063169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((5978509887/10000000000 : ℝ)*X 1 0+(3360021793/10000000000 : ℝ)*X 1 1+(663343681/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2956982173/5000000000 : ℝ)*X 2 0+(-3411249667/10000000000 : ℝ)*X 2 1+(-668329781/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((3190898423/10000000000 : ℝ)*X 0 0+(-42413393/250000000 : ℝ)*X 0 1+(3665828021/5000000000 : ℝ)*X 0 2+(3190898423/10000000000 : ℝ)*X 1 0+(-42413393/250000000 : ℝ)*X 1 1+(3665828021/5000000000 : ℝ)*X 1 2+(3190898423/10000000000 : ℝ)*X 2 0+(-42413393/250000000 : ℝ)*X 2 1+(3665828021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-10127493/2000000000 : ℝ)*X 0 0+(-2829959747/5000000000 : ℝ)*X 0 1+(6019242337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((6701166137/10000000000 : ℝ)*X 1 0+(3132851433/10000000000 : ℝ)*X 1 1+(1324742301/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((778362123/1250000000 : ℝ)*X 2 0+(-353563507/1000000000 : ℝ)*X 2 1+(-2831833841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1670020981/5000000000 : ℝ)*X 0 0+(-2502213621/10000000000 : ℝ)*X 0 1+(6644956673/10000000000 : ℝ)*X 0 2+(1670020981/5000000000 : ℝ)*X 1 0+(-2502213621/10000000000 : ℝ)*X 1 1+(6644956673/10000000000 : ℝ)*X 1 2+(1670020981/5000000000 : ℝ)*X 2 0+(-2502213621/10000000000 : ℝ)*X 2 1+(6644956673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-5245729/2000000000 : ℝ)*X 0 0+(-3255017731/5000000000 : ℝ)*X 0 1+(5153397181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3362786941/5000000000 : ℝ)*X 1 0+(2981308667/10000000000 : ℝ)*X 1 1+(2774626937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2740083251/5000000000 : ℝ)*X 2 0+(-3789959333/10000000000 : ℝ)*X 2 1+(-865163407/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((5009634863/10000000000 : ℝ)*X 0 0+(-83233111/312500000 : ℝ)*X 0 1+(5003181611/10000000000 : ℝ)*X 0 2+(5009634863/10000000000 : ℝ)*X 1 0+(-83233111/312500000 : ℝ)*X 1 1+(5003181611/10000000000 : ℝ)*X 1 2+(5009634863/10000000000 : ℝ)*X 2 0+(-83233111/312500000 : ℝ)*X 2 1+(5003181611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310086_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((2407/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2407/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2373444689712053957610409036989/263635029614110000000000000000000000 : ℝ) := by norm_num
    linear_combination (218318197423/500000000000 : ℝ)*(base40) + (1638269/1000000000000 : ℝ)*(base50) + (3954417/1000000000000 : ℝ)*(base60) + (734055560129/200000000000 : ℝ)*(major_s2_0) + (734055560129/200000000000 : ℝ)*(major_s2_1) + (734055560129/200000000000 : ℝ)*(major_s2_2) + (297130911/1000000000000 : ℝ)*(sp_s2_2) + (633999191669/125000000000 : ℝ)*(sp_s2_7) + (507205037799/100000000000 : ℝ)*(sp_s2_8) + (5071731809709/1000000000000 : ℝ)*(sp_s2_9) + (1134247489547/500000000000 : ℝ)*(sp_s2_13) + (2143737/100000000000 : ℝ)*(sp_s2_16) + (90541/12500000000 : ℝ)*(sp_s2_20) + (28422319/500000000000 : ℝ)*(sp_s2_21) + (1134251111187/500000000000 : ℝ)*(f.failure) + (507205037799/100000000000 : ℝ)*(f.sum) + (92403216136507916561/111950895480000000000000000000000 : ℝ)*base62 + (332977329952311/1483540000000000000000000000 : ℝ)*base64 + (3950122161443/377310000000000000000000000 : ℝ)*base66 + (445490127497523/741770000000000000000000000 : ℝ)*base68 + (6339197517269589029/20961678430000000000000000000000 : ℝ)*base70 + (492272801827459/1130360000000000000000000000 : ℝ)*base72 + (833378557337233/1509240000000000000000000000 : ℝ)*base74 + (116370126874737/565180000000000000000000000 : ℝ)*base77 + (572622381223242541/42649613160000000000000000000000 : ℝ)*base78 + (28291/50000000000000000 : ℝ)*base87 + (28291/50000000000000000 : ℝ)*base89 + (28291/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-43543/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-43543/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (339634419693109863426189/20961678430000000000000000000 : ℝ) := by norm_num
    linear_combination (4200301/500000000000 : ℝ)*(base13) + (779588419223/500000000000 : ℝ)*(base40) + (348095487761/1000000000000 : ℝ)*(base60) + (3073912971791/500000000000 : ℝ)*(major_s2_0) + (3073912971791/500000000000 : ℝ)*(major_s2_1) + (3073912971791/500000000000 : ℝ)*(major_s2_2) + (9434693/200000000000 : ℝ)*(sp_s2_0) + (60512757/1000000000000 : ℝ)*(sp_s2_13) + (1061972664223/125000000000 : ℝ)*(sp_s2_14) + (4247707927331/500000000000 : ℝ)*(sp_s2_15) + (2123959221963/250000000000 : ℝ)*(sp_s2_16) + (30397787611/8000000000 : ℝ)*(sp_s2_20) + (421033189/1000000000000 : ℝ)*(sp_s2_22) + (5126859/200000000000 : ℝ)*(sp_s2_27) + (3799809598427/1000000000000 : ℝ)*(f.failure) + (2123959221963/250000000000 : ℝ)*(f.sum) + (33045312613459901659/279877238700000000000000000000000 : ℝ)*base63 + (959428485244169/1854425000000000000000000000 : ℝ)*base65 + (449862537357431/943275000000000000000000000 : ℝ)*base66 + (51123474770867/927212500000000000000000000 : ℝ)*base69 + (455406766379244891/818815563671875000000000000000 : ℝ)*base71 + (1175197952742679/2825900000000000000000000000 : ℝ)*base72 + (3577217006646751/3773100000000000000000000000 : ℝ)*base74 + (459443913157239/706475000000000000000000000 : ℝ)*base77 + (8912846278198861/852992263200000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (99611/100000000000000000 : ℝ)*base87 + (99611/100000000000000000 : ℝ)*base89 + (99611/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35829/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35829/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7792363907035556810020597813967/1318175148070550000000000000000000000 : ℝ) := by norm_num
    linear_combination (3226249/1000000000000 : ℝ)*(base39) + (213964413589/125000000000 : ℝ)*(base40) + (1531994737549/250000000000 : ℝ)*(major_s2_0) + (1531994737549/250000000000 : ℝ)*(major_s2_1) + (1531994737549/250000000000 : ℝ)*(major_s2_2) + (14119957/250000000000 : ℝ)*(sp_s2_0) + (30635723/1000000000000 : ℝ)*(sp_s2_1) + (32846019/1000000000000 : ℝ)*(sp_s2_6) + (9968417/250000000000 : ℝ)*(sp_s2_7) + (1619923/8000000000 : ℝ)*(sp_s2_15) + (2117079220709/250000000000 : ℝ)*(sp_s2_21) + (4234090055117/500000000000 : ℝ)*(sp_s2_22) + (2117103309083/250000000000 : ℝ)*(sp_s2_23) + (473438730943/125000000000 : ℝ)*(sp_s2_27) + (3787542693563/1000000000000 : ℝ)*(f.failure) + (2117103309083/250000000000 : ℝ)*(f.sum) + (3468824900108630389/139938619350000000000000000000000 : ℝ)*base62 + (2173207957997409/3708850000000000000000000000 : ℝ)*base65 + (513029885578613/943275000000000000000000000 : ℝ)*base66 + (507982517510299/927212500000000000000000000 : ℝ)*base68 + (42375446325220611831/104808392150000000000000000000000 : ℝ)*base70 + (402550269434199/1412950000000000000000000000 : ℝ)*base73 + (976902607080629/1886550000000000000000000000 : ℝ)*base74 + (164593835831819/1412950000000000000000000000 : ℝ)*base77 + (8439010459754268017/10662403290000000000000000000000 : ℝ)*base79 + (38459/100000000000000000 : ℝ)*base87 + (38459/100000000000000000 : ℝ)*base89 + (38459/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((28259/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28259/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-37731/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-37731/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74177/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74177/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2407/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2407/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-43543/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-43543/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35829/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35829/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310086_s2 p hpa hpb X hX hprev1

#print axioms solution
