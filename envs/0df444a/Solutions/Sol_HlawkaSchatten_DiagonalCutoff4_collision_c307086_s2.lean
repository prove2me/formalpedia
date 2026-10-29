-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307086_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:17:51.743302+00:00
-- url     : https://prove2.me/submissions/a360e6d2-1596-4a29-87af-0f0e36fb1244

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
theorem collision_support_c307086_s2_s2_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-77691033/5000000000 : ℝ)*x 0 + (-49895059/78125000 : ℝ)*x 1 + (5331417777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77691033/5000000000 : ℝ)^17 ≤ (215714263541/50000000000000 : ℝ)^13 := by
    have hnat : (77691033 : ℕ)^17*50000000000000^13 ≤ 215714263541^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77691033 5000000000 215714263541 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49895059/78125000 : ℝ)^17 ≤ (11127044288011/20000000000000 : ℝ)^13 := by
    have hnat : (49895059 : ℕ)^17*20000000000000^13 ≤ 11127044288011^13*78125000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49895059 78125000 11127044288011 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5331417777/10000000000 : ℝ)^17 ≤ (21966675015487/50000000000000 : ℝ)^13 := by
    have hnat : (5331417777 : ℕ)^17*50000000000000^13 ≤ 21966675015487^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5331417777 10000000000 21966675015487 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77691033/5000000000 : ℝ), (-49895059/78125000 : ℝ), (5331417777/10000000000 : ℝ)] ![(215714263541/50000000000000 : ℝ), (11127044288011/20000000000000 : ℝ), (21966675015487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77691033/5000000000 : ℝ)|^17 ≤ (215714263541/50000000000000 : ℝ)^13
        have hw : |(-77691033/5000000000 : ℝ)|=(77691033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49895059/78125000 : ℝ)|^17 ≤ (11127044288011/20000000000000 : ℝ)^13
        have hw : |(-49895059/78125000 : ℝ)|=(49895059/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5331417777/10000000000 : ℝ)|^17 ≤ (21966675015487/50000000000000 : ℝ)^13
        have hw : |(5331417777/10000000000 : ℝ)|=(5331417777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6064834691/10000000000 : ℝ)*x 0 + (-3464064227/10000000000 : ℝ)*x 1 + (-650088049/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6064834691/10000000000 : ℝ)^17 ≤ (51998885427919/100000000000000 : ℝ)^13 := by
    have hnat : (6064834691 : ℕ)^17*100000000000000^13 ≤ 51998885427919^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6064834691 10000000000 51998885427919 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3464064227/10000000000 : ℝ)^17 ≤ (24998852246407/100000000000000 : ℝ)^13 := by
    have hnat : (3464064227 : ℕ)^17*100000000000000^13 ≤ 24998852246407^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3464064227 10000000000 24998852246407 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (650088049/2000000000 : ℝ)^17 ≤ (4600452461167/20000000000000 : ℝ)^13 := by
    have hnat : (650088049 : ℕ)^17*20000000000000^13 ≤ 4600452461167^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650088049 2000000000 4600452461167 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6064834691/10000000000 : ℝ), (-3464064227/10000000000 : ℝ), (-650088049/2000000000 : ℝ)] ![(51998885427919/100000000000000 : ℝ), (24998852246407/100000000000000 : ℝ), (4600452461167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6064834691/10000000000 : ℝ)|^17 ≤ (51998885427919/100000000000000 : ℝ)^13
        have hw : |(6064834691/10000000000 : ℝ)|=(6064834691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3464064227/10000000000 : ℝ)|^17 ≤ (24998852246407/100000000000000 : ℝ)^13
        have hw : |(-3464064227/10000000000 : ℝ)|=(3464064227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-650088049/2000000000 : ℝ)|^17 ≤ (4600452461167/20000000000000 : ℝ)^13
        have hw : |(-650088049/2000000000 : ℝ)|=(650088049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3929137957/10000000000 : ℝ)*x 0 + (-1445099101/5000000000 : ℝ)*x 1 + (2978684221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3929137957/10000000000 : ℝ)^17 ≤ (5895160947127/20000000000000 : ℝ)^13 := by
    have hnat : (3929137957 : ℕ)^17*20000000000000^13 ≤ 5895160947127^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3929137957 10000000000 5895160947127 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1445099101/5000000000 : ℝ)^17 ≤ (19726916391533/100000000000000 : ℝ)^13 := by
    have hnat : (1445099101 : ℕ)^17*100000000000000^13 ≤ 19726916391533^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445099101 5000000000 19726916391533 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2978684221/5000000000 : ℝ)^17 ≤ (50797278858531/100000000000000 : ℝ)^13 := by
    have hnat : (2978684221 : ℕ)^17*100000000000000^13 ≤ 50797278858531^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2978684221 5000000000 50797278858531 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3929137957/10000000000 : ℝ), (-1445099101/5000000000 : ℝ), (2978684221/5000000000 : ℝ)] ![(5895160947127/20000000000000 : ℝ), (19726916391533/100000000000000 : ℝ), (50797278858531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3929137957/10000000000 : ℝ)|^17 ≤ (5895160947127/20000000000000 : ℝ)^13
        have hw : |(3929137957/10000000000 : ℝ)|=(3929137957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1445099101/5000000000 : ℝ)|^17 ≤ (19726916391533/100000000000000 : ℝ)^13
        have hw : |(-1445099101/5000000000 : ℝ)|=(1445099101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2978684221/5000000000 : ℝ)|^17 ≤ (50797278858531/100000000000000 : ℝ)^13
        have hw : |(2978684221/5000000000 : ℝ)|=(2978684221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (502041/5000000000 : ℝ)*x 0 + (-982312561/1250000000 : ℝ)*x 1 + (3677377751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502041/5000000000 : ℝ)^17 ≤ (590941261/100000000000000 : ℝ)^13 := by
    have hnat : (502041 : ℕ)^17*100000000000000^13 ≤ 590941261^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502041 5000000000 590941261 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982312561/1250000000 : ℝ)^17 ≤ (72968683445561/100000000000000 : ℝ)^13 := by
    have hnat : (982312561 : ℕ)^17*100000000000000^13 ≤ 72968683445561^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982312561 1250000000 72968683445561 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3677377751/10000000000 : ℝ)^17 ≤ (13515362801583/50000000000000 : ℝ)^13 := by
    have hnat : (3677377751 : ℕ)^17*50000000000000^13 ≤ 13515362801583^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3677377751 10000000000 13515362801583 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(502041/5000000000 : ℝ), (-982312561/1250000000 : ℝ), (3677377751/10000000000 : ℝ)] ![(590941261/100000000000000 : ℝ), (72968683445561/100000000000000 : ℝ), (13515362801583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(502041/5000000000 : ℝ)|^17 ≤ (590941261/100000000000000 : ℝ)^13
        have hw : |(502041/5000000000 : ℝ)|=(502041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-982312561/1250000000 : ℝ)|^17 ≤ (72968683445561/100000000000000 : ℝ)^13
        have hw : |(-982312561/1250000000 : ℝ)|=(982312561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3677377751/10000000000 : ℝ)|^17 ≤ (13515362801583/50000000000000 : ℝ)^13
        have hw : |(3677377751/10000000000 : ℝ)|=(3677377751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (577952969/1000000000 : ℝ)*x 0 + (762771657/2000000000 : ℝ)*x 1 + (3231429211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (577952969/1000000000 : ℝ)^17 ≤ (48823471139211/100000000000000 : ℝ)^13 := by
    have hnat : (577952969 : ℕ)^17*100000000000000^13 ≤ 48823471139211^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577952969 1000000000 48823471139211 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (762771657/2000000000 : ℝ)^17 ≤ (28350037932317/100000000000000 : ℝ)^13 := by
    have hnat : (762771657 : ℕ)^17*100000000000000^13 ≤ 28350037932317^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762771657 2000000000 28350037932317 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3231429211/10000000000 : ℝ)^17 ≤ (22826490916459/100000000000000 : ℝ)^13 := by
    have hnat : (3231429211 : ℕ)^17*100000000000000^13 ≤ 22826490916459^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3231429211 10000000000 22826490916459 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(577952969/1000000000 : ℝ), (762771657/2000000000 : ℝ), (3231429211/10000000000 : ℝ)] ![(48823471139211/100000000000000 : ℝ), (28350037932317/100000000000000 : ℝ), (22826490916459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(577952969/1000000000 : ℝ)|^17 ≤ (48823471139211/100000000000000 : ℝ)^13
        have hw : |(577952969/1000000000 : ℝ)|=(577952969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(762771657/2000000000 : ℝ)|^17 ≤ (28350037932317/100000000000000 : ℝ)^13
        have hw : |(762771657/2000000000 : ℝ)|=(762771657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3231429211/10000000000 : ℝ)|^17 ≤ (22826490916459/100000000000000 : ℝ)^13
        have hw : |(3231429211/10000000000 : ℝ)|=(3231429211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2791041383/5000000000 : ℝ)*x 0 + (-1736178881/5000000000 : ℝ)*x 1 + (-9513799/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2791041383/5000000000 : ℝ)^17 ≤ (2915865244241/6250000000000 : ℝ)^13 := by
    have hnat : (2791041383 : ℕ)^17*6250000000000^13 ≤ 2915865244241^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791041383 5000000000 2915865244241 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1736178881/5000000000 : ℝ)^17 ≤ (25077148184531/100000000000000 : ℝ)^13 := by
    have hnat : (1736178881 : ℕ)^17*100000000000000^13 ≤ 25077148184531^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736178881 5000000000 25077148184531 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9513799/25000000 : ℝ)^17 ≤ (1413450394671/5000000000000 : ℝ)^13 := by
    have hnat : (9513799 : ℕ)^17*5000000000000^13 ≤ 1413450394671^13*25000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9513799 25000000 1413450394671 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2791041383/5000000000 : ℝ), (-1736178881/5000000000 : ℝ), (-9513799/25000000 : ℝ)] ![(2915865244241/6250000000000 : ℝ), (25077148184531/100000000000000 : ℝ), (1413450394671/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2791041383/5000000000 : ℝ)|^17 ≤ (2915865244241/6250000000000 : ℝ)^13
        have hw : |(2791041383/5000000000 : ℝ)|=(2791041383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1736178881/5000000000 : ℝ)|^17 ≤ (25077148184531/100000000000000 : ℝ)^13
        have hw : |(-1736178881/5000000000 : ℝ)|=(1736178881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9513799/25000000 : ℝ)|^17 ≤ (1413450394671/5000000000000 : ℝ)^13
        have hw : |(-9513799/25000000 : ℝ)|=(9513799/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (643464091/2500000000 : ℝ)*x 0 + (-674731581/5000000000 : ℝ)*x 1 + (4043736623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (643464091/2500000000 : ℝ)^17 ≤ (16952183016039/100000000000000 : ℝ)^13 := by
    have hnat : (643464091 : ℕ)^17*100000000000000^13 ≤ 16952183016039^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643464091 2500000000 16952183016039 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674731581/5000000000 : ℝ)^17 ≤ (3643244173331/50000000000000 : ℝ)^13 := by
    have hnat : (674731581 : ℕ)^17*50000000000000^13 ≤ 3643244173331^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674731581 5000000000 3643244173331 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4043736623/5000000000 : ℝ)^17 ≤ (75761328616781/100000000000000 : ℝ)^13 := by
    have hnat : (4043736623 : ℕ)^17*100000000000000^13 ≤ 75761328616781^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043736623 5000000000 75761328616781 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(643464091/2500000000 : ℝ), (-674731581/5000000000 : ℝ), (4043736623/5000000000 : ℝ)] ![(16952183016039/100000000000000 : ℝ), (3643244173331/50000000000000 : ℝ), (75761328616781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(643464091/2500000000 : ℝ)|^17 ≤ (16952183016039/100000000000000 : ℝ)^13
        have hw : |(643464091/2500000000 : ℝ)|=(643464091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-674731581/5000000000 : ℝ)|^17 ≤ (3643244173331/50000000000000 : ℝ)^13
        have hw : |(-674731581/5000000000 : ℝ)|=(674731581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4043736623/5000000000 : ℝ)|^17 ≤ (75761328616781/100000000000000 : ℝ)^13
        have hw : |(4043736623/5000000000 : ℝ)|=(4043736623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-17753/2500000000 : ℝ)*x 0 + (-2370639921/5000000000 : ℝ)*x 1 + (6965021077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17753/2500000000 : ℝ)^17 ≤ (9249029/50000000000000 : ℝ)^13 := by
    have hnat : (17753 : ℕ)^17*50000000000000^13 ≤ 9249029^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17753 2500000000 9249029 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2370639921/5000000000 : ℝ)^17 ≤ (2355326793199/6250000000000 : ℝ)^13 := by
    have hnat : (2370639921 : ℕ)^17*6250000000000^13 ≤ 2355326793199^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370639921 5000000000 2355326793199 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6965021077/10000000000 : ℝ)^17 ≤ (31157376399429/50000000000000 : ℝ)^13 := by
    have hnat : (6965021077 : ℕ)^17*50000000000000^13 ≤ 31157376399429^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6965021077 10000000000 31157376399429 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17753/2500000000 : ℝ), (-2370639921/5000000000 : ℝ), (6965021077/10000000000 : ℝ)] ![(9249029/50000000000000 : ℝ), (2355326793199/6250000000000 : ℝ), (31157376399429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17753/2500000000 : ℝ)|^17 ≤ (9249029/50000000000000 : ℝ)^13
        have hw : |(-17753/2500000000 : ℝ)|=(17753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2370639921/5000000000 : ℝ)|^17 ≤ (2355326793199/6250000000000 : ℝ)^13
        have hw : |(-2370639921/5000000000 : ℝ)|=(2370639921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6965021077/10000000000 : ℝ)|^17 ≤ (31157376399429/50000000000000 : ℝ)^13
        have hw : |(6965021077/10000000000 : ℝ)|=(6965021077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8001652917/10000000000 : ℝ)*x 0 + (18098947/78125000 : ℝ)*x 1 + (71461889/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8001652917/10000000000 : ℝ)^17 ≤ (74711739932697/100000000000000 : ℝ)^13 := by
    have hnat : (8001652917 : ℕ)^17*100000000000000^13 ≤ 74711739932697^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8001652917 10000000000 74711739932697 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18098947/78125000 : ℝ)^17 ≤ (3692977000163/25000000000000 : ℝ)^13 := by
    have hnat : (18098947 : ℕ)^17*25000000000000^13 ≤ 3692977000163^13*78125000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18098947 78125000 3692977000163 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71461889/400000000 : ℝ)^17 ≤ (10516352049363/100000000000000 : ℝ)^13 := by
    have hnat : (71461889 : ℕ)^17*100000000000000^13 ≤ 10516352049363^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71461889 400000000 10516352049363 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8001652917/10000000000 : ℝ), (18098947/78125000 : ℝ), (71461889/400000000 : ℝ)] ![(74711739932697/100000000000000 : ℝ), (3692977000163/25000000000000 : ℝ), (10516352049363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8001652917/10000000000 : ℝ)|^17 ≤ (74711739932697/100000000000000 : ℝ)^13
        have hw : |(8001652917/10000000000 : ℝ)|=(8001652917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(18098947/78125000 : ℝ)|^17 ≤ (3692977000163/25000000000000 : ℝ)^13
        have hw : |(18098947/78125000 : ℝ)|=(18098947/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(71461889/400000000 : ℝ)|^17 ≤ (10516352049363/100000000000000 : ℝ)^13
        have hw : |(71461889/400000000 : ℝ)|=(71461889/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1877350467/2500000000 : ℝ)*x 0 + (-2946331459/10000000000 : ℝ)*x 1 + (-462630263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1877350467/2500000000 : ℝ)^17 ≤ (17189770440907/25000000000000 : ℝ)^13 := by
    have hnat : (1877350467 : ℕ)^17*25000000000000^13 ≤ 17189770440907^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877350467 2500000000 17189770440907 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2946331459/10000000000 : ℝ)^17 ≤ (1264339341909/6250000000000 : ℝ)^13 := by
    have hnat : (2946331459 : ℕ)^17*6250000000000^13 ≤ 1264339341909^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2946331459 10000000000 1264339341909 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (462630263/2500000000 : ℝ)^17 ≤ (2202297749701/20000000000000 : ℝ)^13 := by
    have hnat : (462630263 : ℕ)^17*20000000000000^13 ≤ 2202297749701^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462630263 2500000000 2202297749701 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1877350467/2500000000 : ℝ), (-2946331459/10000000000 : ℝ), (-462630263/2500000000 : ℝ)] ![(17189770440907/25000000000000 : ℝ), (1264339341909/6250000000000 : ℝ), (2202297749701/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1877350467/2500000000 : ℝ)|^17 ≤ (17189770440907/25000000000000 : ℝ)^13
        have hw : |(1877350467/2500000000 : ℝ)|=(1877350467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2946331459/10000000000 : ℝ)|^17 ≤ (1264339341909/6250000000000 : ℝ)^13
        have hw : |(-2946331459/10000000000 : ℝ)|=(2946331459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-462630263/2500000000 : ℝ)|^17 ≤ (2202297749701/20000000000000 : ℝ)^13
        have hw : |(-462630263/2500000000 : ℝ)|=(462630263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (60261561/250000000 : ℝ)*x 0 + (-177906253/1000000000 : ℝ)*x 1 + (49636557/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60261561/250000000 : ℝ)^17 ≤ (15558846822561/100000000000000 : ℝ)^13 := by
    have hnat : (60261561 : ℕ)^17*100000000000000^13 ≤ 15558846822561^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60261561 250000000 15558846822561 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177906253/1000000000 : ℝ)^17 ≤ (5229387459697/50000000000000 : ℝ)^13 := by
    have hnat : (177906253 : ℕ)^17*50000000000000^13 ≤ 5229387459697^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177906253 1000000000 5229387459697 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49636557/62500000 : ℝ)^17 ≤ (36991189120157/50000000000000 : ℝ)^13 := by
    have hnat : (49636557 : ℕ)^17*50000000000000^13 ≤ 36991189120157^13*62500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49636557 62500000 36991189120157 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(60261561/250000000 : ℝ), (-177906253/1000000000 : ℝ), (49636557/62500000 : ℝ)] ![(15558846822561/100000000000000 : ℝ), (5229387459697/50000000000000 : ℝ), (36991189120157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(60261561/250000000 : ℝ)|^17 ≤ (15558846822561/100000000000000 : ℝ)^13
        have hw : |(60261561/250000000 : ℝ)|=(60261561/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177906253/1000000000 : ℝ)|^17 ≤ (5229387459697/50000000000000 : ℝ)^13
        have hw : |(-177906253/1000000000 : ℝ)|=(177906253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(49636557/62500000 : ℝ)|^17 ≤ (36991189120157/50000000000000 : ℝ)^13
        have hw : |(49636557/62500000 : ℝ)|=(49636557/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (12199873/2500000000 : ℝ)*x 0 + (-967037369/1250000000 : ℝ)*x 1 + (95517829/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12199873/2500000000 : ℝ)^17 ≤ (592977873/625000000000 : ℝ)^13 := by
    have hnat : (12199873 : ℕ)^17*625000000000^13 ≤ 592977873^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12199873 2500000000 592977873 625000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (967037369/1250000000 : ℝ)^17 ≤ (71488433440991/100000000000000 : ℝ)^13 := by
    have hnat : (967037369 : ℕ)^17*100000000000000^13 ≤ 71488433440991^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967037369 1250000000 71488433440991 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95517829/250000000 : ℝ)^17 ≤ (7104172522957/25000000000000 : ℝ)^13 := by
    have hnat : (95517829 : ℕ)^17*25000000000000^13 ≤ 7104172522957^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95517829 250000000 7104172522957 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(12199873/2500000000 : ℝ), (-967037369/1250000000 : ℝ), (95517829/250000000 : ℝ)] ![(592977873/625000000000 : ℝ), (71488433440991/100000000000000 : ℝ), (7104172522957/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(12199873/2500000000 : ℝ)|^17 ≤ (592977873/625000000000 : ℝ)^13
        have hw : |(12199873/2500000000 : ℝ)|=(12199873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-967037369/1250000000 : ℝ)|^17 ≤ (71488433440991/100000000000000 : ℝ)^13
        have hw : |(-967037369/1250000000 : ℝ)|=(967037369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95517829/250000000 : ℝ)|^17 ≤ (7104172522957/25000000000000 : ℝ)^13
        have hw : |(95517829/250000000 : ℝ)|=(95517829/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7638326123/10000000000 : ℝ)*x 0 + (2572092811/10000000000 : ℝ)*x 1 + (2070802321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7638326123/10000000000 : ℝ)^17 ≤ (70306850273087/100000000000000 : ℝ)^13 := by
    have hnat : (7638326123 : ℕ)^17*100000000000000^13 ≤ 70306850273087^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7638326123 10000000000 70306850273087 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2572092811/10000000000 : ℝ)^17 ≤ (2117124424949/12500000000000 : ℝ)^13 := by
    have hnat : (2572092811 : ℕ)^17*12500000000000^13 ≤ 2117124424949^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2572092811 10000000000 2117124424949 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070802321/10000000000 : ℝ)^17 ≤ (12756154304161/100000000000000 : ℝ)^13 := by
    have hnat : (2070802321 : ℕ)^17*100000000000000^13 ≤ 12756154304161^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070802321 10000000000 12756154304161 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7638326123/10000000000 : ℝ), (2572092811/10000000000 : ℝ), (2070802321/10000000000 : ℝ)] ![(70306850273087/100000000000000 : ℝ), (2117124424949/12500000000000 : ℝ), (12756154304161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7638326123/10000000000 : ℝ)|^17 ≤ (70306850273087/100000000000000 : ℝ)^13
        have hw : |(7638326123/10000000000 : ℝ)|=(7638326123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2572092811/10000000000 : ℝ)|^17 ≤ (2117124424949/12500000000000 : ℝ)^13
        have hw : |(2572092811/10000000000 : ℝ)|=(2572092811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2070802321/10000000000 : ℝ)|^17 ≤ (12756154304161/100000000000000 : ℝ)^13
        have hw : |(2070802321/10000000000 : ℝ)|=(2070802321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2287175923/5000000000 : ℝ)*x 0 + (-201456191/400000000 : ℝ)*x 1 + (-3278107127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2287175923/5000000000 : ℝ)^17 ≤ (35959660812371/100000000000000 : ℝ)^13 := by
    have hnat : (2287175923 : ℕ)^17*100000000000000^13 ≤ 35959660812371^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287175923 5000000000 35959660812371 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201456191/400000000 : ℝ)^17 ≤ (5097713788603/12500000000000 : ℝ)^13 := by
    have hnat : (201456191 : ℕ)^17*12500000000000^13 ≤ 5097713788603^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201456191 400000000 5097713788603 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3278107127/10000000000 : ℝ)^17 ≤ (2907328608223/12500000000000 : ℝ)^13 := by
    have hnat : (3278107127 : ℕ)^17*12500000000000^13 ≤ 2907328608223^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3278107127 10000000000 2907328608223 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2287175923/5000000000 : ℝ), (-201456191/400000000 : ℝ), (-3278107127/10000000000 : ℝ)] ![(35959660812371/100000000000000 : ℝ), (5097713788603/12500000000000 : ℝ), (2907328608223/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2287175923/5000000000 : ℝ)|^17 ≤ (35959660812371/100000000000000 : ℝ)^13
        have hw : |(2287175923/5000000000 : ℝ)|=(2287175923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201456191/400000000 : ℝ)|^17 ≤ (5097713788603/12500000000000 : ℝ)^13
        have hw : |(-201456191/400000000 : ℝ)|=(201456191/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3278107127/10000000000 : ℝ)|^17 ≤ (2907328608223/12500000000000 : ℝ)^13
        have hw : |(-3278107127/10000000000 : ℝ)|=(3278107127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307086_s2_s2_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (754540803/1250000000 : ℝ)*x 0 + (-920724663/5000000000 : ℝ)*x 1 + (942368769/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (754540803/1250000000 : ℝ)^17 ≤ (1614983873213/3125000000000 : ℝ)^13 := by
    have hnat : (754540803 : ℕ)^17*3125000000000^13 ≤ 1614983873213^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754540803 1250000000 1614983873213 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (920724663/5000000000 : ℝ)^17 ≤ (5470475672781/50000000000000 : ℝ)^13 := by
    have hnat : (920724663 : ℕ)^17*50000000000000^13 ≤ 5470475672781^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920724663 5000000000 5470475672781 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (942368769/2000000000 : ℝ)^17 ≤ (37379564702791/100000000000000 : ℝ)^13 := by
    have hnat : (942368769 : ℕ)^17*100000000000000^13 ≤ 37379564702791^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942368769 2000000000 37379564702791 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(754540803/1250000000 : ℝ), (-920724663/5000000000 : ℝ), (942368769/2000000000 : ℝ)] ![(1614983873213/3125000000000 : ℝ), (5470475672781/50000000000000 : ℝ), (37379564702791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(754540803/1250000000 : ℝ)|^17 ≤ (1614983873213/3125000000000 : ℝ)^13
        have hw : |(754540803/1250000000 : ℝ)|=(754540803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-920724663/5000000000 : ℝ)|^17 ≤ (5470475672781/50000000000000 : ℝ)^13
        have hw : |(-920724663/5000000000 : ℝ)|=(920724663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(942368769/2000000000 : ℝ)|^17 ≤ (37379564702791/100000000000000 : ℝ)^13
        have hw : |(942368769/2000000000 : ℝ)|=(942368769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307086_s2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((72857/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72857/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-42861/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-42861/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8459/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8459/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1536/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1536/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-73807/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-73807/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1749/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1749/2500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  have s2_pow0 : (72857/100000 : ℝ) ^ (135/32 : ℝ) ≤ (26290614163641072753/100000000000000000000 : ℝ) := by
    have hpowers : (72857/100000 : ℝ)^135 ≤ (26290614163641072753/100000000000000000000 : ℝ)^32 := by
      have hnat : (72857 : ℕ)^135*100000000000000000000^32 ≤ 26290614163641072753^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72857 100000 26290614163641072753 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72857/100000 : ℝ)) (X := (26290614163641072753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (126290614163641072753/100000000000000000000 : ℝ) ≤ (422754939522561/400000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (126290614163641072753/100000000000000000000 : ℝ)^32 ≤ (422754939522561/400000000000000 : ℝ)^135 := by
      have hnat : (126290614163641072753 : ℕ)^32*400000000000000^135 ≤ 422754939522561^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        126290614163641072753 100000000000000000000 422754939522561 400000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (422754939522561/400000000000000 : ℝ)) (X := (126290614163641072753/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (76290614163641072753/50000000000000000000 : ℝ) ≤ (11053417106052507/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (76290614163641072753/50000000000000000000 : ℝ)^32 ≤ (11053417106052507/10000000000000000 : ℝ)^135 := by
      have hnat : (76290614163641072753 : ℕ)^32*10000000000000000^135 ≤ 11053417106052507^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76290614163641072753 50000000000000000000 11053417106052507 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11053417106052507/10000000000000000 : ℝ)) (X := (76290614163641072753/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(22754939522561/291428000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(242271808994241/3642850000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (72857/100000 : ℝ)) (alpha := (22754939522561/291428000000000 : ℝ)) (beta := (242271808994241/3642850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (72857/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(22754939522561/291428000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(242271808994241/3642850000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (42861/50000 : ℝ) ^ (135/32 : ℝ) ≤ (815742606100771377/1562500000000000000 : ℝ) := by
    have hpowers : (42861/50000 : ℝ)^135 ≤ (815742606100771377/1562500000000000000 : ℝ)^32 := by
      have hnat : (42861 : ℕ)^135*1562500000000000000^32 ≤ 815742606100771377^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42861 50000 815742606100771377 1562500000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42861/50000 : ℝ)) (X := (815742606100771377/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (2378242606100771377/1562500000000000000 : ℝ) ≤ (11046994035209303/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2378242606100771377/1562500000000000000 : ℝ)^32 ≤ (11046994035209303/10000000000000000 : ℝ)^135 := by
      have hnat : (2378242606100771377 : ℕ)^32*10000000000000000^135 ≤ 11046994035209303^135*1562500000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2378242606100771377 1562500000000000000 11046994035209303 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11046994035209303/10000000000000000 : ℝ)) (X := (2378242606100771377/1562500000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (1596992606100771377/781250000000000000 : ℝ) ≤ (11846854425487873/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (1596992606100771377/781250000000000000 : ℝ)^32 ≤ (11846854425487873/10000000000000000 : ℝ)^135 := by
      have hnat : (1596992606100771377 : ℕ)^32*10000000000000000^135 ≤ 11846854425487873^135*781250000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1596992606100771377 781250000000000000 11846854425487873 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11846854425487873/10000000000000000 : ℝ)) (X := (1596992606100771377/781250000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1046994035209303/8572200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(79986039027857/857220000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (42861/50000 : ℝ)) (alpha := (1046994035209303/8572200000000000 : ℝ)) (beta := (79986039027857/857220000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (42861/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1046994035209303/8572200000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(79986039027857/857220000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (8459/10000 : ℝ) ^ (135/32 : ℝ) ≤ (49360225666365461219/100000000000000000000 : ℝ) := by
    have hpowers : (8459/10000 : ℝ)^135 ≤ (49360225666365461219/100000000000000000000 : ℝ)^32 := by
      have hnat : (8459 : ℕ)^135*100000000000000000000^32 ≤ 49360225666365461219^32*10000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8459 10000 49360225666365461219 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8459/10000 : ℝ)) (X := (49360225666365461219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (149360225666365461219/100000000000000000000 : ℝ) ≤ (10997656198516753/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (149360225666365461219/100000000000000000000 : ℝ)^32 ≤ (10997656198516753/10000000000000000 : ℝ)^135 := by
      have hnat : (149360225666365461219 : ℕ)^32*10000000000000000^135 ≤ 10997656198516753^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        149360225666365461219 100000000000000000000 10997656198516753 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10997656198516753/10000000000000000 : ℝ)) (X := (149360225666365461219/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (99360225666365461219/50000000000000000000 : ℝ) ≤ (2941944954503639/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (99360225666365461219/50000000000000000000 : ℝ)^32 ≤ (2941944954503639/2500000000000000 : ℝ)^135 := by
      have hnat : (99360225666365461219 : ℕ)^32*2500000000000000^135 ≤ 2941944954503639^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        99360225666365461219 50000000000000000000 2941944954503639 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2941944954503639/2500000000000000 : ℝ)) (X := (99360225666365461219/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(997656198516753/8459000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(770123619497803/8459000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (8459/10000 : ℝ)) (alpha := (997656198516753/8459000000000000 : ℝ)) (beta := (770123619497803/8459000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8459/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(997656198516753/8459000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(770123619497803/8459000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-77691033/5000000000 : ℝ)*X 0 0+(-49895059/78125000 : ℝ)*X 0 1+(5331417777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((6064834691/10000000000 : ℝ)*X 2 0+(-3464064227/10000000000 : ℝ)*X 2 1+(-650088049/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3929137957/10000000000 : ℝ)*X 0 0+(-1445099101/5000000000 : ℝ)*X 0 1+(2978684221/5000000000 : ℝ)*X 0 2+(3929137957/10000000000 : ℝ)*X 1 0+(-1445099101/5000000000 : ℝ)*X 1 1+(2978684221/5000000000 : ℝ)*X 1 2+(3929137957/10000000000 : ℝ)*X 2 0+(-1445099101/5000000000 : ℝ)*X 2 1+(2978684221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((502041/5000000000 : ℝ)*X 0 0+(-982312561/1250000000 : ℝ)*X 0 1+(3677377751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((577952969/1000000000 : ℝ)*X 1 0+(762771657/2000000000 : ℝ)*X 1 1+(3231429211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2791041383/5000000000 : ℝ)*X 2 0+(-1736178881/5000000000 : ℝ)*X 2 1+(-9513799/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((643464091/2500000000 : ℝ)*X 0 0+(-674731581/5000000000 : ℝ)*X 0 1+(4043736623/5000000000 : ℝ)*X 0 2+(643464091/2500000000 : ℝ)*X 1 0+(-674731581/5000000000 : ℝ)*X 1 1+(4043736623/5000000000 : ℝ)*X 1 2+(643464091/2500000000 : ℝ)*X 2 0+(-674731581/5000000000 : ℝ)*X 2 1+(4043736623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-17753/2500000000 : ℝ)*X 0 0+(-2370639921/5000000000 : ℝ)*X 0 1+(6965021077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((8001652917/10000000000 : ℝ)*X 1 0+(18098947/78125000 : ℝ)*X 1 1+(71461889/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1877350467/2500000000 : ℝ)*X 2 0+(-2946331459/10000000000 : ℝ)*X 2 1+(-462630263/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((60261561/250000000 : ℝ)*X 0 0+(-177906253/1000000000 : ℝ)*X 0 1+(49636557/62500000 : ℝ)*X 0 2+(60261561/250000000 : ℝ)*X 1 0+(-177906253/1000000000 : ℝ)*X 1 1+(49636557/62500000 : ℝ)*X 1 2+(60261561/250000000 : ℝ)*X 2 0+(-177906253/1000000000 : ℝ)*X 2 1+(49636557/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((12199873/2500000000 : ℝ)*X 0 0+(-967037369/1250000000 : ℝ)*X 0 1+(95517829/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((7638326123/10000000000 : ℝ)*X 1 0+(2572092811/10000000000 : ℝ)*X 1 1+(2070802321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2287175923/5000000000 : ℝ)*X 2 0+(-201456191/400000000 : ℝ)*X 2 1+(-3278107127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((754540803/1250000000 : ℝ)*X 0 0+(-920724663/5000000000 : ℝ)*X 0 1+(942368769/2000000000 : ℝ)*X 0 2+(754540803/1250000000 : ℝ)*X 1 0+(-920724663/5000000000 : ℝ)*X 1 1+(942368769/2000000000 : ℝ)*X 1 2+(754540803/1250000000 : ℝ)*X 2 0+(-920724663/5000000000 : ℝ)*X 2 1+(942368769/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307086_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((1536/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1536/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (113024697942631207177801859/60426866500000000000000000000000 : ℝ) := by norm_num
    linear_combination (93617063973/200000000000 : ℝ)*(base7) + (1878693/1000000000000 : ℝ)*(base40) + (2645161833073/1000000000000 : ℝ)*(major_s2_0) + (2645161833073/1000000000000 : ℝ)*(major_s2_1) + (2645161833073/1000000000000 : ℝ)*(major_s2_2) + (4193223/1000000000000 : ℝ)*(sp_s2_2) + (1451087/500000000000 : ℝ)*(sp_s2_6) + (659945007499/200000000000 : ℝ)*(sp_s2_7) + (3299848575829/1000000000000 : ℝ)*(sp_s2_8) + (3299842756867/1000000000000 : ℝ)*(sp_s2_9) + (271211484623/125000000000 : ℝ)*(sp_s2_13) + (14140031/500000000000 : ℝ)*(sp_s2_20) + (61769167/500000000000 : ℝ)*(sp_s2_21) + (1625739/1000000000000 : ℝ)*(sp_s2_23) + (425409434839/250000000000 : ℝ)*(f.failure) + (3299848575829/1000000000000 : ℝ)*(f.sum) + (34937211387247212541/362561199000000000000000000000000 : ℝ)*base62 + (5733189460890981/8459000000000000000000000000 : ℝ)*base65 + (4251918194622221/8572200000000000000000000000 : ℝ)*base66 + (5517627192593631/8459000000000000000000000000 : ℝ)*base68 + (253024062843551876433/616297363000000000000000000000000 : ℝ)*base70 + (227409915355371/1821425000000000000000000000 : ℝ)*base72 + (114724306428593/171444000000000000000000000 : ℝ)*base74 + (212824735196789/1457140000000000000000000000 : ℝ)*base77 + (54158535803587406263/124908955080000000000000000000000 : ℝ)*base79 + (871/781250000000000 : ℝ)*base87 + (871/781250000000000 : ℝ)*base89 + (871/781250000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-73807/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-73807/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9892890870522191437655792376297/880504042518100000000000000000000000 : ℝ) := by norm_num
    linear_combination (194490655317/250000000000 : ℝ)*(base7) + (479047/250000000000 : ℝ)*(base33) + (70227230087/500000000000 : ℝ)*(base40) + (16720099033/250000000000 : ℝ)*(base60) + (17177087291/8000000000 : ℝ)*(major_s2_0) + (2147137827563/1000000000000 : ℝ)*(major_s2_1) + (2147137827563/1000000000000 : ℝ)*(major_s2_2) + (14941609/1000000000000 : ℝ)*(sp_s2_6) + (25495681/1000000000000 : ℝ)*(sp_s2_9) + (5820167/25000000000 : ℝ)*(sp_s2_13) + (486592872907/200000000000 : ℝ)*(sp_s2_14) + (2432962448347/1000000000000 : ℝ)*(sp_s2_15) + (1216468476333/500000000000 : ℝ)*(sp_s2_16) + (539743200831/250000000000 : ℝ)*(sp_s2_20) + (276251586069/200000000000 : ℝ)*(f.failure) + (486592872907/200000000000 : ℝ)*(f.sum) + (163148215271002415771/362561199000000000000000000000000 : ℝ)*base62 + (4024765644252889/8459000000000000000000000000 : ℝ)*base64 + (2128047030779671/8572200000000000000000000000 : ℝ)*base66 + (4375389295859861/8459000000000000000000000000 : ℝ)*base68 + (130987883479557471223/616297363000000000000000000000000 : ℝ)*base70 + (49892661723833/364285000000000000000000000 : ℝ)*base72 + (153535012341203/857220000000000000000000000 : ℝ)*base74 + (220163091290129/1457140000000000000000000000 : ℝ)*base76 + (290031001434272644967/624544775400000000000000000000000 : ℝ)*base78 + (761/2500000000000000 : ℝ)*base86 + (761/2500000000000000 : ℝ)*base88 + (761/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1749/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1749/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (228513823811188473040316050699/22012601062952500000000000000000000 : ℝ) := by norm_num
    linear_combination (76914214761/100000000000 : ℝ)*(base7) + (449379479637/1000000000000 : ℝ)*(base40) + (10823389/1000000000000 : ℝ)*(base43) + (549227/200000000000 : ℝ)*(base50) + (36612900359/12500000000 : ℝ)*(major_s2_0) + (292902120533/100000000000 : ℝ)*(major_s2_1) + (36612900359/12500000000 : ℝ)*(major_s2_2) + (13985513/1000000000000 : ℝ)*(sp_s2_0) + (80829317/1000000000000 : ℝ)*(sp_s2_15) + (6690291/500000000000 : ℝ)*(sp_s2_16) + (3499176947599/1000000000000 : ℝ)*(sp_s2_21) + (218695057949/62500000000 : ℝ)*(sp_s2_22) + (349917755253/100000000000 : ℝ)*(sp_s2_23) + (265339413459/100000000000 : ℝ)*(sp_s2_27) + (1884251986979/1000000000000 : ℝ)*(f.failure) + (3499201756501/1000000000000 : ℝ)*(f.sum) + (1576001985719585213/18128059950000000000000000000000 : ℝ)*base63 + (16729506068017/26434375000000000000000000 : ℝ)*base65 + (430081978762003/857220000000000000000000000 : ℝ)*base66 + (41318130218413/422950000000000000000000000 : ℝ)*base69 + (4777683028066067/60185289355468750000000000000 : ℝ)*base71 + (44932437948581/728570000000000000000000000 : ℝ)*base73 + (8035535567429/428610000000000000000000000 : ℝ)*base75 + (93619127678299/182142500000000000000000000 : ℝ)*base77 + (29203099397412642773/62454477540000000000000000000000 : ℝ)*base78 + (11051/12500000000000000 : ℝ)*base86 + (1449/12500000000000000 : ℝ)*base89 + (11051/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((72857/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72857/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-42861/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-42861/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8459/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8459/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1536/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1536/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-73807/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-73807/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1749/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1749/2500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307086_s2 p hpa hpb X hX hprev1

#print axioms solution
