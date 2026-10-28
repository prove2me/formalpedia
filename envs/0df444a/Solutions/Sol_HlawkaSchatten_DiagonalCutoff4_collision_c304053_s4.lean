-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304053_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:45:10.76893+00:00
-- url     : https://prove2.me/submissions/f36d74c8-2126-4829-9ff0-5003b955ee5b

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
theorem collision_support_c304053_s4_s4_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1878904439/10000000000 : ℝ)*x 0 + (5325735089/10000000000 : ℝ)*x 1 + (5461407623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1878904439/10000000000 : ℝ)^67 ≤ (5560067839309/50000000000000 : ℝ)^51 := by
    have hnat : (1878904439 : ℕ)^67*50000000000000^51 ≤ 5560067839309^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878904439 10000000000 5560067839309 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5325735089/10000000000 : ℝ)^67 ≤ (43705677164381/100000000000000 : ℝ)^51 := by
    have hnat : (5325735089 : ℕ)^67*100000000000000^51 ≤ 43705677164381^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5325735089 10000000000 43705677164381 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461407623/10000000000 : ℝ)^67 ≤ (4517418713317/10000000000000 : ℝ)^51 := by
    have hnat : (5461407623 : ℕ)^67*10000000000000^51 ≤ 4517418713317^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461407623 10000000000 4517418713317 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1878904439/10000000000 : ℝ), (5325735089/10000000000 : ℝ), (5461407623/10000000000 : ℝ)] ![(5560067839309/50000000000000 : ℝ), (43705677164381/100000000000000 : ℝ), (4517418713317/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1878904439/10000000000 : ℝ)|^67 ≤ (5560067839309/50000000000000 : ℝ)^51
        have hw : |(-1878904439/10000000000 : ℝ)|=(1878904439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5325735089/10000000000 : ℝ)|^67 ≤ (43705677164381/100000000000000 : ℝ)^51
        have hw : |(5325735089/10000000000 : ℝ)|=(5325735089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461407623/10000000000 : ℝ)|^67 ≤ (4517418713317/10000000000000 : ℝ)^51
        have hw : |(5461407623/10000000000 : ℝ)|=(5461407623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4476487381/10000000000 : ℝ)*x 0 + (-587274677/5000000000 : ℝ)*x 1 + (419418027/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4476487381/10000000000 : ℝ)^67 ≤ (34787844342729/100000000000000 : ℝ)^51 := by
    have hnat : (4476487381 : ℕ)^67*100000000000000^51 ≤ 34787844342729^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476487381 10000000000 34787844342729 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (587274677/5000000000 : ℝ)^67 ≤ (5998824806161/100000000000000 : ℝ)^51 := by
    have hnat : (587274677 : ℕ)^67*100000000000000^51 ≤ 5998824806161^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587274677 5000000000 5998824806161 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419418027/625000000 : ℝ)^67 ≤ (59213330835631/100000000000000 : ℝ)^51 := by
    have hnat : (419418027 : ℕ)^67*100000000000000^51 ≤ 59213330835631^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419418027 625000000 59213330835631 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4476487381/10000000000 : ℝ), (-587274677/5000000000 : ℝ), (419418027/625000000 : ℝ)] ![(34787844342729/100000000000000 : ℝ), (5998824806161/100000000000000 : ℝ), (59213330835631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4476487381/10000000000 : ℝ)|^67 ≤ (34787844342729/100000000000000 : ℝ)^51
        have hw : |(4476487381/10000000000 : ℝ)|=(4476487381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-587274677/5000000000 : ℝ)|^67 ≤ (5998824806161/100000000000000 : ℝ)^51
        have hw : |(-587274677/5000000000 : ℝ)|=(587274677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(419418027/625000000 : ℝ)|^67 ≤ (59213330835631/100000000000000 : ℝ)^51
        have hw : |(419418027/625000000 : ℝ)|=(419418027/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-430073049/2500000000 : ℝ)*x 0 + (4002909793/10000000000 : ℝ)*x 1 + (6783708201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430073049/2500000000 : ℝ)^67 ≤ (4951777875141/50000000000000 : ℝ)^51 := by
    have hnat : (430073049 : ℕ)^67*50000000000000^51 ≤ 4951777875141^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430073049 2500000000 4951777875141 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4002909793/10000000000 : ℝ)^67 ≤ (7508807417157/25000000000000 : ℝ)^51 := by
    have hnat : (4002909793 : ℕ)^67*25000000000000^51 ≤ 7508807417157^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002909793 10000000000 7508807417157 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6783708201/10000000000 : ℝ)^67 ≤ (1501530364231/2500000000000 : ℝ)^51 := by
    have hnat : (6783708201 : ℕ)^67*2500000000000^51 ≤ 1501530364231^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6783708201 10000000000 1501530364231 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430073049/2500000000 : ℝ), (4002909793/10000000000 : ℝ), (6783708201/10000000000 : ℝ)] ![(4951777875141/50000000000000 : ℝ), (7508807417157/25000000000000 : ℝ), (1501530364231/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430073049/2500000000 : ℝ)|^67 ≤ (4951777875141/50000000000000 : ℝ)^51
        have hw : |(-430073049/2500000000 : ℝ)|=(430073049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4002909793/10000000000 : ℝ)|^67 ≤ (7508807417157/25000000000000 : ℝ)^51
        have hw : |(4002909793/10000000000 : ℝ)|=(4002909793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6783708201/10000000000 : ℝ)|^67 ≤ (1501530364231/2500000000000 : ℝ)^51
        have hw : |(6783708201/10000000000 : ℝ)|=(6783708201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (408147753/1250000000 : ℝ)*x 0 + (-297623367/10000000000 : ℝ)*x 1 + (811710753/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408147753/1250000000 : ℝ)^67 ≤ (22983055017883/100000000000000 : ℝ)^51 := by
    have hnat : (408147753 : ℕ)^67*100000000000000^51 ≤ 22983055017883^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408147753 1250000000 22983055017883 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297623367/10000000000 : ℝ)^67 ≤ (988137690559/100000000000000 : ℝ)^51 := by
    have hnat : (297623367 : ℕ)^67*100000000000000^51 ≤ 988137690559^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297623367 10000000000 988137690559 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (811710753/1000000000 : ℝ)^67 ≤ (38014403640043/50000000000000 : ℝ)^51 := by
    have hnat : (811710753 : ℕ)^67*50000000000000^51 ≤ 38014403640043^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811710753 1000000000 38014403640043 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(408147753/1250000000 : ℝ), (-297623367/10000000000 : ℝ), (811710753/1000000000 : ℝ)] ![(22983055017883/100000000000000 : ℝ), (988137690559/100000000000000 : ℝ), (38014403640043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(408147753/1250000000 : ℝ)|^67 ≤ (22983055017883/100000000000000 : ℝ)^51
        have hw : |(408147753/1250000000 : ℝ)|=(408147753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-297623367/10000000000 : ℝ)|^67 ≤ (988137690559/100000000000000 : ℝ)^51
        have hw : |(-297623367/10000000000 : ℝ)|=(297623367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(811710753/1000000000 : ℝ)|^67 ≤ (38014403640043/50000000000000 : ℝ)^51
        have hw : |(811710753/1000000000 : ℝ)|=(811710753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1644361371/5000000000 : ℝ)*x 0 + (506286139/625000000 : ℝ)*x 1 + (-73567479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1644361371/5000000000 : ℝ)^67 ≤ (11600491942103/50000000000000 : ℝ)^51 := by
    have hnat : (1644361371 : ℕ)^67*50000000000000^51 ≤ 11600491942103^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1644361371 5000000000 11600491942103 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506286139/625000000 : ℝ)^67 ≤ (75825479222541/100000000000000 : ℝ)^51 := by
    have hnat : (506286139 : ℕ)^67*100000000000000^51 ≤ 75825479222541^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506286139 625000000 75825479222541 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73567479/2500000000 : ℝ)^67 ≤ (973536886571/100000000000000 : ℝ)^51 := by
    have hnat : (73567479 : ℕ)^67*100000000000000^51 ≤ 973536886571^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73567479 2500000000 973536886571 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1644361371/5000000000 : ℝ), (506286139/625000000 : ℝ), (-73567479/2500000000 : ℝ)] ![(11600491942103/50000000000000 : ℝ), (75825479222541/100000000000000 : ℝ), (973536886571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1644361371/5000000000 : ℝ)|^67 ≤ (11600491942103/50000000000000 : ℝ)^51
        have hw : |(1644361371/5000000000 : ℝ)|=(1644361371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506286139/625000000 : ℝ)|^67 ≤ (75825479222541/100000000000000 : ℝ)^51
        have hw : |(506286139/625000000 : ℝ)|=(506286139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-73567479/2500000000 : ℝ)|^67 ≤ (973536886571/100000000000000 : ℝ)^51
        have hw : |(-73567479/2500000000 : ℝ)|=(73567479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (252449627/400000000 : ℝ)*x 0 + (5361094807/10000000000 : ℝ)*x 1 + (14548097/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252449627/400000000 : ℝ)^67 ≤ (54626785018271/100000000000000 : ℝ)^51 := by
    have hnat : (252449627 : ℕ)^67*100000000000000^51 ≤ 54626785018271^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252449627 400000000 54626785018271 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5361094807/10000000000 : ℝ)^67 ≤ (11021822527729/25000000000000 : ℝ)^51 := by
    have hnat : (5361094807 : ℕ)^67*25000000000000^51 ≤ 11021822527729^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361094807 10000000000 11021822527729 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14548097/400000000 : ℝ)^67 ≤ (642962429177/50000000000000 : ℝ)^51 := by
    have hnat : (14548097 : ℕ)^67*50000000000000^51 ≤ 642962429177^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14548097 400000000 642962429177 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(252449627/400000000 : ℝ), (5361094807/10000000000 : ℝ), (14548097/400000000 : ℝ)] ![(54626785018271/100000000000000 : ℝ), (11021822527729/25000000000000 : ℝ), (642962429177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(252449627/400000000 : ℝ)|^67 ≤ (54626785018271/100000000000000 : ℝ)^51
        have hw : |(252449627/400000000 : ℝ)|=(252449627/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5361094807/10000000000 : ℝ)|^67 ≤ (11021822527729/25000000000000 : ℝ)^51
        have hw : |(5361094807/10000000000 : ℝ)|=(5361094807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14548097/400000000 : ℝ)|^67 ≤ (642962429177/50000000000000 : ℝ)^51
        have hw : |(14548097/400000000 : ℝ)|=(14548097/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-174008841/1250000000 : ℝ)*x 0 + (98514407/250000000 : ℝ)*x 1 + (3520803037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174008841/1250000000 : ℝ)^67 ≤ (3749523049589/50000000000000 : ℝ)^51 := by
    have hnat : (174008841 : ℕ)^67*50000000000000^51 ≤ 3749523049589^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174008841 1250000000 3749523049589 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98514407/250000000 : ℝ)^67 ≤ (29422293240729/100000000000000 : ℝ)^51 := by
    have hnat : (98514407 : ℕ)^67*100000000000000^51 ≤ 29422293240729^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98514407 250000000 29422293240729 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3520803037/5000000000 : ℝ)^67 ≤ (63078660646887/100000000000000 : ℝ)^51 := by
    have hnat : (3520803037 : ℕ)^67*100000000000000^51 ≤ 63078660646887^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3520803037 5000000000 63078660646887 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-174008841/1250000000 : ℝ), (98514407/250000000 : ℝ), (3520803037/5000000000 : ℝ)] ![(3749523049589/50000000000000 : ℝ), (29422293240729/100000000000000 : ℝ), (63078660646887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-174008841/1250000000 : ℝ)|^67 ≤ (3749523049589/50000000000000 : ℝ)^51
        have hw : |(-174008841/1250000000 : ℝ)|=(174008841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(98514407/250000000 : ℝ)|^67 ≤ (29422293240729/100000000000000 : ℝ)^51
        have hw : |(98514407/250000000 : ℝ)|=(98514407/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3520803037/5000000000 : ℝ)|^67 ≤ (63078660646887/100000000000000 : ℝ)^51
        have hw : |(3520803037/5000000000 : ℝ)|=(3520803037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2094711593/10000000000 : ℝ)*x 0 + (-434348191/5000000000 : ℝ)*x 1 + (2172127443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094711593/10000000000 : ℝ)^67 ≤ (12827546702993/100000000000000 : ℝ)^51 := by
    have hnat : (2094711593 : ℕ)^67*100000000000000^51 ≤ 12827546702993^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094711593 10000000000 12827546702993 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434348191/5000000000 : ℝ)^67 ≤ (4036118047257/100000000000000 : ℝ)^51 := by
    have hnat : (434348191 : ℕ)^67*100000000000000^51 ≤ 4036118047257^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434348191 5000000000 4036118047257 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172127443/2500000000 : ℝ)^67 ≤ (41568167619309/50000000000000 : ℝ)^51 := by
    have hnat : (2172127443 : ℕ)^67*50000000000000^51 ≤ 41568167619309^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172127443 2500000000 41568167619309 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2094711593/10000000000 : ℝ), (-434348191/5000000000 : ℝ), (2172127443/2500000000 : ℝ)] ![(12827546702993/100000000000000 : ℝ), (4036118047257/100000000000000 : ℝ), (41568167619309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2094711593/10000000000 : ℝ)|^67 ≤ (12827546702993/100000000000000 : ℝ)^51
        have hw : |(2094711593/10000000000 : ℝ)|=(2094711593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434348191/5000000000 : ℝ)|^67 ≤ (4036118047257/100000000000000 : ℝ)^51
        have hw : |(-434348191/5000000000 : ℝ)|=(434348191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2172127443/2500000000 : ℝ)|^67 ≤ (41568167619309/50000000000000 : ℝ)^51
        have hw : |(2172127443/2500000000 : ℝ)|=(2172127443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (806804387/1250000000 : ℝ)*x 0 + (2553579451/5000000000 : ℝ)*x 1 + (-290063103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (806804387/1250000000 : ℝ)^67 ≤ (56260802229569/100000000000000 : ℝ)^51 := by
    have hnat : (806804387 : ℕ)^67*100000000000000^51 ≤ 56260802229569^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806804387 1250000000 56260802229569 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2553579451/5000000000 : ℝ)^67 ≤ (20682251019059/50000000000000 : ℝ)^51 := by
    have hnat : (2553579451 : ℕ)^67*50000000000000^51 ≤ 20682251019059^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553579451 5000000000 20682251019059 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (290063103/5000000000 : ℝ)^67 ≤ (2374695720123/100000000000000 : ℝ)^51 := by
    have hnat : (290063103 : ℕ)^67*100000000000000^51 ≤ 2374695720123^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290063103 5000000000 2374695720123 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(806804387/1250000000 : ℝ), (2553579451/5000000000 : ℝ), (-290063103/5000000000 : ℝ)] ![(56260802229569/100000000000000 : ℝ), (20682251019059/50000000000000 : ℝ), (2374695720123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(806804387/1250000000 : ℝ)|^67 ≤ (56260802229569/100000000000000 : ℝ)^51
        have hw : |(806804387/1250000000 : ℝ)|=(806804387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2553579451/5000000000 : ℝ)|^67 ≤ (20682251019059/50000000000000 : ℝ)^51
        have hw : |(2553579451/5000000000 : ℝ)|=(2553579451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-290063103/5000000000 : ℝ)|^67 ≤ (2374695720123/100000000000000 : ℝ)^51
        have hw : |(-290063103/5000000000 : ℝ)|=(290063103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (467933703/500000000 : ℝ)*x 0 + (232285487/2000000000 : ℝ)*x 1 + (36879107/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467933703/500000000 : ℝ)^67 ≤ (4583038710783/5000000000000 : ℝ)^51 := by
    have hnat : (467933703 : ℕ)^67*5000000000000^51 ≤ 4583038710783^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467933703 500000000 4583038710783 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232285487/2000000000 : ℝ)^67 ≤ (5910936077493/100000000000000 : ℝ)^51 := by
    have hnat : (232285487 : ℕ)^67*100000000000000^51 ≤ 5910936077493^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232285487 2000000000 5910936077493 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36879107/625000000 : ℝ)^67 ≤ (2428289701337/100000000000000 : ℝ)^51 := by
    have hnat : (36879107 : ℕ)^67*100000000000000^51 ≤ 2428289701337^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36879107 625000000 2428289701337 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(467933703/500000000 : ℝ), (232285487/2000000000 : ℝ), (36879107/625000000 : ℝ)] ![(4583038710783/5000000000000 : ℝ), (5910936077493/100000000000000 : ℝ), (2428289701337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(467933703/500000000 : ℝ)|^67 ≤ (4583038710783/5000000000000 : ℝ)^51
        have hw : |(467933703/500000000 : ℝ)|=(467933703/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(232285487/2000000000 : ℝ)|^67 ≤ (5910936077493/100000000000000 : ℝ)^51
        have hw : |(232285487/2000000000 : ℝ)|=(232285487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36879107/625000000 : ℝ)|^67 ≤ (2428289701337/100000000000000 : ℝ)^51
        have hw : |(36879107/625000000 : ℝ)|=(36879107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-704662191/5000000000 : ℝ)*x 0 + (65355841/100000000 : ℝ)*x 1 + (564438097/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (704662191/5000000000 : ℝ)^67 ≤ (1905346744031/25000000000000 : ℝ)^51 := by
    have hnat : (704662191 : ℕ)^67*25000000000000^51 ≤ 1905346744031^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704662191 5000000000 1905346744031 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65355841/100000000 : ℝ)^67 ≤ (57191885915557/100000000000000 : ℝ)^51 := by
    have hnat : (65355841 : ℕ)^67*100000000000000^51 ≤ 57191885915557^51*100000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65355841 100000000 57191885915557 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564438097/1250000000 : ℝ)^67 ≤ (4398340885551/12500000000000 : ℝ)^51 := by
    have hnat : (564438097 : ℕ)^67*12500000000000^51 ≤ 4398340885551^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564438097 1250000000 4398340885551 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-704662191/5000000000 : ℝ), (65355841/100000000 : ℝ), (564438097/1250000000 : ℝ)] ![(1905346744031/25000000000000 : ℝ), (57191885915557/100000000000000 : ℝ), (4398340885551/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-704662191/5000000000 : ℝ)|^67 ≤ (1905346744031/25000000000000 : ℝ)^51
        have hw : |(-704662191/5000000000 : ℝ)|=(704662191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65355841/100000000 : ℝ)|^67 ≤ (57191885915557/100000000000000 : ℝ)^51
        have hw : |(65355841/100000000 : ℝ)|=(65355841/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564438097/1250000000 : ℝ)|^67 ≤ (4398340885551/12500000000000 : ℝ)^51
        have hw : |(564438097/1250000000 : ℝ)|=(564438097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (102414479/156250000 : ℝ)*x 0 + (-105515721/2000000000 : ℝ)*x 1 + (2512571261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102414479/156250000 : ℝ)^67 ≤ (57409752433129/100000000000000 : ℝ)^51 := by
    have hnat : (102414479 : ℕ)^67*100000000000000^51 ≤ 57409752433129^51*156250000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102414479 156250000 57409752433129 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105515721/2000000000 : ℝ)^67 ≤ (1048108148101/50000000000000 : ℝ)^51 := by
    have hnat : (105515721 : ℕ)^67*50000000000000^51 ≤ 1048108148101^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105515721 2000000000 1048108148101 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512571261/5000000000 : ℝ)^67 ≤ (40494031260623/100000000000000 : ℝ)^51 := by
    have hnat : (2512571261 : ℕ)^67*100000000000000^51 ≤ 40494031260623^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512571261 5000000000 40494031260623 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(102414479/156250000 : ℝ), (-105515721/2000000000 : ℝ), (2512571261/5000000000 : ℝ)] ![(57409752433129/100000000000000 : ℝ), (1048108148101/50000000000000 : ℝ), (40494031260623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(102414479/156250000 : ℝ)|^67 ≤ (57409752433129/100000000000000 : ℝ)^51
        have hw : |(102414479/156250000 : ℝ)|=(102414479/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105515721/2000000000 : ℝ)|^67 ≤ (1048108148101/50000000000000 : ℝ)^51
        have hw : |(-105515721/2000000000 : ℝ)|=(105515721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2512571261/5000000000 : ℝ)|^67 ≤ (40494031260623/100000000000000 : ℝ)^51
        have hw : |(2512571261/5000000000 : ℝ)|=(2512571261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1092016937/5000000000 : ℝ)*x 0 + (8622944297/10000000000 : ℝ)*x 1 + (-885007877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092016937/5000000000 : ℝ)^67 ≤ (3387725401531/25000000000000 : ℝ)^51 := by
    have hnat : (1092016937 : ℕ)^67*25000000000000^51 ≤ 3387725401531^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092016937 5000000000 3387725401531 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8622944297/10000000000 : ℝ)^67 ≤ (10289140772423/12500000000000 : ℝ)^51 := by
    have hnat : (8622944297 : ℕ)^67*12500000000000^51 ≤ 10289140772423^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8622944297 10000000000 10289140772423 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (885007877/10000000000 : ℝ)^67 ≤ (4135972192891/100000000000000 : ℝ)^51 := by
    have hnat : (885007877 : ℕ)^67*100000000000000^51 ≤ 4135972192891^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885007877 10000000000 4135972192891 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092016937/5000000000 : ℝ), (8622944297/10000000000 : ℝ), (-885007877/10000000000 : ℝ)] ![(3387725401531/25000000000000 : ℝ), (10289140772423/12500000000000 : ℝ), (4135972192891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092016937/5000000000 : ℝ)|^67 ≤ (3387725401531/25000000000000 : ℝ)^51
        have hw : |(1092016937/5000000000 : ℝ)|=(1092016937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8622944297/10000000000 : ℝ)|^67 ≤ (10289140772423/12500000000000 : ℝ)^51
        have hw : |(8622944297/10000000000 : ℝ)|=(8622944297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-885007877/10000000000 : ℝ)|^67 ≤ (4135972192891/100000000000000 : ℝ)^51
        have hw : |(-885007877/10000000000 : ℝ)|=(885007877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s4_s4_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9387774933/10000000000 : ℝ)*x 0 + (454948667/5000000000 : ℝ)*x 1 + (808902699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9387774933/10000000000 : ℝ)^67 ≤ (92035394660597/100000000000000 : ℝ)^51 := by
    have hnat : (9387774933 : ℕ)^67*100000000000000^51 ≤ 92035394660597^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9387774933 10000000000 92035394660597 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454948667/5000000000 : ℝ)^67 ≤ (2144725793939/50000000000000 : ℝ)^51 := by
    have hnat : (454948667 : ℕ)^67*50000000000000^51 ≤ 2144725793939^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454948667 5000000000 2144725793939 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (808902699/10000000000 : ℝ)^67 ≤ (735030747459/20000000000000 : ℝ)^51 := by
    have hnat : (808902699 : ℕ)^67*20000000000000^51 ≤ 735030747459^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808902699 10000000000 735030747459 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9387774933/10000000000 : ℝ), (454948667/5000000000 : ℝ), (808902699/10000000000 : ℝ)] ![(92035394660597/100000000000000 : ℝ), (2144725793939/50000000000000 : ℝ), (735030747459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9387774933/10000000000 : ℝ)|^67 ≤ (92035394660597/100000000000000 : ℝ)^51
        have hw : |(9387774933/10000000000 : ℝ)|=(9387774933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(454948667/5000000000 : ℝ)|^67 ≤ (2144725793939/50000000000000 : ℝ)^51
        have hw : |(454948667/5000000000 : ℝ)|=(454948667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(808902699/10000000000 : ℝ)|^67 ≤ (735030747459/20000000000000 : ℝ)^51
        have hw : |(808902699/10000000000 : ℝ)|=(808902699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304053_s4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((77983/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77983/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10457/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10457/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41409/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41409/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((68167/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68167/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76869/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76869/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76073/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76073/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (77983/100000 : ℝ) ^ (33/8 : ℝ) ≤ (8962718467079654667/25000000000000000000 : ℝ) := by
    have hpowers : (77983/100000 : ℝ)^33 ≤ (8962718467079654667/25000000000000000000 : ℝ)^8 := by
      have hnat : (77983 : ℕ)^33*25000000000000000000^8 ≤ 8962718467079654667^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77983 100000 8962718467079654667 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77983/100000 : ℝ)) (X := (8962718467079654667/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner0a : (33962718467079654667/25000000000000000000 : ℝ) ≤ (10771038056074403/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (33962718467079654667/25000000000000000000 : ℝ)^8 ≤ (10771038056074403/10000000000000000 : ℝ)^33 := by
      have hnat : (33962718467079654667 : ℕ)^8*10000000000000000^33 ≤ 10771038056074403^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33962718467079654667 25000000000000000000 10771038056074403 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10771038056074403/10000000000000000 : ℝ)) (X := (33962718467079654667/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner0b : (21462718467079654667/12500000000000000000 : ℝ) ≤ (11400268569063713/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (21462718467079654667/12500000000000000000 : ℝ)^8 ≤ (11400268569063713/10000000000000000 : ℝ)^33 := by
      have hnat : (21462718467079654667 : ℕ)^8*10000000000000000^33 ≤ 11400268569063713^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21462718467079654667 12500000000000000000 11400268569063713 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11400268569063713/10000000000000000 : ℝ)) (X := (21462718467079654667/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(771038056074403/7798300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(62923051298931/779830000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (77983/100000 : ℝ)) (alpha := (771038056074403/7798300000000000 : ℝ)) (beta := (62923051298931/779830000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (77983/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(771038056074403/7798300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(62923051298931/779830000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (10457/12500 : ℝ) ^ (33/8 : ℝ) ≤ (9579228051639597303/20000000000000000000 : ℝ) := by
    have hpowers : (10457/12500 : ℝ)^33 ≤ (9579228051639597303/20000000000000000000 : ℝ)^8 := by
      have hnat : (10457 : ℕ)^33*20000000000000000000^8 ≤ 9579228051639597303^8*12500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10457 12500 9579228051639597303 20000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10457/12500 : ℝ)) (X := (9579228051639597303/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner1a : (29579228051639597303/20000000000000000000 : ℝ) ≤ (1374395331235189/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (29579228051639597303/20000000000000000000 : ℝ)^8 ≤ (1374395331235189/1250000000000000 : ℝ)^33 := by
      have hnat : (29579228051639597303 : ℕ)^8*1250000000000000^33 ≤ 1374395331235189^33*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29579228051639597303 20000000000000000000 1374395331235189 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1374395331235189/1250000000000000 : ℝ)) (X := (29579228051639597303/20000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner1b : (19579228051639597303/10000000000000000000 : ℝ) ≤ (735560392908387/625000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (19579228051639597303/10000000000000000000 : ℝ)^8 ≤ (735560392908387/625000000000000 : ℝ)^33 := by
      have hnat : (19579228051639597303 : ℕ)^8*625000000000000^33 ≤ 735560392908387^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19579228051639597303 10000000000000000000 735560392908387 625000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (735560392908387/625000000000000 : ℝ)) (X := (19579228051639597303/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(124395331235189/1045700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(19345090916317/209140000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (10457/12500 : ℝ)) (alpha := (124395331235189/1045700000000000 : ℝ)) (beta := (19345090916317/209140000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (10457/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(124395331235189/1045700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(19345090916317/209140000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (41409/50000 : ℝ) ^ (33/8 : ℝ) ≤ (45947781353090126827/100000000000000000000 : ℝ) := by
    have hpowers : (41409/50000 : ℝ)^33 ≤ (45947781353090126827/100000000000000000000 : ℝ)^8 := by
      have hnat : (41409 : ℕ)^33*100000000000000000000^8 ≤ 45947781353090126827^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41409 50000 45947781353090126827 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41409/50000 : ℝ)) (X := (45947781353090126827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner2a : (145947781353090126827/100000000000000000000 : ℝ) ≤ (2739967822366113/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (145947781353090126827/100000000000000000000 : ℝ)^8 ≤ (2739967822366113/2500000000000000 : ℝ)^33 := by
      have hnat : (145947781353090126827 : ℕ)^8*2500000000000000^33 ≤ 2739967822366113^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        145947781353090126827 100000000000000000000 2739967822366113 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2739967822366113/2500000000000000 : ℝ)) (X := (145947781353090126827/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner2b : (95947781353090126827/50000000000000000000 : ℝ) ≤ (11711750228667113/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (95947781353090126827/50000000000000000000 : ℝ)^8 ≤ (11711750228667113/10000000000000000 : ℝ)^33 := by
      have hnat : (95947781353090126827 : ℕ)^8*10000000000000000^33 ≤ 11711750228667113^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        95947781353090126827 50000000000000000000 11711750228667113 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11711750228667113/10000000000000000 : ℝ)) (X := (95947781353090126827/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(239967822366113/2070450000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(751878939202661/8281800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (41409/50000 : ℝ)) (alpha := (239967822366113/2070450000000000 : ℝ)) (beta := (751878939202661/8281800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (41409/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(239967822366113/2070450000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(751878939202661/8281800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-1878904439/10000000000 : ℝ)*X 0 0+(5325735089/10000000000 : ℝ)*X 0 1+(5461407623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((4476487381/10000000000 : ℝ)*X 1 0+(-587274677/5000000000 : ℝ)*X 1 1+(419418027/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-430073049/2500000000 : ℝ)*X 0 0+(4002909793/10000000000 : ℝ)*X 0 1+(6783708201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((408147753/1250000000 : ℝ)*X 1 0+(-297623367/10000000000 : ℝ)*X 1 1+(811710753/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((1644361371/5000000000 : ℝ)*X 2 0+(506286139/625000000 : ℝ)*X 2 1+(-73567479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((252449627/400000000 : ℝ)*X 0 0+(5361094807/10000000000 : ℝ)*X 0 1+(14548097/400000000 : ℝ)*X 0 2+(252449627/400000000 : ℝ)*X 1 0+(5361094807/10000000000 : ℝ)*X 1 1+(14548097/400000000 : ℝ)*X 1 2+(252449627/400000000 : ℝ)*X 2 0+(5361094807/10000000000 : ℝ)*X 2 1+(14548097/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-174008841/1250000000 : ℝ)*X 0 0+(98514407/250000000 : ℝ)*X 0 1+(3520803037/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((2094711593/10000000000 : ℝ)*X 1 0+(-434348191/5000000000 : ℝ)*X 1 1+(2172127443/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((806804387/1250000000 : ℝ)*X 2 0+(2553579451/5000000000 : ℝ)*X 2 1+(-290063103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((467933703/500000000 : ℝ)*X 0 0+(232285487/2000000000 : ℝ)*X 0 1+(36879107/625000000 : ℝ)*X 0 2+(467933703/500000000 : ℝ)*X 1 0+(232285487/2000000000 : ℝ)*X 1 1+(36879107/625000000 : ℝ)*X 1 2+(467933703/500000000 : ℝ)*X 2 0+(232285487/2000000000 : ℝ)*X 2 1+(36879107/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-704662191/5000000000 : ℝ)*X 0 0+(65355841/100000000 : ℝ)*X 0 1+(564438097/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((102414479/156250000 : ℝ)*X 1 0+(-105515721/2000000000 : ℝ)*X 1 1+(2512571261/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((1092016937/5000000000 : ℝ)*X 2 0+(8622944297/10000000000 : ℝ)*X 2 1+(-885007877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((9387774933/10000000000 : ℝ)*X 0 0+(454948667/5000000000 : ℝ)*X 0 1+(808902699/10000000000 : ℝ)*X 0 2+(9387774933/10000000000 : ℝ)*X 1 0+(454948667/5000000000 : ℝ)*X 1 1+(808902699/10000000000 : ℝ)*X 1 2+(9387774933/10000000000 : ℝ)*X 2 0+(454948667/5000000000 : ℝ)*X 2 1+(808902699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((68167/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68167/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34088025962605634296529969/3608449275000000000000000000000 : ℝ) := by norm_num
    linear_combination (195124088253/1000000000000 : ℝ)*(base7) + (239899/1000000000000 : ℝ)*(base49) + (681093/1000000000000 : ℝ)*(base53) + (326311/1000000000000 : ℝ)*(base59) + (1459603600099/500000000000 : ℝ)*(major_s4_0) + (1459603600099/500000000000 : ℝ)*(major_s4_1) + (583841303821/200000000000 : ℝ)*(major_s4_2) + (12323761/500000000000 : ℝ)*(sp_s4_0) + (3791426314053/1000000000000 : ℝ)*(sp_s4_7) + (1481079819/390625000 : ℝ)*(sp_s4_8) + (30332524757/8000000000 : ℝ)*(sp_s4_9) + (2119808407177/1000000000000 : ℝ)*(sp_s4_13) + (56975979/500000000000 : ℝ)*(sp_s4_14) + (576893/1000000000000 : ℝ)*(sp_s4_15) + (481171079731/250000000000 : ℝ)*(f.failure) + (30332524757/8000000000 : ℝ)*(f.sum) + (4914889077787850221/21650695650000000000000000000000 : ℝ)*base62 + (227212323833657/1656360000000000000000000000 : ℝ)*base64 + (15434693001283/20914000000000000000000000 : ℝ)*base66 + (298343520819283/414090000000000000000000000 : ℝ)*base68 + (220594350673434875357/645839609400000000000000000000000 : ℝ)*base71 + (146532817383741/155966000000000000000000000 : ℝ)*base72 + (115416962545207/261425000000000000000000000 : ℝ)*base74 + (254355436899447/974787500000000000000000000 : ℝ)*base76 + (332772648182054251/4077341155000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1279/3125000000000000 : ℝ)*base87 + (1279/3125000000000000 : ℝ)*base89 + (1279/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76869/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76869/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6973264804394826046556220184771/562795399624650000000000000000000000 : ℝ) := by norm_num
    linear_combination (137976076141/250000000000 : ℝ)*(base7) + (12961863/1000000000000 : ℝ)*(base27) + (27063815681/125000000000 : ℝ)*(base53) + (972061255623/500000000000 : ℝ)*(major_s4_0) + (972061255623/500000000000 : ℝ)*(major_s4_1) + (1727611985797/1000000000000 : ℝ)*(major_s4_2) + (12058799/1000000000000 : ℝ)*(sp_s4_0) + (97660073/1000000000000 : ℝ)*(sp_s4_8) + (255546524367/125000000000 : ℝ)*(sp_s4_14) + (2044308034537/1000000000000 : ℝ)*(sp_s4_15) + (1130458110029/500000000000 : ℝ)*(sp_s4_16) + (229199944849/125000000000 : ℝ)*(sp_s4_20) + (5360219/250000000000 : ℝ)*(sp_s4_21) + (85728239/1000000000000 : ℝ)*(sp_s4_27) + (1281793944331/1000000000000 : ℝ)*(f.failure) + (1130458110029/500000000000 : ℝ)*(f.sum) + (1414755549709038451/2165069565000000000000000000000 : ℝ)*base63 + (387539455046477/8281800000000000000000000000 : ℝ)*base64 + (18095145379973/20914000000000000000000000 : ℝ)*base66 + (1867672505930561/2070450000000000000000000000 : ℝ)*base69 + (84086014022687614033/645839609400000000000000000000000 : ℝ)*base71 + (190490270566251/779830000000000000000000000 : ℝ)*base72 + (155620108614093/130712500000000000000000000 : ℝ)*base75 + (2408043706959339/3899150000000000000000000000 : ℝ)*base77 + (5117855898129349/4077341155000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (3571/12500000000000000 : ℝ)*base86 + (3571/12500000000000000 : ℝ)*base88 + (8929/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76073/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76073/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2906456011352786401477157971661/225118159849860000000000000000000000 : ℝ) := by norm_num
    linear_combination (264696214157/500000000000 : ℝ)*(base7) + (4299263/250000000000 : ℝ)*(base27) + (30138538631/1000000000000 : ℝ)*(base40) + (2120330737/6250000000 : ℝ)*(base43) + (377293410869/200000000000 : ℝ)*(major_s4_0) + (61888565457/40000000000 : ℝ)*(major_s4_1) + (377293410869/200000000000 : ℝ)*(major_s4_2) + (7228331/1000000000000 : ℝ)*(sp_s4_1) + (109021339/1000000000000 : ℝ)*(sp_s4_9) + (12185153/1000000000000 : ℝ)*(sp_s4_14) + (929223645161/500000000000 : ℝ)*(sp_s4_21) + (2197705165063/1000000000000 : ℝ)*(sp_s4_22) + (232293806767/125000000000 : ℝ)*(sp_s4_23) + (354631185071/200000000000 : ℝ)*(sp_s4_27) + (1243780694093/1000000000000 : ℝ)*(f.failure) + (1098856196697/500000000000 : ℝ)*(f.sum) + (2939125288491235741/8660278260000000000000000000000 : ℝ)*base63 + (612922978504369/1656360000000000000000000000 : ℝ)*base64 + (40029637056571/209140000000000000000000000 : ℝ)*base66 + (207393975376711/414090000000000000000000000 : ℝ)*base69 + (61491414609494998549/129167921880000000000000000000000 : ℝ)*base70 + (290816567132293/389915000000000000000000000 : ℝ)*base73 + (58599126747927/209140000000000000000000000 : ℝ)*base75 + (1572062780613261/1559660000000000000000000000 : ℝ)*base76 + (8423659782015675317/16309364620000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (3313/12500000000000000 : ℝ)*base86 + (3313/12500000000000000 : ℝ)*base88 + (3313/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((77983/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77983/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10457/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10457/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41409/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41409/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((68167/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68167/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76869/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76869/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76073/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76073/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304053_s4 p hpa hpb X hX hprev3

#print axioms solution
