-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305083_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:34:06.45113+00:00
-- url     : https://prove2.me/submissions/402adf4c-efe6-4b3d-998b-2188b8fb7f80

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
theorem collision_support_c305083_s2_s2_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1866414377/5000000000 : ℝ)*x 0 + (407225941/625000000 : ℝ)*x 1 + (-243541649/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1866414377/5000000000 : ℝ)^67 ≤ (6850393331327/25000000000000 : ℝ)^51 := by
    have hnat : (1866414377 : ℕ)^67*25000000000000^51 ≤ 6850393331327^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866414377 5000000000 6850393331327 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (407225941/625000000 : ℝ)^67 ≤ (2848121386243/5000000000000 : ℝ)^51 := by
    have hnat : (407225941 : ℕ)^67*5000000000000^51 ≤ 2848121386243^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407225941 625000000 2848121386243 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243541649/1000000000 : ℝ)^67 ≤ (781799946459/5000000000000 : ℝ)^51 := by
    have hnat : (243541649 : ℕ)^67*5000000000000^51 ≤ 781799946459^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243541649 1000000000 781799946459 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1866414377/5000000000 : ℝ), (407225941/625000000 : ℝ), (-243541649/1000000000 : ℝ)] ![(6850393331327/25000000000000 : ℝ), (2848121386243/5000000000000 : ℝ), (781799946459/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1866414377/5000000000 : ℝ)|^67 ≤ (6850393331327/25000000000000 : ℝ)^51
        have hw : |(1866414377/5000000000 : ℝ)|=(1866414377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(407225941/625000000 : ℝ)|^67 ≤ (2848121386243/5000000000000 : ℝ)^51
        have hw : |(407225941/625000000 : ℝ)|=(407225941/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-243541649/1000000000 : ℝ)|^67 ≤ (781799946459/5000000000000 : ℝ)^51
        have hw : |(-243541649/1000000000 : ℝ)|=(243541649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s2_s2_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2199982431/10000000000 : ℝ)*x 0 + (1251457997/2500000000 : ℝ)*x 1 + (5539916827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199982431/10000000000 : ℝ)^67 ≤ (3420261929673/25000000000000 : ℝ)^51 := by
    have hnat : (2199982431 : ℕ)^67*25000000000000^51 ≤ 3420261929673^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199982431 10000000000 3420261929673 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1251457997/2500000000 : ℝ)^67 ≤ (10072431512551/25000000000000 : ℝ)^51 := by
    have hnat : (1251457997 : ℕ)^67*25000000000000^51 ≤ 10072431512551^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251457997 2500000000 10072431512551 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5539916827/10000000000 : ℝ)^67 ≤ (23014613110257/50000000000000 : ℝ)^51 := by
    have hnat : (5539916827 : ℕ)^67*50000000000000^51 ≤ 23014613110257^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5539916827 10000000000 23014613110257 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2199982431/10000000000 : ℝ), (1251457997/2500000000 : ℝ), (5539916827/10000000000 : ℝ)] ![(3420261929673/25000000000000 : ℝ), (10072431512551/25000000000000 : ℝ), (23014613110257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2199982431/10000000000 : ℝ)|^67 ≤ (3420261929673/25000000000000 : ℝ)^51
        have hw : |(-2199982431/10000000000 : ℝ)|=(2199982431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1251457997/2500000000 : ℝ)|^67 ≤ (10072431512551/25000000000000 : ℝ)^51
        have hw : |(1251457997/2500000000 : ℝ)|=(1251457997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5539916827/10000000000 : ℝ)|^67 ≤ (23014613110257/50000000000000 : ℝ)^51
        have hw : |(5539916827/10000000000 : ℝ)|=(5539916827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s2_s2_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3264484599/5000000000 : ℝ)*x 0 + (134931/10000000000 : ℝ)*x 1 + (2624679063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3264484599/5000000000 : ℝ)^67 ≤ (5711585169847/10000000000000 : ℝ)^51 := by
    have hnat : (3264484599 : ℕ)^67*10000000000000^51 ≤ 5711585169847^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3264484599 5000000000 5711585169847 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134931/10000000000 : ℝ)^67 ≤ (40022449/100000000000000 : ℝ)^51 := by
    have hnat : (134931 : ℕ)^67*100000000000000^51 ≤ 40022449^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134931 10000000000 40022449 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2624679063/5000000000 : ℝ)^67 ≤ (42884108266161/100000000000000 : ℝ)^51 := by
    have hnat : (2624679063 : ℕ)^67*100000000000000^51 ≤ 42884108266161^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624679063 5000000000 42884108266161 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3264484599/5000000000 : ℝ), (134931/10000000000 : ℝ), (2624679063/5000000000 : ℝ)] ![(5711585169847/10000000000000 : ℝ), (40022449/100000000000000 : ℝ), (42884108266161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3264484599/5000000000 : ℝ)|^67 ≤ (5711585169847/10000000000000 : ℝ)^51
        have hw : |(3264484599/5000000000 : ℝ)|=(3264484599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134931/10000000000 : ℝ)|^67 ≤ (40022449/100000000000000 : ℝ)^51
        have hw : |(134931/10000000000 : ℝ)|=(134931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2624679063/5000000000 : ℝ)|^67 ≤ (42884108266161/100000000000000 : ℝ)^51
        have hw : |(2624679063/5000000000 : ℝ)|=(2624679063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s2_s2_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (389809207/1250000000 : ℝ)*x 0 + (754275359/1000000000 : ℝ)*x 1 + (-1642948071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389809207/1250000000 : ℝ)^67 ≤ (4327218310309/20000000000000 : ℝ)^51 := by
    have hnat : (389809207 : ℕ)^67*20000000000000^51 ≤ 4327218310309^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389809207 1250000000 4327218310309 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (754275359/1000000000 : ℝ)^67 ≤ (69041136919277/100000000000000 : ℝ)^51 := by
    have hnat : (754275359 : ℕ)^67*100000000000000^51 ≤ 69041136919277^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754275359 1000000000 69041136919277 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1642948071/10000000000 : ℝ)^67 ≤ (9322771514539/100000000000000 : ℝ)^51 := by
    have hnat : (1642948071 : ℕ)^67*100000000000000^51 ≤ 9322771514539^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1642948071 10000000000 9322771514539 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(389809207/1250000000 : ℝ), (754275359/1000000000 : ℝ), (-1642948071/10000000000 : ℝ)] ![(4327218310309/20000000000000 : ℝ), (69041136919277/100000000000000 : ℝ), (9322771514539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(389809207/1250000000 : ℝ)|^67 ≤ (4327218310309/20000000000000 : ℝ)^51
        have hw : |(389809207/1250000000 : ℝ)|=(389809207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(754275359/1000000000 : ℝ)|^67 ≤ (69041136919277/100000000000000 : ℝ)^51
        have hw : |(754275359/1000000000 : ℝ)|=(754275359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1642948071/10000000000 : ℝ)|^67 ≤ (9322771514539/100000000000000 : ℝ)^51
        have hw : |(-1642948071/10000000000 : ℝ)|=(1642948071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s2_s2_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (635982839/2000000000 : ℝ)*x 0 + (4753861433/10000000000 : ℝ)*x 1 + (499312297/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (635982839/2000000000 : ℝ)^67 ≤ (22197825308111/100000000000000 : ℝ)^51 := by
    have hnat : (635982839 : ℕ)^67*100000000000000^51 ≤ 22197825308111^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635982839 2000000000 22197825308111 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4753861433/10000000000 : ℝ)^67 ≤ (18823387541401/50000000000000 : ℝ)^51 := by
    have hnat : (4753861433 : ℕ)^67*50000000000000^51 ≤ 18823387541401^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4753861433 10000000000 18823387541401 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499312297/1000000000 : ℝ)^67 ≤ (40155399588881/100000000000000 : ℝ)^51 := by
    have hnat : (499312297 : ℕ)^67*100000000000000^51 ≤ 40155399588881^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499312297 1000000000 40155399588881 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(635982839/2000000000 : ℝ), (4753861433/10000000000 : ℝ), (499312297/1000000000 : ℝ)] ![(22197825308111/100000000000000 : ℝ), (18823387541401/50000000000000 : ℝ), (40155399588881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(635982839/2000000000 : ℝ)|^67 ≤ (22197825308111/100000000000000 : ℝ)^51
        have hw : |(635982839/2000000000 : ℝ)|=(635982839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4753861433/10000000000 : ℝ)|^67 ≤ (18823387541401/50000000000000 : ℝ)^51
        have hw : |(4753861433/10000000000 : ℝ)|=(4753861433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(499312297/1000000000 : ℝ)|^67 ≤ (40155399588881/100000000000000 : ℝ)^51
        have hw : |(499312297/1000000000 : ℝ)|=(499312297/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s2_s2_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1153057713/10000000000 : ℝ)*x 0 + (3558157257/10000000000 : ℝ)*x 1 + (7490657221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1153057713/10000000000 : ℝ)^67 ≤ (585503916531/10000000000000 : ℝ)^51 := by
    have hnat : (1153057713 : ℕ)^67*10000000000000^51 ≤ 585503916531^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153057713 10000000000 585503916531 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3558157257/10000000000 : ℝ)^67 ≤ (12864799712029/50000000000000 : ℝ)^51 := by
    have hnat : (3558157257 : ℕ)^67*50000000000000^51 ≤ 12864799712029^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3558157257 10000000000 12864799712029 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7490657221/10000000000 : ℝ)^67 ≤ (34207680699153/50000000000000 : ℝ)^51 := by
    have hnat : (7490657221 : ℕ)^67*50000000000000^51 ≤ 34207680699153^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7490657221 10000000000 34207680699153 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1153057713/10000000000 : ℝ), (3558157257/10000000000 : ℝ), (7490657221/10000000000 : ℝ)] ![(585503916531/10000000000000 : ℝ), (12864799712029/50000000000000 : ℝ), (34207680699153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1153057713/10000000000 : ℝ)|^67 ≤ (585503916531/10000000000000 : ℝ)^51
        have hw : |(-1153057713/10000000000 : ℝ)|=(1153057713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3558157257/10000000000 : ℝ)|^67 ≤ (12864799712029/50000000000000 : ℝ)^51
        have hw : |(3558157257/10000000000 : ℝ)|=(3558157257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7490657221/10000000000 : ℝ)|^67 ≤ (34207680699153/50000000000000 : ℝ)^51
        have hw : |(7490657221/10000000000 : ℝ)|=(7490657221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s2_s2_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (420677417/500000000 : ℝ)*x 0 + (-385970719/10000000000 : ℝ)*x 1 + (2814908811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420677417/500000000 : ℝ)^67 ≤ (9962154396509/12500000000000 : ℝ)^51 := by
    have hnat : (420677417 : ℕ)^67*12500000000000^51 ≤ 9962154396509^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420677417 500000000 9962154396509 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385970719/10000000000 : ℝ)^67 ≤ (1390338126369/100000000000000 : ℝ)^51 := by
    have hnat : (385970719 : ℕ)^67*100000000000000^51 ≤ 1390338126369^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385970719 10000000000 1390338126369 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2814908811/10000000000 : ℝ)^67 ≤ (18912426692347/100000000000000 : ℝ)^51 := by
    have hnat : (2814908811 : ℕ)^67*100000000000000^51 ≤ 18912426692347^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814908811 10000000000 18912426692347 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420677417/500000000 : ℝ), (-385970719/10000000000 : ℝ), (2814908811/10000000000 : ℝ)] ![(9962154396509/12500000000000 : ℝ), (1390338126369/100000000000000 : ℝ), (18912426692347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420677417/500000000 : ℝ)|^67 ≤ (9962154396509/12500000000000 : ℝ)^51
        have hw : |(420677417/500000000 : ℝ)|=(420677417/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-385970719/10000000000 : ℝ)|^67 ≤ (1390338126369/100000000000000 : ℝ)^51
        have hw : |(-385970719/10000000000 : ℝ)|=(385970719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2814908811/10000000000 : ℝ)|^67 ≤ (18912426692347/100000000000000 : ℝ)^51
        have hw : |(2814908811/10000000000 : ℝ)|=(2814908811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s2_s2_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (160285717/400000000 : ℝ)*x 0 + (278430997/400000000 : ℝ)*x 1 + (-716771423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (160285717/400000000 : ℝ)^67 ≤ (30076964014507/100000000000000 : ℝ)^51 := by
    have hnat : (160285717 : ℕ)^67*100000000000000^51 ≤ 30076964014507^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160285717 400000000 30076964014507 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278430997/400000000 : ℝ)^67 ≤ (62129129235159/100000000000000 : ℝ)^51 := by
    have hnat : (278430997 : ℕ)^67*100000000000000^51 ≤ 62129129235159^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278430997 400000000 62129129235159 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (716771423/5000000000 : ℝ)^67 ≤ (779390672709/10000000000000 : ℝ)^51 := by
    have hnat : (716771423 : ℕ)^67*10000000000000^51 ≤ 779390672709^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716771423 5000000000 779390672709 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(160285717/400000000 : ℝ), (278430997/400000000 : ℝ), (-716771423/5000000000 : ℝ)] ![(30076964014507/100000000000000 : ℝ), (62129129235159/100000000000000 : ℝ), (779390672709/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(160285717/400000000 : ℝ)|^67 ≤ (30076964014507/100000000000000 : ℝ)^51
        have hw : |(160285717/400000000 : ℝ)|=(160285717/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(278430997/400000000 : ℝ)|^67 ≤ (62129129235159/100000000000000 : ℝ)^51
        have hw : |(278430997/400000000 : ℝ)|=(278430997/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-716771423/5000000000 : ℝ)|^67 ≤ (779390672709/10000000000000 : ℝ)^51
        have hw : |(-716771423/5000000000 : ℝ)|=(716771423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s2_s2_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (660805957/2500000000 : ℝ)*x 0 + (1831080429/5000000000 : ℝ)*x 1 + (6419940951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660805957/2500000000 : ℝ)^67 ≤ (17411758223633/100000000000000 : ℝ)^51 := by
    have hnat : (660805957 : ℕ)^67*100000000000000^51 ≤ 17411758223633^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660805957 2500000000 17411758223633 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1831080429/5000000000 : ℝ)^67 ≤ (13361054267943/50000000000000 : ℝ)^51 := by
    have hnat : (1831080429 : ℕ)^67*50000000000000^51 ≤ 13361054267943^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831080429 5000000000 13361054267943 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6419940951/10000000000 : ℝ)^67 ≤ (11173226645193/20000000000000 : ℝ)^51 := by
    have hnat : (6419940951 : ℕ)^67*20000000000000^51 ≤ 11173226645193^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6419940951 10000000000 11173226645193 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660805957/2500000000 : ℝ), (1831080429/5000000000 : ℝ), (6419940951/10000000000 : ℝ)] ![(17411758223633/100000000000000 : ℝ), (13361054267943/50000000000000 : ℝ), (11173226645193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660805957/2500000000 : ℝ)|^67 ≤ (17411758223633/100000000000000 : ℝ)^51
        have hw : |(660805957/2500000000 : ℝ)|=(660805957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1831080429/5000000000 : ℝ)|^67 ≤ (13361054267943/50000000000000 : ℝ)^51
        have hw : |(1831080429/5000000000 : ℝ)|=(1831080429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6419940951/10000000000 : ℝ)|^67 ≤ (11173226645193/20000000000000 : ℝ)^51
        have hw : |(6419940951/10000000000 : ℝ)|=(6419940951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s2_s2_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1678768627/10000000000 : ℝ)*x 0 + (5777986459/10000000000 : ℝ)*x 1 + (5144672757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1678768627/10000000000 : ℝ)^67 ≤ (2397677268581/25000000000000 : ℝ)^51 := by
    have hnat : (1678768627 : ℕ)^67*25000000000000^51 ≤ 2397677268581^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678768627 10000000000 2397677268581 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5777986459/10000000000 : ℝ)^67 ≤ (24322585903541/50000000000000 : ℝ)^51 := by
    have hnat : (5777986459 : ℕ)^67*50000000000000^51 ≤ 24322585903541^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5777986459 10000000000 24322585903541 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5144672757/10000000000 : ℝ)^67 ≤ (2088205955151/5000000000000 : ℝ)^51 := by
    have hnat : (5144672757 : ℕ)^67*5000000000000^51 ≤ 2088205955151^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144672757 10000000000 2088205955151 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1678768627/10000000000 : ℝ), (5777986459/10000000000 : ℝ), (5144672757/10000000000 : ℝ)] ![(2397677268581/25000000000000 : ℝ), (24322585903541/50000000000000 : ℝ), (2088205955151/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1678768627/10000000000 : ℝ)|^67 ≤ (2397677268581/25000000000000 : ℝ)^51
        have hw : |(-1678768627/10000000000 : ℝ)|=(1678768627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5777986459/10000000000 : ℝ)|^67 ≤ (24322585903541/50000000000000 : ℝ)^51
        have hw : |(5777986459/10000000000 : ℝ)|=(5777986459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5144672757/10000000000 : ℝ)|^67 ≤ (2088205955151/5000000000000 : ℝ)^51
        have hw : |(5144672757/10000000000 : ℝ)|=(5144672757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s2_s2_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (966939111/1250000000 : ℝ)*x 0 + (-13227/10000000000 : ℝ)*x 1 + (96492899/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (966939111/1250000000 : ℝ)^67 ≤ (17842073140127/25000000000000 : ℝ)^51 := by
    have hnat : (966939111 : ℕ)^67*25000000000000^51 ≤ 17842073140127^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966939111 1250000000 17842073140127 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13227/10000000000 : ℝ)^67 ≤ (1893277/100000000000000 : ℝ)^51 := by
    have hnat : (13227 : ℕ)^67*100000000000000^51 ≤ 1893277^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13227 10000000000 1893277 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96492899/250000000 : ℝ)^67 ≤ (28631705536383/100000000000000 : ℝ)^51 := by
    have hnat : (96492899 : ℕ)^67*100000000000000^51 ≤ 28631705536383^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96492899 250000000 28631705536383 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(966939111/1250000000 : ℝ), (-13227/10000000000 : ℝ), (96492899/250000000 : ℝ)] ![(17842073140127/25000000000000 : ℝ), (1893277/100000000000000 : ℝ), (28631705536383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(966939111/1250000000 : ℝ)|^67 ≤ (17842073140127/25000000000000 : ℝ)^51
        have hw : |(966939111/1250000000 : ℝ)|=(966939111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13227/10000000000 : ℝ)|^67 ≤ (1893277/100000000000000 : ℝ)^51
        have hw : |(-13227/10000000000 : ℝ)|=(13227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(96492899/250000000 : ℝ)|^67 ≤ (28631705536383/100000000000000 : ℝ)^51
        have hw : |(96492899/250000000 : ℝ)|=(96492899/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s2_s2_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3438160119/10000000000 : ℝ)*x 0 + (1714379533/2500000000 : ℝ)*x 1 + (-1148741517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3438160119/10000000000 : ℝ)^67 ≤ (6148933341203/25000000000000 : ℝ)^51 := by
    have hnat : (3438160119 : ℕ)^67*25000000000000^51 ≤ 6148933341203^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3438160119 10000000000 6148933341203 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1714379533/2500000000 : ℝ)^67 ≤ (60921188211143/100000000000000 : ℝ)^51 := by
    have hnat : (1714379533 : ℕ)^67*100000000000000^51 ≤ 60921188211143^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714379533 2500000000 60921188211143 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1148741517/5000000000 : ℝ)^67 ≤ (14483078404661/100000000000000 : ℝ)^51 := by
    have hnat : (1148741517 : ℕ)^67*100000000000000^51 ≤ 14483078404661^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148741517 5000000000 14483078404661 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3438160119/10000000000 : ℝ), (1714379533/2500000000 : ℝ), (-1148741517/5000000000 : ℝ)] ![(6148933341203/25000000000000 : ℝ), (60921188211143/100000000000000 : ℝ), (14483078404661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3438160119/10000000000 : ℝ)|^67 ≤ (6148933341203/25000000000000 : ℝ)^51
        have hw : |(3438160119/10000000000 : ℝ)|=(3438160119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1714379533/2500000000 : ℝ)|^67 ≤ (60921188211143/100000000000000 : ℝ)^51
        have hw : |(1714379533/2500000000 : ℝ)|=(1714379533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1148741517/5000000000 : ℝ)|^67 ≤ (14483078404661/100000000000000 : ℝ)^51
        have hw : |(-1148741517/5000000000 : ℝ)|=(1148741517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s2_s2_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (825615519/2000000000 : ℝ)*x 0 + (4574630109/10000000000 : ℝ)*x 1 + (4293493181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825615519/2000000000 : ℝ)^67 ≤ (7818765127293/25000000000000 : ℝ)^51 := by
    have hnat : (825615519 : ℕ)^67*25000000000000^51 ≤ 7818765127293^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825615519 2000000000 7818765127293 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4574630109/10000000000 : ℝ)^67 ≤ (1118538714487/3125000000000 : ℝ)^51 := by
    have hnat : (4574630109 : ℕ)^67*3125000000000^51 ≤ 1118538714487^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574630109 10000000000 1118538714487 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4293493181/10000000000 : ℝ)^67 ≤ (6586340124577/20000000000000 : ℝ)^51 := by
    have hnat : (4293493181 : ℕ)^67*20000000000000^51 ≤ 6586340124577^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4293493181 10000000000 6586340124577 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(825615519/2000000000 : ℝ), (4574630109/10000000000 : ℝ), (4293493181/10000000000 : ℝ)] ![(7818765127293/25000000000000 : ℝ), (1118538714487/3125000000000 : ℝ), (6586340124577/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(825615519/2000000000 : ℝ)|^67 ≤ (7818765127293/25000000000000 : ℝ)^51
        have hw : |(825615519/2000000000 : ℝ)|=(825615519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4574630109/10000000000 : ℝ)|^67 ≤ (1118538714487/3125000000000 : ℝ)^51
        have hw : |(4574630109/10000000000 : ℝ)|=(4574630109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4293493181/10000000000 : ℝ)|^67 ≤ (6586340124577/20000000000000 : ℝ)^51
        have hw : |(4293493181/10000000000 : ℝ)|=(4293493181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305083_s2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((8417/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8417/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((17511/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(17511/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76733/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76733/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((41479/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41479/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((5139/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5139/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22697/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22697/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (8417/12500 : ℝ) ^ (133/32 : ℝ) ≤ (4831621533784419517/25000000000000000000 : ℝ) := by
    have hpowers : (8417/12500 : ℝ)^133 ≤ (4831621533784419517/25000000000000000000 : ℝ)^32 := by
      have hnat : (8417 : ℕ)^133*25000000000000000000^32 ≤ 4831621533784419517^32*12500^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8417 12500 4831621533784419517 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8417/12500 : ℝ)) (X := (4831621533784419517/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (29831621533784419517/25000000000000000000 : ℝ) ≤ (2608573095103717/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (29831621533784419517/25000000000000000000 : ℝ)^32 ≤ (2608573095103717/2500000000000000 : ℝ)^133 := by
      have hnat : (29831621533784419517 : ℕ)^32*2500000000000000^133 ≤ 2608573095103717^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29831621533784419517 25000000000000000000 2608573095103717 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2608573095103717/2500000000000000 : ℝ)) (X := (29831621533784419517/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (17331621533784419517/12500000000000000000 : ℝ) ≤ (216360696448411/200000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (17331621533784419517/12500000000000000000 : ℝ)^32 ≤ (216360696448411/200000000000000 : ℝ)^133 := by
      have hnat : (17331621533784419517 : ℕ)^32*200000000000000^133 ≤ 216360696448411^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17331621533784419517 12500000000000000000 216360696448411 200000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (216360696448411/200000000000000 : ℝ)) (X := (17331621533784419517/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(108573095103717/1683400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(10098485315939/177200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (8417/12500 : ℝ)) (alpha := (108573095103717/1683400000000000 : ℝ)) (beta := (10098485315939/177200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (8417/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(108573095103717/1683400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(10098485315939/177200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (17511/25000 : ℝ) ^ (133/32 : ℝ) ≤ (5691974887906032963/25000000000000000000 : ℝ) := by
    have hpowers : (17511/25000 : ℝ)^133 ≤ (5691974887906032963/25000000000000000000 : ℝ)^32 := by
      have hnat : (17511 : ℕ)^133*25000000000000000000^32 ≤ 5691974887906032963^32*25000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17511 25000 5691974887906032963 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17511/25000 : ℝ)) (X := (5691974887906032963/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (30691974887906032963/25000000000000000000 : ℝ) ≤ (2101183291442327/2000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (30691974887906032963/25000000000000000000 : ℝ)^32 ≤ (2101183291442327/2000000000000000 : ℝ)^133 := by
      have hnat : (30691974887906032963 : ℕ)^32*2000000000000000^133 ≤ 2101183291442327^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30691974887906032963 25000000000000000000 2101183291442327 2000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2101183291442327/2000000000000000 : ℝ)) (X := (30691974887906032963/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (18191974887906032963/12500000000000000000 : ℝ) ≤ (10944874531713817/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (18191974887906032963/12500000000000000000 : ℝ)^32 ≤ (10944874531713817/10000000000000000 : ℝ)^133 := by
      have hnat : (18191974887906032963 : ℕ)^32*10000000000000000^133 ≤ 10944874531713817^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18191974887906032963 12500000000000000000 10944874531713817 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10944874531713817/10000000000000000 : ℝ)) (X := (18191974887906032963/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(33727763814109/466960000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(73159679083697/1167400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (17511/25000 : ℝ)) (alpha := (33727763814109/466960000000000 : ℝ)) (beta := (73159679083697/1167400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (17511/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(33727763814109/466960000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(73159679083697/1167400000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (76733/100000 : ℝ) ^ (133/32 : ℝ) ≤ (33262675363658974077/100000000000000000000 : ℝ) := by
    have hpowers : (76733/100000 : ℝ)^133 ≤ (33262675363658974077/100000000000000000000 : ℝ)^32 := by
      have hnat : (76733 : ℕ)^133*100000000000000000000^32 ≤ 33262675363658974077^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76733 100000 33262675363658974077 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76733/100000 : ℝ)) (X := (33262675363658974077/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (133262675363658974077/100000000000000000000 : ℝ) ≤ (10715317880252749/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (133262675363658974077/100000000000000000000 : ℝ)^32 ≤ (10715317880252749/10000000000000000 : ℝ)^133 := by
      have hnat : (133262675363658974077 : ℕ)^32*10000000000000000^133 ≤ 10715317880252749^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        133262675363658974077 100000000000000000000 10715317880252749 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10715317880252749/10000000000000000 : ℝ)) (X := (133262675363658974077/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (83262675363658974077/50000000000000000000 : ℝ) ≤ (5652733503943049/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (83262675363658974077/50000000000000000000 : ℝ)^32 ≤ (5652733503943049/5000000000000000 : ℝ)^133 := by
      have hnat : (83262675363658974077 : ℕ)^32*5000000000000000^133 ≤ 5652733503943049^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83262675363658974077 50000000000000000000 5652733503943049 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5652733503943049/5000000000000000 : ℝ)) (X := (83262675363658974077/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(715317880252749/7673300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(590149127633349/7673300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (76733/100000 : ℝ)) (alpha := (715317880252749/7673300000000000 : ℝ)) (beta := (590149127633349/7673300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (76733/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(715317880252749/7673300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(590149127633349/7673300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_2 : ((1866414377/5000000000 : ℝ)*X 2 0+(407225941/625000000 : ℝ)*X 2 1+(-243541649/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-2199982431/10000000000 : ℝ)*X 0 0+(1251457997/2500000000 : ℝ)*X 0 1+(5539916827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((3264484599/5000000000 : ℝ)*X 1 0+(134931/10000000000 : ℝ)*X 1 1+(2624679063/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((389809207/1250000000 : ℝ)*X 2 0+(754275359/1000000000 : ℝ)*X 2 1+(-1642948071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((635982839/2000000000 : ℝ)*X 0 0+(4753861433/10000000000 : ℝ)*X 0 1+(499312297/1000000000 : ℝ)*X 0 2+(635982839/2000000000 : ℝ)*X 1 0+(4753861433/10000000000 : ℝ)*X 1 1+(499312297/1000000000 : ℝ)*X 1 2+(635982839/2000000000 : ℝ)*X 2 0+(4753861433/10000000000 : ℝ)*X 2 1+(499312297/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1153057713/10000000000 : ℝ)*X 0 0+(3558157257/10000000000 : ℝ)*X 0 1+(7490657221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((420677417/500000000 : ℝ)*X 1 0+(-385970719/10000000000 : ℝ)*X 1 1+(2814908811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((160285717/400000000 : ℝ)*X 2 0+(278430997/400000000 : ℝ)*X 2 1+(-716771423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((660805957/2500000000 : ℝ)*X 0 0+(1831080429/5000000000 : ℝ)*X 0 1+(6419940951/10000000000 : ℝ)*X 0 2+(660805957/2500000000 : ℝ)*X 1 0+(1831080429/5000000000 : ℝ)*X 1 1+(6419940951/10000000000 : ℝ)*X 1 2+(660805957/2500000000 : ℝ)*X 2 0+(1831080429/5000000000 : ℝ)*X 2 1+(6419940951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1678768627/10000000000 : ℝ)*X 0 0+(5777986459/10000000000 : ℝ)*X 0 1+(5144672757/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((966939111/1250000000 : ℝ)*X 1 0+(-13227/10000000000 : ℝ)*X 1 1+(96492899/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((3438160119/10000000000 : ℝ)*X 2 0+(1714379533/2500000000 : ℝ)*X 2 1+(-1148741517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((825615519/2000000000 : ℝ)*X 0 0+(4574630109/10000000000 : ℝ)*X 0 1+(4293493181/10000000000 : ℝ)*X 0 2+(825615519/2000000000 : ℝ)*X 1 0+(4574630109/10000000000 : ℝ)*X 1 1+(4293493181/10000000000 : ℝ)*X 1 2+(825615519/2000000000 : ℝ)*X 2 0+(4574630109/10000000000 : ℝ)*X 2 1+(4293493181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((41479/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41479/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (388034403972206716722091173/129172332200000000000000000000000 : ℝ) := by norm_num
    linear_combination (2356773/1000000000000 : ℝ)*(base19) + (652587/250000000000 : ℝ)*(base23) + (50190966221/500000000000 : ℝ)*(base40) + (443570316517/500000000000 : ℝ)*(base49) + (387777343857/1000000000000 : ℝ)*(base60) + (4204942238521/1000000000000 : ℝ)*(major_s2_0) + (4204942238521/1000000000000 : ℝ)*(major_s2_1) + (4204942238521/1000000000000 : ℝ)*(major_s2_2) + (5660239129621/1000000000000 : ℝ)*(sp_s2_7) + (1415064729649/250000000000 : ℝ)*(sp_s2_8) + (283012933251/50000000000 : ℝ)*(sp_s2_9) + (1374806089331/500000000000 : ℝ)*(sp_s2_13) + (2505417/250000000000 : ℝ)*(sp_s2_20) + (22145747/1000000000000 : ℝ)*(sp_s2_21) + (274962220033/100000000000 : ℝ)*(f.failure) + (5660261275369/1000000000000 : ℝ)*(f.sum) + (210139873452742431/17915620840000000000000000000000 : ℝ)*base62 + (4134943048030199/7673300000000000000000000000 : ℝ)*base65 + (35796024469761/93392000000000000000000000 : ℝ)*base67 + (4459391118996431/7673300000000000000000000000 : ℝ)*base68 + (93240157896270501147/129172332200000000000000000000000 : ℝ)*base71 + (95681605004661/177200000000000000000000000 : ℝ)*base72 + (348069098351503/1167400000000000000000000000 : ℝ)*base75 + (1468399448461957/1683400000000000000000000000 : ℝ)*base77 + (92288589525136191/517158200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (211/625000000000000 : ℝ)*base86 + (211/625000000000000 : ℝ)*base88 + (211/625000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((5139/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5139/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (120024615861238763392389357099/39683100160600000000000000000000000 : ℝ) := by norm_num
    linear_combination (82119/31250000000 : ℝ)*(base21) + (493003/500000000000 : ℝ)*(base33) + (90714231669/125000000000 : ℝ)*(base40) + (632470543179/1000000000000 : ℝ)*(base49) + (298077224101/500000000000 : ℝ)*(base60) + (2809868679957/1000000000000 : ℝ)*(major_s2_0) + (2809869665963/1000000000000 : ℝ)*(major_s2_1) + (2809869665963/1000000000000 : ℝ)*(major_s2_2) + (3309639/1000000000000 : ℝ)*(sp_s2_2) + (378235755241/100000000000 : ℝ)*(sp_s2_14) + (945585605097/250000000000 : ℝ)*(sp_s2_15) + (3782350628957/1000000000000 : ℝ)*(sp_s2_16) + (1837380771319/1000000000000 : ℝ)*(sp_s2_20) + (442063/31250000000 : ℝ)*(sp_s2_22) + (1837380771319/1000000000000 : ℝ)*(f.failure) + (378235755241/100000000000 : ℝ)*(f.sum) + (11208626344226621187/17915620840000000000000000000000 : ℝ)*base63 + (3149941599677673/7673300000000000000000000000 : ℝ)*base64 + (77892036900583/466960000000000000000000000 : ℝ)*base67 + (3280884814306487/7673300000000000000000000000 : ℝ)*base69 + (6877396223657887/41335146304000000000000000000 : ℝ)*base71 + (80043842460217/177200000000000000000000000 : ℝ)*base72 + (740125823146169/1167400000000000000000000000 : ℝ)*base75 + (159938281649571/1683400000000000000000000000 : ℝ)*base76 + (23402715647988331/258579100000000000000000000000 : ℝ)*base78 + (437/1562500000000000 : ℝ)*base86 + (437/1562500000000000 : ℝ)*base88 + (437/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22697/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22697/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (235708739265573931162677/20686328000000000000000000000 : ℝ) := by norm_num
    linear_combination (4213103/1000000000000 : ℝ)*(base11) + (723557838369/1000000000000 : ℝ)*(base40) + (117313767679/125000000000 : ℝ)*(base49) + (68919/20000000000 : ℝ)*(base50) + (4587369129823/1000000000000 : ℝ)*(major_s2_0) + (4587369129823/1000000000000 : ℝ)*(major_s2_1) + (4587369129823/1000000000000 : ℝ)*(major_s2_2) + (847419/250000000000 : ℝ)*(sp_s2_9) + (47365651/1000000000000 : ℝ)*(sp_s2_15) + (8900449/200000000000 : ℝ)*(sp_s2_16) + (3087519075789/500000000000 : ℝ)*(sp_s2_21) + (6174994999031/1000000000000 : ℝ)*(sp_s2_22) + (6174994472761/1000000000000 : ℝ)*(sp_s2_23) + (2999692096819/1000000000000 : ℝ)*(sp_s2_27) + (2999692096819/1000000000000 : ℝ)*(f.failure) + (3087521182341/500000000000 : ℝ)*(f.sum) + (10080639586446797139/17915620840000000000000000000000 : ℝ)*base63 + (280169371062863/7673300000000000000000000000 : ℝ)*base64 + (24588827520347/466960000000000000000000000 : ℝ)*base67 + (5979994043944663/7673300000000000000000000000 : ℝ)*base68 + (1973424558962672459/6798543800000000000000000000000 : ℝ)*base71 + (160801713582403/177200000000000000000000000 : ℝ)*base72 + (130459995685069/1167400000000000000000000000 : ℝ)*base75 + (33920232223991/88600000000000000000000000 : ℝ)*base76 + (18816164907079133/517158200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (563/1562500000000000 : ℝ)*base87 + (563/1562500000000000 : ℝ)*base89 + (563/1562500000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((8417/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8417/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((17511/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(17511/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76733/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76733/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((41479/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41479/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((5139/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5139/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22697/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22697/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305083_s2 p hpa hpb X hX hprev1

#print axioms solution
