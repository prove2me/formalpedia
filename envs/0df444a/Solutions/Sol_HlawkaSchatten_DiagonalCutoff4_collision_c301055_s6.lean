-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301055_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:33:06.97099+00:00
-- url     : https://prove2.me/submissions/90539deb-638d-4b1e-9dd2-53b0d9aa947b

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
theorem collision_support_c301055_s6_s6_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-905152531/5000000000 : ℝ)*x 0 + (2961341859/5000000000 : ℝ)*x 1 + (997179879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905152531/5000000000 : ℝ)^65 ≤ (10360602113043/100000000000000 : ℝ)^49 := by
    have hnat : (905152531 : ℕ)^65*100000000000000^49 ≤ 10360602113043^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905152531 5000000000 10360602113043 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2961341859/5000000000 : ℝ)^65 ≤ (24957948570629/50000000000000 : ℝ)^49 := by
    have hnat : (2961341859 : ℕ)^65*50000000000000^49 ≤ 24957948570629^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2961341859 5000000000 24957948570629 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (997179879/2000000000 : ℝ)^65 ≤ (19861750363323/50000000000000 : ℝ)^49 := by
    have hnat : (997179879 : ℕ)^65*50000000000000^49 ≤ 19861750363323^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997179879 2000000000 19861750363323 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-905152531/5000000000 : ℝ), (2961341859/5000000000 : ℝ), (997179879/2000000000 : ℝ)] ![(10360602113043/100000000000000 : ℝ), (24957948570629/50000000000000 : ℝ), (19861750363323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-905152531/5000000000 : ℝ)|^65 ≤ (10360602113043/100000000000000 : ℝ)^49
        have hw : |(-905152531/5000000000 : ℝ)|=(905152531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2961341859/5000000000 : ℝ)|^65 ≤ (24957948570629/50000000000000 : ℝ)^49
        have hw : |(2961341859/5000000000 : ℝ)|=(2961341859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(997179879/2000000000 : ℝ)|^65 ≤ (19861750363323/50000000000000 : ℝ)^49
        have hw : |(997179879/2000000000 : ℝ)|=(997179879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (612119637/1250000000 : ℝ)*x 0 + (-378888737/5000000000 : ℝ)*x 1 + (331398423/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (612119637/1250000000 : ℝ)^65 ≤ (38786245641093/100000000000000 : ℝ)^49 := by
    have hnat : (612119637 : ℕ)^65*100000000000000^49 ≤ 38786245641093^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612119637 1250000000 38786245641093 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378888737/5000000000 : ℝ)^65 ≤ (1631727969519/50000000000000 : ℝ)^49 := by
    have hnat : (378888737 : ℕ)^65*50000000000000^49 ≤ 1631727969519^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378888737 5000000000 1631727969519 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (331398423/500000000 : ℝ)^65 ≤ (11590059679489/20000000000000 : ℝ)^49 := by
    have hnat : (331398423 : ℕ)^65*20000000000000^49 ≤ 11590059679489^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331398423 500000000 11590059679489 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(612119637/1250000000 : ℝ), (-378888737/5000000000 : ℝ), (331398423/500000000 : ℝ)] ![(38786245641093/100000000000000 : ℝ), (1631727969519/50000000000000 : ℝ), (11590059679489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(612119637/1250000000 : ℝ)|^65 ≤ (38786245641093/100000000000000 : ℝ)^49
        have hw : |(612119637/1250000000 : ℝ)|=(612119637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-378888737/5000000000 : ℝ)|^65 ≤ (1631727969519/50000000000000 : ℝ)^49
        have hw : |(-378888737/5000000000 : ℝ)|=(378888737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(331398423/500000000 : ℝ)|^65 ≤ (11590059679489/20000000000000 : ℝ)^49
        have hw : |(331398423/500000000 : ℝ)|=(331398423/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4873885839/10000000000 : ℝ)*x 0 + (1508281077/2500000000 : ℝ)*x 1 + (-1802530177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4873885839/10000000000 : ℝ)^65 ≤ (7708805637251/20000000000000 : ℝ)^49 := by
    have hnat : (4873885839 : ℕ)^65*20000000000000^49 ≤ 7708805637251^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4873885839 10000000000 7708805637251 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1508281077/2500000000 : ℝ)^65 ≤ (51154354403369/100000000000000 : ℝ)^49 := by
    have hnat : (1508281077 : ℕ)^65*100000000000000^49 ≤ 51154354403369^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508281077 2500000000 51154354403369 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1802530177/10000000000 : ℝ)^65 ≤ (10301617388463/100000000000000 : ℝ)^49 := by
    have hnat : (1802530177 : ℕ)^65*100000000000000^49 ≤ 10301617388463^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802530177 10000000000 10301617388463 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4873885839/10000000000 : ℝ), (1508281077/2500000000 : ℝ), (-1802530177/10000000000 : ℝ)] ![(7708805637251/20000000000000 : ℝ), (51154354403369/100000000000000 : ℝ), (10301617388463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4873885839/10000000000 : ℝ)|^65 ≤ (7708805637251/20000000000000 : ℝ)^49
        have hw : |(4873885839/10000000000 : ℝ)|=(4873885839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1508281077/2500000000 : ℝ)|^65 ≤ (51154354403369/100000000000000 : ℝ)^49
        have hw : |(1508281077/2500000000 : ℝ)|=(1508281077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1802530177/10000000000 : ℝ)|^65 ≤ (10301617388463/100000000000000 : ℝ)^49
        have hw : |(-1802530177/10000000000 : ℝ)|=(1802530177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1568024929/2500000000 : ℝ)*x 0 + (399251791/1000000000 : ℝ)*x 1 + (2577765339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1568024929/2500000000 : ℝ)^65 ≤ (53859470839891/100000000000000 : ℝ)^49 := by
    have hnat : (1568024929 : ℕ)^65*100000000000000^49 ≤ 53859470839891^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568024929 2500000000 53859470839891 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399251791/1000000000 : ℝ)^65 ≤ (14791484905261/50000000000000 : ℝ)^49 := by
    have hnat : (399251791 : ℕ)^65*50000000000000^49 ≤ 14791484905261^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399251791 1000000000 14791484905261 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2577765339/10000000000 : ℝ)^65 ≤ (8278779669607/50000000000000 : ℝ)^49 := by
    have hnat : (2577765339 : ℕ)^65*50000000000000^49 ≤ 8278779669607^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577765339 10000000000 8278779669607 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1568024929/2500000000 : ℝ), (399251791/1000000000 : ℝ), (2577765339/10000000000 : ℝ)] ![(53859470839891/100000000000000 : ℝ), (14791484905261/50000000000000 : ℝ), (8278779669607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1568024929/2500000000 : ℝ)|^65 ≤ (53859470839891/100000000000000 : ℝ)^49
        have hw : |(1568024929/2500000000 : ℝ)|=(1568024929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(399251791/1000000000 : ℝ)|^65 ≤ (14791484905261/50000000000000 : ℝ)^49
        have hw : |(399251791/1000000000 : ℝ)|=(399251791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2577765339/10000000000 : ℝ)|^65 ≤ (8278779669607/50000000000000 : ℝ)^49
        have hw : |(2577765339/10000000000 : ℝ)|=(2577765339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-784616643/5000000000 : ℝ)*x 0 + (2269653687/5000000000 : ℝ)*x 1 + (6489904247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784616643/5000000000 : ℝ)^65 ≤ (1714292235313/20000000000000 : ℝ)^49 := by
    have hnat : (784616643 : ℕ)^65*20000000000000^49 ≤ 1714292235313^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784616643 5000000000 1714292235313 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269653687/5000000000 : ℝ)^65 ≤ (2192129518337/6250000000000 : ℝ)^49 := by
    have hnat : (2269653687 : ℕ)^65*6250000000000^49 ≤ 2192129518337^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269653687 5000000000 2192129518337 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6489904247/10000000000 : ℝ)^65 ≤ (56354466511441/100000000000000 : ℝ)^49 := by
    have hnat : (6489904247 : ℕ)^65*100000000000000^49 ≤ 56354466511441^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6489904247 10000000000 56354466511441 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-784616643/5000000000 : ℝ), (2269653687/5000000000 : ℝ), (6489904247/10000000000 : ℝ)] ![(1714292235313/20000000000000 : ℝ), (2192129518337/6250000000000 : ℝ), (56354466511441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-784616643/5000000000 : ℝ)|^65 ≤ (1714292235313/20000000000000 : ℝ)^49
        have hw : |(-784616643/5000000000 : ℝ)|=(784616643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2269653687/5000000000 : ℝ)|^65 ≤ (2192129518337/6250000000000 : ℝ)^49
        have hw : |(2269653687/5000000000 : ℝ)|=(2269653687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6489904247/10000000000 : ℝ)|^65 ≤ (56354466511441/100000000000000 : ℝ)^49
        have hw : |(6489904247/10000000000 : ℝ)|=(6489904247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3979543677/10000000000 : ℝ)*x 0 + (-31813/10000000000 : ℝ)*x 1 + (1537426801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3979543677/10000000000 : ℝ)^65 ≤ (29455512948737/100000000000000 : ℝ)^49 := by
    have hnat : (3979543677 : ℕ)^65*100000000000000^49 ≤ 29455512948737^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979543677 10000000000 29455512948737 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31813/10000000000 : ℝ)^65 ≤ (637451/12500000000000 : ℝ)^49 := by
    have hnat : (31813 : ℕ)^65*12500000000000^49 ≤ 637451^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31813 10000000000 637451 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1537426801/2000000000 : ℝ)^65 ≤ (70544481939141/100000000000000 : ℝ)^49 := by
    have hnat : (1537426801 : ℕ)^65*100000000000000^49 ≤ 70544481939141^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537426801 2000000000 70544481939141 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3979543677/10000000000 : ℝ), (-31813/10000000000 : ℝ), (1537426801/2000000000 : ℝ)] ![(29455512948737/100000000000000 : ℝ), (637451/12500000000000 : ℝ), (70544481939141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3979543677/10000000000 : ℝ)|^65 ≤ (29455512948737/100000000000000 : ℝ)^49
        have hw : |(3979543677/10000000000 : ℝ)|=(3979543677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31813/10000000000 : ℝ)|^65 ≤ (637451/12500000000000 : ℝ)^49
        have hw : |(-31813/10000000000 : ℝ)|=(31813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1537426801/2000000000 : ℝ)|^65 ≤ (70544481939141/100000000000000 : ℝ)^49
        have hw : |(1537426801/2000000000 : ℝ)|=(1537426801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3954483043/10000000000 : ℝ)*x 0 + (3688222727/5000000000 : ℝ)*x 1 + (-44194381/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3954483043/10000000000 : ℝ)^65 ≤ (5841941074361/20000000000000 : ℝ)^49 := by
    have hnat : (3954483043 : ℕ)^65*20000000000000^49 ≤ 5841941074361^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3954483043 10000000000 5841941074361 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3688222727/5000000000 : ℝ)^65 ≤ (66787498818099/100000000000000 : ℝ)^49 := by
    have hnat : (3688222727 : ℕ)^65*100000000000000^49 ≤ 66787498818099^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688222727 5000000000 66787498818099 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44194381/500000000 : ℝ)^65 ≤ (1000698949273/25000000000000 : ℝ)^49 := by
    have hnat : (44194381 : ℕ)^65*25000000000000^49 ≤ 1000698949273^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44194381 500000000 1000698949273 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3954483043/10000000000 : ℝ), (3688222727/5000000000 : ℝ), (-44194381/500000000 : ℝ)] ![(5841941074361/20000000000000 : ℝ), (66787498818099/100000000000000 : ℝ), (1000698949273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3954483043/10000000000 : ℝ)|^65 ≤ (5841941074361/20000000000000 : ℝ)^49
        have hw : |(3954483043/10000000000 : ℝ)|=(3954483043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3688222727/5000000000 : ℝ)|^65 ≤ (66787498818099/100000000000000 : ℝ)^49
        have hw : |(3688222727/5000000000 : ℝ)|=(3688222727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44194381/500000000 : ℝ)|^65 ≤ (1000698949273/25000000000000 : ℝ)^49
        have hw : |(-44194381/500000000 : ℝ)|=(44194381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (37822849/80000000 : ℝ)*x 0 + (3203656047/5000000000 : ℝ)*x 1 + (1429679923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37822849/80000000 : ℝ)^65 ≤ (37019638277373/100000000000000 : ℝ)^49 := by
    have hnat : (37822849 : ℕ)^65*100000000000000^49 ≤ 37019638277373^49*80000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37822849 80000000 37019638277373 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3203656047/5000000000 : ℝ)^65 ≤ (11081017238651/20000000000000 : ℝ)^49 := by
    have hnat : (3203656047 : ℕ)^65*20000000000000^49 ≤ 11081017238651^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3203656047 5000000000 11081017238651 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1429679923/10000000000 : ℝ)^65 ≤ (7575275510089/100000000000000 : ℝ)^49 := by
    have hnat : (1429679923 : ℕ)^65*100000000000000^49 ≤ 7575275510089^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429679923 10000000000 7575275510089 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(37822849/80000000 : ℝ), (3203656047/5000000000 : ℝ), (1429679923/10000000000 : ℝ)] ![(37019638277373/100000000000000 : ℝ), (11081017238651/20000000000000 : ℝ), (7575275510089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(37822849/80000000 : ℝ)|^65 ≤ (37019638277373/100000000000000 : ℝ)^49
        have hw : |(37822849/80000000 : ℝ)|=(37822849/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3203656047/5000000000 : ℝ)|^65 ≤ (11081017238651/20000000000000 : ℝ)^49
        have hw : |(3203656047/5000000000 : ℝ)|=(3203656047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1429679923/10000000000 : ℝ)|^65 ≤ (7575275510089/100000000000000 : ℝ)^49
        have hw : |(1429679923/10000000000 : ℝ)|=(1429679923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-62026507/1000000000 : ℝ)*x 0 + (2425995421/5000000000 : ℝ)*x 1 + (6734003813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62026507/1000000000 : ℝ)^65 ≤ (1251085134093/50000000000000 : ℝ)^49 := by
    have hnat : (62026507 : ℕ)^65*50000000000000^49 ≤ 1251085134093^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62026507 1000000000 1251085134093 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2425995421/5000000000 : ℝ)^65 ≤ (3831450585449/10000000000000 : ℝ)^49 := by
    have hnat : (2425995421 : ℕ)^65*10000000000000^49 ≤ 3831450585449^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2425995421 5000000000 3831450585449 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6734003813/10000000000 : ℝ)^65 ≤ (14795830964947/25000000000000 : ℝ)^49 := by
    have hnat : (6734003813 : ℕ)^65*25000000000000^49 ≤ 14795830964947^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6734003813 10000000000 14795830964947 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62026507/1000000000 : ℝ), (2425995421/5000000000 : ℝ), (6734003813/10000000000 : ℝ)] ![(1251085134093/50000000000000 : ℝ), (3831450585449/10000000000000 : ℝ), (14795830964947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62026507/1000000000 : ℝ)|^65 ≤ (1251085134093/50000000000000 : ℝ)^49
        have hw : |(-62026507/1000000000 : ℝ)|=(62026507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2425995421/5000000000 : ℝ)|^65 ≤ (3831450585449/10000000000000 : ℝ)^49
        have hw : |(2425995421/5000000000 : ℝ)|=(2425995421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6734003813/10000000000 : ℝ)|^65 ≤ (14795830964947/25000000000000 : ℝ)^49
        have hw : |(6734003813/10000000000 : ℝ)|=(6734003813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1765487303/5000000000 : ℝ)*x 0 + (-393200013/10000000000 : ℝ)*x 1 + (1585717527/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1765487303/5000000000 : ℝ)^65 ≤ (25134389404437/100000000000000 : ℝ)^49 := by
    have hnat : (1765487303 : ℕ)^65*100000000000000^49 ≤ 25134389404437^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765487303 5000000000 25134389404437 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393200013/10000000000 : ℝ)^65 ≤ (42713173381/3125000000000 : ℝ)^49 := by
    have hnat : (393200013 : ℕ)^65*3125000000000^49 ≤ 42713173381^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393200013 10000000000 42713173381 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1585717527/2000000000 : ℝ)^65 ≤ (2296837157551/3125000000000 : ℝ)^49 := by
    have hnat : (1585717527 : ℕ)^65*3125000000000^49 ≤ 2296837157551^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585717527 2000000000 2296837157551 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1765487303/5000000000 : ℝ), (-393200013/10000000000 : ℝ), (1585717527/2000000000 : ℝ)] ![(25134389404437/100000000000000 : ℝ), (42713173381/3125000000000 : ℝ), (2296837157551/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1765487303/5000000000 : ℝ)|^65 ≤ (25134389404437/100000000000000 : ℝ)^49
        have hw : |(1765487303/5000000000 : ℝ)|=(1765487303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-393200013/10000000000 : ℝ)|^65 ≤ (42713173381/3125000000000 : ℝ)^49
        have hw : |(-393200013/10000000000 : ℝ)|=(393200013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1585717527/2000000000 : ℝ)|^65 ≤ (2296837157551/3125000000000 : ℝ)^49
        have hw : |(1585717527/2000000000 : ℝ)|=(1585717527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6624249721/10000000000 : ℝ)*x 0 + (621461243/1250000000 : ℝ)*x 1 + (-19484009/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6624249721/10000000000 : ℝ)^65 ≤ (1158143429577/2000000000000 : ℝ)^49 := by
    have hnat : (6624249721 : ℕ)^65*2000000000000^49 ≤ 1158143429577^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6624249721 10000000000 1158143429577 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621461243/1250000000 : ℝ)^65 ≤ (7914679064529/20000000000000 : ℝ)^49 := by
    have hnat : (621461243 : ℕ)^65*20000000000000^49 ≤ 7914679064529^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621461243 1250000000 7914679064529 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19484009/312500000 : ℝ)^65 ≤ (157464574531/6250000000000 : ℝ)^49 := by
    have hnat : (19484009 : ℕ)^65*6250000000000^49 ≤ 157464574531^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19484009 312500000 157464574531 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6624249721/10000000000 : ℝ), (621461243/1250000000 : ℝ), (-19484009/312500000 : ℝ)] ![(1158143429577/2000000000000 : ℝ), (7914679064529/20000000000000 : ℝ), (157464574531/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6624249721/10000000000 : ℝ)|^65 ≤ (1158143429577/2000000000000 : ℝ)^49
        have hw : |(6624249721/10000000000 : ℝ)|=(6624249721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(621461243/1250000000 : ℝ)|^65 ≤ (7914679064529/20000000000000 : ℝ)^49
        have hw : |(621461243/1250000000 : ℝ)|=(621461243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19484009/312500000 : ℝ)|^65 ≤ (157464574531/6250000000000 : ℝ)^49
        have hw : |(-19484009/312500000 : ℝ)|=(19484009/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (513812869/625000000 : ℝ)*x 0 + (171640969/625000000 : ℝ)*x 1 + (512792397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513812869/625000000 : ℝ)^65 ≤ (38558076404063/50000000000000 : ℝ)^49 := by
    have hnat : (513812869 : ℕ)^65*50000000000000^49 ≤ 38558076404063^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513812869 625000000 38558076404063 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171640969/625000000 : ℝ)^65 ≤ (18008298299783/100000000000000 : ℝ)^49 := by
    have hnat : (171640969 : ℕ)^65*100000000000000^49 ≤ 18008298299783^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171640969 625000000 18008298299783 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512792397/5000000000 : ℝ)^65 ≤ (4875548885439/100000000000000 : ℝ)^49 := by
    have hnat : (512792397 : ℕ)^65*100000000000000^49 ≤ 4875548885439^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512792397 5000000000 4875548885439 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(513812869/625000000 : ℝ), (171640969/625000000 : ℝ), (512792397/5000000000 : ℝ)] ![(38558076404063/50000000000000 : ℝ), (18008298299783/100000000000000 : ℝ), (4875548885439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(513812869/625000000 : ℝ)|^65 ≤ (38558076404063/50000000000000 : ℝ)^49
        have hw : |(513812869/625000000 : ℝ)|=(513812869/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171640969/625000000 : ℝ)|^65 ≤ (18008298299783/100000000000000 : ℝ)^49
        have hw : |(171640969/625000000 : ℝ)|=(171640969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(512792397/5000000000 : ℝ)|^65 ≤ (4875548885439/100000000000000 : ℝ)^49
        have hw : |(512792397/5000000000 : ℝ)|=(512792397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-862611537/10000000000 : ℝ)*x 0 + (145004159/200000000 : ℝ)*x 1 + (4120651071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862611537/10000000000 : ℝ)^65 ≤ (775097549851/20000000000000 : ℝ)^49 := by
    have hnat : (862611537 : ℕ)^65*20000000000000^49 ≤ 775097549851^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862611537 10000000000 775097549851 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145004159/200000000 : ℝ)^65 ≤ (8159445151449/12500000000000 : ℝ)^49 := by
    have hnat : (145004159 : ℕ)^65*12500000000000^49 ≤ 8159445151449^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145004159 200000000 8159445151449 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4120651071/10000000000 : ℝ)^65 ≤ (30848951029547/100000000000000 : ℝ)^49 := by
    have hnat : (4120651071 : ℕ)^65*100000000000000^49 ≤ 30848951029547^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4120651071 10000000000 30848951029547 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-862611537/10000000000 : ℝ), (145004159/200000000 : ℝ), (4120651071/10000000000 : ℝ)] ![(775097549851/20000000000000 : ℝ), (8159445151449/12500000000000 : ℝ), (30848951029547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-862611537/10000000000 : ℝ)|^65 ≤ (775097549851/20000000000000 : ℝ)^49
        have hw : |(-862611537/10000000000 : ℝ)|=(862611537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(145004159/200000000 : ℝ)|^65 ≤ (8159445151449/12500000000000 : ℝ)^49
        have hw : |(145004159/200000000 : ℝ)|=(145004159/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4120651071/10000000000 : ℝ)|^65 ≤ (30848951029547/100000000000000 : ℝ)^49
        have hw : |(4120651071/10000000000 : ℝ)|=(4120651071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6681323957/10000000000 : ℝ)*x 0 + (-42993299/10000000000 : ℝ)*x 1 + (5139738173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6681323957/10000000000 : ℝ)^65 ≤ (58569940728501/100000000000000 : ℝ)^49 := by
    have hnat : (6681323957 : ℕ)^65*100000000000000^49 ≤ 58569940728501^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6681323957 10000000000 58569940728501 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42993299/10000000000 : ℝ)^65 ≤ (72549375081/100000000000000 : ℝ)^49 := by
    have hnat : (42993299 : ℕ)^65*100000000000000^49 ≤ 72549375081^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42993299 10000000000 72549375081 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139738173/10000000000 : ℝ)^65 ≤ (41357509889127/100000000000000 : ℝ)^49 := by
    have hnat : (5139738173 : ℕ)^65*100000000000000^49 ≤ 41357509889127^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139738173 10000000000 41357509889127 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6681323957/10000000000 : ℝ), (-42993299/10000000000 : ℝ), (5139738173/10000000000 : ℝ)] ![(58569940728501/100000000000000 : ℝ), (72549375081/100000000000000 : ℝ), (41357509889127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6681323957/10000000000 : ℝ)|^65 ≤ (58569940728501/100000000000000 : ℝ)^49
        have hw : |(6681323957/10000000000 : ℝ)|=(6681323957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42993299/10000000000 : ℝ)|^65 ≤ (72549375081/100000000000000 : ℝ)^49
        have hw : |(-42993299/10000000000 : ℝ)|=(42993299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139738173/10000000000 : ℝ)|^65 ≤ (41357509889127/100000000000000 : ℝ)^49
        have hw : |(5139738173/10000000000 : ℝ)|=(5139738173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3245122089/10000000000 : ℝ)*x 0 + (1519003031/2000000000 : ℝ)*x 1 + (-1504160183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3245122089/10000000000 : ℝ)^65 ≤ (224715491543/1000000000000 : ℝ)^49 := by
    have hnat : (3245122089 : ℕ)^65*1000000000000^49 ≤ 224715491543^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3245122089 10000000000 224715491543 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1519003031/2000000000 : ℝ)^65 ≤ (1388505440261/2000000000000 : ℝ)^49 := by
    have hnat : (1519003031 : ℕ)^65*2000000000000^49 ≤ 1388505440261^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519003031 2000000000 1388505440261 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1504160183/10000000000 : ℝ)^65 ≤ (810317882221/10000000000000 : ℝ)^49 := by
    have hnat : (1504160183 : ℕ)^65*10000000000000^49 ≤ 810317882221^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504160183 10000000000 810317882221 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3245122089/10000000000 : ℝ), (1519003031/2000000000 : ℝ), (-1504160183/10000000000 : ℝ)] ![(224715491543/1000000000000 : ℝ), (1388505440261/2000000000000 : ℝ), (810317882221/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3245122089/10000000000 : ℝ)|^65 ≤ (224715491543/1000000000000 : ℝ)^49
        have hw : |(3245122089/10000000000 : ℝ)|=(3245122089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1519003031/2000000000 : ℝ)|^65 ≤ (1388505440261/2000000000000 : ℝ)^49
        have hw : |(1519003031/2000000000 : ℝ)|=(1519003031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1504160183/10000000000 : ℝ)|^65 ≤ (810317882221/10000000000000 : ℝ)^49
        have hw : |(-1504160183/10000000000 : ℝ)|=(1504160183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s6_s6_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8065570701/10000000000 : ℝ)*x 0 + (1153431247/5000000000 : ℝ)*x 1 + (1831536953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8065570701/10000000000 : ℝ)^65 ≤ (1879700314129/2500000000000 : ℝ)^49 := by
    have hnat : (8065570701 : ℕ)^65*2500000000000^49 ≤ 1879700314129^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8065570701 10000000000 1879700314129 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1153431247/5000000000 : ℝ)^65 ≤ (14289887065033/100000000000000 : ℝ)^49 := by
    have hnat : (1153431247 : ℕ)^65*100000000000000^49 ≤ 14289887065033^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153431247 5000000000 14289887065033 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1831536953/10000000000 : ℝ)^65 ≤ (2104420072083/20000000000000 : ℝ)^49 := by
    have hnat : (1831536953 : ℕ)^65*20000000000000^49 ≤ 2104420072083^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831536953 10000000000 2104420072083 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8065570701/10000000000 : ℝ), (1153431247/5000000000 : ℝ), (1831536953/10000000000 : ℝ)] ![(1879700314129/2500000000000 : ℝ), (14289887065033/100000000000000 : ℝ), (2104420072083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8065570701/10000000000 : ℝ)|^65 ≤ (1879700314129/2500000000000 : ℝ)^49
        have hw : |(8065570701/10000000000 : ℝ)|=(8065570701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1153431247/5000000000 : ℝ)|^65 ≤ (14289887065033/100000000000000 : ℝ)^49
        have hw : |(1153431247/5000000000 : ℝ)|=(1153431247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1831536953/10000000000 : ℝ)|^65 ≤ (2104420072083/20000000000000 : ℝ)^49
        have hw : |(1831536953/10000000000 : ℝ)|=(1831536953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301055_s6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((74259/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74259/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(73129/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(73129/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74103/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74103/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31961/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31961/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63987/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63987/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65421/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65421/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (74259/100000 : ℝ) ^ (129/32 : ℝ) ≤ (6025419535044481337/20000000000000000000 : ℝ) := by
    have hpowers : (74259/100000 : ℝ)^129 ≤ (6025419535044481337/20000000000000000000 : ℝ)^32 := by
      have hnat : (74259 : ℕ)^129*20000000000000000000^32 ≤ 6025419535044481337^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74259 100000 6025419535044481337 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74259/100000 : ℝ)) (X := (6025419535044481337/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner0a : (26025419535044481337/20000000000000000000 : ℝ) ≤ (427002368801961/400000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (26025419535044481337/20000000000000000000 : ℝ)^32 ≤ (427002368801961/400000000000000 : ℝ)^129 := by
      have hnat : (26025419535044481337 : ℕ)^32*400000000000000^129 ≤ 427002368801961^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26025419535044481337 20000000000000000000 427002368801961 400000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (427002368801961/400000000000000 : ℝ)) (X := (26025419535044481337/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner0b : (16025419535044481337/10000000000000000000 : ℝ) ≤ (11241012597463141/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (16025419535044481337/10000000000000000000 : ℝ)^32 ≤ (11241012597463141/10000000000000000 : ℝ)^129 := by
      have hnat : (16025419535044481337 : ℕ)^32*10000000000000000^129 ≤ 11241012597463141^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16025419535044481337 10000000000000000000 11241012597463141 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11241012597463141/10000000000000000 : ℝ)) (X := (16025419535044481337/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27002368801961/297036000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(141488344353529/1856475000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (74259/100000 : ℝ)) (alpha := (27002368801961/297036000000000 : ℝ)) (beta := (141488344353529/1856475000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (74259/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27002368801961/297036000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(141488344353529/1856475000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (73129/100000 : ℝ) ^ (129/32 : ℝ) ≤ (2832117972091288619/10000000000000000000 : ℝ) := by
    have hpowers : (73129/100000 : ℝ)^129 ≤ (2832117972091288619/10000000000000000000 : ℝ)^32 := by
      have hnat : (73129 : ℕ)^129*10000000000000000000^32 ≤ 2832117972091288619^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73129 100000 2832117972091288619 10000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73129/100000 : ℝ)) (X := (2832117972091288619/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner1a : (12832117972091288619/10000000000000000000 : ℝ) ≤ (5319057801123773/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (12832117972091288619/10000000000000000000 : ℝ)^32 ≤ (5319057801123773/5000000000000000 : ℝ)^129 := by
      have hnat : (12832117972091288619 : ℕ)^32*5000000000000000^129 ≤ 5319057801123773^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12832117972091288619 10000000000000000000 5319057801123773 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5319057801123773/5000000000000000 : ℝ)) (X := (12832117972091288619/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner1b : (7832117972091288619/5000000000000000000 : ℝ) ≤ (11177625969865177/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (7832117972091288619/5000000000000000000 : ℝ)^32 ≤ (11177625969865177/10000000000000000 : ℝ)^129 := by
      have hnat : (7832117972091288619 : ℕ)^32*10000000000000000^129 ≤ 11177625969865177^129*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7832117972091288619 5000000000000000000 11177625969865177 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11177625969865177/10000000000000000 : ℝ)) (X := (7832117972091288619/5000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(319057801123773/3656450000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(539510367617631/7312900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (73129/100000 : ℝ)) (alpha := (319057801123773/3656450000000000 : ℝ)) (beta := (539510367617631/7312900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (73129/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(319057801123773/3656450000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(539510367617631/7312900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (74103/100000 : ℝ) ^ (129/32 : ℝ) ≤ (14936386200890140293/50000000000000000000 : ℝ) := by
    have hpowers : (74103/100000 : ℝ)^129 ≤ (14936386200890140293/50000000000000000000 : ℝ)^32 := by
      have hnat : (74103 : ℕ)^129*50000000000000000000^32 ≤ 14936386200890140293^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74103 100000 14936386200890140293 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74103/100000 : ℝ)) (X := (14936386200890140293/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner2a : (64936386200890140293/50000000000000000000 : ℝ) ≤ (213397598248203/200000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (64936386200890140293/50000000000000000000 : ℝ)^32 ≤ (213397598248203/200000000000000 : ℝ)^129 := by
      have hnat : (64936386200890140293 : ℕ)^32*200000000000000^129 ≤ 213397598248203^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64936386200890140293 50000000000000000000 213397598248203 200000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (213397598248203/200000000000000 : ℝ)) (X := (64936386200890140293/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner2b : (39936386200890140293/25000000000000000000 : ℝ) ≤ (11232151352927769/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (39936386200890140293/25000000000000000000 : ℝ)^32 ≤ (11232151352927769/10000000000000000 : ℝ)^129 := by
      have hnat : (39936386200890140293 : ℕ)^32*10000000000000000^129 ≤ 11232151352927769^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39936386200890140293 25000000000000000000 11232151352927769 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11232151352927769/10000000000000000 : ℝ)) (X := (39936386200890140293/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(13397598248203/148206000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(187423813505873/2470100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (74103/100000 : ℝ)) (alpha := (13397598248203/148206000000000 : ℝ)) (beta := (187423813505873/2470100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (74103/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(13397598248203/148206000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(187423813505873/2470100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-905152531/5000000000 : ℝ)*X 0 0+(2961341859/5000000000 : ℝ)*X 0 1+(997179879/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((612119637/1250000000 : ℝ)*X 1 0+(-378888737/5000000000 : ℝ)*X 1 1+(331398423/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((4873885839/10000000000 : ℝ)*X 2 0+(1508281077/2500000000 : ℝ)*X 2 1+(-1802530177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((1568024929/2500000000 : ℝ)*X 0 0+(399251791/1000000000 : ℝ)*X 0 1+(2577765339/10000000000 : ℝ)*X 0 2+(1568024929/2500000000 : ℝ)*X 1 0+(399251791/1000000000 : ℝ)*X 1 1+(2577765339/10000000000 : ℝ)*X 1 2+(1568024929/2500000000 : ℝ)*X 2 0+(399251791/1000000000 : ℝ)*X 2 1+(2577765339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-784616643/5000000000 : ℝ)*X 0 0+(2269653687/5000000000 : ℝ)*X 0 1+(6489904247/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((3979543677/10000000000 : ℝ)*X 1 0+(-31813/10000000000 : ℝ)*X 1 1+(1537426801/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((3954483043/10000000000 : ℝ)*X 2 0+(3688222727/5000000000 : ℝ)*X 2 1+(-44194381/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((37822849/80000000 : ℝ)*X 0 0+(3203656047/5000000000 : ℝ)*X 0 1+(1429679923/10000000000 : ℝ)*X 0 2+(37822849/80000000 : ℝ)*X 1 0+(3203656047/5000000000 : ℝ)*X 1 1+(1429679923/10000000000 : ℝ)*X 1 2+(37822849/80000000 : ℝ)*X 2 0+(3203656047/5000000000 : ℝ)*X 2 1+(1429679923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-62026507/1000000000 : ℝ)*X 0 0+(2425995421/5000000000 : ℝ)*X 0 1+(6734003813/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((1765487303/5000000000 : ℝ)*X 1 0+(-393200013/10000000000 : ℝ)*X 1 1+(1585717527/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((6624249721/10000000000 : ℝ)*X 2 0+(621461243/1250000000 : ℝ)*X 2 1+(-19484009/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((513812869/625000000 : ℝ)*X 0 0+(171640969/625000000 : ℝ)*X 0 1+(512792397/5000000000 : ℝ)*X 0 2+(513812869/625000000 : ℝ)*X 1 0+(171640969/625000000 : ℝ)*X 1 1+(512792397/5000000000 : ℝ)*X 1 2+(513812869/625000000 : ℝ)*X 2 0+(171640969/625000000 : ℝ)*X 2 1+(512792397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-862611537/10000000000 : ℝ)*X 0 0+(145004159/200000000 : ℝ)*X 0 1+(4120651071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((6681323957/10000000000 : ℝ)*X 1 0+(-42993299/10000000000 : ℝ)*X 1 1+(5139738173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((3245122089/10000000000 : ℝ)*X 2 0+(1519003031/2000000000 : ℝ)*X 2 1+(-1504160183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((8065570701/10000000000 : ℝ)*X 0 0+(1153431247/5000000000 : ℝ)*X 0 1+(1831536953/10000000000 : ℝ)*X 0 2+(8065570701/10000000000 : ℝ)*X 1 0+(1153431247/5000000000 : ℝ)*X 1 1+(1831536953/10000000000 : ℝ)*X 1 2+(8065570701/10000000000 : ℝ)*X 2 0+(1153431247/5000000000 : ℝ)*X 2 1+(1831536953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((31961/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31961/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10833043138988827823302337424469/745213582433950000000000000000000000 : ℝ) := by norm_num
    linear_combination (33947773517/100000000000 : ℝ)*(base7) + (27861/12500000000 : ℝ)*(base49) + (165139/125000000000 : ℝ)*(base60) + (2937678914103/1000000000000 : ℝ)*(major_s6_0) + (2937678914103/1000000000000 : ℝ)*(major_s6_1) + (2937678914103/1000000000000 : ℝ)*(major_s6_2) + (12120121/500000000000 : ℝ)*(sp_s6_0) + (992239/250000000000 : ℝ)*(sp_s6_6) + (1840113970891/500000000000 : ℝ)*(sp_s6_7) + (368031707519/100000000000 : ℝ)*(sp_s6_8) + (3680298517369/1000000000000 : ℝ)*(sp_s6_9) + (1162705878707/500000000000 : ℝ)*(sp_s6_13) + (32446583/500000000000 : ℝ)*(sp_s6_14) + (18557821/1000000000000 : ℝ)*(sp_s6_23) + (2482422489/1250000000 : ℝ)*(f.failure) + (368031707519/100000000000 : ℝ)*(f.sum) + (7733001020178212139/22579492862500000000000000000000 : ℝ)*base62 + (117519264685801/2470100000000000000000000000 : ℝ)*base64 + (4108811300181313/7312900000000000000000000000 : ℝ)*base66 + (207514580676561/247010000000000000000000000 : ℝ)*base68 + (7458736016248926713/15285596325000000000000000000000 : ℝ)*base71 + (387965685521341/618825000000000000000000000 : ℝ)*base72 + (1554479272831771/3656450000000000000000000000 : ℝ)*base74 + (250320569336137/495060000000000000000000000 : ℝ)*base76 + (18800049181224307/7240648548000000000000000000000 : ℝ)*base78 + (39/125000000000000 : ℝ)*base86 + (39/125000000000000 : ℝ)*base88 + (39/125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63987/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63987/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (94991784189015082610340537/18063594290000000000000000000000 : ℝ) := by norm_num
    linear_combination (141825773263/500000000000 : ℝ)*(base7) + (1507089/500000000000 : ℝ)*(base27) + (255413998107/100000000000 : ℝ)*(major_s6_0) + (255413998107/100000000000 : ℝ)*(major_s6_1) + (255413998107/100000000000 : ℝ)*(major_s6_2) + (6631767/1000000000000 : ℝ)*(sp_s6_0) + (6575997/1000000000000 : ℝ)*(sp_s6_2) + (3304791/50000000000 : ℝ)*(sp_s6_8) + (320690171831/100000000000 : ℝ)*(sp_s6_14) + (3206842860693/1000000000000 : ℝ)*(sp_s6_15) + (801725595129/250000000000 : ℝ)*(sp_s6_16) + (2010285242767/1000000000000 : ℝ)*(sp_s6_20) + (121287/200000000000 : ℝ)*(sp_s6_21) + (20208721/1000000000000 : ℝ)*(sp_s6_27) + (1726656919141/1000000000000 : ℝ)*(f.failure) + (3206908956513/1000000000000 : ℝ)*(f.sum) + (30708324756019327/70560915195312500000000000000 : ℝ)*base63 + (137378504953093/247010000000000000000000000 : ℝ)*base65 + (86076262823661/182822500000000000000000000 : ℝ)*base67 + (90423135314563/247010000000000000000000000 : ℝ)*base69 + (367519705653511313/2038079510000000000000000000000 : ℝ)*base71 + (5507681436249/41255000000000000000000000 : ℝ)*base72 + (24122563503369/73129000000000000000000000 : ℝ)*base75 + (1395775317347/82510000000000000000000000 : ℝ)*base76 + (680556491323667919/6033873790000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (3321/25000000000000000 : ℝ)*base87 + (3321/25000000000000000 : ℝ)*base89 + (3321/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65421/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65421/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (284501067728068731190491018097/44712814946037000000000000000000000 : ℝ) := by norm_num
    linear_combination (224434549053/500000000000 : ℝ)*(base7) + (6468394011/100000000000 : ℝ)*(base40) + (977647/1000000000000 : ℝ)*(base43) + (177401/500000000000 : ℝ)*(base59) + (121181147371/50000000000 : ℝ)*(major_s6_0) + (605905492443/250000000000 : ℝ)*(major_s6_1) + (121181147371/50000000000 : ℝ)*(major_s6_2) + (373367/500000000000 : ℝ)*(sp_s6_1) + (11067221/250000000000 : ℝ)*(sp_s6_9) + (18215767/1000000000000 : ℝ)*(sp_s6_20) + (2932341938281/1000000000000 : ℝ)*(sp_s6_21) + (586468433839/200000000000 : ℝ)*(sp_s6_22) + (2932297669397/1000000000000 : ℝ)*(sp_s6_23) + (2087275308003/1000000000000 : ℝ)*(sp_s6_27) + (25600381651/15625000000 : ℝ)*(f.failure) + (2932342915929/1000000000000 : ℝ)*(f.sum) + (408421814488046839/135476957175000000000000000000000 : ℝ)*base63 + (33305293542617/123505000000000000000000000 : ℝ)*base64 + (1169514205791887/1828225000000000000000000000 : ℝ)*base67 + (5249195507273/14820600000000000000000000 : ℝ)*base69 + (10554146945901791467/18342715590000000000000000000000 : ℝ)*base70 + (878525533207/1450371093750000000000000 : ℝ)*base73 + (526500762420859/914112500000000000000000000 : ℝ)*base75 + (43185232469011/742590000000000000000000000 : ℝ)*base77 + (5499033495006548927/33940540068750000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (613/781250000000000 : ℝ)*base86 + (673/3125000000000000 : ℝ)*base89 + (613/781250000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((74259/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74259/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(73129/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(73129/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74103/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74103/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31961/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31961/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63987/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63987/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65421/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65421/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301055_s6 p hpa hpb X hX hprev5

#print axioms solution
