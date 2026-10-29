-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:46:56.872361+00:00
-- url     : https://prove2.me/submissions/12564bc5-2402-4b71-b26c-e1d56bc275d1

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
theorem collision_support_c314055_s2_s2_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-393087799/2000000000 : ℝ)*x 0 + (5637930563/10000000000 : ℝ)*x 1 + (955307497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393087799/2000000000 : ℝ)^75 ≤ (12643152707653/100000000000000 : ℝ)^59 := by
    have hnat : (393087799 : ℕ)^75*100000000000000^59 ≤ 12643152707653^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393087799 2000000000 12643152707653 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5637930563/10000000000 : ℝ)^75 ≤ (48264383844193/100000000000000 : ℝ)^59 := by
    have hnat : (5637930563 : ℕ)^75*100000000000000^59 ≤ 48264383844193^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5637930563 10000000000 48264383844193 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955307497/2000000000 : ℝ)^75 ≤ (7818492685647/20000000000000 : ℝ)^59 := by
    have hnat : (955307497 : ℕ)^75*20000000000000^59 ≤ 7818492685647^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955307497 2000000000 7818492685647 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393087799/2000000000 : ℝ), (5637930563/10000000000 : ℝ), (955307497/2000000000 : ℝ)] ![(12643152707653/100000000000000 : ℝ), (48264383844193/100000000000000 : ℝ), (7818492685647/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393087799/2000000000 : ℝ)|^75 ≤ (12643152707653/100000000000000 : ℝ)^59
        have hw : |(-393087799/2000000000 : ℝ)|=(393087799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5637930563/10000000000 : ℝ)|^75 ≤ (48264383844193/100000000000000 : ℝ)^59
        have hw : |(5637930563/10000000000 : ℝ)|=(5637930563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(955307497/2000000000 : ℝ)|^75 ≤ (7818492685647/20000000000000 : ℝ)^59
        have hw : |(955307497/2000000000 : ℝ)|=(955307497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4754509291/10000000000 : ℝ)*x 0 + (2831902111/5000000000 : ℝ)*x 1 + (-61218461/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4754509291/10000000000 : ℝ)^75 ≤ (19431715750199/50000000000000 : ℝ)^59 := by
    have hnat : (4754509291 : ℕ)^75*50000000000000^59 ≤ 19431715750199^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4754509291 10000000000 19431715750199 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2831902111/5000000000 : ℝ)^75 ≤ (24273060461551/50000000000000 : ℝ)^59 := by
    have hnat : (2831902111 : ℕ)^75*50000000000000^59 ≤ 24273060461551^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831902111 5000000000 24273060461551 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61218461/312500000 : ℝ)^75 ≤ (6295223778059/50000000000000 : ℝ)^59 := by
    have hnat : (61218461 : ℕ)^75*50000000000000^59 ≤ 6295223778059^59*312500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61218461 312500000 6295223778059 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4754509291/10000000000 : ℝ), (2831902111/5000000000 : ℝ), (-61218461/312500000 : ℝ)] ![(19431715750199/50000000000000 : ℝ), (24273060461551/50000000000000 : ℝ), (6295223778059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4754509291/10000000000 : ℝ)|^75 ≤ (19431715750199/50000000000000 : ℝ)^59
        have hw : |(4754509291/10000000000 : ℝ)|=(4754509291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2831902111/5000000000 : ℝ)|^75 ≤ (24273060461551/50000000000000 : ℝ)^59
        have hw : |(2831902111/5000000000 : ℝ)|=(2831902111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61218461/312500000 : ℝ)|^75 ≤ (6295223778059/50000000000000 : ℝ)^59
        have hw : |(-61218461/312500000 : ℝ)|=(61218461/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1617756287/10000000000 : ℝ)*x 0 + (985885673/2000000000 : ℝ)*x 1 + (5745555643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1617756287/10000000000 : ℝ)^75 ≤ (9871452374663/100000000000000 : ℝ)^59 := by
    have hnat : (1617756287 : ℕ)^75*100000000000000^59 ≤ 9871452374663^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617756287 10000000000 9871452374663 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (985885673/2000000000 : ℝ)^75 ≤ (20344974816013/50000000000000 : ℝ)^59 := by
    have hnat : (985885673 : ℕ)^75*50000000000000^59 ≤ 20344974816013^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985885673 2000000000 20344974816013 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5745555643/10000000000 : ℝ)^75 ≤ (1977543918901/4000000000000 : ℝ)^59 := by
    have hnat : (5745555643 : ℕ)^75*4000000000000^59 ≤ 1977543918901^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5745555643 10000000000 1977543918901 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1617756287/10000000000 : ℝ), (985885673/2000000000 : ℝ), (5745555643/10000000000 : ℝ)] ![(9871452374663/100000000000000 : ℝ), (20344974816013/50000000000000 : ℝ), (1977543918901/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1617756287/10000000000 : ℝ)|^75 ≤ (9871452374663/100000000000000 : ℝ)^59
        have hw : |(-1617756287/10000000000 : ℝ)|=(1617756287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(985885673/2000000000 : ℝ)|^75 ≤ (20344974816013/50000000000000 : ℝ)^59
        have hw : |(985885673/2000000000 : ℝ)|=(985885673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5745555643/10000000000 : ℝ)|^75 ≤ (1977543918901/4000000000000 : ℝ)^59
        have hw : |(5745555643/10000000000 : ℝ)|=(5745555643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2295004427/5000000000 : ℝ)*x 0 + (-353453981/10000000000 : ℝ)*x 1 + (681419623/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2295004427/5000000000 : ℝ)^75 ≤ (37162244503093/100000000000000 : ℝ)^59 := by
    have hnat : (2295004427 : ℕ)^75*100000000000000^59 ≤ 37162244503093^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295004427 5000000000 37162244503093 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (353453981/10000000000 : ℝ)^75 ≤ (713888591899/50000000000000 : ℝ)^59 := by
    have hnat : (353453981 : ℕ)^75*50000000000000^59 ≤ 713888591899^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353453981 10000000000 713888591899 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681419623/1000000000 : ℝ)^75 ≤ (61409978301589/100000000000000 : ℝ)^59 := by
    have hnat : (681419623 : ℕ)^75*100000000000000^59 ≤ 61409978301589^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681419623 1000000000 61409978301589 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2295004427/5000000000 : ℝ), (-353453981/10000000000 : ℝ), (681419623/1000000000 : ℝ)] ![(37162244503093/100000000000000 : ℝ), (713888591899/50000000000000 : ℝ), (61409978301589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2295004427/5000000000 : ℝ)|^75 ≤ (37162244503093/100000000000000 : ℝ)^59
        have hw : |(2295004427/5000000000 : ℝ)|=(2295004427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-353453981/10000000000 : ℝ)|^75 ≤ (713888591899/50000000000000 : ℝ)^59
        have hw : |(-353453981/10000000000 : ℝ)|=(353453981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681419623/1000000000 : ℝ)|^75 ≤ (61409978301589/100000000000000 : ℝ)^59
        have hw : |(681419623/1000000000 : ℝ)|=(681419623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4576118123/10000000000 : ℝ)*x 0 + (644955867/1000000000 : ℝ)*x 1 + (-210548069/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4576118123/10000000000 : ℝ)^75 ≤ (18509670251191/50000000000000 : ℝ)^59 := by
    have hnat : (4576118123 : ℕ)^75*50000000000000^59 ≤ 18509670251191^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4576118123 10000000000 18509670251191 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (644955867/1000000000 : ℝ)^75 ≤ (57263398053861/100000000000000 : ℝ)^59 := by
    have hnat : (644955867 : ℕ)^75*100000000000000^59 ≤ 57263398053861^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644955867 1000000000 57263398053861 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210548069/2000000000 : ℝ)^75 ≤ (35732883933/625000000000 : ℝ)^59 := by
    have hnat : (210548069 : ℕ)^75*625000000000^59 ≤ 35732883933^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210548069 2000000000 35732883933 625000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4576118123/10000000000 : ℝ), (644955867/1000000000 : ℝ), (-210548069/2000000000 : ℝ)] ![(18509670251191/50000000000000 : ℝ), (57263398053861/100000000000000 : ℝ), (35732883933/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4576118123/10000000000 : ℝ)|^75 ≤ (18509670251191/50000000000000 : ℝ)^59
        have hw : |(4576118123/10000000000 : ℝ)|=(4576118123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(644955867/1000000000 : ℝ)|^75 ≤ (57263398053861/100000000000000 : ℝ)^59
        have hw : |(644955867/1000000000 : ℝ)|=(644955867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210548069/2000000000 : ℝ)|^75 ≤ (35732883933/625000000000 : ℝ)^59
        have hw : |(-210548069/2000000000 : ℝ)|=(210548069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5211774969/10000000000 : ℝ)*x 0 + (2885226471/5000000000 : ℝ)*x 1 + (1180532389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5211774969/10000000000 : ℝ)^75 ≤ (10918827671751/25000000000000 : ℝ)^59 := by
    have hnat : (5211774969 : ℕ)^75*25000000000000^59 ≤ 10918827671751^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5211774969 10000000000 10918827671751 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2885226471/5000000000 : ℝ)^75 ≤ (24855543943469/50000000000000 : ℝ)^59 := by
    have hnat : (2885226471 : ℕ)^75*50000000000000^59 ≤ 24855543943469^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2885226471 5000000000 24855543943469 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1180532389/10000000000 : ℝ)^75 ≤ (1653400352393/25000000000000 : ℝ)^59 := by
    have hnat : (1180532389 : ℕ)^75*25000000000000^59 ≤ 1653400352393^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180532389 10000000000 1653400352393 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5211774969/10000000000 : ℝ), (2885226471/5000000000 : ℝ), (1180532389/10000000000 : ℝ)] ![(10918827671751/25000000000000 : ℝ), (24855543943469/50000000000000 : ℝ), (1653400352393/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5211774969/10000000000 : ℝ)|^75 ≤ (10918827671751/25000000000000 : ℝ)^59
        have hw : |(5211774969/10000000000 : ℝ)|=(5211774969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2885226471/5000000000 : ℝ)|^75 ≤ (24855543943469/50000000000000 : ℝ)^59
        have hw : |(2885226471/5000000000 : ℝ)|=(2885226471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1180532389/10000000000 : ℝ)|^75 ≤ (1653400352393/25000000000000 : ℝ)^59
        have hw : |(1180532389/10000000000 : ℝ)|=(1180532389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-470323181/5000000000 : ℝ)*x 0 + (658919953/1250000000 : ℝ)*x 1 + (5863665801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470323181/5000000000 : ℝ)^75 ≤ (4954884485541/100000000000000 : ℝ)^59 := by
    have hnat : (470323181 : ℕ)^75*100000000000000^59 ≤ 4954884485541^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470323181 5000000000 4954884485541 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658919953/1250000000 : ℝ)^75 ≤ (4431102924677/10000000000000 : ℝ)^59 := by
    have hnat : (658919953 : ℕ)^75*10000000000000^59 ≤ 4431102924677^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658919953 1250000000 4431102924677 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5863665801/10000000000 : ℝ)^75 ≤ (50734086254831/100000000000000 : ℝ)^59 := by
    have hnat : (5863665801 : ℕ)^75*100000000000000^59 ≤ 50734086254831^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5863665801 10000000000 50734086254831 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-470323181/5000000000 : ℝ), (658919953/1250000000 : ℝ), (5863665801/10000000000 : ℝ)] ![(4954884485541/100000000000000 : ℝ), (4431102924677/10000000000000 : ℝ), (50734086254831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-470323181/5000000000 : ℝ)|^75 ≤ (4954884485541/100000000000000 : ℝ)^59
        have hw : |(-470323181/5000000000 : ℝ)|=(470323181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658919953/1250000000 : ℝ)|^75 ≤ (4431102924677/10000000000000 : ℝ)^59
        have hw : |(658919953/1250000000 : ℝ)|=(658919953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5863665801/10000000000 : ℝ)|^75 ≤ (50734086254831/100000000000000 : ℝ)^59
        have hw : |(5863665801/10000000000 : ℝ)|=(5863665801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4283339113/10000000000 : ℝ)*x 0 + (-13638153/156250000 : ℝ)*x 1 + (6818521413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283339113/10000000000 : ℝ)^75 ≤ (34035086179299/100000000000000 : ℝ)^59 := by
    have hnat : (4283339113 : ℕ)^75*100000000000000^59 ≤ 34035086179299^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283339113 10000000000 34035086179299 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13638153/156250000 : ℝ)^75 ≤ (4505381887947/100000000000000 : ℝ)^59 := by
    have hnat : (13638153 : ℕ)^75*100000000000000^59 ≤ 4505381887947^59*156250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13638153 156250000 4505381887947 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6818521413/10000000000 : ℝ)^75 ≤ (30729765962579/50000000000000 : ℝ)^59 := by
    have hnat : (6818521413 : ℕ)^75*50000000000000^59 ≤ 30729765962579^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6818521413 10000000000 30729765962579 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283339113/10000000000 : ℝ), (-13638153/156250000 : ℝ), (6818521413/10000000000 : ℝ)] ![(34035086179299/100000000000000 : ℝ), (4505381887947/100000000000000 : ℝ), (30729765962579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283339113/10000000000 : ℝ)|^75 ≤ (34035086179299/100000000000000 : ℝ)^59
        have hw : |(4283339113/10000000000 : ℝ)|=(4283339113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13638153/156250000 : ℝ)|^75 ≤ (4505381887947/100000000000000 : ℝ)^59
        have hw : |(-13638153/156250000 : ℝ)|=(13638153/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6818521413/10000000000 : ℝ)|^75 ≤ (30729765962579/50000000000000 : ℝ)^59
        have hw : |(6818521413/10000000000 : ℝ)|=(6818521413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (365120317/625000000 : ℝ)*x 0 + (331092143/625000000 : ℝ)*x 1 + (-934631721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (365120317/625000000 : ℝ)^75 ≤ (10099017526387/20000000000000 : ℝ)^59 := by
    have hnat : (365120317 : ℕ)^75*20000000000000^59 ≤ 10099017526387^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365120317 625000000 10099017526387 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331092143/625000000 : ℝ)^75 ≤ (22295133511323/50000000000000 : ℝ)^59 := by
    have hnat : (331092143 : ℕ)^75*50000000000000^59 ≤ 22295133511323^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331092143 625000000 22295133511323 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (934631721/10000000000 : ℝ)^75 ≤ (4914645332549/100000000000000 : ℝ)^59 := by
    have hnat : (934631721 : ℕ)^75*100000000000000^59 ≤ 4914645332549^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934631721 10000000000 4914645332549 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(365120317/625000000 : ℝ), (331092143/625000000 : ℝ), (-934631721/10000000000 : ℝ)] ![(10099017526387/20000000000000 : ℝ), (22295133511323/50000000000000 : ℝ), (4914645332549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(365120317/625000000 : ℝ)|^75 ≤ (10099017526387/20000000000000 : ℝ)^59
        have hw : |(365120317/625000000 : ℝ)|=(365120317/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(331092143/625000000 : ℝ)|^75 ≤ (22295133511323/50000000000000 : ℝ)^59
        have hw : |(331092143/625000000 : ℝ)|=(331092143/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-934631721/10000000000 : ℝ)|^75 ≤ (4914645332549/100000000000000 : ℝ)^59
        have hw : |(-934631721/10000000000 : ℝ)|=(934631721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1479541843/2000000000 : ℝ)*x 0 + (1695508221/5000000000 : ℝ)*x 1 + (5849853/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1479541843/2000000000 : ℝ)^75 ≤ (34085385606051/50000000000000 : ℝ)^59 := by
    have hnat : (1479541843 : ℕ)^75*50000000000000^59 ≤ 34085385606051^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479541843 2000000000 34085385606051 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1695508221/5000000000 : ℝ)^75 ≤ (12645375670781/50000000000000 : ℝ)^59 := by
    have hnat : (1695508221 : ℕ)^75*50000000000000^59 ≤ 12645375670781^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1695508221 5000000000 12645375670781 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5849853/50000000 : ℝ)^75 ≤ (6538477438879/100000000000000 : ℝ)^59 := by
    have hnat : (5849853 : ℕ)^75*100000000000000^59 ≤ 6538477438879^59*50000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5849853 50000000 6538477438879 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1479541843/2000000000 : ℝ), (1695508221/5000000000 : ℝ), (5849853/50000000 : ℝ)] ![(34085385606051/50000000000000 : ℝ), (12645375670781/50000000000000 : ℝ), (6538477438879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1479541843/2000000000 : ℝ)|^75 ≤ (34085385606051/50000000000000 : ℝ)^59
        have hw : |(1479541843/2000000000 : ℝ)|=(1479541843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1695508221/5000000000 : ℝ)|^75 ≤ (12645375670781/50000000000000 : ℝ)^59
        have hw : |(1695508221/5000000000 : ℝ)|=(1695508221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5849853/50000000 : ℝ)|^75 ≤ (6538477438879/100000000000000 : ℝ)^59
        have hw : |(5849853/50000000 : ℝ)|=(5849853/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-941706277/10000000000 : ℝ)*x 0 + (6285640393/10000000000 : ℝ)*x 1 + (4827004123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (941706277/10000000000 : ℝ)^75 ≤ (992396555227/20000000000000 : ℝ)^59 := by
    have hnat : (941706277 : ℕ)^75*20000000000000^59 ≤ 992396555227^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941706277 10000000000 992396555227 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6285640393/10000000000 : ℝ)^75 ≤ (55419762217897/100000000000000 : ℝ)^59 := by
    have hnat : (6285640393 : ℕ)^75*100000000000000^59 ≤ 55419762217897^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6285640393 10000000000 55419762217897 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4827004123/10000000000 : ℝ)^75 ≤ (1980912749823/5000000000000 : ℝ)^59 := by
    have hnat : (4827004123 : ℕ)^75*5000000000000^59 ≤ 1980912749823^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827004123 10000000000 1980912749823 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-941706277/10000000000 : ℝ), (6285640393/10000000000 : ℝ), (4827004123/10000000000 : ℝ)] ![(992396555227/20000000000000 : ℝ), (55419762217897/100000000000000 : ℝ), (1980912749823/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-941706277/10000000000 : ℝ)|^75 ≤ (992396555227/20000000000000 : ℝ)^59
        have hw : |(-941706277/10000000000 : ℝ)|=(941706277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6285640393/10000000000 : ℝ)|^75 ≤ (55419762217897/100000000000000 : ℝ)^59
        have hw : |(6285640393/10000000000 : ℝ)|=(6285640393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4827004123/10000000000 : ℝ)|^75 ≤ (1980912749823/5000000000000 : ℝ)^59
        have hw : |(4827004123/10000000000 : ℝ)|=(4827004123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5854756761/10000000000 : ℝ)*x 0 + (-322174797/10000000000 : ℝ)*x 1 + (5622336569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5854756761/10000000000 : ℝ)^75 ≤ (25318059461493/50000000000000 : ℝ)^59 := by
    have hnat : (5854756761 : ℕ)^75*50000000000000^59 ≤ 25318059461493^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5854756761 10000000000 25318059461493 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322174797/10000000000 : ℝ)^75 ≤ (1269130335059/100000000000000 : ℝ)^59 := by
    have hnat : (322174797 : ℕ)^75*100000000000000^59 ≤ 1269130335059^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322174797 10000000000 1269130335059 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5622336569/10000000000 : ℝ)^75 ≤ (4809475072779/10000000000000 : ℝ)^59 := by
    have hnat : (5622336569 : ℕ)^75*10000000000000^59 ≤ 4809475072779^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5622336569 10000000000 4809475072779 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5854756761/10000000000 : ℝ), (-322174797/10000000000 : ℝ), (5622336569/10000000000 : ℝ)] ![(25318059461493/50000000000000 : ℝ), (1269130335059/100000000000000 : ℝ), (4809475072779/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5854756761/10000000000 : ℝ)|^75 ≤ (25318059461493/50000000000000 : ℝ)^59
        have hw : |(5854756761/10000000000 : ℝ)|=(5854756761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-322174797/10000000000 : ℝ)|^75 ≤ (1269130335059/100000000000000 : ℝ)^59
        have hw : |(-322174797/10000000000 : ℝ)|=(322174797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5622336569/10000000000 : ℝ)|^75 ≤ (4809475072779/10000000000000 : ℝ)^59
        have hw : |(5622336569/10000000000 : ℝ)|=(5622336569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (211291083/500000000 : ℝ)*x 0 + (1620209431/2500000000 : ℝ)*x 1 + (-11958853/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211291083/500000000 : ℝ)^75 ≤ (3345517801507/10000000000000 : ℝ)^59 := by
    have hnat : (211291083 : ℕ)^75*10000000000000^59 ≤ 3345517801507^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211291083 500000000 3345517801507 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1620209431/2500000000 : ℝ)^75 ≤ (57616658604959/100000000000000 : ℝ)^59 := by
    have hnat : (1620209431 : ℕ)^75*100000000000000^59 ≤ 57616658604959^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1620209431 2500000000 57616658604959 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11958853/80000000 : ℝ)^75 ≤ (8928163354927/100000000000000 : ℝ)^59 := by
    have hnat : (11958853 : ℕ)^75*100000000000000^59 ≤ 8928163354927^59*80000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11958853 80000000 8928163354927 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211291083/500000000 : ℝ), (1620209431/2500000000 : ℝ), (-11958853/80000000 : ℝ)] ![(3345517801507/10000000000000 : ℝ), (57616658604959/100000000000000 : ℝ), (8928163354927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211291083/500000000 : ℝ)|^75 ≤ (3345517801507/10000000000000 : ℝ)^59
        have hw : |(211291083/500000000 : ℝ)|=(211291083/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1620209431/2500000000 : ℝ)|^75 ≤ (57616658604959/100000000000000 : ℝ)^59
        have hw : |(1620209431/2500000000 : ℝ)|=(1620209431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11958853/80000000 : ℝ)|^75 ≤ (8928163354927/100000000000000 : ℝ)^59
        have hw : |(-11958853/80000000 : ℝ)|=(11958853/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s2_s2_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7504215413/10000000000 : ℝ)*x 0 + (6148563/25000000 : ℝ)*x 1 + (2101560907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7504215413/10000000000 : ℝ)^75 ≤ (8677603279307/12500000000000 : ℝ)^59 := by
    have hnat : (7504215413 : ℕ)^75*12500000000000^59 ≤ 8677603279307^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7504215413 10000000000 8677603279307 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6148563/25000000 : ℝ)^75 ≤ (8406320815443/50000000000000 : ℝ)^59 := by
    have hnat : (6148563 : ℕ)^75*50000000000000^59 ≤ 8406320815443^59*25000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6148563 25000000 8406320815443 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2101560907/10000000000 : ℝ)^75 ≤ (6883266058727/50000000000000 : ℝ)^59 := by
    have hnat : (2101560907 : ℕ)^75*50000000000000^59 ≤ 6883266058727^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101560907 10000000000 6883266058727 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7504215413/10000000000 : ℝ), (6148563/25000000 : ℝ), (2101560907/10000000000 : ℝ)] ![(8677603279307/12500000000000 : ℝ), (8406320815443/50000000000000 : ℝ), (6883266058727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7504215413/10000000000 : ℝ)|^75 ≤ (8677603279307/12500000000000 : ℝ)^59
        have hw : |(7504215413/10000000000 : ℝ)|=(7504215413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6148563/25000000 : ℝ)|^75 ≤ (8406320815443/50000000000000 : ℝ)^59
        have hw : |(6148563/25000000 : ℝ)|=(6148563/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2101560907/10000000000 : ℝ)|^75 ≤ (6883266058727/50000000000000 : ℝ)^59
        have hw : |(2101560907/10000000000 : ℝ)|=(2101560907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314055_s2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((12573/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12573/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61511/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61511/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62479/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(62479/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9851/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9851/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10059/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10059/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3997/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3997/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  have s2_pow0 : (12573/20000 : ℝ) ^ (37/8 : ℝ) ≤ (11685337342185818159/100000000000000000000 : ℝ) := by
    have hpowers : (12573/20000 : ℝ)^37 ≤ (11685337342185818159/100000000000000000000 : ℝ)^8 := by
      have hnat : (12573 : ℕ)^37*100000000000000000000^8 ≤ 11685337342185818159^8*20000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12573 20000 11685337342185818159 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12573/20000 : ℝ)) (X := (11685337342185818159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (111685337342185818159/100000000000000000000 : ℝ) ≤ (1024182965327839/1000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (111685337342185818159/100000000000000000000 : ℝ)^8 ≤ (1024182965327839/1000000000000000 : ℝ)^37 := by
      have hnat : (111685337342185818159 : ℕ)^8*1000000000000000^37 ≤ 1024182965327839^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111685337342185818159 100000000000000000000 1024182965327839 1000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1024182965327839/1000000000000000 : ℝ)) (X := (111685337342185818159/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (61685337342185818159/50000000000000000000 : ℝ) ≤ (10464572724328873/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (61685337342185818159/50000000000000000000 : ℝ)^8 ≤ (10464572724328873/10000000000000000 : ℝ)^37 := by
      have hnat : (61685337342185818159 : ℕ)^8*10000000000000000^37 ≤ 10464572724328873^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61685337342185818159 50000000000000000000 10464572724328873 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10464572724328873/10000000000000000 : ℝ)) (X := (61685337342185818159/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(8060988442613/209550000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(74247690350161/2095500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (12573/20000 : ℝ)) (alpha := (8060988442613/209550000000000 : ℝ)) (beta := (74247690350161/2095500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (12573/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(8060988442613/209550000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(74247690350161/2095500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (61511/100000 : ℝ) ^ (37/8 : ℝ) ≤ (10565903557790323471/100000000000000000000 : ℝ) := by
    have hpowers : (61511/100000 : ℝ)^37 ≤ (10565903557790323471/100000000000000000000 : ℝ)^8 := by
      have hnat : (61511 : ℕ)^37*100000000000000000000^8 ≤ 10565903557790323471^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61511 100000 10565903557790323471 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61511/100000 : ℝ)) (X := (10565903557790323471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (110565903557790323471/100000000000000000000 : ℝ) ≤ (638721642889533/625000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (110565903557790323471/100000000000000000000 : ℝ)^8 ≤ (638721642889533/625000000000000 : ℝ)^37 := by
      have hnat : (110565903557790323471 : ℕ)^8*625000000000000^37 ≤ 638721642889533^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110565903557790323471 100000000000000000000 638721642889533 625000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (638721642889533/625000000000000 : ℝ)) (X := (110565903557790323471/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (60565903557790323471/50000000000000000000 : ℝ) ≤ (1302902103345673/1250000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (60565903557790323471/50000000000000000000 : ℝ)^8 ≤ (1302902103345673/1250000000000000 : ℝ)^37 := by
      have hnat : (60565903557790323471 : ℕ)^8*1250000000000000^37 ≤ 1302902103345673^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60565903557790323471 50000000000000000000 1302902103345673 1250000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1302902103345673/1250000000000000 : ℝ)) (X := (60565903557790323471/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(13721642889533/384443750000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(25458817566607/768887500000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (61511/100000 : ℝ)) (alpha := (13721642889533/384443750000000 : ℝ)) (beta := (25458817566607/768887500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (61511/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(13721642889533/384443750000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(25458817566607/768887500000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (62479/100000 : ℝ) ^ (37/8 : ℝ) ≤ (2839292150928445327/25000000000000000000 : ℝ) := by
    have hpowers : (62479/100000 : ℝ)^37 ≤ (2839292150928445327/25000000000000000000 : ℝ)^8 := by
      have hnat : (62479 : ℕ)^37*25000000000000000000^8 ≤ 2839292150928445327^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62479 100000 2839292150928445327 25000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62479/100000 : ℝ)) (X := (2839292150928445327/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (27839292150928445327/25000000000000000000 : ℝ) ≤ (5117657678258527/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (27839292150928445327/25000000000000000000 : ℝ)^8 ≤ (5117657678258527/5000000000000000 : ℝ)^37 := by
      have hnat : (27839292150928445327 : ℕ)^8*5000000000000000^37 ≤ 5117657678258527^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27839292150928445327 25000000000000000000 5117657678258527 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5117657678258527/5000000000000000 : ℝ)) (X := (27839292150928445327/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (15339292150928445327/12500000000000000000 : ℝ) ≤ (1306563795123779/1250000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (15339292150928445327/12500000000000000000 : ℝ)^8 ≤ (1306563795123779/1250000000000000 : ℝ)^37 := by
      have hnat : (15339292150928445327 : ℕ)^8*1250000000000000^37 ≤ 1306563795123779^37*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15339292150928445327 12500000000000000000 1306563795123779 1250000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1306563795123779/1250000000000000 : ℝ)) (X := (15339292150928445327/12500000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(117657678258527/3123950000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(108597502236589/3123950000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (62479/100000 : ℝ)) (alpha := (117657678258527/3123950000000000 : ℝ)) (beta := (108597502236589/3123950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (62479/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(117657678258527/3123950000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(108597502236589/3123950000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-393087799/2000000000 : ℝ)*X 0 0+(5637930563/10000000000 : ℝ)*X 0 1+(955307497/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4754509291/10000000000 : ℝ)*X 2 0+(2831902111/5000000000 : ℝ)*X 2 1+(-61218461/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1617756287/10000000000 : ℝ)*X 0 0+(985885673/2000000000 : ℝ)*X 0 1+(5745555643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2295004427/5000000000 : ℝ)*X 1 0+(-353453981/10000000000 : ℝ)*X 1 1+(681419623/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4576118123/10000000000 : ℝ)*X 2 0+(644955867/1000000000 : ℝ)*X 2 1+(-210548069/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((5211774969/10000000000 : ℝ)*X 0 0+(2885226471/5000000000 : ℝ)*X 0 1+(1180532389/10000000000 : ℝ)*X 0 2+(5211774969/10000000000 : ℝ)*X 1 0+(2885226471/5000000000 : ℝ)*X 1 1+(1180532389/10000000000 : ℝ)*X 1 2+(5211774969/10000000000 : ℝ)*X 2 0+(2885226471/5000000000 : ℝ)*X 2 1+(1180532389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-470323181/5000000000 : ℝ)*X 0 0+(658919953/1250000000 : ℝ)*X 0 1+(5863665801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4283339113/10000000000 : ℝ)*X 1 0+(-13638153/156250000 : ℝ)*X 1 1+(6818521413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((365120317/625000000 : ℝ)*X 2 0+(331092143/625000000 : ℝ)*X 2 1+(-934631721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1479541843/2000000000 : ℝ)*X 0 0+(1695508221/5000000000 : ℝ)*X 0 1+(5849853/50000000 : ℝ)*X 0 2+(1479541843/2000000000 : ℝ)*X 1 0+(1695508221/5000000000 : ℝ)*X 1 1+(5849853/50000000 : ℝ)*X 1 2+(1479541843/2000000000 : ℝ)*X 2 0+(1695508221/5000000000 : ℝ)*X 2 1+(5849853/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-941706277/10000000000 : ℝ)*X 0 0+(6285640393/10000000000 : ℝ)*X 0 1+(4827004123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5854756761/10000000000 : ℝ)*X 1 0+(-322174797/10000000000 : ℝ)*X 1 1+(5622336569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((211291083/500000000 : ℝ)*X 2 0+(1620209431/2500000000 : ℝ)*X 2 1+(-11958853/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((7504215413/10000000000 : ℝ)*X 0 0+(6148563/25000000 : ℝ)*X 0 1+(2101560907/10000000000 : ℝ)*X 0 2+(7504215413/10000000000 : ℝ)*X 1 0+(6148563/25000000 : ℝ)*X 1 1+(2101560907/10000000000 : ℝ)*X 1 2+(7504215413/10000000000 : ℝ)*X 2 0+(6148563/25000000 : ℝ)*X 2 1+(2101560907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((9851/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9851/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (889187433161876055698548053/192157288450000000000000000000000 : ℝ) := by norm_num
    linear_combination (2898803/1000000000000 : ℝ)*(base19) + (195965063423/500000000000 : ℝ)*(base49) + (4909/500000000000 : ℝ)*(base60) + (4717506006919/1000000000000 : ℝ)*(major_s2_0) + (4717506006919/1000000000000 : ℝ)*(major_s2_1) + (4717506006919/1000000000000 : ℝ)*(major_s2_2) + (8563477/1000000000000 : ℝ)*(sp_s2_0) + (267734532687/40000000000 : ℝ)*(sp_s2_7) + (1338670974047/200000000000 : ℝ)*(sp_s2_8) + (6693315669343/1000000000000 : ℝ)*(sp_s2_9) + (1370818104051/500000000000 : ℝ)*(sp_s2_13) + (16494229/1000000000000 : ℝ)*(sp_s2_15) + (476523/200000000000 : ℝ)*(sp_s2_21) + (2343757/40000000000 : ℝ)*(sp_s2_23) + (1370818104051/500000000000 : ℝ)*(f.failure) + (6693374263267/1000000000000 : ℝ)*(f.sum) + (15335286313772476791/24019661056250000000000000000000 : ℝ)*base62 + (614355108754579/780987500000000000000000000 : ℝ)*base65 + (99737001528447/3075550000000000000000000000 : ℝ)*base66 + (364526242140831/1561975000000000000000000000 : ℝ)*base68 + (4859877927190472249/13092474450000000000000000000000 : ℝ)*base71 + (1097324869601209/2095500000000000000000000000 : ℝ)*base73 + (296226704085869/3075550000000000000000000000 : ℝ)*base74 + (63353256287923/209550000000000000000000000 : ℝ)*base76 + (52345882341579482971/128896300500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (1519/50000000000000000 : ℝ)*base87 + (1519/50000000000000000 : ℝ)*base89 + (1519/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10059/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10059/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (304720490923822097791752677531/53688746392930000000000000000000000 : ℝ) := by norm_num
    linear_combination (513051/1000000000000 : ℝ)*(base39) + (300011439539/1000000000000 : ℝ)*(base49) + (832509/1000000000000 : ℝ)*(base60) + (35856942289/8000000000 : ℝ)*(major_s2_0) + (35856942289/8000000000 : ℝ)*(major_s2_1) + (35856942289/8000000000 : ℝ)*(major_s2_2) + (432363/100000000000 : ℝ)*(sp_s2_2) + (14958389/1000000000000 : ℝ)*(sp_s2_7) + (25738077/1000000000000 : ℝ)*(sp_s2_8) + (1589845313009/250000000000 : ℝ)*(sp_s2_14) + (6359370472347/1000000000000 : ℝ)*(sp_s2_15) + (1271878377359/200000000000 : ℝ)*(sp_s2_16) + (40700196671/15625000000 : ℝ)*(sp_s2_20) + (24882981/1000000000000 : ℝ)*(sp_s2_27) + (104193498797/40000000000 : ℝ)*(f.failure) + (254375848417/40000000000 : ℝ)*(f.sum) + (16865559225883583603/38431457690000000000000000000000 : ℝ)*base63 + (232449632073069/312395000000000000000000000 : ℝ)*base64 + (10336219533127/61511000000000000000000000 : ℝ)*base67 + (348384405441297/624790000000000000000000000 : ℝ)*base69 + (1355527848018111193/2618494890000000000000000000000 : ℝ)*base70 + (7520049535171/83820000000000000000000000 : ℝ)*base72 + (213459699899613/615110000000000000000000000 : ℝ)*base74 + (13724946671263/41910000000000000000000000 : ℝ)*base76 + (385688233258513171/5155852020000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (993/4000000000000000 : ℝ)*base87 + (993/4000000000000000 : ℝ)*base89 + (993/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3997/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3997/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (823425862805195851339324864927/67110932991162500000000000000000000 : ℝ) := by norm_num
    linear_combination (20939417151/200000000000 : ℝ)*(base40) + (298028762639/1000000000000 : ℝ)*(base49) + (5142647/1000000000000 : ℝ)*(base59) + (4363996504397/1000000000000 : ℝ)*(major_s2_0) + (4363996504397/1000000000000 : ℝ)*(major_s2_1) + (4363996504397/1000000000000 : ℝ)*(major_s2_2) + (24592239/1000000000000 : ℝ)*(sp_s2_0) + (27795139/1000000000000 : ℝ)*(sp_s2_2) + (38806891/1000000000000 : ℝ)*(sp_s2_9) + (9846761/100000000000 : ℝ)*(sp_s2_20) + (6191774481671/1000000000000 : ℝ)*(sp_s2_21) + (619179907391/100000000000 : ℝ)*(sp_s2_22) + (6191732471879/1000000000000 : ℝ)*(sp_s2_23) + (2536091377393/1000000000000 : ℝ)*(sp_s2_27) + (1268094922501/500000000000 : ℝ)*(f.failure) + (619179907391/100000000000 : ℝ)*(f.sum) + (47256602290994650537/96078644225000000000000000000000 : ℝ)*base62 + (1515234261847767/3123950000000000000000000000 : ℝ)*base64 + (1349502080670861/3075550000000000000000000000 : ℝ)*base66 + (217550495015317/390493750000000000000000000 : ℝ)*base68 + (1106075886409113091/1636559306250000000000000000000 : ℝ)*base70 + (202253250856367/2095500000000000000000000000 : ℝ)*base73 + (379427116704947/3075550000000000000000000000 : ℝ)*base74 + (1723152444659/209550000000000000000000000 : ℝ)*base76 + (21681335934475734623/128896300500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (25431/50000000000000000 : ℝ)*base86 + (25431/50000000000000000 : ℝ)*base88 + (25431/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((12573/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12573/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61511/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61511/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62479/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(62479/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9851/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9851/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10059/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10059/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3997/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3997/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314055_s2 p hpa hpb X hX hprev1

#print axioms solution
