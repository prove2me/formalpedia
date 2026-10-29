-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314055_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:46:57.673835+00:00
-- url     : https://prove2.me/submissions/319c93d1-e7d0-44b9-b338-3c6e3d34b481

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
theorem collision_support_c314055_s3_s3_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2232344/9765625 : ℝ)*x 0 + (5461313821/10000000000 : ℝ)*x 1 + (470307473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2232344/9765625 : ℝ)^75 ≤ (15319589582349/100000000000000 : ℝ)^59 := by
    have hnat : (2232344 : ℕ)^75*100000000000000^59 ≤ 15319589582349^59*9765625^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232344 9765625 15319589582349 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461313821/10000000000 : ℝ)^75 ≤ (23175316919357/50000000000000 : ℝ)^59 := by
    have hnat : (5461313821 : ℕ)^75*50000000000000^59 ≤ 23175316919357^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461313821 10000000000 23175316919357 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470307473/1000000000 : ℝ)^75 ≤ (9582444140141/25000000000000 : ℝ)^59 := by
    have hnat : (470307473 : ℕ)^75*25000000000000^59 ≤ 9582444140141^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470307473 1000000000 9582444140141 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2232344/9765625 : ℝ), (5461313821/10000000000 : ℝ), (470307473/1000000000 : ℝ)] ![(15319589582349/100000000000000 : ℝ), (23175316919357/50000000000000 : ℝ), (9582444140141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2232344/9765625 : ℝ)|^75 ≤ (15319589582349/100000000000000 : ℝ)^59
        have hw : |(-2232344/9765625 : ℝ)|=(2232344/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461313821/10000000000 : ℝ)|^75 ≤ (23175316919357/50000000000000 : ℝ)^59
        have hw : |(5461313821/10000000000 : ℝ)|=(5461313821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(470307473/1000000000 : ℝ)|^75 ≤ (9582444140141/25000000000000 : ℝ)^59
        have hw : |(470307473/1000000000 : ℝ)|=(470307473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1175374701/2500000000 : ℝ)*x 0 + (-1530150571/10000000000 : ℝ)*x 1 + (6022693797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1175374701/2500000000 : ℝ)^75 ≤ (19156725281147/50000000000000 : ℝ)^59 := by
    have hnat : (1175374701 : ℕ)^75*50000000000000^59 ≤ 19156725281147^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175374701 2500000000 19156725281147 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1530150571/10000000000 : ℝ)^75 ≤ (2299244405073/25000000000000 : ℝ)^59 := by
    have hnat : (1530150571 : ℕ)^75*25000000000000^59 ≤ 2299244405073^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530150571 10000000000 2299244405073 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6022693797/10000000000 : ℝ)^75 ≤ (6561196475381/12500000000000 : ℝ)^59 := by
    have hnat : (6022693797 : ℕ)^75*12500000000000^59 ≤ 6561196475381^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6022693797 10000000000 6561196475381 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1175374701/2500000000 : ℝ), (-1530150571/10000000000 : ℝ), (6022693797/10000000000 : ℝ)] ![(19156725281147/50000000000000 : ℝ), (2299244405073/25000000000000 : ℝ), (6561196475381/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1175374701/2500000000 : ℝ)|^75 ≤ (19156725281147/50000000000000 : ℝ)^59
        have hw : |(1175374701/2500000000 : ℝ)|=(1175374701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1530150571/10000000000 : ℝ)|^75 ≤ (2299244405073/25000000000000 : ℝ)^59
        have hw : |(-1530150571/10000000000 : ℝ)|=(1530150571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6022693797/10000000000 : ℝ)|^75 ≤ (6561196475381/12500000000000 : ℝ)^59
        have hw : |(6022693797/10000000000 : ℝ)|=(6022693797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2351407881/5000000000 : ℝ)*x 0 + (2729594131/5000000000 : ℝ)*x 1 + (-91557053/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2351407881/5000000000 : ℝ)^75 ≤ (9581773411999/25000000000000 : ℝ)^59 := by
    have hnat : (2351407881 : ℕ)^75*25000000000000^59 ≤ 9581773411999^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351407881 5000000000 9581773411999 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729594131/5000000000 : ℝ)^75 ≤ (46327703100371/100000000000000 : ℝ)^59 := by
    have hnat : (2729594131 : ℕ)^75*100000000000000^59 ≤ 46327703100371^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729594131 5000000000 46327703100371 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91557053/400000000 : ℝ)^75 ≤ (1918150405429/12500000000000 : ℝ)^59 := by
    have hnat : (91557053 : ℕ)^75*12500000000000^59 ≤ 1918150405429^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91557053 400000000 1918150405429 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2351407881/5000000000 : ℝ), (2729594131/5000000000 : ℝ), (-91557053/400000000 : ℝ)] ![(9581773411999/25000000000000 : ℝ), (46327703100371/100000000000000 : ℝ), (1918150405429/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2351407881/5000000000 : ℝ)|^75 ≤ (9581773411999/25000000000000 : ℝ)^59
        have hw : |(2351407881/5000000000 : ℝ)|=(2351407881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729594131/5000000000 : ℝ)|^75 ≤ (46327703100371/100000000000000 : ℝ)^59
        have hw : |(2729594131/5000000000 : ℝ)|=(2729594131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91557053/400000000 : ℝ)|^75 ≤ (1918150405429/12500000000000 : ℝ)^59
        have hw : |(-91557053/400000000 : ℝ)|=(91557053/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5854160019/10000000000 : ℝ)*x 0 + (1998216851/5000000000 : ℝ)*x 1 + (1309229679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5854160019/10000000000 : ℝ)^75 ≤ (12657389588867/25000000000000 : ℝ)^59 := by
    have hnat : (5854160019 : ℕ)^75*25000000000000^59 ≤ 12657389588867^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5854160019 10000000000 12657389588867 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1998216851/5000000000 : ℝ)^75 ≤ (15581943694391/50000000000000 : ℝ)^59 := by
    have hnat : (1998216851 : ℕ)^75*50000000000000^59 ≤ 15581943694391^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998216851 5000000000 15581943694391 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309229679/5000000000 : ℝ)^75 ≤ (3641310849543/20000000000000 : ℝ)^59 := by
    have hnat : (1309229679 : ℕ)^75*20000000000000^59 ≤ 3641310849543^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309229679 5000000000 3641310849543 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5854160019/10000000000 : ℝ), (1998216851/5000000000 : ℝ), (1309229679/5000000000 : ℝ)] ![(12657389588867/25000000000000 : ℝ), (15581943694391/50000000000000 : ℝ), (3641310849543/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5854160019/10000000000 : ℝ)|^75 ≤ (12657389588867/25000000000000 : ℝ)^59
        have hw : |(5854160019/10000000000 : ℝ)|=(5854160019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1998216851/5000000000 : ℝ)|^75 ≤ (15581943694391/50000000000000 : ℝ)^59
        have hw : |(1998216851/5000000000 : ℝ)|=(1998216851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309229679/5000000000 : ℝ)|^75 ≤ (3641310849543/20000000000000 : ℝ)^59
        have hw : |(1309229679/5000000000 : ℝ)|=(1309229679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-88469017/400000000 : ℝ)*x 0 + (1309092697/2500000000 : ℝ)*x 1 + (2497165819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88469017/400000000 : ℝ)^75 ≤ (14690318090103/100000000000000 : ℝ)^59 := by
    have hnat : (88469017 : ℕ)^75*100000000000000^59 ≤ 14690318090103^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88469017 400000000 14690318090103 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309092697/2500000000 : ℝ)^75 ≤ (21968744989653/50000000000000 : ℝ)^59 := by
    have hnat : (1309092697 : ℕ)^75*50000000000000^59 ≤ 21968744989653^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309092697 2500000000 21968744989653 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2497165819/5000000000 : ℝ)^75 ≤ (8274438382357/20000000000000 : ℝ)^59 := by
    have hnat : (2497165819 : ℕ)^75*20000000000000^59 ≤ 8274438382357^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497165819 5000000000 8274438382357 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88469017/400000000 : ℝ), (1309092697/2500000000 : ℝ), (2497165819/5000000000 : ℝ)] ![(14690318090103/100000000000000 : ℝ), (21968744989653/50000000000000 : ℝ), (8274438382357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88469017/400000000 : ℝ)|^75 ≤ (14690318090103/100000000000000 : ℝ)^59
        have hw : |(-88469017/400000000 : ℝ)|=(88469017/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309092697/2500000000 : ℝ)|^75 ≤ (21968744989653/50000000000000 : ℝ)^59
        have hw : |(1309092697/2500000000 : ℝ)|=(1309092697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2497165819/5000000000 : ℝ)|^75 ≤ (8274438382357/20000000000000 : ℝ)^59
        have hw : |(2497165819/5000000000 : ℝ)|=(2497165819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (936503487/2000000000 : ℝ)*x 0 + (-647843199/5000000000 : ℝ)*x 1 + (6197950349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936503487/2000000000 : ℝ)^75 ≤ (19058463715413/50000000000000 : ℝ)^59 := by
    have hnat : (936503487 : ℕ)^75*50000000000000^59 ≤ 19058463715413^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936503487 2000000000 19058463715413 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647843199/5000000000 : ℝ)^75 ≤ (1488853279693/20000000000000 : ℝ)^59 := by
    have hnat : (647843199 : ℕ)^75*20000000000000^59 ≤ 1488853279693^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647843199 5000000000 1488853279693 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6197950349/10000000000 : ℝ)^75 ≤ (27219403080617/50000000000000 : ℝ)^59 := by
    have hnat : (6197950349 : ℕ)^75*50000000000000^59 ≤ 27219403080617^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6197950349 10000000000 27219403080617 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(936503487/2000000000 : ℝ), (-647843199/5000000000 : ℝ), (6197950349/10000000000 : ℝ)] ![(19058463715413/50000000000000 : ℝ), (1488853279693/20000000000000 : ℝ), (27219403080617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(936503487/2000000000 : ℝ)|^75 ≤ (19058463715413/50000000000000 : ℝ)^59
        have hw : |(936503487/2000000000 : ℝ)|=(936503487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-647843199/5000000000 : ℝ)|^75 ≤ (1488853279693/20000000000000 : ℝ)^59
        have hw : |(-647843199/5000000000 : ℝ)|=(647843199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6197950349/10000000000 : ℝ)|^75 ≤ (27219403080617/50000000000000 : ℝ)^59
        have hw : |(6197950349/10000000000 : ℝ)|=(6197950349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4683834471/10000000000 : ℝ)*x 0 + (2849193683/5000000000 : ℝ)*x 1 + (-100120277/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4683834471/10000000000 : ℝ)^75 ≤ (38130556366499/100000000000000 : ℝ)^59 := by
    have hnat : (4683834471 : ℕ)^75*100000000000000^59 ≤ 38130556366499^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4683834471 10000000000 38130556366499 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2849193683/5000000000 : ℝ)^75 ≤ (9784648070983/20000000000000 : ℝ)^59 := by
    have hnat : (2849193683 : ℕ)^75*20000000000000^59 ≤ 9784648070983^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2849193683 5000000000 9784648070983 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100120277/500000000 : ℝ)^75 ≤ (12946203261989/100000000000000 : ℝ)^59 := by
    have hnat : (100120277 : ℕ)^75*100000000000000^59 ≤ 12946203261989^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100120277 500000000 12946203261989 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4683834471/10000000000 : ℝ), (2849193683/5000000000 : ℝ), (-100120277/500000000 : ℝ)] ![(38130556366499/100000000000000 : ℝ), (9784648070983/20000000000000 : ℝ), (12946203261989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4683834471/10000000000 : ℝ)|^75 ≤ (38130556366499/100000000000000 : ℝ)^59
        have hw : |(4683834471/10000000000 : ℝ)|=(4683834471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2849193683/5000000000 : ℝ)|^75 ≤ (9784648070983/20000000000000 : ℝ)^59
        have hw : |(2849193683/5000000000 : ℝ)|=(2849193683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100120277/500000000 : ℝ)|^75 ≤ (12946203261989/100000000000000 : ℝ)^59
        have hw : |(-100120277/500000000 : ℝ)|=(100120277/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (566924241/1000000000 : ℝ)*x 0 + (4554637379/10000000000 : ℝ)*x 1 + (2200550981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (566924241/1000000000 : ℝ)^75 ≤ (48605381557199/100000000000000 : ℝ)^59 := by
    have hnat : (566924241 : ℕ)^75*100000000000000^59 ≤ 48605381557199^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566924241 1000000000 48605381557199 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4554637379/10000000000 : ℝ)^75 ≤ (367985841573/1000000000000 : ℝ)^59 := by
    have hnat : (4554637379 : ℕ)^75*1000000000000^59 ≤ 367985841573^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554637379 10000000000 367985841573 1000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200550981/10000000000 : ℝ)^75 ≤ (7298017134443/50000000000000 : ℝ)^59 := by
    have hnat : (2200550981 : ℕ)^75*50000000000000^59 ≤ 7298017134443^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200550981 10000000000 7298017134443 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(566924241/1000000000 : ℝ), (4554637379/10000000000 : ℝ), (2200550981/10000000000 : ℝ)] ![(48605381557199/100000000000000 : ℝ), (367985841573/1000000000000 : ℝ), (7298017134443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(566924241/1000000000 : ℝ)|^75 ≤ (48605381557199/100000000000000 : ℝ)^59
        have hw : |(566924241/1000000000 : ℝ)|=(566924241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4554637379/10000000000 : ℝ)|^75 ≤ (367985841573/1000000000000 : ℝ)^59
        have hw : |(4554637379/10000000000 : ℝ)|=(4554637379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2200550981/10000000000 : ℝ)|^75 ≤ (7298017134443/50000000000000 : ℝ)^59
        have hw : |(2200550981/10000000000 : ℝ)|=(2200550981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1966316771/10000000000 : ℝ)*x 0 + (5394348277/10000000000 : ℝ)*x 1 + (5027359797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1966316771/10000000000 : ℝ)^75 ≤ (12650330899561/100000000000000 : ℝ)^59 := by
    have hnat : (1966316771 : ℕ)^75*100000000000000^59 ≤ 12650330899561^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966316771 10000000000 12650330899561 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394348277/10000000000 : ℝ)^75 ≤ (9125873931521/20000000000000 : ℝ)^59 := by
    have hnat : (5394348277 : ℕ)^75*20000000000000^59 ≤ 9125873931521^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394348277 10000000000 9125873931521 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5027359797/10000000000 : ℝ)^75 ≤ (20860149715263/50000000000000 : ℝ)^59 := by
    have hnat : (5027359797 : ℕ)^75*50000000000000^59 ≤ 20860149715263^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027359797 10000000000 20860149715263 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1966316771/10000000000 : ℝ), (5394348277/10000000000 : ℝ), (5027359797/10000000000 : ℝ)] ![(12650330899561/100000000000000 : ℝ), (9125873931521/20000000000000 : ℝ), (20860149715263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1966316771/10000000000 : ℝ)|^75 ≤ (12650330899561/100000000000000 : ℝ)^59
        have hw : |(-1966316771/10000000000 : ℝ)|=(1966316771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394348277/10000000000 : ℝ)|^75 ≤ (9125873931521/20000000000000 : ℝ)^59
        have hw : |(5394348277/10000000000 : ℝ)|=(5394348277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5027359797/10000000000 : ℝ)|^75 ≤ (20860149715263/50000000000000 : ℝ)^59
        have hw : |(5027359797/10000000000 : ℝ)|=(5027359797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (181650897/400000000 : ℝ)*x 0 + (-373772743/2500000000 : ℝ)*x 1 + (1239050429/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181650897/400000000 : ℝ)^75 ≤ (36661375640813/100000000000000 : ℝ)^59 := by
    have hnat : (181650897 : ℕ)^75*100000000000000^59 ≤ 36661375640813^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181650897 400000000 36661375640813 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (373772743/2500000000 : ℝ)^75 ≤ (4464971309621/50000000000000 : ℝ)^59 := by
    have hnat : (373772743 : ℕ)^75*50000000000000^59 ≤ 4464971309621^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373772743 2500000000 4464971309621 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1239050429/2000000000 : ℝ)^75 ≤ (6801085215921/12500000000000 : ℝ)^59 := by
    have hnat : (1239050429 : ℕ)^75*12500000000000^59 ≤ 6801085215921^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239050429 2000000000 6801085215921 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(181650897/400000000 : ℝ), (-373772743/2500000000 : ℝ), (1239050429/2000000000 : ℝ)] ![(36661375640813/100000000000000 : ℝ), (4464971309621/50000000000000 : ℝ), (6801085215921/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(181650897/400000000 : ℝ)|^75 ≤ (36661375640813/100000000000000 : ℝ)^59
        have hw : |(181650897/400000000 : ℝ)|=(181650897/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-373772743/2500000000 : ℝ)|^75 ≤ (4464971309621/50000000000000 : ℝ)^59
        have hw : |(-373772743/2500000000 : ℝ)|=(373772743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1239050429/2000000000 : ℝ)|^75 ≤ (6801085215921/12500000000000 : ℝ)^59
        have hw : |(1239050429/2000000000 : ℝ)|=(1239050429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1005430663/2000000000 : ℝ)*x 0 + (5392221423/10000000000 : ℝ)*x 1 + (-1969378687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005430663/2000000000 : ℝ)^75 ≤ (41718121236913/100000000000000 : ℝ)^59 := by
    have hnat : (1005430663 : ℕ)^75*100000000000000^59 ≤ 41718121236913^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005430663 2000000000 41718121236913 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392221423/10000000000 : ℝ)^75 ≤ (45606501604281/100000000000000 : ℝ)^59 := by
    have hnat : (5392221423 : ℕ)^75*100000000000000^59 ≤ 45606501604281^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392221423 10000000000 45606501604281 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1969378687/10000000000 : ℝ)^75 ≤ (6337688571007/50000000000000 : ℝ)^59 := by
    have hnat : (1969378687 : ℕ)^75*50000000000000^59 ≤ 6337688571007^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969378687 10000000000 6337688571007 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1005430663/2000000000 : ℝ), (5392221423/10000000000 : ℝ), (-1969378687/10000000000 : ℝ)] ![(41718121236913/100000000000000 : ℝ), (45606501604281/100000000000000 : ℝ), (6337688571007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1005430663/2000000000 : ℝ)|^75 ≤ (41718121236913/100000000000000 : ℝ)^59
        have hw : |(1005430663/2000000000 : ℝ)|=(1005430663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392221423/10000000000 : ℝ)|^75 ≤ (45606501604281/100000000000000 : ℝ)^59
        have hw : |(5392221423/10000000000 : ℝ)|=(5392221423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1969378687/10000000000 : ℝ)|^75 ≤ (6337688571007/50000000000000 : ℝ)^59
        have hw : |(-1969378687/10000000000 : ℝ)|=(1969378687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (390819251/625000000 : ℝ)*x 0 + (244269349/625000000 : ℝ)*x 1 + (2207141819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390819251/625000000 : ℝ)^75 ≤ (13763849671653/25000000000000 : ℝ)^59 := by
    have hnat : (390819251 : ℕ)^75*25000000000000^59 ≤ 13763849671653^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390819251 625000000 13763849671653 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244269349/625000000 : ℝ)^75 ≤ (30292972827387/100000000000000 : ℝ)^59 := by
    have hnat : (244269349 : ℕ)^75*100000000000000^59 ≤ 30292972827387^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244269349 625000000 30292972827387 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207141819/10000000000 : ℝ)^75 ≤ (228931694931/1562500000000 : ℝ)^59 := by
    have hnat : (2207141819 : ℕ)^75*1562500000000^59 ≤ 228931694931^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207141819 10000000000 228931694931 1562500000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(390819251/625000000 : ℝ), (244269349/625000000 : ℝ), (2207141819/10000000000 : ℝ)] ![(13763849671653/25000000000000 : ℝ), (30292972827387/100000000000000 : ℝ), (228931694931/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(390819251/625000000 : ℝ)|^75 ≤ (13763849671653/25000000000000 : ℝ)^59
        have hw : |(390819251/625000000 : ℝ)|=(390819251/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(244269349/625000000 : ℝ)|^75 ≤ (30292972827387/100000000000000 : ℝ)^59
        have hw : |(244269349/625000000 : ℝ)|=(244269349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2207141819/10000000000 : ℝ)|^75 ≤ (228931694931/1562500000000 : ℝ)^59
        have hw : |(2207141819/10000000000 : ℝ)|=(2207141819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-499490451/2500000000 : ℝ)*x 0 + (5703539749/10000000000 : ℝ)*x 1 + (4681928011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499490451/2500000000 : ℝ)^75 ≤ (12909692818209/100000000000000 : ℝ)^59 := by
    have hnat : (499490451 : ℕ)^75*100000000000000^59 ≤ 12909692818209^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499490451 2500000000 12909692818209 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5703539749/10000000000 : ℝ)^75 ≤ (24489739436357/50000000000000 : ℝ)^59 := by
    have hnat : (5703539749 : ℕ)^75*50000000000000^59 ≤ 24489739436357^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5703539749 10000000000 24489739436357 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4681928011/10000000000 : ℝ)^75 ≤ (4763853537171/12500000000000 : ℝ)^59 := by
    have hnat : (4681928011 : ℕ)^75*12500000000000^59 ≤ 4763853537171^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4681928011 10000000000 4763853537171 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-499490451/2500000000 : ℝ), (5703539749/10000000000 : ℝ), (4681928011/10000000000 : ℝ)] ![(12909692818209/100000000000000 : ℝ), (24489739436357/50000000000000 : ℝ), (4763853537171/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-499490451/2500000000 : ℝ)|^75 ≤ (12909692818209/100000000000000 : ℝ)^59
        have hw : |(-499490451/2500000000 : ℝ)|=(499490451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5703539749/10000000000 : ℝ)|^75 ≤ (24489739436357/50000000000000 : ℝ)^59
        have hw : |(5703539749/10000000000 : ℝ)|=(5703539749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4681928011/10000000000 : ℝ)|^75 ≤ (4763853537171/12500000000000 : ℝ)^59
        have hw : |(4681928011/10000000000 : ℝ)|=(4681928011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4994194147/10000000000 : ℝ)*x 0 + (-1292659551/10000000000 : ℝ)*x 1 + (2953314339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4994194147/10000000000 : ℝ)^75 ≤ (41370744096843/100000000000000 : ℝ)^59 := by
    have hnat : (4994194147 : ℕ)^75*100000000000000^59 ≤ 41370744096843^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4994194147 10000000000 41370744096843 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292659551/10000000000 : ℝ)^75 ≤ (7422166816389/100000000000000 : ℝ)^59 := by
    have hnat : (1292659551 : ℕ)^75*100000000000000^59 ≤ 7422166816389^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292659551 10000000000 7422166816389 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2953314339/5000000000 : ℝ)^75 ≤ (51207089072527/100000000000000 : ℝ)^59 := by
    have hnat : (2953314339 : ℕ)^75*100000000000000^59 ≤ 51207089072527^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2953314339 5000000000 51207089072527 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4994194147/10000000000 : ℝ), (-1292659551/10000000000 : ℝ), (2953314339/5000000000 : ℝ)] ![(41370744096843/100000000000000 : ℝ), (7422166816389/100000000000000 : ℝ), (51207089072527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4994194147/10000000000 : ℝ)|^75 ≤ (41370744096843/100000000000000 : ℝ)^59
        have hw : |(4994194147/10000000000 : ℝ)|=(4994194147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1292659551/10000000000 : ℝ)|^75 ≤ (7422166816389/100000000000000 : ℝ)^59
        have hw : |(-1292659551/10000000000 : ℝ)|=(1292659551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2953314339/5000000000 : ℝ)|^75 ≤ (51207089072527/100000000000000 : ℝ)^59
        have hw : |(2953314339/5000000000 : ℝ)|=(2953314339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2255607821/5000000000 : ℝ)*x 0 + (2850706569/5000000000 : ℝ)*x 1 + (-2211750599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2255607821/5000000000 : ℝ)^75 ≤ (18176602098149/50000000000000 : ℝ)^59 := by
    have hnat : (2255607821 : ℕ)^75*50000000000000^59 ≤ 18176602098149^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255607821 5000000000 18176602098149 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2850706569/5000000000 : ℝ)^75 ≤ (24478132568493/50000000000000 : ℝ)^59 := by
    have hnat : (2850706569 : ℕ)^75*50000000000000^59 ≤ 24478132568493^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850706569 5000000000 24478132568493 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211750599/10000000000 : ℝ)^75 ≤ (14690530640607/100000000000000 : ℝ)^59 := by
    have hnat : (2211750599 : ℕ)^75*100000000000000^59 ≤ 14690530640607^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211750599 10000000000 14690530640607 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2255607821/5000000000 : ℝ), (2850706569/5000000000 : ℝ), (-2211750599/10000000000 : ℝ)] ![(18176602098149/50000000000000 : ℝ), (24478132568493/50000000000000 : ℝ), (14690530640607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2255607821/5000000000 : ℝ)|^75 ≤ (18176602098149/50000000000000 : ℝ)^59
        have hw : |(2255607821/5000000000 : ℝ)|=(2255607821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2850706569/5000000000 : ℝ)|^75 ≤ (24478132568493/50000000000000 : ℝ)^59
        have hw : |(2850706569/5000000000 : ℝ)|=(2850706569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2211750599/10000000000 : ℝ)|^75 ≤ (14690530640607/100000000000000 : ℝ)^59
        have hw : |(-2211750599/10000000000 : ℝ)|=(2211750599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314055_s3_s3_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6329707299/10000000000 : ℝ)*x 0 + (85352509/250000000 : ℝ)*x 1 + (1330087741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6329707299/10000000000 : ℝ)^75 ≤ (27957064274201/50000000000000 : ℝ)^59 := by
    have hnat : (6329707299 : ℕ)^75*50000000000000^59 ≤ 27957064274201^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6329707299 10000000000 27957064274201 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85352509/250000000 : ℝ)^75 ≤ (12754902531063/50000000000000 : ℝ)^59 := by
    have hnat : (85352509 : ℕ)^75*50000000000000^59 ≤ 12754902531063^59*250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85352509 250000000 12754902531063 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1330087741/5000000000 : ℝ)^75 ≤ (18576066361601/100000000000000 : ℝ)^59 := by
    have hnat : (1330087741 : ℕ)^75*100000000000000^59 ≤ 18576066361601^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330087741 5000000000 18576066361601 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6329707299/10000000000 : ℝ), (85352509/250000000 : ℝ), (1330087741/5000000000 : ℝ)] ![(27957064274201/50000000000000 : ℝ), (12754902531063/50000000000000 : ℝ), (18576066361601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6329707299/10000000000 : ℝ)|^75 ≤ (27957064274201/50000000000000 : ℝ)^59
        have hw : |(6329707299/10000000000 : ℝ)|=(6329707299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85352509/250000000 : ℝ)|^75 ≤ (12754902531063/50000000000000 : ℝ)^59
        have hw : |(85352509/250000000 : ℝ)|=(85352509/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1330087741/5000000000 : ℝ)|^75 ≤ (18576066361601/100000000000000 : ℝ)^59
        have hw : |(1330087741/5000000000 : ℝ)|=(1330087741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314055_s3 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((9851/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9851/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10059/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10059/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3997/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3997/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2637/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2637/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22033/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22033/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21281/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21281/100000 : ℝ)*X 1 2) := by
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
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (9851/25000 : ℝ) ^ (37/8 : ℝ) ≤ (21047182246303743/1562500000000000000 : ℝ) := by
    have hpowers : (9851/25000 : ℝ)^37 ≤ (21047182246303743/1562500000000000000 : ℝ)^8 := by
      have hnat : (9851 : ℕ)^37*1562500000000000000^8 ≤ 21047182246303743^8*25000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9851 25000 21047182246303743 1562500000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9851/25000 : ℝ)) (X := (21047182246303743/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (1583547182246303743/1562500000000000000 : ℝ) ≤ (5014486111977277/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (1583547182246303743/1562500000000000000 : ℝ)^8 ≤ (5014486111977277/5000000000000000 : ℝ)^37 := by
      have hnat : (1583547182246303743 : ℕ)^8*5000000000000000^37 ≤ 5014486111977277^37*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1583547182246303743 1562500000000000000 5014486111977277 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014486111977277/5000000000000000 : ℝ)) (X := (1583547182246303743/1562500000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (802297182246303743/781250000000000000 : ℝ) ≤ (5028822093559757/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (802297182246303743/781250000000000000 : ℝ)^8 ≤ (5028822093559757/5000000000000000 : ℝ)^37 := by
      have hnat : (802297182246303743 : ℕ)^8*5000000000000000^37 ≤ 5028822093559757^37*781250000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        802297182246303743 781250000000000000 5028822093559757 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028822093559757/5000000000000000 : ℝ)) (X := (802297182246303743/781250000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(14486111977277/1970200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(179199769781/24627500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (9851/25000 : ℝ)) (alpha := (14486111977277/1970200000000000 : ℝ)) (beta := (179199769781/24627500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (9851/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(14486111977277/1970200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(179199769781/24627500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (10059/25000 : ℝ) ^ (37/8 : ℝ) ≤ (1483690949757283737/100000000000000000000 : ℝ) := by
    have hpowers : (10059/25000 : ℝ)^37 ≤ (1483690949757283737/100000000000000000000 : ℝ)^8 := by
      have hnat : (10059 : ℕ)^37*100000000000000000000^8 ≤ 1483690949757283737^8*25000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10059 25000 1483690949757283737 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10059/25000 : ℝ)) (X := (1483690949757283737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (101483690949757283737/100000000000000000000 : ℝ) ≤ (5015947453081049/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (101483690949757283737/100000000000000000000 : ℝ)^8 ≤ (5015947453081049/5000000000000000 : ℝ)^37 := by
      have hnat : (101483690949757283737 : ℕ)^8*5000000000000000^37 ≤ 5015947453081049^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101483690949757283737 100000000000000000000 5015947453081049 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015947453081049/5000000000000000 : ℝ)) (X := (101483690949757283737/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (51483690949757283737/50000000000000000000 : ℝ) ≤ (10063426399445713/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (51483690949757283737/50000000000000000000 : ℝ)^8 ≤ (10063426399445713/10000000000000000 : ℝ)^37 := by
      have hnat : (51483690949757283737 : ℕ)^8*10000000000000000^37 ≤ 10063426399445713^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51483690949757283737 50000000000000000000 10063426399445713 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10063426399445713/10000000000000000 : ℝ)) (X := (51483690949757283737/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(759402527669/95800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(2102099552241/268240000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (10059/25000 : ℝ)) (alpha := (759402527669/95800000000000 : ℝ)) (beta := (2102099552241/268240000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (10059/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(759402527669/95800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(2102099552241/268240000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (3997/10000 : ℝ) ^ (37/8 : ℝ) ≤ (17985828530459887/1250000000000000000 : ℝ) := by
    have hpowers : (3997/10000 : ℝ)^37 ≤ (17985828530459887/1250000000000000000 : ℝ)^8 := by
      have hnat : (3997 : ℕ)^37*1250000000000000000^8 ≤ 17985828530459887^8*10000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3997 10000 17985828530459887 1250000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3997/10000 : ℝ)) (X := (17985828530459887/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (1267985828530459887/1250000000000000000 : ℝ) ≤ (10030936681717619/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (1267985828530459887/1250000000000000000 : ℝ)^8 ≤ (10030936681717619/10000000000000000 : ℝ)^37 := by
      have hnat : (1267985828530459887 : ℕ)^8*10000000000000000^37 ≤ 10030936681717619^37*1250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1267985828530459887 1250000000000000000 10030936681717619 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030936681717619/10000000000000000 : ℝ)) (X := (1267985828530459887/1250000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (642985828530459887/625000000000000000 : ℝ) ≤ (10061531309740943/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (642985828530459887/625000000000000000 : ℝ)^8 ≤ (10061531309740943/10000000000000000 : ℝ)^37 := by
      have hnat : (642985828530459887 : ℕ)^8*10000000000000000^37 ≤ 10061531309740943^37*625000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        642985828530459887 625000000000000000 10061531309740943 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10061531309740943/10000000000000000 : ℝ)) (X := (642985828530459887/625000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(30936681717619/3997000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7648657005831/999250000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (3997/10000 : ℝ)) (alpha := (30936681717619/3997000000000000 : ℝ)) (beta := (7648657005831/999250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (3997/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(30936681717619/3997000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7648657005831/999250000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2232344/9765625 : ℝ)*X 0 0+(5461313821/10000000000 : ℝ)*X 0 1+(470307473/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((1175374701/2500000000 : ℝ)*X 1 0+(-1530150571/10000000000 : ℝ)*X 1 1+(6022693797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((2351407881/5000000000 : ℝ)*X 2 0+(2729594131/5000000000 : ℝ)*X 2 1+(-91557053/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((5854160019/10000000000 : ℝ)*X 0 0+(1998216851/5000000000 : ℝ)*X 0 1+(1309229679/5000000000 : ℝ)*X 0 2+(5854160019/10000000000 : ℝ)*X 1 0+(1998216851/5000000000 : ℝ)*X 1 1+(1309229679/5000000000 : ℝ)*X 1 2+(5854160019/10000000000 : ℝ)*X 2 0+(1998216851/5000000000 : ℝ)*X 2 1+(1309229679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-88469017/400000000 : ℝ)*X 0 0+(1309092697/2500000000 : ℝ)*X 0 1+(2497165819/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((936503487/2000000000 : ℝ)*X 1 0+(-647843199/5000000000 : ℝ)*X 1 1+(6197950349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4683834471/10000000000 : ℝ)*X 2 0+(2849193683/5000000000 : ℝ)*X 2 1+(-100120277/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((566924241/1000000000 : ℝ)*X 0 0+(4554637379/10000000000 : ℝ)*X 0 1+(2200550981/10000000000 : ℝ)*X 0 2+(566924241/1000000000 : ℝ)*X 1 0+(4554637379/10000000000 : ℝ)*X 1 1+(2200550981/10000000000 : ℝ)*X 1 2+(566924241/1000000000 : ℝ)*X 2 0+(4554637379/10000000000 : ℝ)*X 2 1+(2200550981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1966316771/10000000000 : ℝ)*X 0 0+(5394348277/10000000000 : ℝ)*X 0 1+(5027359797/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((181650897/400000000 : ℝ)*X 1 0+(-373772743/2500000000 : ℝ)*X 1 1+(1239050429/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((1005430663/2000000000 : ℝ)*X 2 0+(5392221423/10000000000 : ℝ)*X 2 1+(-1969378687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((390819251/625000000 : ℝ)*X 0 0+(244269349/625000000 : ℝ)*X 0 1+(2207141819/10000000000 : ℝ)*X 0 2+(390819251/625000000 : ℝ)*X 1 0+(244269349/625000000 : ℝ)*X 1 1+(2207141819/10000000000 : ℝ)*X 1 2+(390819251/625000000 : ℝ)*X 2 0+(244269349/625000000 : ℝ)*X 2 1+(2207141819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-499490451/2500000000 : ℝ)*X 0 0+(5703539749/10000000000 : ℝ)*X 0 1+(4681928011/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((4994194147/10000000000 : ℝ)*X 1 0+(-1292659551/10000000000 : ℝ)*X 1 1+(2953314339/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((2255607821/5000000000 : ℝ)*X 2 0+(2850706569/5000000000 : ℝ)*X 2 1+(-2211750599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((6329707299/10000000000 : ℝ)*X 0 0+(85352509/250000000 : ℝ)*X 0 1+(1330087741/5000000000 : ℝ)*X 0 2+(6329707299/10000000000 : ℝ)*X 1 0+(85352509/250000000 : ℝ)*X 1 1+(1330087741/5000000000 : ℝ)*X 1 2+(6329707299/10000000000 : ℝ)*X 2 0+(85352509/250000000 : ℝ)*X 2 1+(1330087741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314055_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((2637/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2637/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13966875625886073368095214679/754414404520000000000000000000000 : ℝ) := by norm_num
    linear_combination (2363761104409/1000000000000 : ℝ)*(base49) + (1501559/1000000000000 : ℝ)*(base60) + (15185252761503/1000000000000 : ℝ)*(major_s3_0) + (15185252761503/1000000000000 : ℝ)*(major_s3_1) + (15185252761503/1000000000000 : ℝ)*(major_s3_2) + (197587429/500000000000 : ℝ)*(sp_s3_0) + (49140201/200000000000 : ℝ)*(sp_s3_2) + (125660251/1000000000000 : ℝ)*(sp_s3_6) + (21545009150261/1000000000000 : ℝ)*(sp_s3_7) + (21544836726171/1000000000000 : ℝ)*(sp_s3_8) + (21544682306223/1000000000000 : ℝ)*(sp_s3_9) + (1764993873291/200000000000 : ℝ)*(sp_s3_13) + (141899737/250000000000 : ℝ)*(sp_s3_15) + (476317891/1000000000000 : ℝ)*(sp_s3_23) + (4412547513353/500000000000 : ℝ)*(f.failure) + (21545404325119/1000000000000 : ℝ)*(f.sum) + (495257942834886299/957281500000000000000000000000 : ℝ)*base63 + (59994506352629/124906250000000000000000000 : ℝ)*base64 + (72074064890727/268240000000000000000000000 : ℝ)*base66 + (1186769986902557/3997000000000000000000000000 : ℝ)*base69 + (10263268350741114893/39374447000000000000000000000000 : ℝ)*base70 + (784505752609/4925500000000000000000000 : ℝ)*base72 + (7277356516213/95800000000000000000000000 : ℝ)*base74 + (265200781324329/1970200000000000000000000000 : ℝ)*base76 + (76505018369952061/2642432240000000000000000000000 : ℝ)*base78 + (12643/50000000000000000 : ℝ)*base86 + (12643/50000000000000000 : ℝ)*base88 + (12643/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22033/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22033/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3424261306344293146862498031/377207202260000000000000000000000 : ℝ) := by norm_num
    linear_combination (8556169809/3906250000 : ℝ)*(base49) + (1794429/1000000000000 : ℝ)*(base60) + (7272575703791/500000000000 : ℝ)*(major_s3_0) + (7272575703791/500000000000 : ℝ)*(major_s3_1) + (7272575703791/500000000000 : ℝ)*(major_s3_2) + (85233767/500000000000 : ℝ)*(sp_s3_1) + (25916677/1000000000000 : ℝ)*(sp_s3_2) + (20611949/250000000000 : ℝ)*(sp_s3_7) + (35878641/500000000000 : ℝ)*(sp_s3_8) + (10318562515493/500000000000 : ℝ)*(sp_s3_14) + (20636965253967/1000000000000 : ℝ)*(sp_s3_15) + (4127436312421/200000000000 : ℝ)*(sp_s3_16) + (845302474781/100000000000 : ℝ)*(sp_s3_20) + (6756259/100000000000 : ℝ)*(sp_s3_27) + (2641591347/312500000 : ℝ)*(f.failure) + (10318603739391/500000000000 : ℝ)*(f.sum) + (271472784634070497/478640750000000000000000000000 : ℝ)*base62 + (74409471680799/124906250000000000000000000 : ℝ)*base65 + (14366413103151/134120000000000000000000000 : ℝ)*base66 + (1339863551853721/1998500000000000000000000000 : ℝ)*base68 + (7877507206410521979/19687223500000000000000000000000 : ℝ)*base71 + (30960959163683/98510000000000000000000000 : ℝ)*base72 + (8183911965169/47900000000000000000000000 : ℝ)*base75 + (221770378558317/985100000000000000000000000 : ℝ)*base77 + (122215048643339417/264243224000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (11/62500000000000 : ℝ)*base87 + (11/62500000000000 : ℝ)*base89 + (11/62500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21281/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21281/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (84526404176601853686598017/4921805875000000000000000000000 : ℝ) := by norm_num
    linear_combination (246811/125000000000 : ℝ)*(base39) + (2431077/500000000000 : ℝ)*(base40) + (144308209437/62500000000 : ℝ)*(base49) + (3638345076019/250000000000 : ℝ)*(major_s3_0) + (3638345076019/250000000000 : ℝ)*(major_s3_1) + (3638345076019/250000000000 : ℝ)*(major_s3_2) + (189074681/500000000000 : ℝ)*(sp_s3_0) + (93639073/200000000000 : ℝ)*(sp_s3_1) + (211312313/1000000000000 : ℝ)*(sp_s3_2) + (63815391/250000000000 : ℝ)*(sp_s3_20) + (4129700420021/200000000000 : ℝ)*(sp_s3_21) + (20648412054103/1000000000000 : ℝ)*(sp_s3_22) + (10324334468577/500000000000 : ℝ)*(sp_s3_23) + (8457619372493/1000000000000 : ℝ)*(sp_s3_27) + (8457874634057/1000000000000 : ℝ)*(f.failure) + (20648880249467/1000000000000 : ℝ)*(f.sum) + (15528462510395571/478640750000000000000000000000 : ℝ)*base62 + (548513534719881/999250000000000000000000000 : ℝ)*base65 + (35014166429779/67060000000000000000000000 : ℝ)*base67 + (60738053631161/999250000000000000000000000 : ℝ)*base69 + (4658150414240896411/9843611750000000000000000000000 : ℝ)*base71 + (81708620936707/98510000000000000000000000 : ℝ)*base72 + (402691314273/748437500000000000000000 : ℝ)*base75 + (445677974375193/492550000000000000000000000 : ℝ)*base77 + (558609748867630611/660608060000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (46067/100000000000000000 : ℝ)*base86 + (46067/100000000000000000 : ℝ)*base88 + (46067/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((9851/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9851/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10059/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10059/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3997/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3997/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2637/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2637/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22033/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22033/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21281/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21281/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314055_s3 p hpa hpb X hX hprev2

#print axioms solution
