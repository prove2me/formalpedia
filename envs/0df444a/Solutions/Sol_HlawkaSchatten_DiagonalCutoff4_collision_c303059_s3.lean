-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303059_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:57:01.158532+00:00
-- url     : https://prove2.me/submissions/83133e3c-4097-454e-9e79-c21e95a2a721

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
theorem collision_support_c303059_s3_s3_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3977035173/10000000000 : ℝ)*x 0 + (1096681153/2000000000 : ℝ)*x 1 + (175718437/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3977035173/10000000000 : ℝ)^33 ≤ (925269979819/3125000000000 : ℝ)^25 := by
    have hnat : (3977035173 : ℕ)^33*3125000000000^25 ≤ 925269979819^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3977035173 10000000000 925269979819 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096681153/2000000000 : ℝ)^33 ≤ (2262124542787/5000000000000 : ℝ)^25 := by
    have hnat : (1096681153 : ℕ)^33*5000000000000^25 ≤ 2262124542787^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096681153 2000000000 2262124542787 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175718437/500000000 : ℝ)^33 ≤ (25148869772217/100000000000000 : ℝ)^25 := by
    have hnat : (175718437 : ℕ)^33*100000000000000^25 ≤ 25148869772217^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175718437 500000000 25148869772217 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3977035173/10000000000 : ℝ), (1096681153/2000000000 : ℝ), (175718437/500000000 : ℝ)] ![(925269979819/3125000000000 : ℝ), (2262124542787/5000000000000 : ℝ), (25148869772217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3977035173/10000000000 : ℝ)|^33 ≤ (925269979819/3125000000000 : ℝ)^25
        have hw : |(3977035173/10000000000 : ℝ)|=(3977035173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1096681153/2000000000 : ℝ)|^33 ≤ (2262124542787/5000000000000 : ℝ)^25
        have hw : |(1096681153/2000000000 : ℝ)|=(1096681153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(175718437/500000000 : ℝ)|^33 ≤ (25148869772217/100000000000000 : ℝ)^25
        have hw : |(175718437/500000000 : ℝ)|=(175718437/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s3_s3_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-682894157/2500000000 : ℝ)*x 0 + (1195656717/5000000000 : ℝ)*x 1 + (368480239/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (682894157/2500000000 : ℝ)^33 ≤ (3606580813779/20000000000000 : ℝ)^25 := by
    have hnat : (682894157 : ℕ)^33*20000000000000^25 ≤ 3606580813779^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682894157 2500000000 3606580813779 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1195656717/5000000000 : ℝ)^33 ≤ (15128650320083/100000000000000 : ℝ)^25 := by
    have hnat : (1195656717 : ℕ)^33*100000000000000^25 ≤ 15128650320083^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195656717 5000000000 15128650320083 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368480239/500000000 : ℝ)^33 ≤ (16709611398843/25000000000000 : ℝ)^25 := by
    have hnat : (368480239 : ℕ)^33*25000000000000^25 ≤ 16709611398843^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368480239 500000000 16709611398843 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-682894157/2500000000 : ℝ), (1195656717/5000000000 : ℝ), (368480239/500000000 : ℝ)] ![(3606580813779/20000000000000 : ℝ), (15128650320083/100000000000000 : ℝ), (16709611398843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-682894157/2500000000 : ℝ)|^33 ≤ (3606580813779/20000000000000 : ℝ)^25
        have hw : |(-682894157/2500000000 : ℝ)|=(682894157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1195656717/5000000000 : ℝ)|^33 ≤ (15128650320083/100000000000000 : ℝ)^25
        have hw : |(1195656717/5000000000 : ℝ)|=(1195656717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(368480239/500000000 : ℝ)|^33 ≤ (16709611398843/25000000000000 : ℝ)^25
        have hw : |(368480239/500000000 : ℝ)|=(368480239/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s3_s3_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2797926867/10000000000 : ℝ)*x 0 + (-287946971/1250000000 : ℝ)*x 1 + (115343103/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2797926867/10000000000 : ℝ)^33 ≤ (1861332640937/10000000000000 : ℝ)^25 := by
    have hnat : (2797926867 : ℕ)^33*10000000000000^25 ≤ 1861332640937^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2797926867 10000000000 1861332640937 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287946971/1250000000 : ℝ)^33 ≤ (7200146055153/50000000000000 : ℝ)^25 := by
    have hnat : (287946971 : ℕ)^33*50000000000000^25 ≤ 7200146055153^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287946971 1250000000 7200146055153 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115343103/156250000 : ℝ)^33 ≤ (66986381463731/100000000000000 : ℝ)^25 := by
    have hnat : (115343103 : ℕ)^33*100000000000000^25 ≤ 66986381463731^25*156250000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115343103 156250000 66986381463731 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2797926867/10000000000 : ℝ), (-287946971/1250000000 : ℝ), (115343103/156250000 : ℝ)] ![(1861332640937/10000000000000 : ℝ), (7200146055153/50000000000000 : ℝ), (66986381463731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2797926867/10000000000 : ℝ)|^33 ≤ (1861332640937/10000000000000 : ℝ)^25
        have hw : |(2797926867/10000000000 : ℝ)|=(2797926867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-287946971/1250000000 : ℝ)|^33 ≤ (7200146055153/50000000000000 : ℝ)^25
        have hw : |(-287946971/1250000000 : ℝ)|=(287946971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(115343103/156250000 : ℝ)|^33 ≤ (66986381463731/100000000000000 : ℝ)^25
        have hw : |(115343103/156250000 : ℝ)|=(115343103/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s3_s3_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (525030883/1000000000 : ℝ)*x 0 + (3278169639/5000000000 : ℝ)*x 1 + (-182187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525030883/1000000000 : ℝ)^33 ≤ (21360627482769/50000000000000 : ℝ)^25 := by
    have hnat : (525030883 : ℕ)^33*50000000000000^25 ≤ 21360627482769^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525030883 1000000000 21360627482769 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3278169639/5000000000 : ℝ)^33 ≤ (5727868957383/10000000000000 : ℝ)^25 := by
    have hnat : (3278169639 : ℕ)^33*10000000000000^25 ≤ 5727868957383^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3278169639 5000000000 5727868957383 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182187/10000000000 : ℝ)^33 ≤ (443581/800000000000 : ℝ)^25 := by
    have hnat : (182187 : ℕ)^33*800000000000^25 ≤ 443581^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182187 10000000000 443581 800000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525030883/1000000000 : ℝ), (3278169639/5000000000 : ℝ), (-182187/10000000000 : ℝ)] ![(21360627482769/50000000000000 : ℝ), (5727868957383/10000000000000 : ℝ), (443581/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525030883/1000000000 : ℝ)|^33 ≤ (21360627482769/50000000000000 : ℝ)^25
        have hw : |(525030883/1000000000 : ℝ)|=(525030883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3278169639/5000000000 : ℝ)|^33 ≤ (5727868957383/10000000000000 : ℝ)^25
        have hw : |(3278169639/5000000000 : ℝ)|=(3278169639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-182187/10000000000 : ℝ)|^33 ≤ (443581/800000000000 : ℝ)^25
        have hw : |(-182187/10000000000 : ℝ)|=(182187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s3_s3_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1503979027/5000000000 : ℝ)*x 0 + (1841344109/2500000000 : ℝ)*x 1 + (209850227/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1503979027/5000000000 : ℝ)^33 ≤ (20479471455247/100000000000000 : ℝ)^25 := by
    have hnat : (1503979027 : ℕ)^33*100000000000000^25 ≤ 20479471455247^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503979027 5000000000 20479471455247 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1841344109/2500000000 : ℝ)^33 ≤ (33393914874027/50000000000000 : ℝ)^25 := by
    have hnat : (1841344109 : ℕ)^33*50000000000000^25 ≤ 33393914874027^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841344109 2500000000 33393914874027 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209850227/1000000000 : ℝ)^33 ≤ (3183174696419/25000000000000 : ℝ)^25 := by
    have hnat : (209850227 : ℕ)^33*25000000000000^25 ≤ 3183174696419^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209850227 1000000000 3183174696419 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1503979027/5000000000 : ℝ), (1841344109/2500000000 : ℝ), (209850227/1000000000 : ℝ)] ![(20479471455247/100000000000000 : ℝ), (33393914874027/50000000000000 : ℝ), (3183174696419/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1503979027/5000000000 : ℝ)|^33 ≤ (20479471455247/100000000000000 : ℝ)^25
        have hw : |(1503979027/5000000000 : ℝ)|=(1503979027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1841344109/2500000000 : ℝ)|^33 ≤ (33393914874027/50000000000000 : ℝ)^25
        have hw : |(1841344109/2500000000 : ℝ)|=(1841344109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209850227/1000000000 : ℝ)|^33 ≤ (3183174696419/25000000000000 : ℝ)^25
        have hw : |(209850227/1000000000 : ℝ)|=(209850227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s3_s3_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2503464269/10000000000 : ℝ)*x 0 + (1421217533/5000000000 : ℝ)*x 1 + (7209016441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2503464269/10000000000 : ℝ)^33 ≤ (16072174698387/100000000000000 : ℝ)^25 := by
    have hnat : (2503464269 : ℕ)^33*100000000000000^25 ≤ 16072174698387^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503464269 10000000000 16072174698387 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1421217533/5000000000 : ℝ)^33 ≤ (9502579973101/50000000000000 : ℝ)^25 := by
    have hnat : (1421217533 : ℕ)^33*50000000000000^25 ≤ 9502579973101^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1421217533 5000000000 9502579973101 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7209016441/10000000000 : ℝ)^33 ≤ (3246133267149/5000000000000 : ℝ)^25 := by
    have hnat : (7209016441 : ℕ)^33*5000000000000^25 ≤ 3246133267149^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7209016441 10000000000 3246133267149 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2503464269/10000000000 : ℝ), (1421217533/5000000000 : ℝ), (7209016441/10000000000 : ℝ)] ![(16072174698387/100000000000000 : ℝ), (9502579973101/50000000000000 : ℝ), (3246133267149/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2503464269/10000000000 : ℝ)|^33 ≤ (16072174698387/100000000000000 : ℝ)^25
        have hw : |(-2503464269/10000000000 : ℝ)|=(2503464269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1421217533/5000000000 : ℝ)|^33 ≤ (9502579973101/50000000000000 : ℝ)^25
        have hw : |(1421217533/5000000000 : ℝ)|=(1421217533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7209016441/10000000000 : ℝ)|^33 ≤ (3246133267149/5000000000000 : ℝ)^25
        have hw : |(7209016441/10000000000 : ℝ)|=(7209016441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s3_s3_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1240310609/5000000000 : ℝ)*x 0 + (-2848050011/10000000000 : ℝ)*x 1 + (7221103529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1240310609/5000000000 : ℝ)^33 ≤ (15878877541791/100000000000000 : ℝ)^25 := by
    have hnat : (1240310609 : ℕ)^33*100000000000000^25 ≤ 15878877541791^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240310609 5000000000 15878877541791 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2848050011/10000000000 : ℝ)^33 ≤ (19054732078063/100000000000000 : ℝ)^25 := by
    have hnat : (2848050011 : ℕ)^33*100000000000000^25 ≤ 19054732078063^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848050011 10000000000 19054732078063 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7221103529/10000000000 : ℝ)^33 ≤ (6506639036601/10000000000000 : ℝ)^25 := by
    have hnat : (7221103529 : ℕ)^33*10000000000000^25 ≤ 6506639036601^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7221103529 10000000000 6506639036601 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1240310609/5000000000 : ℝ), (-2848050011/10000000000 : ℝ), (7221103529/10000000000 : ℝ)] ![(15878877541791/100000000000000 : ℝ), (19054732078063/100000000000000 : ℝ), (6506639036601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1240310609/5000000000 : ℝ)|^33 ≤ (15878877541791/100000000000000 : ℝ)^25
        have hw : |(1240310609/5000000000 : ℝ)|=(1240310609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2848050011/10000000000 : ℝ)|^33 ≤ (19054732078063/100000000000000 : ℝ)^25
        have hw : |(-2848050011/10000000000 : ℝ)|=(2848050011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7221103529/10000000000 : ℝ)|^33 ≤ (6506639036601/10000000000000 : ℝ)^25
        have hw : |(7221103529/10000000000 : ℝ)|=(7221103529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s3_s3_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7111852997/10000000000 : ℝ)*x 0 + (57925493/125000000 : ℝ)*x 1 + (2147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7111852997/10000000000 : ℝ)^33 ≤ (63770123474447/100000000000000 : ℝ)^25 := by
    have hnat : (7111852997 : ℕ)^33*100000000000000^25 ≤ 63770123474447^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7111852997 10000000000 63770123474447 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57925493/125000000 : ℝ)^33 ≤ (3622987519301/10000000000000 : ℝ)^25 := by
    have hnat : (57925493 : ℕ)^33*10000000000000^25 ≤ 3622987519301^25*125000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57925493 125000000 3622987519301 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2147/2000000000 : ℝ)^33 ≤ (660129/50000000000000 : ℝ)^25 := by
    have hnat : (2147 : ℕ)^33*50000000000000^25 ≤ 660129^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147 2000000000 660129 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7111852997/10000000000 : ℝ), (57925493/125000000 : ℝ), (2147/2000000000 : ℝ)] ![(63770123474447/100000000000000 : ℝ), (3622987519301/10000000000000 : ℝ), (660129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7111852997/10000000000 : ℝ)|^33 ≤ (63770123474447/100000000000000 : ℝ)^25
        have hw : |(7111852997/10000000000 : ℝ)|=(7111852997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57925493/125000000 : ℝ)|^33 ≤ (3622987519301/10000000000000 : ℝ)^25
        have hw : |(57925493/125000000 : ℝ)|=(57925493/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2147/2000000000 : ℝ)|^33 ≤ (660129/50000000000000 : ℝ)^25
        have hw : |(2147/2000000000 : ℝ)|=(2147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s3_s3_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6020099791/10000000000 : ℝ)*x 0 + (4524517383/10000000000 : ℝ)*x 1 + (2220511299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6020099791/10000000000 : ℝ)^33 ≤ (51177241252761/100000000000000 : ℝ)^25 := by
    have hnat : (6020099791 : ℕ)^33*100000000000000^25 ≤ 51177241252761^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6020099791 10000000000 51177241252761 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524517383/10000000000 : ℝ)^33 ≤ (35103901286417/100000000000000 : ℝ)^25 := by
    have hnat : (4524517383 : ℕ)^33*100000000000000^25 ≤ 35103901286417^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524517383 10000000000 35103901286417 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2220511299/10000000000 : ℝ)^33 ≤ (685942872383/5000000000000 : ℝ)^25 := by
    have hnat : (2220511299 : ℕ)^33*5000000000000^25 ≤ 685942872383^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220511299 10000000000 685942872383 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6020099791/10000000000 : ℝ), (4524517383/10000000000 : ℝ), (2220511299/10000000000 : ℝ)] ![(51177241252761/100000000000000 : ℝ), (35103901286417/100000000000000 : ℝ), (685942872383/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6020099791/10000000000 : ℝ)|^33 ≤ (51177241252761/100000000000000 : ℝ)^25
        have hw : |(6020099791/10000000000 : ℝ)|=(6020099791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524517383/10000000000 : ℝ)|^33 ≤ (35103901286417/100000000000000 : ℝ)^25
        have hw : |(4524517383/10000000000 : ℝ)|=(4524517383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2220511299/10000000000 : ℝ)|^33 ≤ (685942872383/5000000000000 : ℝ)^25
        have hw : |(2220511299/10000000000 : ℝ)|=(2220511299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s3_s3_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3345646587/10000000000 : ℝ)*x 0 + (334547921/1000000000 : ℝ)*x 1 + (6170047959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3345646587/10000000000 : ℝ)^33 ≤ (23567509078773/100000000000000 : ℝ)^25 := by
    have hnat : (3345646587 : ℕ)^33*100000000000000^25 ≤ 23567509078773^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3345646587 10000000000 23567509078773 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (334547921/1000000000 : ℝ)^33 ≤ (23565952755347/100000000000000 : ℝ)^25 := by
    have hnat : (334547921 : ℕ)^33*100000000000000^25 ≤ 23565952755347^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334547921 1000000000 23565952755347 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6170047959/10000000000 : ℝ)^33 ≤ (26433269073623/50000000000000 : ℝ)^25 := by
    have hnat : (6170047959 : ℕ)^33*50000000000000^25 ≤ 26433269073623^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6170047959 10000000000 26433269073623 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3345646587/10000000000 : ℝ), (334547921/1000000000 : ℝ), (6170047959/10000000000 : ℝ)] ![(23567509078773/100000000000000 : ℝ), (23565952755347/100000000000000 : ℝ), (26433269073623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3345646587/10000000000 : ℝ)|^33 ≤ (23567509078773/100000000000000 : ℝ)^25
        have hw : |(-3345646587/10000000000 : ℝ)|=(3345646587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(334547921/1000000000 : ℝ)|^33 ≤ (23565952755347/100000000000000 : ℝ)^25
        have hw : |(334547921/1000000000 : ℝ)|=(334547921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6170047959/10000000000 : ℝ)|^33 ≤ (26433269073623/50000000000000 : ℝ)^25
        have hw : |(6170047959/10000000000 : ℝ)|=(6170047959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s3_s3_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (133095643/400000000 : ℝ)*x 0 + (-3326997297/10000000000 : ℝ)*x 1 + (6200200593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133095643/400000000 : ℝ)^33 ≤ (4679582133719/20000000000000 : ℝ)^25 := by
    have hnat : (133095643 : ℕ)^33*20000000000000^25 ≤ 4679582133719^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133095643 400000000 4679582133719 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3326997297/10000000000 : ℝ)^33 ≤ (11697127821647/50000000000000 : ℝ)^25 := by
    have hnat : (3326997297 : ℕ)^33*50000000000000^25 ≤ 11697127821647^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3326997297 10000000000 11697127821647 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6200200593/10000000000 : ℝ)^33 ≤ (1662744802197/3125000000000 : ℝ)^25 := by
    have hnat : (6200200593 : ℕ)^33*3125000000000^25 ≤ 1662744802197^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6200200593 10000000000 1662744802197 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133095643/400000000 : ℝ), (-3326997297/10000000000 : ℝ), (6200200593/10000000000 : ℝ)] ![(4679582133719/20000000000000 : ℝ), (11697127821647/50000000000000 : ℝ), (1662744802197/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133095643/400000000 : ℝ)|^33 ≤ (4679582133719/20000000000000 : ℝ)^25
        have hw : |(133095643/400000000 : ℝ)|=(133095643/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3326997297/10000000000 : ℝ)|^33 ≤ (11697127821647/50000000000000 : ℝ)^25
        have hw : |(-3326997297/10000000000 : ℝ)|=(3326997297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6200200593/10000000000 : ℝ)|^33 ≤ (1662744802197/3125000000000 : ℝ)^25
        have hw : |(6200200593/10000000000 : ℝ)|=(6200200593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s3_s3_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7228901867/10000000000 : ℝ)*x 0 + (2249403691/5000000000 : ℝ)*x 1 + (2669/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7228901867/10000000000 : ℝ)^33 ≤ (32579579818701/50000000000000 : ℝ)^25 := by
    have hnat : (7228901867 : ℕ)^33*50000000000000^25 ≤ 32579579818701^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7228901867 10000000000 32579579818701 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249403691/5000000000 : ℝ)^33 ≤ (17420417980793/50000000000000 : ℝ)^25 := by
    have hnat : (2249403691 : ℕ)^33*50000000000000^25 ≤ 17420417980793^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249403691 5000000000 17420417980793 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2669/1000000000 : ℝ)^33 ≤ (549149/12500000000000 : ℝ)^25 := by
    have hnat : (2669 : ℕ)^33*12500000000000^25 ≤ 549149^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2669 1000000000 549149 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7228901867/10000000000 : ℝ), (2249403691/5000000000 : ℝ), (2669/1000000000 : ℝ)] ![(32579579818701/50000000000000 : ℝ), (17420417980793/50000000000000 : ℝ), (549149/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7228901867/10000000000 : ℝ)|^33 ≤ (32579579818701/50000000000000 : ℝ)^25
        have hw : |(7228901867/10000000000 : ℝ)|=(7228901867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249403691/5000000000 : ℝ)|^33 ≤ (17420417980793/50000000000000 : ℝ)^25
        have hw : |(2249403691/5000000000 : ℝ)|=(2249403691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2669/1000000000 : ℝ)|^33 ≤ (549149/12500000000000 : ℝ)^25
        have hw : |(2669/1000000000 : ℝ)|=(2669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303059_s3_s3_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1081672211/5000000000 : ℝ)*x 0 + (7647593633/10000000000 : ℝ)*x 1 + (640177433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081672211/5000000000 : ℝ)^33 ≤ (13254577290833/100000000000000 : ℝ)^25 := by
    have hnat : (1081672211 : ℕ)^33*100000000000000^25 ≤ 13254577290833^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081672211 5000000000 13254577290833 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7647593633/10000000000 : ℝ)^33 ≤ (17546590818359/25000000000000 : ℝ)^25 := by
    have hnat : (7647593633 : ℕ)^33*25000000000000^25 ≤ 17546590818359^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7647593633 10000000000 17546590818359 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640177433/2500000000 : ℝ)^33 ≤ (258735303503/1562500000000 : ℝ)^25 := by
    have hnat : (640177433 : ℕ)^33*1562500000000^25 ≤ 258735303503^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640177433 2500000000 258735303503 1562500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081672211/5000000000 : ℝ), (7647593633/10000000000 : ℝ), (640177433/2500000000 : ℝ)] ![(13254577290833/100000000000000 : ℝ), (17546590818359/25000000000000 : ℝ), (258735303503/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081672211/5000000000 : ℝ)|^33 ≤ (13254577290833/100000000000000 : ℝ)^25
        have hw : |(1081672211/5000000000 : ℝ)|=(1081672211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7647593633/10000000000 : ℝ)|^33 ≤ (17546590818359/25000000000000 : ℝ)^25
        have hw : |(7647593633/10000000000 : ℝ)|=(7647593633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(640177433/2500000000 : ℝ)|^33 ≤ (258735303503/1562500000000 : ℝ)^25
        have hw : |(640177433/2500000000 : ℝ)|=(640177433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303059_s3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((5031/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5031/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39883/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39883/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(61709/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(61709/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13483/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13483/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2597/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2597/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16663/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16663/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91389/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s3_pow0 : (5031/6250 : ℝ) ^ (131/32 : ℝ) ≤ (10284982314025344207/25000000000000000000 : ℝ) := by
    have hpowers : (5031/6250 : ℝ)^131 ≤ (10284982314025344207/25000000000000000000 : ℝ)^32 := by
      have hnat : (5031 : ℕ)^131*25000000000000000000^32 ≤ 10284982314025344207^32*6250^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5031 6250 10284982314025344207 25000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5031/6250 : ℝ)) (X := (10284982314025344207/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (35284982314025344207/25000000000000000000 : ℝ) ≤ (2175633289233093/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (35284982314025344207/25000000000000000000 : ℝ)^32 ≤ (2175633289233093/2000000000000000 : ℝ)^131 := by
      have hnat : (35284982314025344207 : ℕ)^32*2000000000000000^131 ≤ 2175633289233093^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35284982314025344207 25000000000000000000 2175633289233093 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2175633289233093/2000000000000000 : ℝ)) (X := (35284982314025344207/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (22784982314025344207/12500000000000000000 : ℝ) ≤ (5789777794915373/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (22784982314025344207/12500000000000000000 : ℝ)^32 ≤ (5789777794915373/5000000000000000 : ℝ)^131 := by
      have hnat : (22784982314025344207 : ℕ)^32*5000000000000000^131 ≤ 5789777794915373^131*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22784982314025344207 12500000000000000000 5789777794915373 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5789777794915373/5000000000000000 : ℝ)) (X := (22784982314025344207/12500000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(175633289233093/1609920000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(701389143665281/8049600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (5031/6250 : ℝ)) (alpha := (175633289233093/1609920000000000 : ℝ)) (beta := (701389143665281/8049600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5031/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(175633289233093/1609920000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(701389143665281/8049600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (39883/50000 : ℝ) ^ (131/32 : ℝ) ≤ (4954235988318493751/12500000000000000000 : ℝ) := by
    have hpowers : (39883/50000 : ℝ)^131 ≤ (4954235988318493751/12500000000000000000 : ℝ)^32 := by
      have hnat : (39883 : ℕ)^131*12500000000000000000^32 ≤ 4954235988318493751^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39883 50000 4954235988318493751 12500000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39883/50000 : ℝ)) (X := (4954235988318493751/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (17454235988318493751/12500000000000000000 : ℝ) ≤ (2169939388301993/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (17454235988318493751/12500000000000000000 : ℝ)^32 ≤ (2169939388301993/2000000000000000 : ℝ)^131 := by
      have hnat : (17454235988318493751 : ℕ)^32*2000000000000000^131 ≤ 2169939388301993^131*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17454235988318493751 12500000000000000000 2169939388301993 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2169939388301993/2000000000000000 : ℝ)) (X := (17454235988318493751/12500000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (11204235988318493751/6250000000000000000 : ℝ) ≤ (11532519799699551/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (11204235988318493751/6250000000000000000 : ℝ)^32 ≤ (11532519799699551/10000000000000000 : ℝ)^131 := by
      have hnat : (11204235988318493751 : ℕ)^32*10000000000000000^131 ≤ 11532519799699551^131*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11204235988318493751 6250000000000000000 11532519799699551 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11532519799699551/10000000000000000 : ℝ)) (X := (11204235988318493751/6250000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(169939388301993/1595320000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(341411429094793/3988300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (39883/50000 : ℝ)) (alpha := (169939388301993/1595320000000000 : ℝ)) (beta := (341411429094793/3988300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (39883/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(169939388301993/1595320000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(341411429094793/3988300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (61709/100000 : ℝ) ^ (131/32 : ℝ) ≤ (13859233360768602001/100000000000000000000 : ℝ) := by
    have hpowers : (61709/100000 : ℝ)^131 ≤ (13859233360768602001/100000000000000000000 : ℝ)^32 := by
      have hnat : (61709 : ℕ)^131*100000000000000000000^32 ≤ 13859233360768602001^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61709 100000 13859233360768602001 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61709/100000 : ℝ)) (X := (13859233360768602001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (113859233360768602001/100000000000000000000 : ℝ) ≤ (645133155302487/625000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (113859233360768602001/100000000000000000000 : ℝ)^32 ≤ (645133155302487/625000000000000 : ℝ)^131 := by
      have hnat : (113859233360768602001 : ℕ)^32*625000000000000^131 ≤ 645133155302487^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113859233360768602001 100000000000000000000 645133155302487 625000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (645133155302487/625000000000000 : ℝ)) (X := (113859233360768602001/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (63859233360768602001/50000000000000000000 : ℝ) ≤ (10615858016285223/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (63859233360768602001/50000000000000000000 : ℝ)^32 ≤ (10615858016285223/10000000000000000 : ℝ)^131 := by
      have hnat : (63859233360768602001 : ℕ)^32*10000000000000000^131 ≤ 10615858016285223^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63859233360768602001 50000000000000000000 10615858016285223 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10615858016285223/10000000000000000 : ℝ)) (X := (63859233360768602001/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(875354578369/16768750000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(293727531445431/6170900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (61709/100000 : ℝ)) (alpha := (875354578369/16768750000000 : ℝ)) (beta := (293727531445431/6170900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (61709/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(875354578369/16768750000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(293727531445431/6170900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_6 : ((3977035173/10000000000 : ℝ)*X 0 0+(1096681153/2000000000 : ℝ)*X 0 1+(175718437/500000000 : ℝ)*X 0 2+(3977035173/10000000000 : ℝ)*X 1 0+(1096681153/2000000000 : ℝ)*X 1 1+(175718437/500000000 : ℝ)*X 1 2+(3977035173/10000000000 : ℝ)*X 2 0+(1096681153/2000000000 : ℝ)*X 2 1+(175718437/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-682894157/2500000000 : ℝ)*X 0 0+(1195656717/5000000000 : ℝ)*X 0 1+(368480239/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((2797926867/10000000000 : ℝ)*X 1 0+(-287946971/1250000000 : ℝ)*X 1 1+(115343103/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((525030883/1000000000 : ℝ)*X 2 0+(3278169639/5000000000 : ℝ)*X 2 1+(-182187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((1503979027/5000000000 : ℝ)*X 0 0+(1841344109/2500000000 : ℝ)*X 0 1+(209850227/1000000000 : ℝ)*X 0 2+(1503979027/5000000000 : ℝ)*X 1 0+(1841344109/2500000000 : ℝ)*X 1 1+(209850227/1000000000 : ℝ)*X 1 2+(1503979027/5000000000 : ℝ)*X 2 0+(1841344109/2500000000 : ℝ)*X 2 1+(209850227/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-2503464269/10000000000 : ℝ)*X 0 0+(1421217533/5000000000 : ℝ)*X 0 1+(7209016441/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((1240310609/5000000000 : ℝ)*X 1 0+(-2848050011/10000000000 : ℝ)*X 1 1+(7221103529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((7111852997/10000000000 : ℝ)*X 2 0+(57925493/125000000 : ℝ)*X 2 1+(2147/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((6020099791/10000000000 : ℝ)*X 0 0+(4524517383/10000000000 : ℝ)*X 0 1+(2220511299/10000000000 : ℝ)*X 0 2+(6020099791/10000000000 : ℝ)*X 1 0+(4524517383/10000000000 : ℝ)*X 1 1+(2220511299/10000000000 : ℝ)*X 1 2+(6020099791/10000000000 : ℝ)*X 2 0+(4524517383/10000000000 : ℝ)*X 2 1+(2220511299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-3345646587/10000000000 : ℝ)*X 0 0+(334547921/1000000000 : ℝ)*X 0 1+(6170047959/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((133095643/400000000 : ℝ)*X 1 0+(-3326997297/10000000000 : ℝ)*X 1 1+(6200200593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((7228901867/10000000000 : ℝ)*X 2 0+(2249403691/5000000000 : ℝ)*X 2 1+(2669/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((1081672211/5000000000 : ℝ)*X 0 0+(7647593633/10000000000 : ℝ)*X 0 1+(640177433/2500000000 : ℝ)*X 0 2+(1081672211/5000000000 : ℝ)*X 1 0+(7647593633/10000000000 : ℝ)*X 1 1+(640177433/2500000000 : ℝ)*X 1 2+(1081672211/5000000000 : ℝ)*X 2 0+(7647593633/10000000000 : ℝ)*X 2 1+(640177433/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303059_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((13483/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13483/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (165672465195686255131485898769/14355936900240000000000000000000000 : ℝ) := by norm_num
    linear_combination (256075786993/500000000000 : ℝ)*(base7) + (419579/100000000000 : ℝ)*(base19) + (468837959813/1000000000000 : ℝ)*(base60) + (323240879617/100000000000 : ℝ)*(major_s3_0) + (323240879617/100000000000 : ℝ)*(major_s3_1) + (323240879617/100000000000 : ℝ)*(major_s3_2) + (41513/20000000000 : ℝ)*(sp_s3_6) + (1000962647499/250000000000 : ℝ)*(sp_s3_7) + (400376821907/100000000000 : ℝ)*(sp_s3_8) + (800771612469/200000000000 : ℝ)*(sp_s3_9) + (2661045320209/1000000000000 : ℝ)*(sp_s3_13) + (7472349/1000000000000 : ℝ)*(sp_s3_14) + (21411871/250000000000 : ℝ)*(sp_s3_15) + (26393371/1000000000000 : ℝ)*(sp_s3_27) + (537230553811/250000000000 : ℝ)*(f.failure) + (800771612469/200000000000 : ℝ)*(f.sum) + (42863363153509593/428024356000000000000000000000 : ℝ)*base63 + (580487176237/38568125000000000000000000 : ℝ)*base65 + (32276693552293/99707500000000000000000000 : ℝ)*base66 + (1046472441433/6707500000000000000000000 : ℝ)*base69 + (21557814450197431/397386213120000000000000000000 : ℝ)*base70 + (346586856648289/804960000000000000000000000 : ℝ)*base73 + (195059256782963/797660000000000000000000000 : ℝ)*base74 + (146601353452087/804960000000000000000000000 : ℝ)*base76 + (2522478193570812149/32104219680000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (31/1250000000000000 : ℝ)*base87 + (31/1250000000000000 : ℝ)*base89 + (31/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2597/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2597/4000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (241615684301370548496457214639/13757772862730000000000000000000000 : ℝ) := by norm_num
    linear_combination (431108621881/1000000000000 : ℝ)*(base7) + (4318339/500000000000 : ℝ)*(base59) + (630363925761/1000000000000 : ℝ)*(base60) + (95293351499/25000000000 : ℝ)*(major_s3_0) + (95293351499/25000000000 : ℝ)*(major_s3_1) + (95293351499/25000000000 : ℝ)*(major_s3_2) + (7134141/500000000000 : ℝ)*(sp_s3_6) + (23552171/200000000000 : ℝ)*(sp_s3_7) + (5595951/250000000000 : ℝ)*(sp_s3_8) + (965325319191/200000000000 : ℝ)*(sp_s3_14) + (4826721973007/1000000000000 : ℝ)*(sp_s3_15) + (965248858247/200000000000 : ℝ)*(sp_s3_16) + (185322188981/62500000000 : ℝ)*(sp_s3_20) + (62508197/125000000000 : ℝ)*(sp_s3_23) + (2534060670097/1000000000000 : ℝ)*(f.failure) + (4826744356811/1000000000000 : ℝ)*(f.sum) + (15005642710384121/214012178000000000000000000000 : ℝ)*base62 + (235362053155547/308545000000000000000000000 : ℝ)*base65 + (305233751392991/398830000000000000000000000 : ℝ)*base67 + (1421660212997/6707500000000000000000000 : ℝ)*base69 + (1139822851072866991/2483663832000000000000000000000 : ℝ)*base71 + (6742055005799/201240000000000000000000000 : ℝ)*base73 + (37272174030123/398830000000000000000000000 : ℝ)*base75 + (7819825151903/40248000000000000000000000 : ℝ)*base77 + (722777079785963141/8026054920000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (463/5000000000000000 : ℝ)*base86 + (463/5000000000000000 : ℝ)*base88 + (463/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16663/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16663/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1344734215608198220026746188999/206366592940950000000000000000000000 : ℝ) := by norm_num
    linear_combination (326651/200000000000 : ℝ)*(base7) + (7787/1000000000000 : ℝ)*(base8) + (65439/31250000000 : ℝ)*(base40) + (4671184821/500000000000 : ℝ)*(base50) + (69232187869/200000000000 : ℝ)*(base60) + (3742406914733/1000000000000 : ℝ)*(major_s3_0) + (3742406914733/1000000000000 : ℝ)*(major_s3_1) + (3742406914733/1000000000000 : ℝ)*(major_s3_2) + (100652239/1000000000000 : ℝ)*(sp_s3_13) + (37591561/100000000000 : ℝ)*(sp_s3_16) + (2498419515951/500000000000 : ℝ)*(sp_s3_21) + (499683903969/100000000000 : ℝ)*(sp_s3_22) + (62455789051/12500000000 : ℝ)*(sp_s3_23) + (2487872603629/1000000000000 : ℝ)*(sp_s3_27) + (621992905653/250000000000 : ℝ)*(f.failure) + (499683903969/100000000000 : ℝ)*(f.sum) + (23892208381045975077/21401217800000000000000000000000 : ℝ)*base62 + (2337729157702367/6170900000000000000000000000 : ℝ)*base64 + (2300165643817189/3988300000000000000000000000 : ℝ)*base67 + (21139909799913/67075000000000000000000000 : ℝ)*base68 + (513436001871006610927/496732766400000000000000000000000 : ℝ)*base70 + (2705361153890093/8049600000000000000000000000 : ℝ)*base73 + (307734314428099/1595320000000000000000000000 : ℝ)*base74 + (1013183374211263/1609920000000000000000000000 : ℝ)*base76 + (123049152538032354143/321042196800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (37/1250000000000000 : ℝ)*base86 + (37/1250000000000000 : ℝ)*base88 + (37/1250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((5031/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5031/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39883/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39883/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(61709/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(61709/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13483/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13483/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2597/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2597/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16663/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16663/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303059_s3 p hpa hpb X hX hprev2

#print axioms solution
