-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:07:15.979885+00:00
-- url     : https://prove2.me/submissions/f2528aed-dcb6-4058-b050-4560d47b24ef

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
theorem collision_support_c316055_s1_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-301253281/2000000000 : ℝ)*x 0 + (722779379/1250000000 : ℝ)*x 1 + (491052983/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (301253281/2000000000 : ℝ)^77 ≤ (9167891661433/100000000000000 : ℝ)^61 := by
    have hnat : (301253281 : ℕ)^77*100000000000000^61 ≤ 9167891661433^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301253281 2000000000 9167891661433 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (722779379/1250000000 : ℝ)^77 ≤ (6260436810297/12500000000000 : ℝ)^61 := by
    have hnat : (722779379 : ℕ)^77*12500000000000^61 ≤ 6260436810297^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722779379 1250000000 6260436810297 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491052983/1000000000 : ℝ)^77 ≤ (40748613840601/100000000000000 : ℝ)^61 := by
    have hnat : (491052983 : ℕ)^77*100000000000000^61 ≤ 40748613840601^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491052983 1000000000 40748613840601 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-301253281/2000000000 : ℝ), (722779379/1250000000 : ℝ), (491052983/1000000000 : ℝ)] ![(9167891661433/100000000000000 : ℝ), (6260436810297/12500000000000 : ℝ), (40748613840601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-301253281/2000000000 : ℝ)|^77 ≤ (9167891661433/100000000000000 : ℝ)^61
        have hw : |(-301253281/2000000000 : ℝ)|=(301253281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(722779379/1250000000 : ℝ)|^77 ≤ (6260436810297/12500000000000 : ℝ)^61
        have hw : |(722779379/1250000000 : ℝ)|=(722779379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(491052983/1000000000 : ℝ)|^77 ≤ (40748613840601/100000000000000 : ℝ)^61
        have hw : |(491052983/1000000000 : ℝ)|=(491052983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2416536749/5000000000 : ℝ)*x 0 + (-124976333/2500000000 : ℝ)*x 1 + (6475817143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2416536749/5000000000 : ℝ)^77 ≤ (39938959870501/100000000000000 : ℝ)^61 := by
    have hnat : (2416536749 : ℕ)^77*100000000000000^61 ≤ 39938959870501^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416536749 5000000000 39938959870501 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124976333/2500000000 : ℝ)^77 ≤ (284788496427/12500000000000 : ℝ)^61 := by
    have hnat : (124976333 : ℕ)^77*12500000000000^61 ≤ 284788496427^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124976333 2500000000 284788496427 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6475817143/10000000000 : ℝ)^77 ≤ (57782732144157/100000000000000 : ℝ)^61 := by
    have hnat : (6475817143 : ℕ)^77*100000000000000^61 ≤ 57782732144157^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6475817143 10000000000 57782732144157 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2416536749/5000000000 : ℝ), (-124976333/2500000000 : ℝ), (6475817143/10000000000 : ℝ)] ![(39938959870501/100000000000000 : ℝ), (284788496427/12500000000000 : ℝ), (57782732144157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2416536749/5000000000 : ℝ)|^77 ≤ (39938959870501/100000000000000 : ℝ)^61
        have hw : |(2416536749/5000000000 : ℝ)|=(2416536749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-124976333/2500000000 : ℝ)|^77 ≤ (284788496427/12500000000000 : ℝ)^61
        have hw : |(-124976333/2500000000 : ℝ)|=(124976333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6475817143/10000000000 : ℝ)|^77 ≤ (57782732144157/100000000000000 : ℝ)^61
        have hw : |(6475817143/10000000000 : ℝ)|=(6475817143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (645297767/1000000000 : ℝ)*x 0 + (241083/640000 : ℝ)*x 1 + (2024468659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (645297767/1000000000 : ℝ)^77 ≤ (57525604148863/100000000000000 : ℝ)^61 := by
    have hnat : (645297767 : ℕ)^77*100000000000000^61 ≤ 57525604148863^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645297767 1000000000 57525604148863 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241083/640000 : ℝ)^77 ≤ (29158822827871/100000000000000 : ℝ)^61 := by
    have hnat : (241083 : ℕ)^77*100000000000000^61 ≤ 29158822827871^61*640000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241083 640000 29158822827871 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2024468659/10000000000 : ℝ)^77 ≤ (13315572999091/100000000000000 : ℝ)^61 := by
    have hnat : (2024468659 : ℕ)^77*100000000000000^61 ≤ 13315572999091^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024468659 10000000000 13315572999091 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(645297767/1000000000 : ℝ), (241083/640000 : ℝ), (2024468659/10000000000 : ℝ)] ![(57525604148863/100000000000000 : ℝ), (29158822827871/100000000000000 : ℝ), (13315572999091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(645297767/1000000000 : ℝ)|^77 ≤ (57525604148863/100000000000000 : ℝ)^61
        have hw : |(645297767/1000000000 : ℝ)|=(645297767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241083/640000 : ℝ)|^77 ≤ (29158822827871/100000000000000 : ℝ)^61
        have hw : |(241083/640000 : ℝ)|=(241083/640000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2024468659/10000000000 : ℝ)|^77 ≤ (13315572999091/100000000000000 : ℝ)^61
        have hw : |(2024468659/10000000000 : ℝ)|=(2024468659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1584219217/10000000000 : ℝ)*x 0 + (3938098719/10000000000 : ℝ)*x 1 + (3308962597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1584219217/10000000000 : ℝ)^77 ≤ (977081430597/10000000000000 : ℝ)^61 := by
    have hnat : (1584219217 : ℕ)^77*10000000000000^61 ≤ 977081430597^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584219217 10000000000 977081430597 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3938098719/10000000000 : ℝ)^77 ≤ (30841270748751/100000000000000 : ℝ)^61 := by
    have hnat : (3938098719 : ℕ)^77*100000000000000^61 ≤ 30841270748751^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3938098719 10000000000 30841270748751 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3308962597/5000000000 : ℝ)^77 ≤ (29693957463179/50000000000000 : ℝ)^61 := by
    have hnat : (3308962597 : ℕ)^77*50000000000000^61 ≤ 29693957463179^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3308962597 5000000000 29693957463179 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1584219217/10000000000 : ℝ), (3938098719/10000000000 : ℝ), (3308962597/5000000000 : ℝ)] ![(977081430597/10000000000000 : ℝ), (30841270748751/100000000000000 : ℝ), (29693957463179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1584219217/10000000000 : ℝ)|^77 ≤ (977081430597/10000000000000 : ℝ)^61
        have hw : |(-1584219217/10000000000 : ℝ)|=(1584219217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3938098719/10000000000 : ℝ)|^77 ≤ (30841270748751/100000000000000 : ℝ)^61
        have hw : |(3938098719/10000000000 : ℝ)|=(3938098719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3308962597/5000000000 : ℝ)|^77 ≤ (29693957463179/50000000000000 : ℝ)^61
        have hw : |(3308962597/5000000000 : ℝ)|=(3308962597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3807711723/10000000000 : ℝ)*x 0 + (-1769353/5000000000 : ℝ)*x 1 + (1893955733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3807711723/10000000000 : ℝ)^77 ≤ (29557949758601/100000000000000 : ℝ)^61 := by
    have hnat : (3807711723 : ℕ)^77*100000000000000^61 ≤ 29557949758601^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3807711723 10000000000 29557949758601 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1769353/5000000000 : ℝ)^77 ≤ (440172963/10000000000000 : ℝ)^61 := by
    have hnat : (1769353 : ℕ)^77*10000000000000^61 ≤ 440172963^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769353 5000000000 440172963 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1893955733/2500000000 : ℝ)^77 ≤ (35218824251243/50000000000000 : ℝ)^61 := by
    have hnat : (1893955733 : ℕ)^77*50000000000000^61 ≤ 35218824251243^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893955733 2500000000 35218824251243 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3807711723/10000000000 : ℝ), (-1769353/5000000000 : ℝ), (1893955733/2500000000 : ℝ)] ![(29557949758601/100000000000000 : ℝ), (440172963/10000000000000 : ℝ), (35218824251243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3807711723/10000000000 : ℝ)|^77 ≤ (29557949758601/100000000000000 : ℝ)^61
        have hw : |(3807711723/10000000000 : ℝ)|=(3807711723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1769353/5000000000 : ℝ)|^77 ≤ (440172963/10000000000000 : ℝ)^61
        have hw : |(-1769353/5000000000 : ℝ)|=(1769353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1893955733/2500000000 : ℝ)|^77 ≤ (35218824251243/50000000000000 : ℝ)^61
        have hw : |(1893955733/2500000000 : ℝ)|=(1893955733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3783930069/10000000000 : ℝ)*x 0 + (3656485337/5000000000 : ℝ)*x 1 + (-335862287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3783930069/10000000000 : ℝ)^77 ≤ (29325110200547/100000000000000 : ℝ)^61 := by
    have hnat : (3783930069 : ℕ)^77*100000000000000^61 ≤ 29325110200547^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3783930069 10000000000 29325110200547 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3656485337/5000000000 : ℝ)^77 ≤ (33683430556253/50000000000000 : ℝ)^61 := by
    have hnat : (3656485337 : ℕ)^77*50000000000000^61 ≤ 33683430556253^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3656485337 5000000000 33683430556253 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (335862287/5000000000 : ℝ)^77 ≤ (1654014338837/50000000000000 : ℝ)^61 := by
    have hnat : (335862287 : ℕ)^77*50000000000000^61 ≤ 1654014338837^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335862287 5000000000 1654014338837 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3783930069/10000000000 : ℝ), (3656485337/5000000000 : ℝ), (-335862287/5000000000 : ℝ)] ![(29325110200547/100000000000000 : ℝ), (33683430556253/50000000000000 : ℝ), (1654014338837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3783930069/10000000000 : ℝ)|^77 ≤ (29325110200547/100000000000000 : ℝ)^61
        have hw : |(3783930069/10000000000 : ℝ)|=(3783930069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3656485337/5000000000 : ℝ)|^77 ≤ (33683430556253/50000000000000 : ℝ)^61
        have hw : |(3656485337/5000000000 : ℝ)|=(3656485337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-335862287/5000000000 : ℝ)|^77 ≤ (1654014338837/50000000000000 : ℝ)^61
        have hw : |(-335862287/5000000000 : ℝ)|=(335862287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (837510059/2000000000 : ℝ)*x 0 + (6711272599/10000000000 : ℝ)*x 1 + (8867759/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837510059/2000000000 : ℝ)^77 ≤ (33327444427771/100000000000000 : ℝ)^61 := by
    have hnat : (837510059 : ℕ)^77*100000000000000^61 ≤ 33327444427771^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837510059 2000000000 33327444427771 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6711272599/10000000000 : ℝ)^77 ≤ (12089452874511/20000000000000 : ℝ)^61 := by
    have hnat : (6711272599 : ℕ)^77*20000000000000^61 ≤ 12089452874511^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6711272599 10000000000 12089452874511 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8867759/80000000 : ℝ)^77 ≤ (1556322797173/25000000000000 : ℝ)^61 := by
    have hnat : (8867759 : ℕ)^77*25000000000000^61 ≤ 1556322797173^61*80000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8867759 80000000 1556322797173 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(837510059/2000000000 : ℝ), (6711272599/10000000000 : ℝ), (8867759/80000000 : ℝ)] ![(33327444427771/100000000000000 : ℝ), (12089452874511/20000000000000 : ℝ), (1556322797173/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(837510059/2000000000 : ℝ)|^77 ≤ (33327444427771/100000000000000 : ℝ)^61
        have hw : |(837510059/2000000000 : ℝ)|=(837510059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6711272599/10000000000 : ℝ)|^77 ≤ (12089452874511/20000000000000 : ℝ)^61
        have hw : |(6711272599/10000000000 : ℝ)|=(6711272599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8867759/80000000 : ℝ)|^77 ≤ (1556322797173/25000000000000 : ℝ)^61
        have hw : |(8867759/80000000 : ℝ)|=(8867759/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-117068433/2500000000 : ℝ)*x 0 + (2247945681/5000000000 : ℝ)*x 1 + (849888903/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117068433/2500000000 : ℝ)^77 ≤ (2097869319891/100000000000000 : ℝ)^61 := by
    have hnat : (117068433 : ℕ)^77*100000000000000^61 ≤ 2097869319891^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117068433 2500000000 2097869319891 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247945681/5000000000 : ℝ)^77 ≤ (7290899270427/20000000000000 : ℝ)^61 := by
    have hnat : (2247945681 : ℕ)^77*20000000000000^61 ≤ 7290899270427^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247945681 5000000000 7290899270427 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849888903/1250000000 : ℝ)^77 ≤ (7680954288533/12500000000000 : ℝ)^61 := by
    have hnat : (849888903 : ℕ)^77*12500000000000^61 ≤ 7680954288533^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849888903 1250000000 7680954288533 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117068433/2500000000 : ℝ), (2247945681/5000000000 : ℝ), (849888903/1250000000 : ℝ)] ![(2097869319891/100000000000000 : ℝ), (7290899270427/20000000000000 : ℝ), (7680954288533/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117068433/2500000000 : ℝ)|^77 ≤ (2097869319891/100000000000000 : ℝ)^61
        have hw : |(-117068433/2500000000 : ℝ)|=(117068433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247945681/5000000000 : ℝ)|^77 ≤ (7290899270427/20000000000000 : ℝ)^61
        have hw : |(2247945681/5000000000 : ℝ)|=(2247945681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849888903/1250000000 : ℝ)|^77 ≤ (7680954288533/12500000000000 : ℝ)^61
        have hw : |(849888903/1250000000 : ℝ)|=(849888903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1612003863/5000000000 : ℝ)*x 0 + (-26206291/400000000 : ℝ)*x 1 + (311180507/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1612003863/5000000000 : ℝ)^77 ≤ (23958012202569/100000000000000 : ℝ)^61 := by
    have hnat : (1612003863 : ℕ)^77*100000000000000^61 ≤ 23958012202569^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1612003863 5000000000 23958012202569 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26206291/400000000 : ℝ)^77 ≤ (200335931141/6250000000000 : ℝ)^61 := by
    have hnat : (26206291 : ℕ)^77*6250000000000^61 ≤ 200335931141^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26206291 400000000 200335931141 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311180507/400000000 : ℝ)^77 ≤ (72836612885539/100000000000000 : ℝ)^61 := by
    have hnat : (311180507 : ℕ)^77*100000000000000^61 ≤ 72836612885539^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311180507 400000000 72836612885539 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1612003863/5000000000 : ℝ), (-26206291/400000000 : ℝ), (311180507/400000000 : ℝ)] ![(23958012202569/100000000000000 : ℝ), (200335931141/6250000000000 : ℝ), (72836612885539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1612003863/5000000000 : ℝ)|^77 ≤ (23958012202569/100000000000000 : ℝ)^61
        have hw : |(1612003863/5000000000 : ℝ)|=(1612003863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26206291/400000000 : ℝ)|^77 ≤ (200335931141/6250000000000 : ℝ)^61
        have hw : |(-26206291/400000000 : ℝ)|=(26206291/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(311180507/400000000 : ℝ)|^77 ≤ (72836612885539/100000000000000 : ℝ)^61
        have hw : |(311180507/400000000 : ℝ)|=(311180507/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6694160143/10000000000 : ℝ)*x 0 + (463211659/1000000000 : ℝ)*x 1 + (-215826179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6694160143/10000000000 : ℝ)^77 ≤ (15063193326013/25000000000000 : ℝ)^61 := by
    have hnat : (6694160143 : ℕ)^77*25000000000000^61 ≤ 15063193326013^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6694160143 10000000000 15063193326013 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463211659/1000000000 : ℝ)^77 ≤ (9463572041109/25000000000000 : ℝ)^61 := by
    have hnat : (463211659 : ℕ)^77*25000000000000^61 ≤ 9463572041109^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463211659 1000000000 9463572041109 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215826179/5000000000 : ℝ)^77 ≤ (946469260647/50000000000000 : ℝ)^61 := by
    have hnat : (215826179 : ℕ)^77*50000000000000^61 ≤ 946469260647^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215826179 5000000000 946469260647 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6694160143/10000000000 : ℝ), (463211659/1000000000 : ℝ), (-215826179/5000000000 : ℝ)] ![(15063193326013/25000000000000 : ℝ), (9463572041109/25000000000000 : ℝ), (946469260647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6694160143/10000000000 : ℝ)|^77 ≤ (15063193326013/25000000000000 : ℝ)^61
        have hw : |(6694160143/10000000000 : ℝ)|=(6694160143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(463211659/1000000000 : ℝ)|^77 ≤ (9463572041109/25000000000000 : ℝ)^61
        have hw : |(463211659/1000000000 : ℝ)|=(463211659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-215826179/5000000000 : ℝ)|^77 ≤ (946469260647/50000000000000 : ℝ)^61
        have hw : |(-215826179/5000000000 : ℝ)|=(215826179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (25325839/31250000 : ℝ)*x 0 + (86487323/312500000 : ℝ)*x 1 + (709621201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25325839/31250000 : ℝ)^77 ≤ (38347751840613/50000000000000 : ℝ)^61 := by
    have hnat : (25325839 : ℕ)^77*50000000000000^61 ≤ 38347751840613^61*31250000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25325839 31250000 38347751840613 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86487323/312500000 : ℝ)^77 ≤ (19759167604883/100000000000000 : ℝ)^61 := by
    have hnat : (86487323 : ℕ)^77*100000000000000^61 ≤ 19759167604883^61*312500000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86487323 312500000 19759167604883 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (709621201/10000000000 : ℝ)^77 ≤ (709065738457/20000000000000 : ℝ)^61 := by
    have hnat : (709621201 : ℕ)^77*20000000000000^61 ≤ 709065738457^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709621201 10000000000 709065738457 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(25325839/31250000 : ℝ), (86487323/312500000 : ℝ), (709621201/10000000000 : ℝ)] ![(38347751840613/50000000000000 : ℝ), (19759167604883/100000000000000 : ℝ), (709065738457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(25325839/31250000 : ℝ)|^77 ≤ (38347751840613/50000000000000 : ℝ)^61
        have hw : |(25325839/31250000 : ℝ)|=(25325839/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86487323/312500000 : ℝ)|^77 ≤ (19759167604883/100000000000000 : ℝ)^61
        have hw : |(86487323/312500000 : ℝ)|=(86487323/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(709621201/10000000000 : ℝ)|^77 ≤ (709065738457/20000000000000 : ℝ)^61
        have hw : |(709621201/10000000000 : ℝ)|=(709621201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-357218207/5000000000 : ℝ)*x 0 + (435924137/625000000 : ℝ)*x 1 + (1037877221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (357218207/5000000000 : ℝ)^77 ≤ (3575722981213/100000000000000 : ℝ)^61 := by
    have hnat : (357218207 : ℕ)^77*100000000000000^61 ≤ 3575722981213^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357218207 5000000000 3575722981213 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435924137/625000000 : ℝ)^77 ≤ (31729251549553/50000000000000 : ℝ)^61 := by
    have hnat : (435924137 : ℕ)^77*50000000000000^61 ≤ 31729251549553^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435924137 625000000 31729251549553 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037877221/2500000000 : ℝ)^77 ≤ (16482886950851/50000000000000 : ℝ)^61 := by
    have hnat : (1037877221 : ℕ)^77*50000000000000^61 ≤ 16482886950851^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037877221 2500000000 16482886950851 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-357218207/5000000000 : ℝ), (435924137/625000000 : ℝ), (1037877221/2500000000 : ℝ)] ![(3575722981213/100000000000000 : ℝ), (31729251549553/50000000000000 : ℝ), (16482886950851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-357218207/5000000000 : ℝ)|^77 ≤ (3575722981213/100000000000000 : ℝ)^61
        have hw : |(-357218207/5000000000 : ℝ)|=(357218207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(435924137/625000000 : ℝ)|^77 ≤ (31729251549553/50000000000000 : ℝ)^61
        have hw : |(435924137/625000000 : ℝ)|=(435924137/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037877221/2500000000 : ℝ)|^77 ≤ (16482886950851/50000000000000 : ℝ)^61
        have hw : |(1037877221/2500000000 : ℝ)|=(1037877221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6760023407/10000000000 : ℝ)*x 0 + (-1160891/400000000 : ℝ)*x 1 + (1184149551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6760023407/10000000000 : ℝ)^77 ≤ (12200410531331/20000000000000 : ℝ)^61 := by
    have hnat : (6760023407 : ℕ)^77*20000000000000^61 ≤ 12200410531331^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6760023407 10000000000 12200410531331 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1160891/400000000 : ℝ)^77 ≤ (62692904599/100000000000000 : ℝ)^61 := by
    have hnat : (1160891 : ℕ)^77*100000000000000^61 ≤ 62692904599^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160891 400000000 62692904599 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1184149551/2500000000 : ℝ)^77 ≤ (19467627216051/50000000000000 : ℝ)^61 := by
    have hnat : (1184149551 : ℕ)^77*50000000000000^61 ≤ 19467627216051^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184149551 2500000000 19467627216051 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6760023407/10000000000 : ℝ), (-1160891/400000000 : ℝ), (1184149551/2500000000 : ℝ)] ![(12200410531331/20000000000000 : ℝ), (62692904599/100000000000000 : ℝ), (19467627216051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6760023407/10000000000 : ℝ)|^77 ≤ (12200410531331/20000000000000 : ℝ)^61
        have hw : |(6760023407/10000000000 : ℝ)|=(6760023407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1160891/400000000 : ℝ)|^77 ≤ (62692904599/100000000000000 : ℝ)^61
        have hw : |(-1160891/400000000 : ℝ)|=(1160891/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1184149551/2500000000 : ℝ)|^77 ≤ (19467627216051/50000000000000 : ℝ)^61
        have hw : |(1184149551/2500000000 : ℝ)|=(1184149551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (71529191/250000000 : ℝ)*x 0 + (7519688769/10000000000 : ℝ)*x 1 + (-39102219/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71529191/250000000 : ℝ)^77 ≤ (20606170360287/100000000000000 : ℝ)^61 := by
    have hnat : (71529191 : ℕ)^77*100000000000000^61 ≤ 20606170360287^61*250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71529191 250000000 20606170360287 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7519688769/10000000000 : ℝ)^77 ≤ (69779475340773/100000000000000 : ℝ)^61 := by
    have hnat : (7519688769 : ℕ)^77*100000000000000^61 ≤ 69779475340773^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7519688769 10000000000 69779475340773 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39102219/250000000 : ℝ)^77 ≤ (600897142791/6250000000000 : ℝ)^61 := by
    have hnat : (39102219 : ℕ)^77*6250000000000^61 ≤ 600897142791^61*250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39102219 250000000 600897142791 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(71529191/250000000 : ℝ), (7519688769/10000000000 : ℝ), (-39102219/250000000 : ℝ)] ![(20606170360287/100000000000000 : ℝ), (69779475340773/100000000000000 : ℝ), (600897142791/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(71529191/250000000 : ℝ)|^77 ≤ (20606170360287/100000000000000 : ℝ)^61
        have hw : |(71529191/250000000 : ℝ)|=(71529191/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7519688769/10000000000 : ℝ)|^77 ≤ (69779475340773/100000000000000 : ℝ)^61
        have hw : |(7519688769/10000000000 : ℝ)|=(7519688769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-39102219/250000000 : ℝ)|^77 ≤ (600897142791/6250000000000 : ℝ)^61
        have hw : |(-39102219/250000000 : ℝ)|=(39102219/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s1_s1_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3986163017/5000000000 : ℝ)*x 0 + (2154419591/10000000000 : ℝ)*x 1 + (334773039/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3986163017/5000000000 : ℝ)^77 ≤ (75122718249789/100000000000000 : ℝ)^61 := by
    have hnat : (3986163017 : ℕ)^77*100000000000000^61 ≤ 75122718249789^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3986163017 5000000000 75122718249789 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2154419591/10000000000 : ℝ)^77 ≤ (14403435870227/100000000000000 : ℝ)^61 := by
    have hnat : (2154419591 : ℕ)^77*100000000000000^61 ≤ 14403435870227^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154419591 10000000000 14403435870227 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334773039/2000000000 : ℝ)^77 ≤ (5236922933309/50000000000000 : ℝ)^61 := by
    have hnat : (334773039 : ℕ)^77*50000000000000^61 ≤ 5236922933309^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334773039 2000000000 5236922933309 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3986163017/5000000000 : ℝ), (2154419591/10000000000 : ℝ), (334773039/2000000000 : ℝ)] ![(75122718249789/100000000000000 : ℝ), (14403435870227/100000000000000 : ℝ), (5236922933309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3986163017/5000000000 : ℝ)|^77 ≤ (75122718249789/100000000000000 : ℝ)^61
        have hw : |(3986163017/5000000000 : ℝ)|=(3986163017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2154419591/10000000000 : ℝ)|^77 ≤ (14403435870227/100000000000000 : ℝ)^61
        have hw : |(2154419591/10000000000 : ℝ)|=(2154419591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(334773039/2000000000 : ℝ)|^77 ≤ (5236922933309/50000000000000 : ℝ)^61
        have hw : |(334773039/2000000000 : ℝ)|=(334773039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316055_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((2477/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2477/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76581/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76581/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9697/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9697/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7153/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7153/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56391/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56391/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57007/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57007/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (173433/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (2477/3125 : ℝ) ^ (19/4 : ℝ) ≤ (16579862809118364319/50000000000000000000 : ℝ) := by
    have hpowers : (2477/3125 : ℝ)^19 ≤ (16579862809118364319/50000000000000000000 : ℝ)^4 := by
      have hnat : (2477 : ℕ)^19*50000000000000000000^4 ≤ 16579862809118364319^4*3125^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2477 3125 16579862809118364319 50000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2477/3125 : ℝ)) (X := (16579862809118364319/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (66579862809118364319/50000000000000000000 : ℝ) ≤ (10621448963707429/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (66579862809118364319/50000000000000000000 : ℝ)^4 ≤ (10621448963707429/10000000000000000 : ℝ)^19 := by
      have hnat : (66579862809118364319 : ℕ)^4*10000000000000000^19 ≤ 10621448963707429^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66579862809118364319 50000000000000000000 10621448963707429 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10621448963707429/10000000000000000 : ℝ)) (X := (66579862809118364319/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (41579862809118364319/25000000000000000000 : ℝ) ≤ (1113049105405699/1000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (41579862809118364319/25000000000000000000 : ℝ)^4 ≤ (1113049105405699/1000000000000000 : ℝ)^19 := by
      have hnat : (41579862809118364319 : ℕ)^4*1000000000000000^19 ≤ 1113049105405699^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41579862809118364319 25000000000000000000 1113049105405699 1000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1113049105405699/1000000000000000 : ℝ)) (X := (41579862809118364319/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(621448963707429/7926400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(509042090349561/7926400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (2477/3125 : ℝ)) (alpha := (621448963707429/7926400000000000 : ℝ)) (beta := (509042090349561/7926400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2477/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(621448963707429/7926400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(509042090349561/7926400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (76581/100000 : ℝ) ^ (19/4 : ℝ) ≤ (28156256129710176541/100000000000000000000 : ℝ) := by
    have hpowers : (76581/100000 : ℝ)^19 ≤ (28156256129710176541/100000000000000000000 : ℝ)^4 := by
      have hnat : (76581 : ℕ)^19*100000000000000000000^4 ≤ 28156256129710176541^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76581 100000 28156256129710176541 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76581/100000 : ℝ)) (X := (28156256129710176541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (128156256129710176541/100000000000000000000 : ℝ) ≤ (2107230585702629/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (128156256129710176541/100000000000000000000 : ℝ)^4 ≤ (2107230585702629/2000000000000000 : ℝ)^19 := by
      have hnat : (128156256129710176541 : ℕ)^4*2000000000000000^19 ≤ 2107230585702629^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        128156256129710176541 100000000000000000000 2107230585702629 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2107230585702629/2000000000000000 : ℝ)) (X := (128156256129710176541/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (78156256129710176541/50000000000000000000 : ℝ) ≤ (10986030187090901/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (78156256129710176541/50000000000000000000 : ℝ)^4 ≤ (10986030187090901/10000000000000000 : ℝ)^19 := by
      have hnat : (78156256129710176541 : ℕ)^4*10000000000000000^19 ≤ 10986030187090901^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78156256129710176541 50000000000000000000 10986030187090901 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10986030187090901/10000000000000000 : ℝ)) (X := (78156256129710176541/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(35743528567543/510540000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(112469314644439/1914525000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (76581/100000 : ℝ)) (alpha := (35743528567543/510540000000000 : ℝ)) (beta := (112469314644439/1914525000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (76581/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(35743528567543/510540000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(112469314644439/1914525000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (9697/12500 : ℝ) ^ (19/4 : ℝ) ≤ (1871048670532407979/6250000000000000000 : ℝ) := by
    have hpowers : (9697/12500 : ℝ)^19 ≤ (1871048670532407979/6250000000000000000 : ℝ)^4 := by
      have hnat : (9697 : ℕ)^19*6250000000000000000^4 ≤ 1871048670532407979^4*12500^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9697 12500 1871048670532407979 6250000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9697/12500 : ℝ)) (X := (1871048670532407979/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (8121048670532407979/6250000000000000000 : ℝ) ≤ (660425169746399/625000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (8121048670532407979/6250000000000000000 : ℝ)^4 ≤ (660425169746399/625000000000000 : ℝ)^19 := by
      have hnat : (8121048670532407979 : ℕ)^4*625000000000000^19 ≤ 660425169746399^19*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8121048670532407979 6250000000000000000 660425169746399 625000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (660425169746399/625000000000000 : ℝ)) (X := (8121048670532407979/6250000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (4996048670532407979/3125000000000000000 : ℝ) ≤ (1379781628245983/1250000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (4996048670532407979/3125000000000000000 : ℝ)^4 ≤ (1379781628245983/1250000000000000 : ℝ)^19 := by
      have hnat : (4996048670532407979 : ℕ)^4*1250000000000000^19 ≤ 1379781628245983^19*3125000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4996048670532407979 3125000000000000000 1379781628245983 1250000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1379781628245983/1250000000000000 : ℝ)) (X := (4996048670532407979/3125000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(35425169746399/484850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(11786257750637/193940000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (9697/12500 : ℝ)) (alpha := (35425169746399/484850000000000 : ℝ)) (beta := (11786257750637/193940000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (9697/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(35425169746399/484850000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(11786257750637/193940000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-301253281/2000000000 : ℝ)*X 0 0+(722779379/1250000000 : ℝ)*X 0 1+(491052983/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2416536749/5000000000 : ℝ)*X 1 0+(-124976333/2500000000 : ℝ)*X 1 1+(6475817143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((645297767/1000000000 : ℝ)*X 0 0+(241083/640000 : ℝ)*X 0 1+(2024468659/10000000000 : ℝ)*X 0 2+(645297767/1000000000 : ℝ)*X 1 0+(241083/640000 : ℝ)*X 1 1+(2024468659/10000000000 : ℝ)*X 1 2+(645297767/1000000000 : ℝ)*X 2 0+(241083/640000 : ℝ)*X 2 1+(2024468659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1584219217/10000000000 : ℝ)*X 0 0+(3938098719/10000000000 : ℝ)*X 0 1+(3308962597/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3807711723/10000000000 : ℝ)*X 1 0+(-1769353/5000000000 : ℝ)*X 1 1+(1893955733/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3783930069/10000000000 : ℝ)*X 2 0+(3656485337/5000000000 : ℝ)*X 2 1+(-335862287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((837510059/2000000000 : ℝ)*X 0 0+(6711272599/10000000000 : ℝ)*X 0 1+(8867759/80000000 : ℝ)*X 0 2+(837510059/2000000000 : ℝ)*X 1 0+(6711272599/10000000000 : ℝ)*X 1 1+(8867759/80000000 : ℝ)*X 1 2+(837510059/2000000000 : ℝ)*X 2 0+(6711272599/10000000000 : ℝ)*X 2 1+(8867759/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-117068433/2500000000 : ℝ)*X 0 0+(2247945681/5000000000 : ℝ)*X 0 1+(849888903/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1612003863/5000000000 : ℝ)*X 1 0+(-26206291/400000000 : ℝ)*X 1 1+(311180507/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6694160143/10000000000 : ℝ)*X 2 0+(463211659/1000000000 : ℝ)*X 2 1+(-215826179/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((25325839/31250000 : ℝ)*X 0 0+(86487323/312500000 : ℝ)*X 0 1+(709621201/10000000000 : ℝ)*X 0 2+(25325839/31250000 : ℝ)*X 1 0+(86487323/312500000 : ℝ)*X 1 1+(709621201/10000000000 : ℝ)*X 1 2+(25325839/31250000 : ℝ)*X 2 0+(86487323/312500000 : ℝ)*X 2 1+(709621201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-357218207/5000000000 : ℝ)*X 0 0+(435924137/625000000 : ℝ)*X 0 1+(1037877221/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6760023407/10000000000 : ℝ)*X 1 0+(-1160891/400000000 : ℝ)*X 1 1+(1184149551/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((71529191/250000000 : ℝ)*X 2 0+(7519688769/10000000000 : ℝ)*X 2 1+(-39102219/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3986163017/5000000000 : ℝ)*X 0 0+(2154419591/10000000000 : ℝ)*X 0 1+(334773039/2000000000 : ℝ)*X 0 2+(3986163017/5000000000 : ℝ)*X 1 0+(2154419591/10000000000 : ℝ)*X 1 1+(334773039/2000000000 : ℝ)*X 1 2+(3986163017/5000000000 : ℝ)*X 2 0+(2154419591/10000000000 : ℝ)*X 2 1+(334773039/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((7153/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7153/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9467834722931316659951580266381/490515988130400000000000000000000000 : ℝ) := by norm_num
    linear_combination (158299577123/250000000000 : ℝ)*(base7) + (427983/125000000000 : ℝ)*(base49) + (713001/500000000000 : ℝ)*(base60) + (2406148087703/1000000000000 : ℝ)*(major_s1_0) + (2406148087703/1000000000000 : ℝ)*(major_s1_1) + (2406148087703/1000000000000 : ℝ)*(major_s1_2) + (27683671/1000000000000 : ℝ)*(sp_s1_0) + (1807031/1000000000000 : ℝ)*(sp_s1_6) + (3088706966379/1000000000000 : ℝ)*(sp_s1_7) + (1544398366319/500000000000 : ℝ)*(sp_s1_8) + (1544389484371/500000000000 : ℝ)*(sp_s1_9) + (1990631236171/1000000000000 : ℝ)*(sp_s1_13) + (15520647/250000000000 : ℝ)*(sp_s1_14) + (3552779/200000000000 : ℝ)*(sp_s1_23) + (1357434734709/1000000000000 : ℝ)*(f.failure) + (1544398366319/500000000000 : ℝ)*(f.sum) + (16005638595774346787/24753531900000000000000000000000 : ℝ)*base62 + (119100523009091/193940000000000000000000000 : ℝ)*base64 + (244037939684509/239315625000000000000000000 : ℝ)*base66 + (155932249570667/121212500000000000000000000 : ℝ)*base68 + (3513100488227797421/76862300800000000000000000000000 : ℝ)*base70 + (7098431587680417/7926400000000000000000000000 : ℝ)*base72 + (282940373516773/510540000000000000000000000 : ℝ)*base74 + (3372947808925293/7926400000000000000000000000 : ℝ)*base76 + (207446123509403465669/607011638400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (13213/100000000000000000 : ℝ)*base87 + (13213/100000000000000000 : ℝ)*base89 + (13213/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56391/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56391/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (763180769781742820345801448163/81752664688400000000000000000000000 : ℝ) := by norm_num
    linear_combination (135509083581/250000000000 : ℝ)*(base7) + (41953/250000000000 : ℝ)*(base24) + (4326698177/500000000000 : ℝ)*(base49) + (552919564887/250000000000 : ℝ)*(major_s1_0) + (552919564887/250000000000 : ℝ)*(major_s1_1) + (552919564887/250000000000 : ℝ)*(major_s1_2) + (929091/100000000000 : ℝ)*(sp_s1_1) + (48348827/1000000000000 : ℝ)*(sp_s1_8) + (715568150583/250000000000 : ℝ)*(sp_s1_14) + (2862215069667/1000000000000 : ℝ)*(sp_s1_15) + (357784067699/125000000000 : ℝ)*(sp_s1_16) + (894864746393/500000000000 : ℝ)*(sp_s1_20) + (107073/1000000000000 : ℝ)*(sp_s1_21) + (30914239/1000000000000 : ℝ)*(sp_s1_27) + (1247724072701/1000000000000 : ℝ)*(f.failure) + (572454541881/200000000000 : ℝ)*(f.sum) + (749144776276852529/2062794325000000000000000000000 : ℝ)*base63 + (5599666594827/96970000000000000000000000 : ℝ)*base64 + (539657973767833/1276350000000000000000000000 : ℝ)*base66 + (288506506032387/484850000000000000000000000 : ℝ)*base69 + (1301858151990212851/19215575200000000000000000000000 : ℝ)*base71 + (949062018051007/1981600000000000000000000000 : ℝ)*base73 + (6741756323567/10636250000000000000000000 : ℝ)*base75 + (589890239275523/1981600000000000000000000000 : ℝ)*base77 + (16569950019139107047/50584303200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (38843/100000000000000000 : ℝ)*base86 + (38843/100000000000000000 : ℝ)*base88 + (38843/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57007/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57007/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (92633776196315180590474509/9607787600000000000000000000000 : ℝ) := by norm_num
    linear_combination (687618031771/1000000000000 : ℝ)*(base7) + (13373/500000000000 : ℝ)*(base34) + (104072659777/1000000000000 : ℝ)*(base40) + (10533/15625000000 : ℝ)*(base59) + (2074477530043/1000000000000 : ℝ)*(major_s1_0) + (2074477556789/1000000000000 : ℝ)*(major_s1_1) + (2074477556789/1000000000000 : ℝ)*(major_s1_2) + (768969/500000000000 : ℝ)*(sp_s1_1) + (11892291/250000000000 : ℝ)*(sp_s1_9) + (29790471/1000000000000 : ℝ)*(sp_s1_20) + (2581111075113/1000000000000 : ℝ)*(sp_s1_21) + (2581109563921/1000000000000 : ℝ)*(sp_s1_22) + (516212706539/200000000000 : ℝ)*(sp_s1_23) + (928955076037/500000000000 : ℝ)*(sp_s1_27) + (1170321937519/1000000000000 : ℝ)*(f.failure) + (2581111101859/1000000000000 : ℝ)*(f.sum) + (11233587882841535771/24753531900000000000000000000000 : ℝ)*base62 + (90185281878309/193940000000000000000000000 : ℝ)*base65 + (163936174767593/3829050000000000000000000000 : ℝ)*base67 + (10939926183977/60606250000000000000000000 : ℝ)*base69 + (68643089104785931399/76862300800000000000000000000000 : ℝ)*base71 + (2523653222723037/7926400000000000000000000000 : ℝ)*base72 + (36584304928979/510540000000000000000000000 : ℝ)*base75 + (5552978366929607/7926400000000000000000000000 : ℝ)*base77 + (330661255214281180913/607011638400000000000000000000000 : ℝ)*base78 + (94617/100000000000000000 : ℝ)*base86 + (94617/100000000000000000 : ℝ)*base88 + (94617/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((2477/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2477/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76581/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76581/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9697/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9697/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7153/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7153/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56391/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56391/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57007/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57007/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316055_s1 p hpa hpb X hX hprev0

#print axioms solution
