-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309053_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:02:28.819928+00:00
-- url     : https://prove2.me/submissions/ed0a3869-be48-4e3d-bbd7-d2172fd6bb93

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
theorem collision_support_c309053_s2_s2_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1841387501/10000000000 : ℝ)*x 0 + (2632162259/5000000000 : ℝ)*x 1 + (5430436499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1841387501/10000000000 : ℝ)^35 ≤ (223069620449/2000000000000 : ℝ)^27 := by
    have hnat : (1841387501 : ℕ)^35*2000000000000^27 ≤ 223069620449^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841387501 10000000000 223069620449 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632162259/5000000000 : ℝ)^35 ≤ (21764441042011/50000000000000 : ℝ)^27 := by
    have hnat : (2632162259 : ℕ)^35*50000000000000^27 ≤ 21764441042011^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632162259 5000000000 21764441042011 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430436499/10000000000 : ℝ)^35 ≤ (9063527373421/20000000000000 : ℝ)^27 := by
    have hnat : (5430436499 : ℕ)^35*20000000000000^27 ≤ 9063527373421^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430436499 10000000000 9063527373421 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1841387501/10000000000 : ℝ), (2632162259/5000000000 : ℝ), (5430436499/10000000000 : ℝ)] ![(223069620449/2000000000000 : ℝ), (21764441042011/50000000000000 : ℝ), (9063527373421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1841387501/10000000000 : ℝ)|^35 ≤ (223069620449/2000000000000 : ℝ)^27
        have hw : |(-1841387501/10000000000 : ℝ)|=(1841387501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632162259/5000000000 : ℝ)|^35 ≤ (21764441042011/50000000000000 : ℝ)^27
        have hw : |(2632162259/5000000000 : ℝ)|=(2632162259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430436499/10000000000 : ℝ)|^35 ≤ (9063527373421/20000000000000 : ℝ)^27
        have hw : |(5430436499/10000000000 : ℝ)|=(5430436499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2277782663/5000000000 : ℝ)*x 0 + (-9732401/80000000 : ℝ)*x 1 + (260642001/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2277782663/5000000000 : ℝ)^35 ≤ (1443542623741/4000000000000 : ℝ)^27 := by
    have hnat : (2277782663 : ℕ)^35*4000000000000^27 ≤ 1443542623741^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277782663 5000000000 1443542623741 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9732401/80000000 : ℝ)^35 ≤ (6517145504941/100000000000000 : ℝ)^27 := by
    have hnat : (9732401 : ℕ)^35*100000000000000^27 ≤ 6517145504941^27*80000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9732401 80000000 6517145504941 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260642001/400000000 : ℝ)^35 ≤ (7174286111303/12500000000000 : ℝ)^27 := by
    have hnat : (260642001 : ℕ)^35*12500000000000^27 ≤ 7174286111303^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260642001 400000000 7174286111303 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2277782663/5000000000 : ℝ), (-9732401/80000000 : ℝ), (260642001/400000000 : ℝ)] ![(1443542623741/4000000000000 : ℝ), (6517145504941/100000000000000 : ℝ), (7174286111303/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2277782663/5000000000 : ℝ)|^35 ≤ (1443542623741/4000000000000 : ℝ)^27
        have hw : |(2277782663/5000000000 : ℝ)|=(2277782663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9732401/80000000 : ℝ)|^35 ≤ (6517145504941/100000000000000 : ℝ)^27
        have hw : |(-9732401/80000000 : ℝ)|=(9732401/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260642001/400000000 : ℝ)|^35 ≤ (7174286111303/12500000000000 : ℝ)^27
        have hw : |(260642001/400000000 : ℝ)|=(260642001/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2290037161/5000000000 : ℝ)*x 0 + (1632335467/2500000000 : ℝ)*x 1 + (-578997323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2290037161/5000000000 : ℝ)^35 ≤ (9085112708347/25000000000000 : ℝ)^27 := by
    have hnat : (2290037161 : ℕ)^35*25000000000000^27 ≤ 9085112708347^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290037161 5000000000 9085112708347 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1632335467/2500000000 : ℝ)^35 ≤ (28773050237723/50000000000000 : ℝ)^27 := by
    have hnat : (1632335467 : ℕ)^35*50000000000000^27 ≤ 28773050237723^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1632335467 2500000000 28773050237723 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (578997323/5000000000 : ℝ)^35 ≤ (6113448673631/100000000000000 : ℝ)^27 := by
    have hnat : (578997323 : ℕ)^35*100000000000000^27 ≤ 6113448673631^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578997323 5000000000 6113448673631 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2290037161/5000000000 : ℝ), (1632335467/2500000000 : ℝ), (-578997323/5000000000 : ℝ)] ![(9085112708347/25000000000000 : ℝ), (28773050237723/50000000000000 : ℝ), (6113448673631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2290037161/5000000000 : ℝ)|^35 ≤ (9085112708347/25000000000000 : ℝ)^27
        have hw : |(2290037161/5000000000 : ℝ)|=(2290037161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1632335467/2500000000 : ℝ)|^35 ≤ (28773050237723/50000000000000 : ℝ)^27
        have hw : |(1632335467/2500000000 : ℝ)|=(1632335467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-578997323/5000000000 : ℝ)|^35 ≤ (6113448673631/100000000000000 : ℝ)^27
        have hw : |(-578997323/5000000000 : ℝ)|=(578997323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3615733003/5000000000 : ℝ)*x 0 + (1335842459/5000000000 : ℝ)*x 1 + (2460280917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3615733003/5000000000 : ℝ)^35 ≤ (13138495397041/20000000000000 : ℝ)^27 := by
    have hnat : (3615733003 : ℕ)^35*20000000000000^27 ≤ 13138495397041^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3615733003 5000000000 13138495397041 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1335842459/5000000000 : ℝ)^35 ≤ (9034702000821/50000000000000 : ℝ)^27 := by
    have hnat : (1335842459 : ℕ)^35*50000000000000^27 ≤ 9034702000821^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335842459 5000000000 9034702000821 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2460280917/10000000000 : ℝ)^35 ≤ (811905949849/5000000000000 : ℝ)^27 := by
    have hnat : (2460280917 : ℕ)^35*5000000000000^27 ≤ 811905949849^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2460280917 10000000000 811905949849 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3615733003/5000000000 : ℝ), (1335842459/5000000000 : ℝ), (2460280917/10000000000 : ℝ)] ![(13138495397041/20000000000000 : ℝ), (9034702000821/50000000000000 : ℝ), (811905949849/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3615733003/5000000000 : ℝ)|^35 ≤ (13138495397041/20000000000000 : ℝ)^27
        have hw : |(3615733003/5000000000 : ℝ)|=(3615733003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1335842459/5000000000 : ℝ)|^35 ≤ (9034702000821/50000000000000 : ℝ)^27
        have hw : |(1335842459/5000000000 : ℝ)|=(1335842459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2460280917/10000000000 : ℝ)|^35 ≤ (811905949849/5000000000000 : ℝ)^27
        have hw : |(2460280917/10000000000 : ℝ)|=(2460280917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-210614313/1250000000 : ℝ)*x 0 + (4146618843/10000000000 : ℝ)*x 1 + (41118269/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210614313/1250000000 : ℝ)^35 ≤ (1988134453401/20000000000000 : ℝ)^27 := by
    have hnat : (210614313 : ℕ)^35*20000000000000^27 ≤ 1988134453401^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210614313 1250000000 1988134453401 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4146618843/10000000000 : ℝ)^35 ≤ (31946133311861/100000000000000 : ℝ)^27 := by
    have hnat : (4146618843 : ℕ)^35*100000000000000^27 ≤ 31946133311861^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146618843 10000000000 31946133311861 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41118269/62500000 : ℝ)^35 ≤ (29056597197091/50000000000000 : ℝ)^27 := by
    have hnat : (41118269 : ℕ)^35*50000000000000^27 ≤ 29056597197091^27*62500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41118269 62500000 29056597197091 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210614313/1250000000 : ℝ), (4146618843/10000000000 : ℝ), (41118269/62500000 : ℝ)] ![(1988134453401/20000000000000 : ℝ), (31946133311861/100000000000000 : ℝ), (29056597197091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210614313/1250000000 : ℝ)|^35 ≤ (1988134453401/20000000000000 : ℝ)^27
        have hw : |(-210614313/1250000000 : ℝ)|=(210614313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4146618843/10000000000 : ℝ)|^35 ≤ (31946133311861/100000000000000 : ℝ)^27
        have hw : |(4146618843/10000000000 : ℝ)|=(4146618843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41118269/62500000 : ℝ)|^35 ≤ (29056597197091/50000000000000 : ℝ)^27
        have hw : |(41118269/62500000 : ℝ)|=(41118269/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3655794583/10000000000 : ℝ)*x 0 + (-210058299/5000000000 : ℝ)*x 1 + (962111587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3655794583/10000000000 : ℝ)^35 ≤ (27132818298057/100000000000000 : ℝ)^27 := by
    have hnat : (3655794583 : ℕ)^35*100000000000000^27 ≤ 27132818298057^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3655794583 10000000000 27132818298057 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210058299/5000000000 : ℝ)^35 ≤ (1642401837497/100000000000000 : ℝ)^27 := by
    have hnat : (210058299 : ℕ)^35*100000000000000^27 ≤ 1642401837497^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210058299 5000000000 1642401837497 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (962111587/1250000000 : ℝ)^35 ≤ (14244955970823/20000000000000 : ℝ)^27 := by
    have hnat : (962111587 : ℕ)^35*20000000000000^27 ≤ 14244955970823^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962111587 1250000000 14244955970823 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3655794583/10000000000 : ℝ), (-210058299/5000000000 : ℝ), (962111587/1250000000 : ℝ)] ![(27132818298057/100000000000000 : ℝ), (1642401837497/100000000000000 : ℝ), (14244955970823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3655794583/10000000000 : ℝ)|^35 ≤ (27132818298057/100000000000000 : ℝ)^27
        have hw : |(3655794583/10000000000 : ℝ)|=(3655794583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-210058299/5000000000 : ℝ)|^35 ≤ (1642401837497/100000000000000 : ℝ)^27
        have hw : |(-210058299/5000000000 : ℝ)|=(210058299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(962111587/1250000000 : ℝ)|^35 ≤ (14244955970823/20000000000000 : ℝ)^27
        have hw : |(962111587/1250000000 : ℝ)|=(962111587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (920310563/2500000000 : ℝ)*x 0 + (7739299043/10000000000 : ℝ)*x 1 + (-261474397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (920310563/2500000000 : ℝ)^35 ≤ (1368895040259/5000000000000 : ℝ)^27 := by
    have hnat : (920310563 : ℕ)^35*5000000000000^27 ≤ 1368895040259^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920310563 2500000000 1368895040259 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7739299043/10000000000 : ℝ)^35 ≤ (71733881743361/100000000000000 : ℝ)^27 := by
    have hnat : (7739299043 : ℕ)^35*100000000000000^27 ≤ 71733881743361^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7739299043 10000000000 71733881743361 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261474397/10000000000 : ℝ)^35 ≤ (888217436689/100000000000000 : ℝ)^27 := by
    have hnat : (261474397 : ℕ)^35*100000000000000^27 ≤ 888217436689^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261474397 10000000000 888217436689 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(920310563/2500000000 : ℝ), (7739299043/10000000000 : ℝ), (-261474397/10000000000 : ℝ)] ![(1368895040259/5000000000000 : ℝ), (71733881743361/100000000000000 : ℝ), (888217436689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(920310563/2500000000 : ℝ)|^35 ≤ (1368895040259/5000000000000 : ℝ)^27
        have hw : |(920310563/2500000000 : ℝ)|=(920310563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7739299043/10000000000 : ℝ)|^35 ≤ (71733881743361/100000000000000 : ℝ)^27
        have hw : |(7739299043/10000000000 : ℝ)|=(7739299043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261474397/10000000000 : ℝ)|^35 ≤ (888217436689/100000000000000 : ℝ)^27
        have hw : |(-261474397/10000000000 : ℝ)|=(261474397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3238380293/5000000000 : ℝ)*x 0 + (1012156343/2000000000 : ℝ)*x 1 + (215142867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3238380293/5000000000 : ℝ)^35 ≤ (28473042456141/50000000000000 : ℝ)^27 := by
    have hnat : (3238380293 : ℕ)^35*50000000000000^27 ≤ 28473042456141^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3238380293 5000000000 28473042456141 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012156343/2000000000 : ℝ)^35 ≤ (41359794991087/100000000000000 : ℝ)^27 := by
    have hnat : (1012156343 : ℕ)^35*100000000000000^27 ≤ 41359794991087^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012156343 2000000000 41359794991087 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215142867/5000000000 : ℝ)^35 ≤ (847060041979/50000000000000 : ℝ)^27 := by
    have hnat : (215142867 : ℕ)^35*50000000000000^27 ≤ 847060041979^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215142867 5000000000 847060041979 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3238380293/5000000000 : ℝ), (1012156343/2000000000 : ℝ), (215142867/5000000000 : ℝ)] ![(28473042456141/50000000000000 : ℝ), (41359794991087/100000000000000 : ℝ), (847060041979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3238380293/5000000000 : ℝ)|^35 ≤ (28473042456141/50000000000000 : ℝ)^27
        have hw : |(3238380293/5000000000 : ℝ)|=(3238380293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1012156343/2000000000 : ℝ)|^35 ≤ (41359794991087/100000000000000 : ℝ)^27
        have hw : |(1012156343/2000000000 : ℝ)|=(1012156343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215142867/5000000000 : ℝ)|^35 ≤ (847060041979/50000000000000 : ℝ)^27
        have hw : |(215142867/5000000000 : ℝ)|=(215142867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-114266209/1000000000 : ℝ)*x 0 + (100375619/250000000 : ℝ)*x 1 + (7031989431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114266209/1000000000 : ℝ)^35 ≤ (1502181353233/25000000000000 : ℝ)^27 := by
    have hnat : (114266209 : ℕ)^35*25000000000000^27 ≤ 1502181353233^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114266209 1000000000 1502181353233 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100375619/250000000 : ℝ)^35 ≤ (15319074276809/50000000000000 : ℝ)^27 := by
    have hnat : (100375619 : ℕ)^35*50000000000000^27 ≤ 15319074276809^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100375619 250000000 15319074276809 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7031989431/10000000000 : ℝ)^35 ≤ (63353126031287/100000000000000 : ℝ)^27 := by
    have hnat : (7031989431 : ℕ)^35*100000000000000^27 ≤ 63353126031287^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7031989431 10000000000 63353126031287 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114266209/1000000000 : ℝ), (100375619/250000000 : ℝ), (7031989431/10000000000 : ℝ)] ![(1502181353233/25000000000000 : ℝ), (15319074276809/50000000000000 : ℝ), (63353126031287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114266209/1000000000 : ℝ)|^35 ≤ (1502181353233/25000000000000 : ℝ)^27
        have hw : |(-114266209/1000000000 : ℝ)|=(114266209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100375619/250000000 : ℝ)|^35 ≤ (15319074276809/50000000000000 : ℝ)^27
        have hw : |(100375619/250000000 : ℝ)|=(100375619/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7031989431/10000000000 : ℝ)|^35 ≤ (63353126031287/100000000000000 : ℝ)^27
        have hw : |(7031989431/10000000000 : ℝ)|=(7031989431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (160547677/625000000 : ℝ)*x 0 + (-191409893/2000000000 : ℝ)*x 1 + (2065020767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (160547677/625000000 : ℝ)^35 ≤ (17172258549147/100000000000000 : ℝ)^27 := by
    have hnat : (160547677 : ℕ)^35*100000000000000^27 ≤ 17172258549147^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160547677 625000000 17172258549147 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191409893/2000000000 : ℝ)^35 ≤ (2387585989149/50000000000000 : ℝ)^27 := by
    have hnat : (191409893 : ℕ)^35*50000000000000^27 ≤ 2387585989149^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191409893 2000000000 2387585989149 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065020767/2500000000 : ℝ)^35 ≤ (19513142364863/25000000000000 : ℝ)^27 := by
    have hnat : (2065020767 : ℕ)^35*25000000000000^27 ≤ 19513142364863^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065020767 2500000000 19513142364863 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(160547677/625000000 : ℝ), (-191409893/2000000000 : ℝ), (2065020767/2500000000 : ℝ)] ![(17172258549147/100000000000000 : ℝ), (2387585989149/50000000000000 : ℝ), (19513142364863/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(160547677/625000000 : ℝ)|^35 ≤ (17172258549147/100000000000000 : ℝ)^27
        have hw : |(160547677/625000000 : ℝ)|=(160547677/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-191409893/2000000000 : ℝ)|^35 ≤ (2387585989149/50000000000000 : ℝ)^27
        have hw : |(-191409893/2000000000 : ℝ)|=(191409893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2065020767/2500000000 : ℝ)|^35 ≤ (19513142364863/25000000000000 : ℝ)^27
        have hw : |(2065020767/2500000000 : ℝ)|=(2065020767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6181104129/10000000000 : ℝ)*x 0 + (668605393/1250000000 : ℝ)*x 1 + (-482197669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6181104129/10000000000 : ℝ)^35 ≤ (13399843185921/25000000000000 : ℝ)^27 := by
    have hnat : (6181104129 : ℕ)^35*25000000000000^27 ≤ 13399843185921^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6181104129 10000000000 13399843185921 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (668605393/1250000000 : ℝ)^35 ≤ (11109238091891/25000000000000 : ℝ)^27 := by
    have hnat : (668605393 : ℕ)^35*25000000000000^27 ≤ 11109238091891^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668605393 1250000000 11109238091891 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482197669/10000000000 : ℝ)^35 ≤ (196367487157/10000000000000 : ℝ)^27 := by
    have hnat : (482197669 : ℕ)^35*10000000000000^27 ≤ 196367487157^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482197669 10000000000 196367487157 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6181104129/10000000000 : ℝ), (668605393/1250000000 : ℝ), (-482197669/10000000000 : ℝ)] ![(13399843185921/25000000000000 : ℝ), (11109238091891/25000000000000 : ℝ), (196367487157/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6181104129/10000000000 : ℝ)|^35 ≤ (13399843185921/25000000000000 : ℝ)^27
        have hw : |(6181104129/10000000000 : ℝ)|=(6181104129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(668605393/1250000000 : ℝ)|^35 ≤ (11109238091891/25000000000000 : ℝ)^27
        have hw : |(668605393/1250000000 : ℝ)|=(668605393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-482197669/10000000000 : ℝ)|^35 ≤ (196367487157/10000000000000 : ℝ)^27
        have hw : |(-482197669/10000000000 : ℝ)|=(482197669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (912215819/1000000000 : ℝ)*x 0 + (1500736259/10000000000 : ℝ)*x 1 + (19114423/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (912215819/1000000000 : ℝ)^35 ≤ (44385863165629/50000000000000 : ℝ)^27 := by
    have hnat : (912215819 : ℕ)^35*50000000000000^27 ≤ 44385863165629^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912215819 1000000000 44385863165629 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1500736259/10000000000 : ℝ)^35 ≤ (4277760018793/50000000000000 : ℝ)^27 := by
    have hnat : (1500736259 : ℕ)^35*50000000000000^27 ≤ 4277760018793^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500736259 10000000000 4277760018793 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19114423/312500000 : ℝ)^35 ≤ (668188403341/25000000000000 : ℝ)^27 := by
    have hnat : (19114423 : ℕ)^35*25000000000000^27 ≤ 668188403341^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19114423 312500000 668188403341 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(912215819/1000000000 : ℝ), (1500736259/10000000000 : ℝ), (19114423/312500000 : ℝ)] ![(44385863165629/50000000000000 : ℝ), (4277760018793/50000000000000 : ℝ), (668188403341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(912215819/1000000000 : ℝ)|^35 ≤ (44385863165629/50000000000000 : ℝ)^27
        have hw : |(912215819/1000000000 : ℝ)|=(912215819/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1500736259/10000000000 : ℝ)|^35 ≤ (4277760018793/50000000000000 : ℝ)^27
        have hw : |(1500736259/10000000000 : ℝ)|=(1500736259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19114423/312500000 : ℝ)|^35 ≤ (668188403341/25000000000000 : ℝ)^27
        have hw : |(19114423/312500000 : ℝ)|=(19114423/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-559166053/5000000000 : ℝ)*x 0 + (268229989/400000000 : ℝ)*x 1 + (1102160091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (559166053/5000000000 : ℝ)^35 ≤ (1460850762793/25000000000000 : ℝ)^27 := by
    have hnat : (559166053 : ℕ)^35*25000000000000^27 ≤ 1460850762793^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559166053 5000000000 1460850762793 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268229989/400000000 : ℝ)^35 ≤ (29784775744951/50000000000000 : ℝ)^27 := by
    have hnat : (268229989 : ℕ)^35*50000000000000^27 ≤ 29784775744951^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268229989 400000000 29784775744951 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102160091/2500000000 : ℝ)^35 ≤ (34587045438957/100000000000000 : ℝ)^27 := by
    have hnat : (1102160091 : ℕ)^35*100000000000000^27 ≤ 34587045438957^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102160091 2500000000 34587045438957 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-559166053/5000000000 : ℝ), (268229989/400000000 : ℝ), (1102160091/2500000000 : ℝ)] ![(1460850762793/25000000000000 : ℝ), (29784775744951/50000000000000 : ℝ), (34587045438957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-559166053/5000000000 : ℝ)|^35 ≤ (1460850762793/25000000000000 : ℝ)^27
        have hw : |(-559166053/5000000000 : ℝ)|=(559166053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268229989/400000000 : ℝ)|^35 ≤ (29784775744951/50000000000000 : ℝ)^27
        have hw : |(268229989/400000000 : ℝ)|=(268229989/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102160091/2500000000 : ℝ)|^35 ≤ (34587045438957/100000000000000 : ℝ)^27
        have hw : |(1102160091/2500000000 : ℝ)|=(1102160091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3077990617/5000000000 : ℝ)*x 0 + (-430694821/10000000000 : ℝ)*x 1 + (337488393/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3077990617/5000000000 : ℝ)^35 ≤ (2132685642191/4000000000000 : ℝ)^27 := by
    have hnat : (3077990617 : ℕ)^35*4000000000000^27 ≤ 2132685642191^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3077990617 5000000000 2132685642191 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430694821/10000000000 : ℝ)^35 ≤ (1696208265991/100000000000000 : ℝ)^27 := by
    have hnat : (430694821 : ℕ)^35*100000000000000^27 ≤ 1696208265991^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430694821 10000000000 1696208265991 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337488393/625000000 : ℝ)^35 ≤ (44986650661211/100000000000000 : ℝ)^27 := by
    have hnat : (337488393 : ℕ)^35*100000000000000^27 ≤ 44986650661211^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337488393 625000000 44986650661211 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3077990617/5000000000 : ℝ), (-430694821/10000000000 : ℝ), (337488393/625000000 : ℝ)] ![(2132685642191/4000000000000 : ℝ), (1696208265991/100000000000000 : ℝ), (44986650661211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3077990617/5000000000 : ℝ)|^35 ≤ (2132685642191/4000000000000 : ℝ)^27
        have hw : |(3077990617/5000000000 : ℝ)|=(3077990617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430694821/10000000000 : ℝ)|^35 ≤ (1696208265991/100000000000000 : ℝ)^27
        have hw : |(-430694821/10000000000 : ℝ)|=(430694821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337488393/625000000 : ℝ)|^35 ≤ (44986650661211/100000000000000 : ℝ)^27
        have hw : |(337488393/625000000 : ℝ)|=(337488393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (515690417/2000000000 : ℝ)*x 0 + (8268942279/10000000000 : ℝ)*x 1 + (-185428001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515690417/2000000000 : ℝ)^35 ≤ (17256270368799/100000000000000 : ℝ)^27 := by
    have hnat : (515690417 : ℕ)^35*100000000000000^27 ≤ 17256270368799^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515690417 2000000000 17256270368799 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8268942279/10000000000 : ℝ)^35 ≤ (1563222095629/2000000000000 : ℝ)^27 := by
    have hnat : (8268942279 : ℕ)^35*2000000000000^27 ≤ 1563222095629^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8268942279 10000000000 1563222095629 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185428001/2000000000 : ℝ)^35 ≤ (4582624838437/100000000000000 : ℝ)^27 := by
    have hnat : (185428001 : ℕ)^35*100000000000000^27 ≤ 4582624838437^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185428001 2000000000 4582624838437 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(515690417/2000000000 : ℝ), (8268942279/10000000000 : ℝ), (-185428001/2000000000 : ℝ)] ![(17256270368799/100000000000000 : ℝ), (1563222095629/2000000000000 : ℝ), (4582624838437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(515690417/2000000000 : ℝ)|^35 ≤ (17256270368799/100000000000000 : ℝ)^27
        have hw : |(515690417/2000000000 : ℝ)|=(515690417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8268942279/10000000000 : ℝ)|^35 ≤ (1563222095629/2000000000000 : ℝ)^27
        have hw : |(8268942279/10000000000 : ℝ)|=(8268942279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-185428001/2000000000 : ℝ)|^35 ≤ (4582624838437/100000000000000 : ℝ)^27
        have hw : |(-185428001/2000000000 : ℝ)|=(185428001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s2_s2_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (460109307/500000000 : ℝ)*x 0 + (271796189/2500000000 : ℝ)*x 1 + (463686361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (460109307/500000000 : ℝ)^35 ≤ (17956514917119/20000000000000 : ℝ)^27 := by
    have hnat : (460109307 : ℕ)^35*20000000000000^27 ≤ 17956514917119^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460109307 500000000 17956514917119 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271796189/2500000000 : ℝ)^35 ≤ (1126661886833/20000000000000 : ℝ)^27 := by
    have hnat : (271796189 : ℕ)^35*20000000000000^27 ≤ 1126661886833^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271796189 2500000000 1126661886833 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (463686361/5000000000 : ℝ)^35 ≤ (4584115975353/100000000000000 : ℝ)^27 := by
    have hnat : (463686361 : ℕ)^35*100000000000000^27 ≤ 4584115975353^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463686361 5000000000 4584115975353 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(460109307/500000000 : ℝ), (271796189/2500000000 : ℝ), (463686361/5000000000 : ℝ)] ![(17956514917119/20000000000000 : ℝ), (1126661886833/20000000000000 : ℝ), (4584115975353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(460109307/500000000 : ℝ)|^35 ≤ (17956514917119/20000000000000 : ℝ)^27
        have hw : |(460109307/500000000 : ℝ)|=(460109307/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271796189/2500000000 : ℝ)|^35 ≤ (1126661886833/20000000000000 : ℝ)^27
        have hw : |(271796189/2500000000 : ℝ)|=(271796189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(463686361/5000000000 : ℝ)|^35 ≤ (4584115975353/100000000000000 : ℝ)^27
        have hw : |(463686361/5000000000 : ℝ)|=(463686361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309053_s2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((76993/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76993/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80501/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80501/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79497/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79497/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15043/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15043/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27/40 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27/40 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33139/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33139/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (76993/100000 : ℝ) ^ (69/16 : ℝ) ≤ (32383290918553428567/100000000000000000000 : ℝ) := by
    have hpowers : (76993/100000 : ℝ)^69 ≤ (32383290918553428567/100000000000000000000 : ℝ)^16 := by
      have hnat : (76993 : ℕ)^69*100000000000000000000^16 ≤ 32383290918553428567^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76993 100000 32383290918553428567 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76993/100000 : ℝ)) (X := (32383290918553428567/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (132383290918553428567/100000000000000000000 : ℝ) ≤ (10672131565242653/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (132383290918553428567/100000000000000000000 : ℝ)^16 ≤ (10672131565242653/10000000000000000 : ℝ)^69 := by
      have hnat : (132383290918553428567 : ℕ)^16*10000000000000000^69 ≤ 10672131565242653^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        132383290918553428567 100000000000000000000 10672131565242653 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10672131565242653/10000000000000000 : ℝ)) (X := (132383290918553428567/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (82383290918553428567/50000000000000000000 : ℝ) ≤ (5613820198100171/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (82383290918553428567/50000000000000000000 : ℝ)^16 ≤ (5613820198100171/5000000000000000 : ℝ)^69 := by
      have hnat : (82383290918553428567 : ℕ)^16*5000000000000000^69 ≤ 5613820198100171^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82383290918553428567 50000000000000000000 5613820198100171 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5613820198100171/5000000000000000 : ℝ)) (X := (82383290918553428567/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(672131565242653/7699300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(79358404422527/1099900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (76993/100000 : ℝ)) (alpha := (672131565242653/7699300000000000 : ℝ)) (beta := (79358404422527/1099900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (76993/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(672131565242653/7699300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(79358404422527/1099900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (80501/100000 : ℝ) ^ (69/16 : ℝ) ≤ (19621762016798475359/50000000000000000000 : ℝ) := by
    have hpowers : (80501/100000 : ℝ)^69 ≤ (19621762016798475359/50000000000000000000 : ℝ)^16 := by
      have hnat : (80501 : ℕ)^69*50000000000000000000^16 ≤ 19621762016798475359^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80501 100000 19621762016798475359 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (80501/100000 : ℝ)) (X := (19621762016798475359/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (69621762016798475359/50000000000000000000 : ℝ) ≤ (5398947895502893/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (69621762016798475359/50000000000000000000 : ℝ)^16 ≤ (5398947895502893/5000000000000000 : ℝ)^69 := by
      have hnat : (69621762016798475359 : ℕ)^16*5000000000000000^69 ≤ 5398947895502893^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69621762016798475359 50000000000000000000 5398947895502893 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5398947895502893/5000000000000000 : ℝ)) (X := (69621762016798475359/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (44621762016798475359/25000000000000000000 : ℝ) ≤ (5718914300315247/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (44621762016798475359/25000000000000000000 : ℝ)^16 ≤ (5718914300315247/5000000000000000 : ℝ)^69 := by
      have hnat : (44621762016798475359 : ℕ)^16*5000000000000000^69 ≤ 5718914300315247^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44621762016798475359 25000000000000000000 5718914300315247 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5718914300315247/5000000000000000 : ℝ)) (X := (44621762016798475359/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(398947895502893/4025050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(159983202406177/2012525000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (80501/100000 : ℝ)) (alpha := (398947895502893/4025050000000000 : ℝ)) (beta := (159983202406177/2012525000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (80501/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(398947895502893/4025050000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(159983202406177/2012525000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (79497/100000 : ℝ) ^ (69/16 : ℝ) ≤ (3717599197452527831/10000000000000000000 : ℝ) := by
    have hpowers : (79497/100000 : ℝ)^69 ≤ (3717599197452527831/10000000000000000000 : ℝ)^16 := by
      have hnat : (79497 : ℕ)^69*10000000000000000000^16 ≤ 3717599197452527831^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79497 100000 3717599197452527831 10000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79497/100000 : ℝ)) (X := (3717599197452527831/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (13717599197452527831/10000000000000000000 : ℝ) ≤ (5380251898596649/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (13717599197452527831/10000000000000000000 : ℝ)^16 ≤ (5380251898596649/5000000000000000 : ℝ)^69 := by
      have hnat : (13717599197452527831 : ℕ)^16*5000000000000000^69 ≤ 5380251898596649^69*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13717599197452527831 10000000000000000000 5380251898596649 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5380251898596649/5000000000000000 : ℝ)) (X := (13717599197452527831/10000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (8717599197452527831/5000000000000000000 : ℝ) ≤ (11375828806396769/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (8717599197452527831/5000000000000000000 : ℝ)^16 ≤ (11375828806396769/10000000000000000 : ℝ)^69 := by
      have hnat : (8717599197452527831 : ℕ)^16*10000000000000000^69 ≤ 11375828806396769^69*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8717599197452527831 5000000000000000000 11375828806396769 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11375828806396769/10000000000000000 : ℝ)) (X := (8717599197452527831/5000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(380251898596649/3974850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(205108336401157/2649900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (79497/100000 : ℝ)) (alpha := (380251898596649/3974850000000000 : ℝ)) (beta := (205108336401157/2649900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (79497/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(380251898596649/3974850000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(205108336401157/2649900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1841387501/10000000000 : ℝ)*X 0 0+(2632162259/5000000000 : ℝ)*X 0 1+(5430436499/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((2277782663/5000000000 : ℝ)*X 1 0+(-9732401/80000000 : ℝ)*X 1 1+(260642001/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2290037161/5000000000 : ℝ)*X 2 0+(1632335467/2500000000 : ℝ)*X 2 1+(-578997323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3615733003/5000000000 : ℝ)*X 0 0+(1335842459/5000000000 : ℝ)*X 0 1+(2460280917/10000000000 : ℝ)*X 0 2+(3615733003/5000000000 : ℝ)*X 1 0+(1335842459/5000000000 : ℝ)*X 1 1+(2460280917/10000000000 : ℝ)*X 1 2+(3615733003/5000000000 : ℝ)*X 2 0+(1335842459/5000000000 : ℝ)*X 2 1+(2460280917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-210614313/1250000000 : ℝ)*X 0 0+(4146618843/10000000000 : ℝ)*X 0 1+(41118269/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((3655794583/10000000000 : ℝ)*X 1 0+(-210058299/5000000000 : ℝ)*X 1 1+(962111587/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((920310563/2500000000 : ℝ)*X 2 0+(7739299043/10000000000 : ℝ)*X 2 1+(-261474397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((3238380293/5000000000 : ℝ)*X 0 0+(1012156343/2000000000 : ℝ)*X 0 1+(215142867/5000000000 : ℝ)*X 0 2+(3238380293/5000000000 : ℝ)*X 1 0+(1012156343/2000000000 : ℝ)*X 1 1+(215142867/5000000000 : ℝ)*X 1 2+(3238380293/5000000000 : ℝ)*X 2 0+(1012156343/2000000000 : ℝ)*X 2 1+(215142867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-114266209/1000000000 : ℝ)*X 0 0+(100375619/250000000 : ℝ)*X 0 1+(7031989431/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((160547677/625000000 : ℝ)*X 1 0+(-191409893/2000000000 : ℝ)*X 1 1+(2065020767/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6181104129/10000000000 : ℝ)*X 2 0+(668605393/1250000000 : ℝ)*X 2 1+(-482197669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((912215819/1000000000 : ℝ)*X 0 0+(1500736259/10000000000 : ℝ)*X 0 1+(19114423/312500000 : ℝ)*X 0 2+(912215819/1000000000 : ℝ)*X 1 0+(1500736259/10000000000 : ℝ)*X 1 1+(19114423/312500000 : ℝ)*X 1 2+(912215819/1000000000 : ℝ)*X 2 0+(1500736259/10000000000 : ℝ)*X 2 1+(19114423/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-559166053/5000000000 : ℝ)*X 0 0+(268229989/400000000 : ℝ)*X 0 1+(1102160091/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3077990617/5000000000 : ℝ)*X 1 0+(-430694821/10000000000 : ℝ)*X 1 1+(337488393/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((515690417/2000000000 : ℝ)*X 2 0+(8268942279/10000000000 : ℝ)*X 2 1+(-185428001/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((460109307/500000000 : ℝ)*X 0 0+(271796189/2500000000 : ℝ)*X 0 1+(463686361/5000000000 : ℝ)*X 0 2+(460109307/500000000 : ℝ)*X 1 0+(271796189/2500000000 : ℝ)*X 1 1+(463686361/5000000000 : ℝ)*X 1 2+(460109307/500000000 : ℝ)*X 2 0+(271796189/2500000000 : ℝ)*X 2 1+(463686361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((15043/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15043/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12459043249189218882312178839503/586575569825025000000000000000000000 : ℝ) := by norm_num
    linear_combination (87466122587/1000000000000 : ℝ)*(base7) + (27451/62500000000 : ℝ)*(base49) + (25031294731/250000000000 : ℝ)*(base59) + (1704991886423/500000000000 : ℝ)*(major_s2_0) + (1704991886423/500000000000 : ℝ)*(major_s2_1) + (1704991886423/500000000000 : ℝ)*(major_s2_2) + (71822953/1000000000000 : ℝ)*(sp_s2_0) + (146333/250000000000 : ℝ)*(sp_s2_6) + (925029244893/200000000000 : ℝ)*(sp_s2_7) + (4625391769319/1000000000000 : ℝ)*(sp_s2_8) + (462539190763/100000000000 : ℝ)*(sp_s2_9) + (2228782970453/1000000000000 : ℝ)*(sp_s2_13) + (43465053/250000000000 : ℝ)*(sp_s2_14) + (138311/1000000000000 : ℝ)*(sp_s2_15) + (1070658716599/500000000000 : ℝ)*(f.failure) + (462539190763/100000000000 : ℝ)*(f.sum) + (2760888889426266559/12799175994000000000000000000000 : ℝ)*base63 + (957728289880789/1324950000000000000000000000 : ℝ)*base65 + (1625495560390691/4025050000000000000000000000 : ℝ)*base67 + (1776396259818239/3974850000000000000000000000 : ℝ)*base69 + (1905897461806646281/3643281262500000000000000000000 : ℝ)*base71 + (90654516856511/549950000000000000000000000 : ℝ)*base73 + (441422345364357/1006262500000000000000000000 : ℝ)*base75 + (92371048949061/274975000000000000000000000 : ℝ)*base77 + (1691087840815181217/8854304990000000000000000000000 : ℝ)*base79 + (59047/50000000000000000 : ℝ)*base86 + (59047/50000000000000000 : ℝ)*base88 + (59047/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27/40 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27/40 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4322679036909807075259900332997/1368676329591725000000000000000000000 : ℝ) := by norm_num
    linear_combination (509338203697/1000000000000 : ℝ)*(base7) + (1216691/200000000000 : ℝ)*(base53) + (2259388859473/1000000000000 : ℝ)*(major_s2_0) + (2259388859473/1000000000000 : ℝ)*(major_s2_1) + (1129691388009/500000000000 : ℝ)*(major_s2_2) + (998257/1000000000000 : ℝ)*(sp_s2_0) + (82503/25000000000 : ℝ)*(sp_s2_2) + (8279983/250000000000 : ℝ)*(sp_s2_8) + (557974415273/200000000000 : ℝ)*(sp_s2_14) + (557969387067/200000000000 : ℝ)*(sp_s2_15) + (2789882838601/1000000000000 : ℝ)*(sp_s2_16) + (964063353271/500000000000 : ℝ)*(sp_s2_20) + (1396129/200000000000 : ℝ)*(sp_s2_21) + (3369717/500000000000 : ℝ)*(sp_s2_27) + (35469881057/25000000000 : ℝ)*(f.failure) + (1394943069361/500000000000 : ℝ)*(f.sum) + (2522353188480705091/5332989997500000000000000000000 : ℝ)*base63 + (27952321654229/110412500000000000000000000 : ℝ)*base64 + (139007364571277/251565625000000000000000000 : ℝ)*base66 + (54990582635987/662475000000000000000000000 : ℝ)*base69 + (5581497313096884481/68007916900000000000000000000000 : ℝ)*base71 + (650124820648609/1099900000000000000000000000 : ℝ)*base72 + (16542763335573/31445703125000000000000000 : ℝ)*base75 + (865653071494889/7699300000000000000000000000 : ℝ)*base77 + (15005045540547273/17708609980000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (1579/2500000000000000 : ℝ)*base87 + (1579/2500000000000000 : ℝ)*base89 + (1579/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33139/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33139/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1521306033690696258542545030063/241531116986775000000000000000000000 : ℝ) := by norm_num
    linear_combination (491454138087/1000000000000 : ℝ)*(base7) + (3997401/1000000000000 : ℝ)*(base27) + (632823/1000000000000 : ℝ)*(base34) + (12941357089/200000000000 : ℝ)*(base40) + (297513/500000000000 : ℝ)*(base43) + (1119804285067/500000000000 : ℝ)*(major_s2_0) + (223960860793/100000000000 : ℝ)*(major_s2_1) + (559902300739/250000000000 : ℝ)*(major_s2_2) + (10652957/1000000000000 : ℝ)*(sp_s2_1) + (44932201/1000000000000 : ℝ)*(sp_s2_9) + (693408367083/250000000000 : ℝ)*(sp_s2_21) + (346703005403/125000000000 : ℝ)*(sp_s2_22) + (1386794584477/500000000000 : ℝ)*(sp_s2_23) + (189782400971/100000000000 : ℝ)*(sp_s2_27) + (1406374501847/1000000000000 : ℝ)*(f.failure) + (2773634696181/1000000000000 : ℝ)*(f.sum) + (25335300394616115047/159989699925000000000000000000000 : ℝ)*base63 + (149402669693627/662475000000000000000000000 : ℝ)*base65 + (6844411516591/25156562500000000000000000 : ℝ)*base66 + (884379596495707/1987425000000000000000000000 : ℝ)*base69 + (14015172113450033243/51005937675000000000000000000000 : ℝ)*base71 + (124689016592703/274975000000000000000000000 : ℝ)*base72 + (68503169268039/201252500000000000000000000 : ℝ)*base75 + (124813644633833/1924825000000000000000000000 : ℝ)*base77 + (3622472987841958103/22135762475000000000000000000000 : ℝ)*base78 + (70791/100000000000000000 : ℝ)*base86 + (29209/100000000000000000 : ℝ)*base89 + (29209/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((76993/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76993/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80501/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80501/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79497/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79497/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15043/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15043/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27/40 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27/40 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33139/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33139/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309053_s2 p hpa hpb X hX hprev1

#print axioms solution
