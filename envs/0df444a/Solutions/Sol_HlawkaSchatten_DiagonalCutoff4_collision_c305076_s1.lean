-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305076_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:33:24.681528+00:00
-- url     : https://prove2.me/submissions/81507e50-6e52-42cb-922b-d8c3d028c812

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
theorem collision_support_c305076_s1_s1_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1329128047/2000000000 : ℝ)*x 0 + (3167354929/10000000000 : ℝ)*x 1 + (179773651/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1329128047/2000000000 : ℝ)^67 ≤ (58460443514401/100000000000000 : ℝ)^51 := by
    have hnat : (1329128047 : ℕ)^67*100000000000000^51 ≤ 58460443514401^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1329128047 2000000000 58460443514401 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3167354929/10000000000 : ℝ)^67 ≤ (5520680054857/25000000000000 : ℝ)^51 := by
    have hnat : (3167354929 : ℕ)^67*25000000000000^51 ≤ 5520680054857^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167354929 10000000000 5520680054857 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179773651/625000000 : ℝ)^67 ≤ (19456836252953/100000000000000 : ℝ)^51 := by
    have hnat : (179773651 : ℕ)^67*100000000000000^51 ≤ 19456836252953^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179773651 625000000 19456836252953 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1329128047/2000000000 : ℝ), (3167354929/10000000000 : ℝ), (179773651/625000000 : ℝ)] ![(58460443514401/100000000000000 : ℝ), (5520680054857/25000000000000 : ℝ), (19456836252953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1329128047/2000000000 : ℝ)|^67 ≤ (58460443514401/100000000000000 : ℝ)^51
        have hw : |(1329128047/2000000000 : ℝ)|=(1329128047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3167354929/10000000000 : ℝ)|^67 ≤ (5520680054857/25000000000000 : ℝ)^51
        have hw : |(3167354929/10000000000 : ℝ)|=(3167354929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179773651/625000000 : ℝ)|^67 ≤ (19456836252953/100000000000000 : ℝ)^51
        have hw : |(179773651/625000000 : ℝ)|=(179773651/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2441215371/5000000000 : ℝ)*x 0 + (-2513630577/5000000000 : ℝ)*x 1 + (-2992311809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2441215371/5000000000 : ℝ)^67 ≤ (38990005517037/100000000000000 : ℝ)^51 := by
    have hnat : (2441215371 : ℕ)^67*100000000000000^51 ≤ 38990005517037^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441215371 5000000000 38990005517037 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2513630577/5000000000 : ℝ)^67 ≤ (40516461375737/100000000000000 : ℝ)^51 := by
    have hnat : (2513630577 : ℕ)^67*100000000000000^51 ≤ 40516461375737^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513630577 5000000000 40516461375737 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2992311809/10000000000 : ℝ)^67 ≤ (5123383275261/25000000000000 : ℝ)^51 := by
    have hnat : (2992311809 : ℕ)^67*25000000000000^51 ≤ 5123383275261^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2992311809 10000000000 5123383275261 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2441215371/5000000000 : ℝ), (-2513630577/5000000000 : ℝ), (-2992311809/10000000000 : ℝ)] ![(38990005517037/100000000000000 : ℝ), (40516461375737/100000000000000 : ℝ), (5123383275261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2441215371/5000000000 : ℝ)|^67 ≤ (38990005517037/100000000000000 : ℝ)^51
        have hw : |(2441215371/5000000000 : ℝ)|=(2441215371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2513630577/5000000000 : ℝ)|^67 ≤ (40516461375737/100000000000000 : ℝ)^51
        have hw : |(-2513630577/5000000000 : ℝ)|=(2513630577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2992311809/10000000000 : ℝ)|^67 ≤ (5123383275261/25000000000000 : ℝ)^51
        have hw : |(-2992311809/10000000000 : ℝ)|=(2992311809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-129942301/1250000000 : ℝ)*x 0 + (-7811182003/10000000000 : ℝ)*x 1 + (3224045989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129942301/1250000000 : ℝ)^67 ≤ (5109734752089/100000000000000 : ℝ)^51 := by
    have hnat : (129942301 : ℕ)^67*100000000000000^51 ≤ 5109734752089^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129942301 1250000000 5109734752089 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7811182003/10000000000 : ℝ)^67 ≤ (9035855604739/12500000000000 : ℝ)^51 := by
    have hnat : (7811182003 : ℕ)^67*12500000000000^51 ≤ 9035855604739^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7811182003 10000000000 9035855604739 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3224045989/10000000000 : ℝ)^67 ≤ (22603420394661/100000000000000 : ℝ)^51 := by
    have hnat : (3224045989 : ℕ)^67*100000000000000^51 ≤ 22603420394661^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3224045989 10000000000 22603420394661 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129942301/1250000000 : ℝ), (-7811182003/10000000000 : ℝ), (3224045989/10000000000 : ℝ)] ![(5109734752089/100000000000000 : ℝ), (9035855604739/12500000000000 : ℝ), (22603420394661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129942301/1250000000 : ℝ)|^67 ≤ (5109734752089/100000000000000 : ℝ)^51
        have hw : |(-129942301/1250000000 : ℝ)|=(129942301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7811182003/10000000000 : ℝ)|^67 ≤ (9035855604739/12500000000000 : ℝ)^51
        have hw : |(-7811182003/10000000000 : ℝ)|=(7811182003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3224045989/10000000000 : ℝ)|^67 ≤ (22603420394661/100000000000000 : ℝ)^51
        have hw : |(3224045989/10000000000 : ℝ)|=(3224045989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5031875813/10000000000 : ℝ)*x 0 + (1286335281/2500000000 : ℝ)*x 1 + (2672255199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5031875813/10000000000 : ℝ)^67 ≤ (20282663689429/50000000000000 : ℝ)^51 := by
    have hnat : (5031875813 : ℕ)^67*50000000000000^51 ≤ 20282663689429^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5031875813 10000000000 20282663689429 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1286335281/2500000000 : ℝ)^67 ≤ (1044281180183/2500000000000 : ℝ)^51 := by
    have hnat : (1286335281 : ℕ)^67*2500000000000^51 ≤ 1044281180183^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286335281 2500000000 1044281180183 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2672255199/10000000000 : ℝ)^67 ≤ (8831712701671/50000000000000 : ℝ)^51 := by
    have hnat : (2672255199 : ℕ)^67*50000000000000^51 ≤ 8831712701671^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672255199 10000000000 8831712701671 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5031875813/10000000000 : ℝ), (1286335281/2500000000 : ℝ), (2672255199/10000000000 : ℝ)] ![(20282663689429/50000000000000 : ℝ), (1044281180183/2500000000000 : ℝ), (8831712701671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5031875813/10000000000 : ℝ)|^67 ≤ (20282663689429/50000000000000 : ℝ)^51
        have hw : |(5031875813/10000000000 : ℝ)|=(5031875813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1286335281/2500000000 : ℝ)|^67 ≤ (1044281180183/2500000000000 : ℝ)^51
        have hw : |(1286335281/2500000000 : ℝ)|=(1286335281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2672255199/10000000000 : ℝ)|^67 ≤ (8831712701671/50000000000000 : ℝ)^51
        have hw : |(2672255199/10000000000 : ℝ)|=(2672255199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (151503993/250000000 : ℝ)*x 0 + (-700724533/1250000000 : ℝ)*x 1 + (-16029191/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (151503993/250000000 : ℝ)^67 ≤ (51789745738051/100000000000000 : ℝ)^51 := by
    have hnat : (151503993 : ℕ)^67*100000000000000^51 ≤ 51789745738051^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151503993 250000000 51789745738051 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (700724533/1250000000 : ℝ)^67 ≤ (23374828379999/50000000000000 : ℝ)^51 := by
    have hnat : (700724533 : ℕ)^67*50000000000000^51 ≤ 23374828379999^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700724533 1250000000 23374828379999 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16029191/400000000 : ℝ)^67 ≤ (1460597489477/100000000000000 : ℝ)^51 := by
    have hnat : (16029191 : ℕ)^67*100000000000000^51 ≤ 1460597489477^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16029191 400000000 1460597489477 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(151503993/250000000 : ℝ), (-700724533/1250000000 : ℝ), (-16029191/400000000 : ℝ)] ![(51789745738051/100000000000000 : ℝ), (23374828379999/50000000000000 : ℝ), (1460597489477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(151503993/250000000 : ℝ)|^67 ≤ (51789745738051/100000000000000 : ℝ)^51
        have hw : |(151503993/250000000 : ℝ)|=(151503993/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-700724533/1250000000 : ℝ)|^67 ≤ (23374828379999/50000000000000 : ℝ)^51
        have hw : |(-700724533/1250000000 : ℝ)|=(700724533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16029191/400000000 : ℝ)|^67 ≤ (1460597489477/100000000000000 : ℝ)^51
        have hw : |(-16029191/400000000 : ℝ)|=(16029191/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1499221857/5000000000 : ℝ)*x 0 + (142942279/10000000000 : ℝ)*x 1 + (8363438411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1499221857/5000000000 : ℝ)^67 ≤ (5137180430751/25000000000000 : ℝ)^51 := by
    have hnat : (1499221857 : ℕ)^67*25000000000000^51 ≤ 5137180430751^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499221857 5000000000 5137180430751 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142942279/10000000000 : ℝ)^67 ≤ (377040140767/100000000000000 : ℝ)^51 := by
    have hnat : (142942279 : ℕ)^67*100000000000000^51 ≤ 377040140767^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142942279 10000000000 377040140767 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8363438411/10000000000 : ℝ)^67 ≤ (79074238122701/100000000000000 : ℝ)^51 := by
    have hnat : (8363438411 : ℕ)^67*100000000000000^51 ≤ 79074238122701^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8363438411 10000000000 79074238122701 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1499221857/5000000000 : ℝ), (142942279/10000000000 : ℝ), (8363438411/10000000000 : ℝ)] ![(5137180430751/25000000000000 : ℝ), (377040140767/100000000000000 : ℝ), (79074238122701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1499221857/5000000000 : ℝ)|^67 ≤ (5137180430751/25000000000000 : ℝ)^51
        have hw : |(1499221857/5000000000 : ℝ)|=(1499221857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142942279/10000000000 : ℝ)|^67 ≤ (377040140767/100000000000000 : ℝ)^51
        have hw : |(142942279/10000000000 : ℝ)|=(142942279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8363438411/10000000000 : ℝ)|^67 ≤ (79074238122701/100000000000000 : ℝ)^51
        have hw : |(8363438411/10000000000 : ℝ)|=(8363438411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1343433471/10000000000 : ℝ)*x 0 + (-357262881/1000000000 : ℝ)*x 1 + (3685201267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343433471/10000000000 : ℝ)^67 ≤ (7156741867079/100000000000000 : ℝ)^51 := by
    have hnat : (1343433471 : ℕ)^67*100000000000000^51 ≤ 7156741867079^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343433471 10000000000 7156741867079 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (357262881/1000000000 : ℝ)^67 ≤ (2586716329247/10000000000000 : ℝ)^51 := by
    have hnat : (357262881 : ℕ)^67*10000000000000^51 ≤ 2586716329247^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357262881 1000000000 2586716329247 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3685201267/5000000000 : ℝ)^67 ≤ (16744023707847/25000000000000 : ℝ)^51 := by
    have hnat : (3685201267 : ℕ)^67*25000000000000^51 ≤ 16744023707847^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3685201267 5000000000 16744023707847 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1343433471/10000000000 : ℝ), (-357262881/1000000000 : ℝ), (3685201267/5000000000 : ℝ)] ![(7156741867079/100000000000000 : ℝ), (2586716329247/10000000000000 : ℝ), (16744023707847/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1343433471/10000000000 : ℝ)|^67 ≤ (7156741867079/100000000000000 : ℝ)^51
        have hw : |(-1343433471/10000000000 : ℝ)|=(1343433471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-357262881/1000000000 : ℝ)|^67 ≤ (2586716329247/10000000000000 : ℝ)^51
        have hw : |(-357262881/1000000000 : ℝ)|=(357262881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3685201267/5000000000 : ℝ)|^67 ≤ (16744023707847/25000000000000 : ℝ)^51
        have hw : |(3685201267/5000000000 : ℝ)|=(3685201267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7648228967/10000000000 : ℝ)*x 0 + (351473803/1250000000 : ℝ)*x 1 + (1837956003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7648228967/10000000000 : ℝ)^67 ≤ (35156122227201/50000000000000 : ℝ)^51 := by
    have hnat : (7648228967 : ℕ)^67*50000000000000^51 ≤ 35156122227201^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7648228967 10000000000 35156122227201 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (351473803/1250000000 : ℝ)^67 ≤ (18884907095321/100000000000000 : ℝ)^51 := by
    have hnat : (351473803 : ℕ)^67*100000000000000^51 ≤ 18884907095321^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351473803 1250000000 18884907095321 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1837956003/10000000000 : ℝ)^67 ≤ (10802848439447/100000000000000 : ℝ)^51 := by
    have hnat : (1837956003 : ℕ)^67*100000000000000^51 ≤ 10802848439447^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837956003 10000000000 10802848439447 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7648228967/10000000000 : ℝ), (351473803/1250000000 : ℝ), (1837956003/10000000000 : ℝ)] ![(35156122227201/50000000000000 : ℝ), (18884907095321/100000000000000 : ℝ), (10802848439447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7648228967/10000000000 : ℝ)|^67 ≤ (35156122227201/50000000000000 : ℝ)^51
        have hw : |(7648228967/10000000000 : ℝ)|=(7648228967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(351473803/1250000000 : ℝ)|^67 ≤ (18884907095321/100000000000000 : ℝ)^51
        have hw : |(351473803/1250000000 : ℝ)|=(351473803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1837956003/10000000000 : ℝ)|^67 ≤ (10802848439447/100000000000000 : ℝ)^51
        have hw : |(1837956003/10000000000 : ℝ)|=(1837956003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3866706649/10000000000 : ℝ)*x 0 + (-1804880647/2500000000 : ℝ)*x 1 + (-596242519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3866706649/10000000000 : ℝ)^67 ≤ (28699851447077/100000000000000 : ℝ)^51 := by
    have hnat : (3866706649 : ℕ)^67*100000000000000^51 ≤ 28699851447077^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3866706649 10000000000 28699851447077 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1804880647/2500000000 : ℝ)^67 ≤ (65180694402647/100000000000000 : ℝ)^51 := by
    have hnat : (1804880647 : ℕ)^67*100000000000000^51 ≤ 65180694402647^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804880647 2500000000 65180694402647 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (596242519/5000000000 : ℝ)^67 ≤ (6119454135679/100000000000000 : ℝ)^51 := by
    have hnat : (596242519 : ℕ)^67*100000000000000^51 ≤ 6119454135679^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596242519 5000000000 6119454135679 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3866706649/10000000000 : ℝ), (-1804880647/2500000000 : ℝ), (-596242519/5000000000 : ℝ)] ![(28699851447077/100000000000000 : ℝ), (65180694402647/100000000000000 : ℝ), (6119454135679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3866706649/10000000000 : ℝ)|^67 ≤ (28699851447077/100000000000000 : ℝ)^51
        have hw : |(3866706649/10000000000 : ℝ)|=(3866706649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1804880647/2500000000 : ℝ)|^67 ≤ (65180694402647/100000000000000 : ℝ)^51
        have hw : |(-1804880647/2500000000 : ℝ)|=(1804880647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-596242519/5000000000 : ℝ)|^67 ≤ (6119454135679/100000000000000 : ℝ)^51
        have hw : |(-596242519/5000000000 : ℝ)|=(596242519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (126274143/625000000 : ℝ)*x 0 + (131689/5000000000 : ℝ)*x 1 + (9054487721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126274143/625000000 : ℝ)^67 ≤ (6116478975589/50000000000000 : ℝ)^51 := by
    have hnat : (126274143 : ℕ)^67*50000000000000^51 ≤ 6116478975589^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126274143 625000000 6116478975589 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131689/5000000000 : ℝ)^67 ≤ (96360391/100000000000000 : ℝ)^51 := by
    have hnat : (131689 : ℕ)^67*100000000000000^51 ≤ 96360391^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131689 5000000000 96360391 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9054487721/10000000000 : ℝ)^67 ≤ (21941736419299/25000000000000 : ℝ)^51 := by
    have hnat : (9054487721 : ℕ)^67*25000000000000^51 ≤ 21941736419299^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9054487721 10000000000 21941736419299 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(126274143/625000000 : ℝ), (131689/5000000000 : ℝ), (9054487721/10000000000 : ℝ)] ![(6116478975589/50000000000000 : ℝ), (96360391/100000000000000 : ℝ), (21941736419299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(126274143/625000000 : ℝ)|^67 ≤ (6116478975589/50000000000000 : ℝ)^51
        have hw : |(126274143/625000000 : ℝ)|=(126274143/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131689/5000000000 : ℝ)|^67 ≤ (96360391/100000000000000 : ℝ)^51
        have hw : |(131689/5000000000 : ℝ)|=(131689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9054487721/10000000000 : ℝ)|^67 ≤ (21941736419299/25000000000000 : ℝ)^51
        have hw : |(9054487721/10000000000 : ℝ)|=(9054487721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-361954837/10000000000 : ℝ)*x 0 + (-404271599/500000000 : ℝ)*x 1 + (1637987363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361954837/10000000000 : ℝ)^67 ≤ (638906827843/50000000000000 : ℝ)^51 := by
    have hnat : (361954837 : ℕ)^67*50000000000000^51 ≤ 638906827843^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361954837 10000000000 638906827843 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404271599/500000000 : ℝ)^67 ≤ (18909819635041/25000000000000 : ℝ)^51 := by
    have hnat : (404271599 : ℕ)^67*25000000000000^51 ≤ 18909819635041^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404271599 500000000 18909819635041 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1637987363/5000000000 : ℝ)^67 ≤ (23082907789113/100000000000000 : ℝ)^51 := by
    have hnat : (1637987363 : ℕ)^67*100000000000000^51 ≤ 23082907789113^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1637987363 5000000000 23082907789113 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-361954837/10000000000 : ℝ), (-404271599/500000000 : ℝ), (1637987363/5000000000 : ℝ)] ![(638906827843/50000000000000 : ℝ), (18909819635041/25000000000000 : ℝ), (23082907789113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-361954837/10000000000 : ℝ)|^67 ≤ (638906827843/50000000000000 : ℝ)^51
        have hw : |(-361954837/10000000000 : ℝ)|=(361954837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404271599/500000000 : ℝ)|^67 ≤ (18909819635041/25000000000000 : ℝ)^51
        have hw : |(-404271599/500000000 : ℝ)|=(404271599/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1637987363/5000000000 : ℝ)|^67 ≤ (23082907789113/100000000000000 : ℝ)^51
        have hw : |(1637987363/5000000000 : ℝ)|=(1637987363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7971348069/10000000000 : ℝ)*x 0 + (472655849/2000000000 : ℝ)*x 1 + (91421047/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7971348069/10000000000 : ℝ)^67 ≤ (37120155305227/50000000000000 : ℝ)^51 := by
    have hnat : (7971348069 : ℕ)^67*50000000000000^51 ≤ 37120155305227^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7971348069 10000000000 37120155305227 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (472655849/2000000000 : ℝ)^67 ≤ (15030406973149/100000000000000 : ℝ)^51 := by
    have hnat : (472655849 : ℕ)^67*100000000000000^51 ≤ 15030406973149^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472655849 2000000000 15030406973149 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91421047/500000000 : ℝ)^67 ≤ (2145856479861/20000000000000 : ℝ)^51 := by
    have hnat : (91421047 : ℕ)^67*20000000000000^51 ≤ 2145856479861^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91421047 500000000 2145856479861 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7971348069/10000000000 : ℝ), (472655849/2000000000 : ℝ), (91421047/500000000 : ℝ)] ![(37120155305227/50000000000000 : ℝ), (15030406973149/100000000000000 : ℝ), (2145856479861/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7971348069/10000000000 : ℝ)|^67 ≤ (37120155305227/50000000000000 : ℝ)^51
        have hw : |(7971348069/10000000000 : ℝ)|=(7971348069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(472655849/2000000000 : ℝ)|^67 ≤ (15030406973149/100000000000000 : ℝ)^51
        have hw : |(472655849/2000000000 : ℝ)|=(472655849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(91421047/500000000 : ℝ)|^67 ≤ (2145856479861/20000000000000 : ℝ)^51
        have hw : |(91421047/500000000 : ℝ)|=(91421047/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (95605999/312500000 : ℝ)*x 0 + (-3688911911/5000000000 : ℝ)*x 1 + (-15392961/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95605999/312500000 : ℝ)^67 ≤ (21099188335023/100000000000000 : ℝ)^51 := by
    have hnat : (95605999 : ℕ)^67*100000000000000^51 ≤ 21099188335023^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95605999 312500000 21099188335023 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3688911911/5000000000 : ℝ)^67 ≤ (8383088062189/12500000000000 : ℝ)^51 := by
    have hnat : (3688911911 : ℕ)^67*12500000000000^51 ≤ 8383088062189^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688911911 5000000000 8383088062189 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15392961/78125000 : ℝ)^67 ≤ (5918053574799/50000000000000 : ℝ)^51 := by
    have hnat : (15392961 : ℕ)^67*50000000000000^51 ≤ 5918053574799^51*78125000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15392961 78125000 5918053574799 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(95605999/312500000 : ℝ), (-3688911911/5000000000 : ℝ), (-15392961/78125000 : ℝ)] ![(21099188335023/100000000000000 : ℝ), (8383088062189/12500000000000 : ℝ), (5918053574799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(95605999/312500000 : ℝ)|^67 ≤ (21099188335023/100000000000000 : ℝ)^51
        have hw : |(95605999/312500000 : ℝ)|=(95605999/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3688911911/5000000000 : ℝ)|^67 ≤ (8383088062189/12500000000000 : ℝ)^51
        have hw : |(-3688911911/5000000000 : ℝ)|=(3688911911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15392961/78125000 : ℝ)|^67 ≤ (5918053574799/50000000000000 : ℝ)^51
        have hw : |(-15392961/78125000 : ℝ)|=(15392961/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305076_s1_s1_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6751925359/10000000000 : ℝ)*x 0 + (623687/2500000000 : ℝ)*x 1 + (312962723/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6751925359/10000000000 : ℝ)^67 ≤ (59691807951553/100000000000000 : ℝ)^51 := by
    have hnat : (6751925359 : ℕ)^67*100000000000000^51 ≤ 59691807951553^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6751925359 10000000000 59691807951553 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623687/2500000000 : ℝ)^67 ≤ (1847915521/100000000000000 : ℝ)^51 := by
    have hnat : (623687 : ℕ)^67*100000000000000^51 ≤ 1847915521^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623687 2500000000 1847915521 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312962723/625000000 : ℝ)^67 ≤ (20153172059467/50000000000000 : ℝ)^51 := by
    have hnat : (312962723 : ℕ)^67*50000000000000^51 ≤ 20153172059467^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312962723 625000000 20153172059467 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6751925359/10000000000 : ℝ), (623687/2500000000 : ℝ), (312962723/625000000 : ℝ)] ![(59691807951553/100000000000000 : ℝ), (1847915521/100000000000000 : ℝ), (20153172059467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6751925359/10000000000 : ℝ)|^67 ≤ (59691807951553/100000000000000 : ℝ)^51
        have hw : |(6751925359/10000000000 : ℝ)|=(6751925359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623687/2500000000 : ℝ)|^67 ≤ (1847915521/100000000000000 : ℝ)^51
        have hw : |(623687/2500000000 : ℝ)|=(623687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(312962723/625000000 : ℝ)|^67 ≤ (20153172059467/50000000000000 : ℝ)^51
        have hw : |(312962723/625000000 : ℝ)|=(312962723/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305076_s1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((44609/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44609/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-2914/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-2914/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19231/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19231/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((76491/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76491/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-4101/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-4101/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85927/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85927/100000 : ℝ)*X 1 2) := by
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
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s1_pow0 : (44609/50000 : ℝ) ^ (133/32 : ℝ) ≤ (62239792238853006709/100000000000000000000 : ℝ) := by
    have hpowers : (44609/50000 : ℝ)^133 ≤ (62239792238853006709/100000000000000000000 : ℝ)^32 := by
      have hnat : (44609 : ℕ)^133*100000000000000000000^32 ≤ 62239792238853006709^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44609 50000 62239792238853006709 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44609/50000 : ℝ)) (X := (62239792238853006709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (162239792238853006709/100000000000000000000 : ℝ) ≤ (35108655935993/31250000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (162239792238853006709/100000000000000000000 : ℝ)^32 ≤ (35108655935993/31250000000000 : ℝ)^133 := by
      have hnat : (162239792238853006709 : ℕ)^32*31250000000000^133 ≤ 35108655935993^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        162239792238853006709 100000000000000000000 35108655935993 31250000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (35108655935993/31250000000000 : ℝ)) (X := (162239792238853006709/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (112239792238853006709/50000000000000000000 : ℝ) ≤ (12147689374228169/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (112239792238853006709/50000000000000000000 : ℝ)^32 ≤ (12147689374228169/10000000000000000 : ℝ)^133 := by
      have hnat : (112239792238853006709 : ℕ)^32*10000000000000000^133 ≤ 12147689374228169^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112239792238853006709 50000000000000000000 12147689374228169 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12147689374228169/10000000000000000 : ℝ)) (X := (112239792238853006709/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3858655935993/27880625000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(29449015313239/287800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (44609/50000 : ℝ)) (alpha := (3858655935993/27880625000000 : ℝ)) (beta := (29449015313239/287800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (44609/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3858655935993/27880625000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(29449015313239/287800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2914/3125 : ℝ) ^ (133/32 : ℝ) ≤ (74784962275220752687/100000000000000000000 : ℝ) := by
    have hpowers : (2914/3125 : ℝ)^133 ≤ (74784962275220752687/100000000000000000000 : ℝ)^32 := by
      have hnat : (2914 : ℕ)^133*100000000000000000000^32 ≤ 74784962275220752687^32*3125^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2914 3125 74784962275220752687 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2914/3125 : ℝ)) (X := (74784962275220752687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (174784962275220752687/100000000000000000000 : ℝ) ≤ (2287582883812687/2000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (174784962275220752687/100000000000000000000 : ℝ)^32 ≤ (2287582883812687/2000000000000000 : ℝ)^133 := by
      have hnat : (174784962275220752687 : ℕ)^32*2000000000000000^133 ≤ 2287582883812687^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        174784962275220752687 100000000000000000000 2287582883812687 2000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2287582883812687/2000000000000000 : ℝ)) (X := (174784962275220752687/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (124784962275220752687/50000000000000000000 : ℝ) ≤ (6230674396453279/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (124784962275220752687/50000000000000000000 : ℝ)^32 ≤ (6230674396453279/5000000000000000 : ℝ)^133 := by
      have hnat : (124784962275220752687 : ℕ)^32*5000000000000000^133 ≤ 6230674396453279^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        124784962275220752687 50000000000000000000 6230674396453279 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6230674396453279/5000000000000000 : ℝ)) (X := (124784962275220752687/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(287582883812687/1864960000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1023434373843123/9324800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (2914/3125 : ℝ)) (alpha := (287582883812687/1864960000000000 : ℝ)) (beta := (1023434373843123/9324800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (2914/3125 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(287582883812687/1864960000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1023434373843123/9324800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (19231/20000 : ℝ) ^ (133/32 : ℝ) ≤ (21240603525160423803/25000000000000000000 : ℝ) := by
    have hpowers : (19231/20000 : ℝ)^133 ≤ (21240603525160423803/25000000000000000000 : ℝ)^32 := by
      have hnat : (19231 : ℕ)^133*25000000000000000000^32 ≤ 21240603525160423803^32*20000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19231 20000 21240603525160423803 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19231/20000 : ℝ)) (X := (21240603525160423803/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (46240603525160423803/25000000000000000000 : ℝ) ≤ (5797365643828567/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (46240603525160423803/25000000000000000000 : ℝ)^32 ≤ (5797365643828567/5000000000000000 : ℝ)^133 := by
      have hnat : (46240603525160423803 : ℕ)^32*5000000000000000^133 ≤ 5797365643828567^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46240603525160423803 25000000000000000000 5797365643828567 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5797365643828567/5000000000000000 : ℝ)) (X := (46240603525160423803/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (33740603525160423803/12500000000000000000 : ℝ) ≤ (12698653535554889/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (33740603525160423803/12500000000000000000 : ℝ)^32 ≤ (12698653535554889/10000000000000000 : ℝ)^133 := by
      have hnat : (33740603525160423803 : ℕ)^32*10000000000000000^133 ≤ 12698653535554889^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33740603525160423803 12500000000000000000 12698653535554889 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12698653535554889/10000000000000000 : ℝ)) (X := (33740603525160423803/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(797365643828567/4807750000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(220784449579551/1923100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (19231/20000 : ℝ)) (alpha := (797365643828567/4807750000000000 : ℝ)) (beta := (220784449579551/1923100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (19231/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(797365643828567/4807750000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(220784449579551/1923100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((1329128047/2000000000 : ℝ)*X 1 0+(3167354929/10000000000 : ℝ)*X 1 1+(179773651/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2441215371/5000000000 : ℝ)*X 2 0+(-2513630577/5000000000 : ℝ)*X 2 1+(-2992311809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-129942301/1250000000 : ℝ)*X 0 0+(-7811182003/10000000000 : ℝ)*X 0 1+(3224045989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5031875813/10000000000 : ℝ)*X 1 0+(1286335281/2500000000 : ℝ)*X 1 1+(2672255199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((151503993/250000000 : ℝ)*X 2 0+(-700724533/1250000000 : ℝ)*X 2 1+(-16029191/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1499221857/5000000000 : ℝ)*X 0 0+(142942279/10000000000 : ℝ)*X 0 1+(8363438411/10000000000 : ℝ)*X 0 2+(1499221857/5000000000 : ℝ)*X 1 0+(142942279/10000000000 : ℝ)*X 1 1+(8363438411/10000000000 : ℝ)*X 1 2+(1499221857/5000000000 : ℝ)*X 2 0+(142942279/10000000000 : ℝ)*X 2 1+(8363438411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1343433471/10000000000 : ℝ)*X 0 0+(-357262881/1000000000 : ℝ)*X 0 1+(3685201267/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7648228967/10000000000 : ℝ)*X 1 0+(351473803/1250000000 : ℝ)*X 1 1+(1837956003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3866706649/10000000000 : ℝ)*X 2 0+(-1804880647/2500000000 : ℝ)*X 2 1+(-596242519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((126274143/625000000 : ℝ)*X 0 0+(131689/5000000000 : ℝ)*X 0 1+(9054487721/10000000000 : ℝ)*X 0 2+(126274143/625000000 : ℝ)*X 1 0+(131689/5000000000 : ℝ)*X 1 1+(9054487721/10000000000 : ℝ)*X 1 2+(126274143/625000000 : ℝ)*X 2 0+(131689/5000000000 : ℝ)*X 2 1+(9054487721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-361954837/10000000000 : ℝ)*X 0 0+(-404271599/500000000 : ℝ)*X 0 1+(1637987363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7971348069/10000000000 : ℝ)*X 1 0+(472655849/2000000000 : ℝ)*X 1 1+(91421047/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((95605999/312500000 : ℝ)*X 2 0+(-3688911911/5000000000 : ℝ)*X 2 1+(-15392961/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((6751925359/10000000000 : ℝ)*X 0 0+(623687/2500000000 : ℝ)*X 0 1+(312962723/625000000 : ℝ)*X 0 2+(6751925359/10000000000 : ℝ)*X 1 0+(623687/2500000000 : ℝ)*X 1 1+(312962723/625000000 : ℝ)*X 1 2+(6751925359/10000000000 : ℝ)*X 2 0+(623687/2500000000 : ℝ)*X 2 1+(312962723/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305076_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((76491/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76491/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (619872371953282177527740005929/80640313826000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116549251807/1000000000000 : ℝ)*(base3) + (482427817739/1000000000000 : ℝ)*(base7) + (73517/62500000000 : ℝ)*(base40) + (8124655099/1000000000000 : ℝ)*(base43) + (210444944251/200000000000 : ℝ)*(base54) + (2192027586737/1000000000000 : ℝ)*(major_s1_0) + (2183902931639/1000000000000 : ℝ)*(major_s1_1) + (569901432741/500000000000 : ℝ)*(major_s1_2) + (2642012439827/1000000000000 : ℝ)*(sp_s1_7) + (1383343341919/500000000000 : ℝ)*(sp_s1_8) + (1589773933083/1000000000000 : ℝ)*(sp_s1_9) + (29881045677/40000000000 : ℝ)*(sp_s1_13) + (7061297/500000000000 : ℝ)*(sp_s1_16) + (168553/500000000000 : ℝ)*(sp_s1_21) + (1433372297249/1000000000000 : ℝ)*(f.failure) + (2650137432031/1000000000000 : ℝ)*(f.sum) + (70342280748135096489/896626144000000000000000000000000 : ℝ)*base63 + (101984925940379/961550000000000000000000000 : ℝ)*base64 + (463265000235129/1864960000000000000000000000 : ℝ)*base67 + (378625547451347/2403875000000000000000000000 : ℝ)*base69 + (3576355618297549017/21446891975000000000000000000000 : ℝ)*base71 + (122779299824283/287800000000000000000000000 : ℝ)*base73 + (1972696251635723/9324800000000000000000000000 : ℝ)*base75 + (343212003268163/446090000000000000000000000 : ℝ)*base76 + (5280158623243276707/13418387200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (77/1562500000000000 : ℝ)*base86 + (3279/3125000000000000 : ℝ)*base88 + (77/1562500000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-4101/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-4101/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (256715081427763474800719038563/129024502121600000000000000000000000 : ℝ) := by norm_num
    linear_combination (1789077/1000000000000 : ℝ)*(base3) + (2483283861/4000000000 : ℝ)*(base7) + (153549652993/200000000000 : ℝ)*(base33) + (287799/200000000000 : ℝ)*(base40) + (88056024283/1000000000000 : ℝ)*(base54) + (111767543999/125000000000 : ℝ)*(major_s1_0) + (1661888616957/1000000000000 : ℝ)*(major_s1_1) + (786916296337/500000000000 : ℝ)*(major_s1_2) + (18634003/1000000000000 : ℝ)*(sp_s1_1) + (241433/40000000000 : ℝ)*(sp_s1_13) + (462576105231/250000000000 : ℝ)*(sp_s1_14) + (541269655517/500000000000 : ℝ)*(sp_s1_15) + (994500131677/1000000000000 : ℝ)*(sp_s1_16) + (50608444403/31250000000 : ℝ)*(sp_s1_20) + (16979892263/15625000000 : ℝ)*(f.failure) + (462576105231/250000000000 : ℝ)*(f.sum) + (11062493173034774563/896626144000000000000000000000000 : ℝ)*base63 + (46361800636939/480775000000000000000000000 : ℝ)*base64 + (159292266531987/1864960000000000000000000000 : ℝ)*base67 + (2079366575289617/4807750000000000000000000000 : ℝ)*base68 + (22367840366124091807/42893783950000000000000000000000 : ℝ)*base70 + (19108008672527/71950000000000000000000000 : ℝ)*base73 + (1523969385874791/9324800000000000000000000000 : ℝ)*base74 + (86445669177387/446090000000000000000000000 : ℝ)*base76 + (10880225842721375617/13418387200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1503/3125000000000000 : ℝ)*base87 + (1503/3125000000000000 : ℝ)*base89 + (1503/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85927/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85927/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (332081095870941838527/89218000000000000000000000 : ℝ) := by norm_num
    linear_combination (541067113193/1000000000000 : ℝ)*(base3) + (890475085517/1000000000000 : ℝ)*(base7) + (11069816513/500000000000 : ℝ)*(base33) + (3462279501/25000000000 : ℝ)*(base40) + (1093804247363/500000000000 : ℝ)*(major_s1_0) + (2209748127751/1000000000000 : ℝ)*(major_s1_1) + (2209748127751/1000000000000 : ℝ)*(major_s1_2) + (336989/200000000000 : ℝ)*(sp_s1_2) + (957453/250000000000 : ℝ)*(sp_s1_7) + (17032081/1000000000000 : ℝ)*(sp_s1_16) + (483956642611/200000000000 : ℝ)*(sp_s1_21) + (1469357261517/500000000000 : ℝ)*(sp_s1_22) + (479525738563/200000000000 : ℝ)*(sp_s1_23) + (448591943867/250000000000 : ℝ)*(sp_s1_27) + (1444959803143/1000000000000 : ℝ)*(f.failure) + (2419787042867/1000000000000 : ℝ)*(f.sum) + (100033023895573282983/896626144000000000000000000000000 : ℝ)*base62 + (355902221828121/1923100000000000000000000000 : ℝ)*base65 + (29612495722351/74598400000000000000000000 : ℝ)*base66 + (2246105076295367/4807750000000000000000000000 : ℝ)*base69 + (2335446855728393171/85787567900000000000000000000000 : ℝ)*base70 + (24813900933003/143900000000000000000000000 : ℝ)*base72 + (3803745172609947/9324800000000000000000000000 : ℝ)*base75 + (88628560433/871269531250000000000000 : ℝ)*base76 + (68765536187117331/13418387200000000000000000000000 : ℝ)*base79 + (4603/3125000000000000 : ℝ)*base86 + (739/1562500000000000 : ℝ)*base88 + (739/1562500000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((44609/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44609/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-2914/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-2914/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19231/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19231/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((76491/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76491/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-4101/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-4101/5000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85927/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85927/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305076_s1 p hpa hpb X hX hprev0

#print axioms solution
