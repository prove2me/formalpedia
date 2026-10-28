-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303055_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:56:20.856087+00:00
-- url     : https://prove2.me/submissions/f30f459a-c8ac-4484-ba4b-d8352573211d

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
theorem collision_support_c303055_s4_s4_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-91274231/500000000 : ℝ)*x 0 + (5891951519/10000000000 : ℝ)*x 1 + (310188209/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91274231/500000000 : ℝ)^33 ≤ (5296502720533/50000000000000 : ℝ)^25 := by
    have hnat : (91274231 : ℕ)^33*50000000000000^25 ≤ 5296502720533^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91274231 500000000 5296502720533 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5891951519/10000000000 : ℝ)^33 ≤ (49744159514517/100000000000000 : ℝ)^25 := by
    have hnat : (5891951519 : ℕ)^33*100000000000000^25 ≤ 49744159514517^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5891951519 10000000000 49744159514517 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310188209/625000000 : ℝ)^33 ≤ (991570875749/2500000000000 : ℝ)^25 := by
    have hnat : (310188209 : ℕ)^33*2500000000000^25 ≤ 991570875749^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310188209 625000000 991570875749 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-91274231/500000000 : ℝ), (5891951519/10000000000 : ℝ), (310188209/625000000 : ℝ)] ![(5296502720533/50000000000000 : ℝ), (49744159514517/100000000000000 : ℝ), (991570875749/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-91274231/500000000 : ℝ)|^33 ≤ (5296502720533/50000000000000 : ℝ)^25
        have hw : |(-91274231/500000000 : ℝ)|=(91274231/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5891951519/10000000000 : ℝ)|^33 ≤ (49744159514517/100000000000000 : ℝ)^25
        have hw : |(5891951519/10000000000 : ℝ)|=(5891951519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(310188209/625000000 : ℝ)|^33 ≤ (991570875749/2500000000000 : ℝ)^25
        have hw : |(310188209/625000000 : ℝ)|=(310188209/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2440859713/5000000000 : ℝ)*x 0 + (-391942353/5000000000 : ℝ)*x 1 + (1318945423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2440859713/5000000000 : ℝ)^33 ≤ (1552301607039/4000000000000 : ℝ)^25 := by
    have hnat : (2440859713 : ℕ)^33*4000000000000^25 ≤ 1552301607039^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2440859713 5000000000 1552301607039 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (391942353/5000000000 : ℝ)^33 ≤ (108458330259/3125000000000 : ℝ)^25 := by
    have hnat : (391942353 : ℕ)^33*3125000000000^25 ≤ 108458330259^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391942353 5000000000 108458330259 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318945423/2000000000 : ℝ)^33 ≤ (28860896623887/50000000000000 : ℝ)^25 := by
    have hnat : (1318945423 : ℕ)^33*50000000000000^25 ≤ 28860896623887^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318945423 2000000000 28860896623887 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2440859713/5000000000 : ℝ), (-391942353/5000000000 : ℝ), (1318945423/2000000000 : ℝ)] ![(1552301607039/4000000000000 : ℝ), (108458330259/3125000000000 : ℝ), (28860896623887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2440859713/5000000000 : ℝ)|^33 ≤ (1552301607039/4000000000000 : ℝ)^25
        have hw : |(2440859713/5000000000 : ℝ)|=(2440859713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-391942353/5000000000 : ℝ)|^33 ≤ (108458330259/3125000000000 : ℝ)^25
        have hw : |(-391942353/5000000000 : ℝ)|=(391942353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318945423/2000000000 : ℝ)|^33 ≤ (28860896623887/50000000000000 : ℝ)^25
        have hw : |(1318945423/2000000000 : ℝ)|=(1318945423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4861462467/10000000000 : ℝ)*x 0 + (1199499189/2000000000 : ℝ)*x 1 + (-452715269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4861462467/10000000000 : ℝ)^33 ≤ (4824389571493/12500000000000 : ℝ)^25 := by
    have hnat : (4861462467 : ℕ)^33*12500000000000^25 ≤ 4824389571493^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4861462467 10000000000 4824389571493 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1199499189/2000000000 : ℝ)^33 ≤ (50923746925167/100000000000000 : ℝ)^25 := by
    have hnat : (1199499189 : ℕ)^33*100000000000000^25 ≤ 50923746925167^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199499189 2000000000 50923746925167 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452715269/2500000000 : ℝ)^33 ≤ (10481136489893/100000000000000 : ℝ)^25 := by
    have hnat : (452715269 : ℕ)^33*100000000000000^25 ≤ 10481136489893^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452715269 2500000000 10481136489893 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4861462467/10000000000 : ℝ), (1199499189/2000000000 : ℝ), (-452715269/2500000000 : ℝ)] ![(4824389571493/12500000000000 : ℝ), (50923746925167/100000000000000 : ℝ), (10481136489893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4861462467/10000000000 : ℝ)|^33 ≤ (4824389571493/12500000000000 : ℝ)^25
        have hw : |(4861462467/10000000000 : ℝ)|=(4861462467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1199499189/2000000000 : ℝ)|^33 ≤ (50923746925167/100000000000000 : ℝ)^25
        have hw : |(1199499189/2000000000 : ℝ)|=(1199499189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-452715269/2500000000 : ℝ)|^33 ≤ (10481136489893/100000000000000 : ℝ)^25
        have hw : |(-452715269/2500000000 : ℝ)|=(452715269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6257810939/10000000000 : ℝ)*x 0 + (3982703187/10000000000 : ℝ)*x 1 + (1275383921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6257810939/10000000000 : ℝ)^33 ≤ (26930698797787/50000000000000 : ℝ)^25 := by
    have hnat : (6257810939 : ℕ)^33*50000000000000^25 ≤ 26930698797787^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6257810939 10000000000 26930698797787 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3982703187/10000000000 : ℝ)^33 ≤ (29664353163401/100000000000000 : ℝ)^25 := by
    have hnat : (3982703187 : ℕ)^33*100000000000000^25 ≤ 29664353163401^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3982703187 10000000000 29664353163401 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1275383921/5000000000 : ℝ)^33 ≤ (8237124611469/50000000000000 : ℝ)^25 := by
    have hnat : (1275383921 : ℕ)^33*50000000000000^25 ≤ 8237124611469^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275383921 5000000000 8237124611469 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6257810939/10000000000 : ℝ), (3982703187/10000000000 : ℝ), (1275383921/5000000000 : ℝ)] ![(26930698797787/50000000000000 : ℝ), (29664353163401/100000000000000 : ℝ), (8237124611469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6257810939/10000000000 : ℝ)|^33 ≤ (26930698797787/50000000000000 : ℝ)^25
        have hw : |(6257810939/10000000000 : ℝ)|=(6257810939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3982703187/10000000000 : ℝ)|^33 ≤ (29664353163401/100000000000000 : ℝ)^25
        have hw : |(3982703187/10000000000 : ℝ)|=(3982703187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1275383921/5000000000 : ℝ)|^33 ≤ (8237124611469/50000000000000 : ℝ)^25
        have hw : |(1275383921/5000000000 : ℝ)|=(1275383921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-753594133/5000000000 : ℝ)*x 0 + (36748379/80000000 : ℝ)*x 1 + (6441803157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (753594133/5000000000 : ℝ)^33 ≤ (8225856059291/100000000000000 : ℝ)^25 := by
    have hnat : (753594133 : ℕ)^33*100000000000000^25 ≤ 8225856059291^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753594133 5000000000 8225856059291 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36748379/80000000 : ℝ)^33 ≤ (35812581174699/100000000000000 : ℝ)^25 := by
    have hnat : (36748379 : ℕ)^33*100000000000000^25 ≤ 35812581174699^25*80000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36748379 80000000 35812581174699 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6441803157/10000000000 : ℝ)^33 ≤ (55961562752197/100000000000000 : ℝ)^25 := by
    have hnat : (6441803157 : ℕ)^33*100000000000000^25 ≤ 55961562752197^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6441803157 10000000000 55961562752197 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-753594133/5000000000 : ℝ), (36748379/80000000 : ℝ), (6441803157/10000000000 : ℝ)] ![(8225856059291/100000000000000 : ℝ), (35812581174699/100000000000000 : ℝ), (55961562752197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-753594133/5000000000 : ℝ)|^33 ≤ (8225856059291/100000000000000 : ℝ)^25
        have hw : |(-753594133/5000000000 : ℝ)|=(753594133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36748379/80000000 : ℝ)|^33 ≤ (35812581174699/100000000000000 : ℝ)^25
        have hw : |(36748379/80000000 : ℝ)|=(36748379/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6441803157/10000000000 : ℝ)|^33 ≤ (55961562752197/100000000000000 : ℝ)^25
        have hw : |(6441803157/10000000000 : ℝ)|=(6441803157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4112020111/10000000000 : ℝ)*x 0 + (-262611/2500000000 : ℝ)*x 1 + (7554195473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4112020111/10000000000 : ℝ)^33 ≤ (1547116108413/5000000000000 : ℝ)^25 := by
    have hnat : (4112020111 : ℕ)^33*5000000000000^25 ≤ 1547116108413^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112020111 10000000000 1547116108413 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262611/2500000000 : ℝ)^33 ≤ (112006243/20000000000000 : ℝ)^25 := by
    have hnat : (262611 : ℕ)^33*20000000000000^25 ≤ 112006243^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262611 2500000000 112006243 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7554195473/10000000000 : ℝ)^33 ≤ (34528558893267/50000000000000 : ℝ)^25 := by
    have hnat : (7554195473 : ℕ)^33*50000000000000^25 ≤ 34528558893267^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7554195473 10000000000 34528558893267 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4112020111/10000000000 : ℝ), (-262611/2500000000 : ℝ), (7554195473/10000000000 : ℝ)] ![(1547116108413/5000000000000 : ℝ), (112006243/20000000000000 : ℝ), (34528558893267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4112020111/10000000000 : ℝ)|^33 ≤ (1547116108413/5000000000000 : ℝ)^25
        have hw : |(4112020111/10000000000 : ℝ)|=(4112020111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262611/2500000000 : ℝ)|^33 ≤ (112006243/20000000000000 : ℝ)^25
        have hw : |(-262611/2500000000 : ℝ)|=(262611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7554195473/10000000000 : ℝ)|^33 ≤ (34528558893267/50000000000000 : ℝ)^25
        have hw : |(7554195473/10000000000 : ℝ)|=(7554195473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2045156039/5000000000 : ℝ)*x 0 + (3633154241/5000000000 : ℝ)*x 1 + (-408755209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2045156039/5000000000 : ℝ)^33 ≤ (30726883007487/100000000000000 : ℝ)^25 := by
    have hnat : (2045156039 : ℕ)^33*100000000000000^25 ≤ 30726883007487^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045156039 5000000000 30726883007487 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3633154241/5000000000 : ℝ)^33 ≤ (32802297393511/50000000000000 : ℝ)^25 := by
    have hnat : (3633154241 : ℕ)^33*50000000000000^25 ≤ 32802297393511^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3633154241 5000000000 32802297393511 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408755209/5000000000 : ℝ)^33 ≤ (366852219113/10000000000000 : ℝ)^25 := by
    have hnat : (408755209 : ℕ)^33*10000000000000^25 ≤ 366852219113^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408755209 5000000000 366852219113 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2045156039/5000000000 : ℝ), (3633154241/5000000000 : ℝ), (-408755209/5000000000 : ℝ)] ![(30726883007487/100000000000000 : ℝ), (32802297393511/50000000000000 : ℝ), (366852219113/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2045156039/5000000000 : ℝ)|^33 ≤ (30726883007487/100000000000000 : ℝ)^25
        have hw : |(2045156039/5000000000 : ℝ)|=(2045156039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3633154241/5000000000 : ℝ)|^33 ≤ (32802297393511/50000000000000 : ℝ)^25
        have hw : |(3633154241/5000000000 : ℝ)|=(3633154241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-408755209/5000000000 : ℝ)|^33 ≤ (366852219113/10000000000000 : ℝ)^25
        have hw : |(-408755209/5000000000 : ℝ)|=(408755209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1180863921/2500000000 : ℝ)*x 0 + (51059823/80000000 : ℝ)*x 1 + (1414140573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1180863921/2500000000 : ℝ)^33 ≤ (3715549021121/10000000000000 : ℝ)^25 := by
    have hnat : (1180863921 : ℕ)^33*10000000000000^25 ≤ 3715549021121^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180863921 2500000000 3715549021121 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51059823/80000000 : ℝ)^33 ≤ (55282274075349/100000000000000 : ℝ)^25 := by
    have hnat : (51059823 : ℕ)^33*100000000000000^25 ≤ 55282274075349^25*80000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51059823 80000000 55282274075349 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414140573/10000000000 : ℝ)^33 ≤ (7562235698269/100000000000000 : ℝ)^25 := by
    have hnat : (1414140573 : ℕ)^33*100000000000000^25 ≤ 7562235698269^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414140573 10000000000 7562235698269 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1180863921/2500000000 : ℝ), (51059823/80000000 : ℝ), (1414140573/10000000000 : ℝ)] ![(3715549021121/10000000000000 : ℝ), (55282274075349/100000000000000 : ℝ), (7562235698269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1180863921/2500000000 : ℝ)|^33 ≤ (3715549021121/10000000000000 : ℝ)^25
        have hw : |(1180863921/2500000000 : ℝ)|=(1180863921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51059823/80000000 : ℝ)|^33 ≤ (55282274075349/100000000000000 : ℝ)^25
        have hw : |(51059823/80000000 : ℝ)|=(51059823/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1414140573/10000000000 : ℝ)|^33 ≤ (7562235698269/100000000000000 : ℝ)^25
        have hw : |(1414140573/10000000000 : ℝ)|=(1414140573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-599377019/10000000000 : ℝ)*x 0 + (4905941009/10000000000 : ℝ)*x 1 + (3331104537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (599377019/10000000000 : ℝ)^33 ≤ (1217682654663/50000000000000 : ℝ)^25 := by
    have hnat : (599377019 : ℕ)^33*50000000000000^25 ≤ 1217682654663^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599377019 10000000000 1217682654663 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4905941009/10000000000 : ℝ)^33 ≤ (9765477268011/25000000000000 : ℝ)^25 := by
    have hnat : (4905941009 : ℕ)^33*25000000000000^25 ≤ 9765477268011^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4905941009 10000000000 9765477268011 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3331104537/5000000000 : ℝ)^33 ≤ (3656420350471/6250000000000 : ℝ)^25 := by
    have hnat : (3331104537 : ℕ)^33*6250000000000^25 ≤ 3656420350471^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3331104537 5000000000 3656420350471 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-599377019/10000000000 : ℝ), (4905941009/10000000000 : ℝ), (3331104537/5000000000 : ℝ)] ![(1217682654663/50000000000000 : ℝ), (9765477268011/25000000000000 : ℝ), (3656420350471/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-599377019/10000000000 : ℝ)|^33 ≤ (1217682654663/50000000000000 : ℝ)^25
        have hw : |(-599377019/10000000000 : ℝ)|=(599377019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4905941009/10000000000 : ℝ)|^33 ≤ (9765477268011/25000000000000 : ℝ)^25
        have hw : |(4905941009/10000000000 : ℝ)|=(4905941009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3331104537/5000000000 : ℝ)|^33 ≤ (3656420350471/6250000000000 : ℝ)^25
        have hw : |(3331104537/5000000000 : ℝ)|=(3331104537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1833522331/5000000000 : ℝ)*x 0 + (-452111879/10000000000 : ℝ)*x 1 + (3886950227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1833522331/5000000000 : ℝ)^33 ≤ (26600964475141/100000000000000 : ℝ)^25 := by
    have hnat : (1833522331 : ℕ)^33*100000000000000^25 ≤ 26600964475141^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833522331 5000000000 26600964475141 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452111879/10000000000 : ℝ)^33 ≤ (419628155917/25000000000000 : ℝ)^25 := by
    have hnat : (452111879 : ℕ)^33*25000000000000^25 ≤ 419628155917^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452111879 10000000000 419628155917 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3886950227/5000000000 : ℝ)^33 ≤ (71720522884479/100000000000000 : ℝ)^25 := by
    have hnat : (3886950227 : ℕ)^33*100000000000000^25 ≤ 71720522884479^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3886950227 5000000000 71720522884479 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1833522331/5000000000 : ℝ), (-452111879/10000000000 : ℝ), (3886950227/5000000000 : ℝ)] ![(26600964475141/100000000000000 : ℝ), (419628155917/25000000000000 : ℝ), (71720522884479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1833522331/5000000000 : ℝ)|^33 ≤ (26600964475141/100000000000000 : ℝ)^25
        have hw : |(1833522331/5000000000 : ℝ)|=(1833522331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-452111879/10000000000 : ℝ)|^33 ≤ (419628155917/25000000000000 : ℝ)^25
        have hw : |(-452111879/10000000000 : ℝ)|=(452111879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3886950227/5000000000 : ℝ)|^33 ≤ (71720522884479/100000000000000 : ℝ)^25
        have hw : |(3886950227/5000000000 : ℝ)|=(3886950227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6562263297/10000000000 : ℝ)*x 0 + (1254744479/2500000000 : ℝ)*x 1 + (-59252713/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6562263297/10000000000 : ℝ)^33 ≤ (57347015384983/100000000000000 : ℝ)^25 := by
    have hnat : (6562263297 : ℕ)^33*100000000000000^25 ≤ 57347015384983^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6562263297 10000000000 57347015384983 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1254744479/2500000000 : ℝ)^33 ≤ (805085808993/2000000000000 : ℝ)^25 := by
    have hnat : (1254744479 : ℕ)^33*2000000000000^25 ≤ 805085808993^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254744479 2500000000 805085808993 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59252713/1000000000 : ℝ)^33 ≤ (479738831141/20000000000000 : ℝ)^25 := by
    have hnat : (59252713 : ℕ)^33*20000000000000^25 ≤ 479738831141^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59252713 1000000000 479738831141 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6562263297/10000000000 : ℝ), (1254744479/2500000000 : ℝ), (-59252713/1000000000 : ℝ)] ![(57347015384983/100000000000000 : ℝ), (805085808993/2000000000000 : ℝ), (479738831141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6562263297/10000000000 : ℝ)|^33 ≤ (57347015384983/100000000000000 : ℝ)^25
        have hw : |(6562263297/10000000000 : ℝ)|=(6562263297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1254744479/2500000000 : ℝ)|^33 ≤ (805085808993/2000000000000 : ℝ)^25
        have hw : |(1254744479/2500000000 : ℝ)|=(1254744479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-59252713/1000000000 : ℝ)|^33 ≤ (479738831141/20000000000000 : ℝ)^25
        have hw : |(-59252713/1000000000 : ℝ)|=(59252713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1015256519/1250000000 : ℝ)*x 0 + (113591319/400000000 : ℝ)*x 1 + (518999877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1015256519/1250000000 : ℝ)^33 ≤ (1899760397321/2500000000000 : ℝ)^25 := by
    have hnat : (1015256519 : ℕ)^33*2500000000000^25 ≤ 1899760397321^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015256519 1250000000 1899760397321 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113591319/400000000 : ℝ)^33 ≤ (9490878285987/50000000000000 : ℝ)^25 := by
    have hnat : (113591319 : ℕ)^33*50000000000000^25 ≤ 9490878285987^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113591319 400000000 9490878285987 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518999877/5000000000 : ℝ)^33 ≤ (125695688003/2500000000000 : ℝ)^25 := by
    have hnat : (518999877 : ℕ)^33*2500000000000^25 ≤ 125695688003^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518999877 5000000000 125695688003 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1015256519/1250000000 : ℝ), (113591319/400000000 : ℝ), (518999877/5000000000 : ℝ)] ![(1899760397321/2500000000000 : ℝ), (9490878285987/50000000000000 : ℝ), (125695688003/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1015256519/1250000000 : ℝ)|^33 ≤ (1899760397321/2500000000000 : ℝ)^25
        have hw : |(1015256519/1250000000 : ℝ)|=(1015256519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113591319/400000000 : ℝ)|^33 ≤ (9490878285987/50000000000000 : ℝ)^25
        have hw : |(113591319/400000000 : ℝ)|=(113591319/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518999877/5000000000 : ℝ)|^33 ≤ (125695688003/2500000000000 : ℝ)^25
        have hw : |(518999877/5000000000 : ℝ)|=(518999877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-412418787/5000000000 : ℝ)*x 0 + (7114912193/10000000000 : ℝ)*x 1 + (533260183/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412418787/5000000000 : ℝ)^33 ≤ (463998256677/12500000000000 : ℝ)^25 := by
    have hnat : (412418787 : ℕ)^33*12500000000000^25 ≤ 463998256677^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412418787 5000000000 463998256677 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7114912193/10000000000 : ℝ)^33 ≤ (31903167449363/50000000000000 : ℝ)^25 := by
    have hnat : (7114912193 : ℕ)^33*50000000000000^25 ≤ 31903167449363^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7114912193 10000000000 31903167449363 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533260183/1250000000 : ℝ)^33 ≤ (1624083951651/5000000000000 : ℝ)^25 := by
    have hnat : (533260183 : ℕ)^33*5000000000000^25 ≤ 1624083951651^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533260183 1250000000 1624083951651 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412418787/5000000000 : ℝ), (7114912193/10000000000 : ℝ), (533260183/1250000000 : ℝ)] ![(463998256677/12500000000000 : ℝ), (31903167449363/50000000000000 : ℝ), (1624083951651/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412418787/5000000000 : ℝ)|^33 ≤ (463998256677/12500000000000 : ℝ)^25
        have hw : |(-412418787/5000000000 : ℝ)|=(412418787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7114912193/10000000000 : ℝ)|^33 ≤ (31903167449363/50000000000000 : ℝ)^25
        have hw : |(7114912193/10000000000 : ℝ)|=(7114912193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(533260183/1250000000 : ℝ)|^33 ≤ (1624083951651/5000000000000 : ℝ)^25
        have hw : |(533260183/1250000000 : ℝ)|=(533260183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1323443957/2000000000 : ℝ)*x 0 + (-50544271/10000000000 : ℝ)*x 1 + (161750519/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323443957/2000000000 : ℝ)^33 ≤ (724772575243/1250000000000 : ℝ)^25 := by
    have hnat : (1323443957 : ℕ)^33*1250000000000^25 ≤ 724772575243^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323443957 2000000000 724772575243 1250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50544271/10000000000 : ℝ)^33 ≤ (93077981589/100000000000000 : ℝ)^25 := by
    have hnat : (50544271 : ℕ)^33*100000000000000^25 ≤ 93077981589^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50544271 10000000000 93077981589 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161750519/312500000 : ℝ)^33 ≤ (20962557991727/50000000000000 : ℝ)^25 := by
    have hnat : (161750519 : ℕ)^33*50000000000000^25 ≤ 20962557991727^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161750519 312500000 20962557991727 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323443957/2000000000 : ℝ), (-50544271/10000000000 : ℝ), (161750519/312500000 : ℝ)] ![(724772575243/1250000000000 : ℝ), (93077981589/100000000000000 : ℝ), (20962557991727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323443957/2000000000 : ℝ)|^33 ≤ (724772575243/1250000000000 : ℝ)^25
        have hw : |(1323443957/2000000000 : ℝ)|=(1323443957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50544271/10000000000 : ℝ)|^33 ≤ (93077981589/100000000000000 : ℝ)^25
        have hw : |(-50544271/10000000000 : ℝ)|=(50544271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161750519/312500000 : ℝ)|^33 ≤ (20962557991727/50000000000000 : ℝ)^25
        have hw : |(161750519/312500000 : ℝ)|=(161750519/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (135234979/400000000 : ℝ)*x 0 + (1494763247/2000000000 : ℝ)*x 1 + (-1477901953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135234979/400000000 : ℝ)^33 ≤ (373369095357/1562500000000 : ℝ)^25 := by
    have hnat : (135234979 : ℕ)^33*1562500000000^25 ≤ 373369095357^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135234979 400000000 373369095357 1562500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1494763247/2000000000 : ℝ)^33 ≤ (6808884828063/10000000000000 : ℝ)^25 := by
    have hnat : (1494763247 : ℕ)^33*10000000000000^25 ≤ 6808884828063^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1494763247 2000000000 6808884828063 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1477901953/10000000000 : ℝ)^33 ≤ (1603105920679/20000000000000 : ℝ)^25 := by
    have hnat : (1477901953 : ℕ)^33*20000000000000^25 ≤ 1603105920679^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477901953 10000000000 1603105920679 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135234979/400000000 : ℝ), (1494763247/2000000000 : ℝ), (-1477901953/10000000000 : ℝ)] ![(373369095357/1562500000000 : ℝ), (6808884828063/10000000000000 : ℝ), (1603105920679/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135234979/400000000 : ℝ)|^33 ≤ (373369095357/1562500000000 : ℝ)^25
        have hw : |(135234979/400000000 : ℝ)|=(135234979/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1494763247/2000000000 : ℝ)|^33 ≤ (6808884828063/10000000000000 : ℝ)^25
        have hw : |(1494763247/2000000000 : ℝ)|=(1494763247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1477901953/10000000000 : ℝ)|^33 ≤ (1603105920679/20000000000000 : ℝ)^25
        have hw : |(-1477901953/10000000000 : ℝ)|=(1477901953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s4_s4_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7996747817/10000000000 : ℝ)*x 0 + (582250299/2500000000 : ℝ)*x 1 + (1870970181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7996747817/10000000000 : ℝ)^33 ≤ (37223370318719/50000000000000 : ℝ)^25 := by
    have hnat : (7996747817 : ℕ)^33*50000000000000^25 ≤ 37223370318719^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7996747817 10000000000 37223370318719 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (582250299/2500000000 : ℝ)^33 ≤ (2922092872329/20000000000000 : ℝ)^25 := by
    have hnat : (582250299 : ℕ)^33*20000000000000^25 ≤ 2922092872329^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582250299 2500000000 2922092872329 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870970181/10000000000 : ℝ)^33 ≤ (5471397495699/50000000000000 : ℝ)^25 := by
    have hnat : (1870970181 : ℕ)^33*50000000000000^25 ≤ 5471397495699^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870970181 10000000000 5471397495699 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7996747817/10000000000 : ℝ), (582250299/2500000000 : ℝ), (1870970181/10000000000 : ℝ)] ![(37223370318719/50000000000000 : ℝ), (2922092872329/20000000000000 : ℝ), (5471397495699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7996747817/10000000000 : ℝ)|^33 ≤ (37223370318719/50000000000000 : ℝ)^25
        have hw : |(7996747817/10000000000 : ℝ)|=(7996747817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(582250299/2500000000 : ℝ)|^33 ≤ (2922092872329/20000000000000 : ℝ)^25
        have hw : |(582250299/2500000000 : ℝ)|=(582250299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1870970181/10000000000 : ℝ)|^33 ≤ (5471397495699/50000000000000 : ℝ)^25
        have hw : |(1870970181/10000000000 : ℝ)|=(1870970181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303055_s4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((73627/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73627/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9033/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9033/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18287/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18287/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12257/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12257/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2457/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2457/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31331/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31331/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91389/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (73627/100000 : ℝ) ^ (131/32 : ℝ) ≤ (114220258934395593/400000000000000000 : ℝ) := by
    have hpowers : (73627/100000 : ℝ)^131 ≤ (114220258934395593/400000000000000000 : ℝ)^32 := by
      have hnat : (73627 : ℕ)^131*400000000000000000^32 ≤ 114220258934395593^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73627 100000 114220258934395593 400000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73627/100000 : ℝ)) (X := (114220258934395593/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (514220258934395593/400000000000000000 : ℝ) ≤ (10632802360418431/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (514220258934395593/400000000000000000 : ℝ)^32 ≤ (10632802360418431/10000000000000000 : ℝ)^131 := by
      have hnat : (514220258934395593 : ℕ)^32*10000000000000000^131 ≤ 10632802360418431^131*400000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        514220258934395593 400000000000000000 10632802360418431 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10632802360418431/10000000000000000 : ℝ)) (X := (514220258934395593/400000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (314220258934395593/200000000000000000 : ℝ) ≤ (5583387173620683/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (314220258934395593/200000000000000000 : ℝ)^32 ≤ (5583387173620683/5000000000000000 : ℝ)^131 := by
      have hnat : (314220258934395593 : ℕ)^32*5000000000000000^131 ≤ 5583387173620683^131*200000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        314220258934395593 200000000000000000 5583387173620683 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5583387173620683/5000000000000000 : ℝ)) (X := (314220258934395593/200000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(632802360418431/7362700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(106794397364587/1472540000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (73627/100000 : ℝ)) (alpha := (632802360418431/7362700000000000 : ℝ)) (beta := (106794397364587/1472540000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (73627/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(632802360418431/7362700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(106794397364587/1472540000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (9033/12500 : ℝ) ^ (131/32 : ℝ) ≤ (13226103912630436269/50000000000000000000 : ℝ) := by
    have hpowers : (9033/12500 : ℝ)^131 ≤ (13226103912630436269/50000000000000000000 : ℝ)^32 := by
      have hnat : (9033 : ℕ)^131*50000000000000000000^32 ≤ 13226103912630436269^32*12500^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9033 12500 13226103912630436269 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9033/12500 : ℝ)) (X := (13226103912630436269/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (63226103912630436269/50000000000000000000 : ℝ) ≤ (10590051105214423/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (63226103912630436269/50000000000000000000 : ℝ)^32 ≤ (10590051105214423/10000000000000000 : ℝ)^131 := by
      have hnat : (63226103912630436269 : ℕ)^32*10000000000000000^131 ≤ 10590051105214423^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63226103912630436269 50000000000000000000 10590051105214423 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10590051105214423/10000000000000000 : ℝ)) (X := (63226103912630436269/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (38226103912630436269/25000000000000000000 : ℝ) ≤ (11093003933598401/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (38226103912630436269/25000000000000000000 : ℝ)^32 ≤ (11093003933598401/10000000000000000 : ℝ)^131 := by
      have hnat : (38226103912630436269 : ℕ)^32*10000000000000000^131 ≤ 11093003933598401^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38226103912630436269 25000000000000000000 11093003933598401 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11093003933598401/10000000000000000 : ℝ)) (X := (38226103912630436269/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(196683701738141/2408800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(251476414191989/3613200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (9033/12500 : ℝ)) (alpha := (196683701738141/2408800000000000 : ℝ)) (beta := (251476414191989/3613200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (9033/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(196683701738141/2408800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(251476414191989/3613200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (18287/25000 : ℝ) ^ (131/32 : ℝ) ≤ (13901088539680067037/50000000000000000000 : ℝ) := by
    have hpowers : (18287/25000 : ℝ)^131 ≤ (13901088539680067037/50000000000000000000 : ℝ)^32 := by
      have hnat : (18287 : ℕ)^131*50000000000000000000^32 ≤ 13901088539680067037^32*25000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18287 25000 13901088539680067037 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18287/25000 : ℝ)) (X := (13901088539680067037/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (63901088539680067037/50000000000000000000 : ℝ) ≤ (1327194655584611/1250000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (63901088539680067037/50000000000000000000 : ℝ)^32 ≤ (1327194655584611/1250000000000000 : ℝ)^131 := by
      have hnat : (63901088539680067037 : ℕ)^32*1250000000000000^131 ≤ 1327194655584611^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63901088539680067037 50000000000000000000 1327194655584611 1250000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1327194655584611/1250000000000000 : ℝ)) (X := (63901088539680067037/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (38901088539680067037/25000000000000000000 : ℝ) ≤ (2785133928370497/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (38901088539680067037/25000000000000000000 : ℝ)^32 ≤ (2785133928370497/2500000000000000 : ℝ)^131 := by
      have hnat : (38901088539680067037 : ℕ)^32*2500000000000000^131 ≤ 2785133928370497^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38901088539680067037 25000000000000000000 2785133928370497 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2785133928370497/2500000000000000 : ℝ)) (X := (38901088539680067037/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(77194655584611/914350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5229784688051/73148000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (18287/25000 : ℝ)) (alpha := (77194655584611/914350000000000 : ℝ)) (beta := (5229784688051/73148000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (18287/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(77194655584611/914350000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5229784688051/73148000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-91274231/500000000 : ℝ)*X 0 0+(5891951519/10000000000 : ℝ)*X 0 1+(310188209/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((2440859713/5000000000 : ℝ)*X 1 0+(-391942353/5000000000 : ℝ)*X 1 1+(1318945423/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((4861462467/10000000000 : ℝ)*X 2 0+(1199499189/2000000000 : ℝ)*X 2 1+(-452715269/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((6257810939/10000000000 : ℝ)*X 0 0+(3982703187/10000000000 : ℝ)*X 0 1+(1275383921/5000000000 : ℝ)*X 0 2+(6257810939/10000000000 : ℝ)*X 1 0+(3982703187/10000000000 : ℝ)*X 1 1+(1275383921/5000000000 : ℝ)*X 1 2+(6257810939/10000000000 : ℝ)*X 2 0+(3982703187/10000000000 : ℝ)*X 2 1+(1275383921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-753594133/5000000000 : ℝ)*X 0 0+(36748379/80000000 : ℝ)*X 0 1+(6441803157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((4112020111/10000000000 : ℝ)*X 1 0+(-262611/2500000000 : ℝ)*X 1 1+(7554195473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((2045156039/5000000000 : ℝ)*X 2 0+(3633154241/5000000000 : ℝ)*X 2 1+(-408755209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((1180863921/2500000000 : ℝ)*X 0 0+(51059823/80000000 : ℝ)*X 0 1+(1414140573/10000000000 : ℝ)*X 0 2+(1180863921/2500000000 : ℝ)*X 1 0+(51059823/80000000 : ℝ)*X 1 1+(1414140573/10000000000 : ℝ)*X 1 2+(1180863921/2500000000 : ℝ)*X 2 0+(51059823/80000000 : ℝ)*X 2 1+(1414140573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-599377019/10000000000 : ℝ)*X 0 0+(4905941009/10000000000 : ℝ)*X 0 1+(3331104537/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((1833522331/5000000000 : ℝ)*X 1 0+(-452111879/10000000000 : ℝ)*X 1 1+(3886950227/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((6562263297/10000000000 : ℝ)*X 2 0+(1254744479/2500000000 : ℝ)*X 2 1+(-59252713/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((1015256519/1250000000 : ℝ)*X 0 0+(113591319/400000000 : ℝ)*X 0 1+(518999877/5000000000 : ℝ)*X 0 2+(1015256519/1250000000 : ℝ)*X 1 0+(113591319/400000000 : ℝ)*X 1 1+(518999877/5000000000 : ℝ)*X 1 2+(1015256519/1250000000 : ℝ)*X 2 0+(113591319/400000000 : ℝ)*X 2 1+(518999877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-412418787/5000000000 : ℝ)*X 0 0+(7114912193/10000000000 : ℝ)*X 0 1+(533260183/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((1323443957/2000000000 : ℝ)*X 1 0+(-50544271/10000000000 : ℝ)*X 1 1+(161750519/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((135234979/400000000 : ℝ)*X 2 0+(1494763247/2000000000 : ℝ)*X 2 1+(-1477901953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((7996747817/10000000000 : ℝ)*X 0 0+(582250299/2500000000 : ℝ)*X 0 1+(1870970181/10000000000 : ℝ)*X 0 2+(7996747817/10000000000 : ℝ)*X 1 0+(582250299/2500000000 : ℝ)*X 1 1+(1870970181/10000000000 : ℝ)*X 1 2+(7996747817/10000000000 : ℝ)*X 2 0+(582250299/2500000000 : ℝ)*X 2 1+(1870970181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((12257/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12257/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13323951181463482847112072906727/810812286687800000000000000000000000 : ℝ) := by norm_num
    linear_combination (144436080971/500000000000 : ℝ)*(base7) + (2839073/1000000000000 : ℝ)*(base49) + (1438887/1000000000000 : ℝ)*(base60) + (3057840190471/1000000000000 : ℝ)*(major_s4_0) + (3057840190471/1000000000000 : ℝ)*(major_s4_1) + (3057840190471/1000000000000 : ℝ)*(major_s4_2) + (15305091/500000000000 : ℝ)*(sp_s4_0) + (1185973/250000000000 : ℝ)*(sp_s4_6) + (781339839793/200000000000 : ℝ)*(sp_s4_7) + (488351069203/125000000000 : ℝ)*(sp_s4_8) + (3906785278587/1000000000000 : ℝ)*(sp_s4_9) + (58043387859/25000000000 : ℝ)*(sp_s4_13) + (19686119/250000000000 : ℝ)*(sp_s4_14) + (23275037/1000000000000 : ℝ)*(sp_s4_23) + (2032868096311/1000000000000 : ℝ)*(f.failure) + (488351069203/125000000000 : ℝ)*(f.sum) + (18356967538322814827/44049725600000000000000000000000 : ℝ)*base62 + (578617587880451/365740000000000000000000000 : ℝ)*base65 + (4179544927084261/3613200000000000000000000000 : ℝ)*base67 + (119065022814761/914350000000000000000000000 : ℝ)*base69 + (45007869272215505471/67320847450000000000000000000000 : ℝ)*base71 + (766117485190493/1472540000000000000000000000 : ℝ)*base73 + (1270329670248091/2408800000000000000000000000 : ℝ)*base75 + (5026799751536091/7362700000000000000000000000 : ℝ)*base77 + (32514058880914944427/266029076400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (31/5000000000000000 : ℝ)*base87 + (31/5000000000000000 : ℝ)*base89 + (31/5000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2457/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2457/4000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4919875202772290693159442386941/405406143343900000000000000000000000 : ℝ) := by norm_num
    linear_combination (124892895619/500000000000 : ℝ)*(base7) + (5196649/1000000000000 : ℝ)*(base27) + (670407840611/250000000000 : ℝ)*(major_s4_0) + (670407840611/250000000000 : ℝ)*(major_s4_1) + (670407840611/250000000000 : ℝ)*(major_s4_2) + (8270159/500000000000 : ℝ)*(sp_s4_0) + (4168989/250000000000 : ℝ)*(sp_s4_2) + (27126517/200000000000 : ℝ)*(sp_s4_8) + (3428295104363/1000000000000 : ℝ)*(sp_s4_14) + (3428176049293/1000000000000 : ℝ)*(sp_s4_15) + (1714147502961/500000000000 : ℝ)*(sp_s4_16) + (406500199967/200000000000 : ℝ)*(sp_s4_20) + (9299/250000000000 : ℝ)*(sp_s4_21) + (10525341/250000000000 : ℝ)*(sp_s4_27) + (1782762506611/1000000000000 : ℝ)*(f.failure) + (3428311681877/1000000000000 : ℝ)*(f.sum) + (6590246618214000253/11012431400000000000000000000000 : ℝ)*base63 + (17490705234711/22858750000000000000000000 : ℝ)*base65 + (467477899762961/903300000000000000000000000 : ℝ)*base67 + (664445069909369/914350000000000000000000000 : ℝ)*base69 + (6329950367907937247/33660423725000000000000000000000 : ℝ)*base71 + (38696984031713/736270000000000000000000000 : ℝ)*base72 + (359707376573471/602200000000000000000000000 : ℝ)*base75 + (591726796360147/3681350000000000000000000000 : ℝ)*base77 + (6948151089826996907/66507269100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1331/5000000000000000 : ℝ)*base87 + (1331/5000000000000000 : ℝ)*base89 + (1331/5000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31331/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31331/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (239280733679619094507410225929/16216245733756000000000000000000000 : ℝ) := by norm_num
    linear_combination (209404953839/500000000000 : ℝ)*(base7) + (37617178459/500000000000 : ℝ)*(base40) + (5989/7812500000 : ℝ)*(base59) + (126075676711/50000000000 : ℝ)*(major_s4_0) + (126075676711/50000000000 : ℝ)*(major_s4_1) + (126075676711/50000000000 : ℝ)*(major_s4_2) + (3847/1600000000 : ℝ)*(sp_s4_1) + (1929899/500000000000 : ℝ)*(sp_s4_8) + (54171909/500000000000 : ℝ)*(sp_s4_9) + (40128327/1000000000000 : ℝ)*(sp_s4_20) + (3111542685683/1000000000000 : ℝ)*(sp_s4_21) + (311153642151/100000000000 : ℝ)*(sp_s4_22) + (622286868373/200000000000 : ℝ)*(sp_s4_23) + (523771279803/250000000000 : ℝ)*(sp_s4_27) + (838157669931/500000000000 : ℝ)*(f.failure) + (3111542685683/1000000000000 : ℝ)*(f.sum) + (198746649622022857/440497256000000000000000000000 : ℝ)*base63 + (12685285443899/91435000000000000000000000 : ℝ)*base65 + (27019803727751/180660000000000000000000000 : ℝ)*base66 + (12647320732251/91435000000000000000000000 : ℝ)*base69 + (8701212656747023839/13464169490000000000000000000000 : ℝ)*base71 + (276504689175733/736270000000000000000000000 : ℝ)*base72 + (25832604308423/120440000000000000000000000 : ℝ)*base75 + (21891319804487/368135000000000000000000000 : ℝ)*base76 + (122918205653803423/2660290764000000000000000000000 : ℝ)*base78 + (1051/2500000000000000 : ℝ)*base87 + (1051/2500000000000000 : ℝ)*base89 + (1051/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((73627/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73627/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9033/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9033/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18287/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18287/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12257/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12257/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2457/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2457/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31331/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31331/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303055_s4 p hpa hpb X hX hprev3

#print axioms solution
