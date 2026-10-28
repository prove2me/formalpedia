-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301053_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:31:04.235811+00:00
-- url     : https://prove2.me/submissions/5a13cee6-0f81-40f4-beed-7919d521f514

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
theorem collision_support_c301053_s6_s6_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171162899/10000000000 : ℝ)*x 0 + (5295336213/10000000000 : ℝ)*x 1 + (1341452947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171162899/10000000000 : ℝ)^65 ≤ (3296417294933/25000000000000 : ℝ)^49 := by
    have hnat : (2171162899 : ℕ)^65*25000000000000^49 ≤ 3296417294933^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171162899 10000000000 3296417294933 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5295336213/10000000000 : ℝ)^65 ≤ (4302653055299/10000000000000 : ℝ)^49 := by
    have hnat : (5295336213 : ℕ)^65*10000000000000^49 ≤ 4302653055299^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295336213 10000000000 4302653055299 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1341452947/2500000000 : ℝ)^65 ≤ (21893900129907/50000000000000 : ℝ)^49 := by
    have hnat : (1341452947 : ℕ)^65*50000000000000^49 ≤ 21893900129907^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341452947 2500000000 21893900129907 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171162899/10000000000 : ℝ), (5295336213/10000000000 : ℝ), (1341452947/2500000000 : ℝ)] ![(3296417294933/25000000000000 : ℝ), (4302653055299/10000000000000 : ℝ), (21893900129907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171162899/10000000000 : ℝ)|^65 ≤ (3296417294933/25000000000000 : ℝ)^49
        have hw : |(-2171162899/10000000000 : ℝ)|=(2171162899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5295336213/10000000000 : ℝ)|^65 ≤ (4302653055299/10000000000000 : ℝ)^49
        have hw : |(5295336213/10000000000 : ℝ)|=(5295336213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1341452947/2500000000 : ℝ)|^65 ≤ (21893900129907/50000000000000 : ℝ)^49
        have hw : |(1341452947/2500000000 : ℝ)|=(1341452947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1150793543/2500000000 : ℝ)*x 0 + (-1676998601/10000000000 : ℝ)*x 1 + (6364005889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1150793543/2500000000 : ℝ)^65 ≤ (35730190921851/100000000000000 : ℝ)^49 := by
    have hnat : (1150793543 : ℕ)^65*100000000000000^49 ≤ 35730190921851^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1150793543 2500000000 35730190921851 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1676998601/10000000000 : ℝ)^65 ≤ (9360927640047/100000000000000 : ℝ)^49 := by
    have hnat : (1676998601 : ℕ)^65*100000000000000^49 ≤ 9360927640047^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676998601 10000000000 9360927640047 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6364005889/10000000000 : ℝ)^65 ≤ (54908881432981/100000000000000 : ℝ)^49 := by
    have hnat : (6364005889 : ℕ)^65*100000000000000^49 ≤ 54908881432981^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6364005889 10000000000 54908881432981 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1150793543/2500000000 : ℝ), (-1676998601/10000000000 : ℝ), (6364005889/10000000000 : ℝ)] ![(35730190921851/100000000000000 : ℝ), (9360927640047/100000000000000 : ℝ), (54908881432981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1150793543/2500000000 : ℝ)|^65 ≤ (35730190921851/100000000000000 : ℝ)^49
        have hw : |(1150793543/2500000000 : ℝ)|=(1150793543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1676998601/10000000000 : ℝ)|^65 ≤ (9360927640047/100000000000000 : ℝ)^49
        have hw : |(-1676998601/10000000000 : ℝ)|=(1676998601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6364005889/10000000000 : ℝ)|^65 ≤ (54908881432981/100000000000000 : ℝ)^49
        have hw : |(6364005889/10000000000 : ℝ)|=(6364005889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4619862327/10000000000 : ℝ)*x 0 + (6365723391/10000000000 : ℝ)*x 1 + (-330211657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4619862327/10000000000 : ℝ)^65 ≤ (17951062171031/50000000000000 : ℝ)^49 := by
    have hnat : (4619862327 : ℕ)^65*50000000000000^49 ≤ 17951062171031^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4619862327 10000000000 17951062171031 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6365723391/10000000000 : ℝ)^65 ≤ (54928539720649/100000000000000 : ℝ)^49 := by
    have hnat : (6365723391 : ℕ)^65*100000000000000^49 ≤ 54928539720649^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6365723391 10000000000 54928539720649 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330211657/2000000000 : ℝ)^65 ≤ (2292333982561/25000000000000 : ℝ)^49 := by
    have hnat : (330211657 : ℕ)^65*25000000000000^49 ≤ 2292333982561^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330211657 2000000000 2292333982561 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4619862327/10000000000 : ℝ), (6365723391/10000000000 : ℝ), (-330211657/2000000000 : ℝ)] ![(17951062171031/50000000000000 : ℝ), (54928539720649/100000000000000 : ℝ), (2292333982561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4619862327/10000000000 : ℝ)|^65 ≤ (17951062171031/50000000000000 : ℝ)^49
        have hw : |(4619862327/10000000000 : ℝ)|=(4619862327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6365723391/10000000000 : ℝ)|^65 ≤ (54928539720649/100000000000000 : ℝ)^49
        have hw : |(6365723391/10000000000 : ℝ)|=(6365723391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-330211657/2000000000 : ℝ)|^65 ≤ (2292333982561/25000000000000 : ℝ)^49
        have hw : |(-330211657/2000000000 : ℝ)|=(330211657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1371437269/2000000000 : ℝ)*x 0 + (744959591/2500000000 : ℝ)*x 1 + (361803979/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1371437269/2000000000 : ℝ)^65 ≤ (60623720953349/100000000000000 : ℝ)^49 := by
    have hnat : (1371437269 : ℕ)^65*100000000000000^49 ≤ 60623720953349^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371437269 2000000000 60623720953349 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744959591/2500000000 : ℝ)^65 ≤ (10033917693869/50000000000000 : ℝ)^49 := by
    have hnat : (744959591 : ℕ)^65*50000000000000^49 ≤ 10033917693869^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744959591 2500000000 10033917693869 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (361803979/1250000000 : ℝ)^65 ≤ (9654221821297/50000000000000 : ℝ)^49 := by
    have hnat : (361803979 : ℕ)^65*50000000000000^49 ≤ 9654221821297^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361803979 1250000000 9654221821297 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1371437269/2000000000 : ℝ), (744959591/2500000000 : ℝ), (361803979/1250000000 : ℝ)] ![(60623720953349/100000000000000 : ℝ), (10033917693869/50000000000000 : ℝ), (9654221821297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1371437269/2000000000 : ℝ)|^65 ≤ (60623720953349/100000000000000 : ℝ)^49
        have hw : |(1371437269/2000000000 : ℝ)|=(1371437269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(744959591/2500000000 : ℝ)|^65 ≤ (10033917693869/50000000000000 : ℝ)^49
        have hw : |(744959591/2500000000 : ℝ)|=(744959591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(361803979/1250000000 : ℝ)|^65 ≤ (9654221821297/50000000000000 : ℝ)^49
        have hw : |(361803979/1250000000 : ℝ)|=(361803979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2012578129/10000000000 : ℝ)*x 0 + (4234635949/10000000000 : ℝ)*x 1 + (3233483357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2012578129/10000000000 : ℝ)^65 ≤ (2980895259/25000000000 : ℝ)^49 := by
    have hnat : (2012578129 : ℕ)^65*25000000000^49 ≤ 2980895259^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012578129 10000000000 2980895259 25000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234635949/10000000000 : ℝ)^65 ≤ (255888102091/800000000000 : ℝ)^49 := by
    have hnat : (4234635949 : ℕ)^65*800000000000^49 ≤ 255888102091^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234635949 10000000000 255888102091 800000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3233483357/5000000000 : ℝ)^65 ≤ (56090406181341/100000000000000 : ℝ)^49 := by
    have hnat : (3233483357 : ℕ)^65*100000000000000^49 ≤ 56090406181341^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3233483357 5000000000 56090406181341 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2012578129/10000000000 : ℝ), (4234635949/10000000000 : ℝ), (3233483357/5000000000 : ℝ)] ![(2980895259/25000000000 : ℝ), (255888102091/800000000000 : ℝ), (56090406181341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2012578129/10000000000 : ℝ)|^65 ≤ (2980895259/25000000000 : ℝ)^49
        have hw : |(-2012578129/10000000000 : ℝ)|=(2012578129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234635949/10000000000 : ℝ)|^65 ≤ (255888102091/800000000000 : ℝ)^49
        have hw : |(4234635949/10000000000 : ℝ)|=(4234635949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3233483357/5000000000 : ℝ)|^65 ≤ (56090406181341/100000000000000 : ℝ)^49
        have hw : |(3233483357/5000000000 : ℝ)|=(3233483357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3904651423/10000000000 : ℝ)*x 0 + (-107990241/1250000000 : ℝ)*x 1 + (7426907713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3904651423/10000000000 : ℝ)^65 ≤ (14361221554871/50000000000000 : ℝ)^49 := by
    have hnat : (3904651423 : ℕ)^65*50000000000000^49 ≤ 14361221554871^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3904651423 10000000000 14361221554871 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107990241/1250000000 : ℝ)^65 ≤ (776659858877/20000000000000 : ℝ)^49 := by
    have hnat : (107990241 : ℕ)^65*20000000000000^49 ≤ 776659858877^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107990241 1250000000 776659858877 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7426907713/10000000000 : ℝ)^65 ≤ (67394257583553/100000000000000 : ℝ)^49 := by
    have hnat : (7426907713 : ℕ)^65*100000000000000^49 ≤ 67394257583553^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7426907713 10000000000 67394257583553 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3904651423/10000000000 : ℝ), (-107990241/1250000000 : ℝ), (7426907713/10000000000 : ℝ)] ![(14361221554871/50000000000000 : ℝ), (776659858877/20000000000000 : ℝ), (67394257583553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3904651423/10000000000 : ℝ)|^65 ≤ (14361221554871/50000000000000 : ℝ)^49
        have hw : |(3904651423/10000000000 : ℝ)|=(3904651423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107990241/1250000000 : ℝ)|^65 ≤ (776659858877/20000000000000 : ℝ)^49
        have hw : |(-107990241/1250000000 : ℝ)|=(107990241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7426907713/10000000000 : ℝ)|^65 ≤ (67394257583553/100000000000000 : ℝ)^49
        have hw : |(7426907713/10000000000 : ℝ)|=(7426907713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1960824163/5000000000 : ℝ)*x 0 + (7500979027/10000000000 : ℝ)*x 1 + (-679547383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1960824163/5000000000 : ℝ)^65 ≤ (28888414954097/100000000000000 : ℝ)^49 := by
    have hnat : (1960824163 : ℕ)^65*100000000000000^49 ≤ 28888414954097^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960824163 5000000000 28888414954097 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7500979027/10000000000 : ℝ)^65 ≤ (4267958193201/6250000000000 : ℝ)^49 := by
    have hnat : (7500979027 : ℕ)^65*6250000000000^49 ≤ 4267958193201^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7500979027 10000000000 4267958193201 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679547383/10000000000 : ℝ)^65 ≤ (564850786893/20000000000000 : ℝ)^49 := by
    have hnat : (679547383 : ℕ)^65*20000000000000^49 ≤ 564850786893^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679547383 10000000000 564850786893 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1960824163/5000000000 : ℝ), (7500979027/10000000000 : ℝ), (-679547383/10000000000 : ℝ)] ![(28888414954097/100000000000000 : ℝ), (4267958193201/6250000000000 : ℝ), (564850786893/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1960824163/5000000000 : ℝ)|^65 ≤ (28888414954097/100000000000000 : ℝ)^49
        have hw : |(1960824163/5000000000 : ℝ)|=(1960824163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7500979027/10000000000 : ℝ)|^65 ≤ (4267958193201/6250000000000 : ℝ)^49
        have hw : |(7500979027/10000000000 : ℝ)|=(7500979027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-679547383/10000000000 : ℝ)|^65 ≤ (564850786893/20000000000000 : ℝ)^49
        have hw : |(-679547383/10000000000 : ℝ)|=(679547383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6468039183/10000000000 : ℝ)*x 0 + (2454428181/5000000000 : ℝ)*x 1 + (1043040991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6468039183/10000000000 : ℝ)^65 ≤ (56102745800093/100000000000000 : ℝ)^49 := by
    have hnat : (6468039183 : ℕ)^65*100000000000000^49 ≤ 56102745800093^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6468039183 10000000000 56102745800093 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2454428181/5000000000 : ℝ)^65 ≤ (19455658959691/50000000000000 : ℝ)^49 := by
    have hnat : (2454428181 : ℕ)^65*50000000000000^49 ≤ 19455658959691^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454428181 5000000000 19455658959691 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043040991/10000000000 : ℝ)^65 ≤ (498593627713/10000000000000 : ℝ)^49 := by
    have hnat : (1043040991 : ℕ)^65*10000000000000^49 ≤ 498593627713^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043040991 10000000000 498593627713 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6468039183/10000000000 : ℝ), (2454428181/5000000000 : ℝ), (1043040991/10000000000 : ℝ)] ![(56102745800093/100000000000000 : ℝ), (19455658959691/50000000000000 : ℝ), (498593627713/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6468039183/10000000000 : ℝ)|^65 ≤ (56102745800093/100000000000000 : ℝ)^49
        have hw : |(6468039183/10000000000 : ℝ)|=(6468039183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2454428181/5000000000 : ℝ)|^65 ≤ (19455658959691/50000000000000 : ℝ)^49
        have hw : |(2454428181/5000000000 : ℝ)|=(2454428181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043040991/10000000000 : ℝ)|^65 ≤ (498593627713/10000000000000 : ℝ)^49
        have hw : |(1043040991/10000000000 : ℝ)|=(1043040991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1164868351/10000000000 : ℝ)*x 0 + (2426631/5000000 : ℝ)*x 1 + (806294401/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1164868351/10000000000 : ℝ)^65 ≤ (288640758393/5000000000000 : ℝ)^49 := by
    have hnat : (1164868351 : ℕ)^65*5000000000000^49 ≤ 288640758393^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164868351 10000000000 288640758393 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2426631/5000000 : ℝ)^65 ≤ (38327822003389/100000000000000 : ℝ)^49 := by
    have hnat : (2426631 : ℕ)^65*100000000000000^49 ≤ 38327822003389^49*5000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2426631 5000000 38327822003389 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806294401/1250000000 : ℝ)^65 ≤ (55899362812483/100000000000000 : ℝ)^49 := by
    have hnat : (806294401 : ℕ)^65*100000000000000^49 ≤ 55899362812483^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806294401 1250000000 55899362812483 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1164868351/10000000000 : ℝ), (2426631/5000000 : ℝ), (806294401/1250000000 : ℝ)] ![(288640758393/5000000000000 : ℝ), (38327822003389/100000000000000 : ℝ), (55899362812483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1164868351/10000000000 : ℝ)|^65 ≤ (288640758393/5000000000000 : ℝ)^49
        have hw : |(-1164868351/10000000000 : ℝ)|=(1164868351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2426631/5000000 : ℝ)|^65 ≤ (38327822003389/100000000000000 : ℝ)^49
        have hw : |(2426631/5000000 : ℝ)|=(2426631/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806294401/1250000000 : ℝ)|^65 ≤ (55899362812483/100000000000000 : ℝ)^49
        have hw : |(806294401/1250000000 : ℝ)|=(806294401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3759686603/10000000000 : ℝ)*x 0 + (-224288309/2000000000 : ℝ)*x 1 + (3705148519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3759686603/10000000000 : ℝ)^65 ≤ (27316537608137/100000000000000 : ℝ)^49 := by
    have hnat : (3759686603 : ℕ)^65*100000000000000^49 ≤ 27316537608137^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3759686603 10000000000 27316537608137 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224288309/2000000000 : ℝ)^65 ≤ (5489080826121/100000000000000 : ℝ)^49 := by
    have hnat : (224288309 : ℕ)^65*100000000000000^49 ≤ 5489080826121^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224288309 2000000000 5489080826121 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3705148519/5000000000 : ℝ)^65 ≤ (67194381545743/100000000000000 : ℝ)^49 := by
    have hnat : (3705148519 : ℕ)^65*100000000000000^49 ≤ 67194381545743^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705148519 5000000000 67194381545743 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3759686603/10000000000 : ℝ), (-224288309/2000000000 : ℝ), (3705148519/5000000000 : ℝ)] ![(27316537608137/100000000000000 : ℝ), (5489080826121/100000000000000 : ℝ), (67194381545743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3759686603/10000000000 : ℝ)|^65 ≤ (27316537608137/100000000000000 : ℝ)^49
        have hw : |(3759686603/10000000000 : ℝ)|=(3759686603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224288309/2000000000 : ℝ)|^65 ≤ (5489080826121/100000000000000 : ℝ)^49
        have hw : |(-224288309/2000000000 : ℝ)|=(224288309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3705148519/5000000000 : ℝ)|^65 ≤ (67194381545743/100000000000000 : ℝ)^49
        have hw : |(3705148519/5000000000 : ℝ)|=(3705148519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2875814503/5000000000 : ℝ)*x 0 + (5846969887/10000000000 : ℝ)*x 1 + (-696159521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2875814503/5000000000 : ℝ)^65 ≤ (48012600516617/100000000000000 : ℝ)^49 := by
    have hnat : (2875814503 : ℕ)^65*100000000000000^49 ≤ 48012600516617^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2875814503 5000000000 48012600516617 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5846969887/10000000000 : ℝ)^65 ≤ (3066949779459/6250000000000 : ℝ)^49 := by
    have hnat : (5846969887 : ℕ)^65*6250000000000^49 ≤ 3066949779459^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5846969887 10000000000 3066949779459 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (696159521/10000000000 : ℝ)^65 ≤ (2916202999411/100000000000000 : ℝ)^49 := by
    have hnat : (696159521 : ℕ)^65*100000000000000^49 ≤ 2916202999411^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696159521 10000000000 2916202999411 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2875814503/5000000000 : ℝ), (5846969887/10000000000 : ℝ), (-696159521/10000000000 : ℝ)] ![(48012600516617/100000000000000 : ℝ), (3066949779459/6250000000000 : ℝ), (2916202999411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2875814503/5000000000 : ℝ)|^65 ≤ (48012600516617/100000000000000 : ℝ)^49
        have hw : |(2875814503/5000000000 : ℝ)|=(2875814503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5846969887/10000000000 : ℝ)|^65 ≤ (3066949779459/6250000000000 : ℝ)^49
        have hw : |(5846969887/10000000000 : ℝ)|=(5846969887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-696159521/10000000000 : ℝ)|^65 ≤ (2916202999411/100000000000000 : ℝ)^49
        have hw : |(-696159521/10000000000 : ℝ)|=(696159521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2168927081/2500000000 : ℝ)*x 0 + (80800663/400000000 : ℝ)*x 1 + (1075573867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168927081/2500000000 : ℝ)^65 ≤ (82824651623519/100000000000000 : ℝ)^49 := by
    have hnat : (2168927081 : ℕ)^65*100000000000000^49 ≤ 82824651623519^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168927081 2500000000 82824651623519 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80800663/400000000 : ℝ)^65 ≤ (2995518890233/25000000000000 : ℝ)^49 := by
    have hnat : (80800663 : ℕ)^65*25000000000000^49 ≤ 2995518890233^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80800663 400000000 2995518890233 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075573867/10000000000 : ℝ)^65 ≤ (5193272806027/100000000000000 : ℝ)^49 := by
    have hnat : (1075573867 : ℕ)^65*100000000000000^49 ≤ 5193272806027^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075573867 10000000000 5193272806027 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168927081/2500000000 : ℝ), (80800663/400000000 : ℝ), (1075573867/10000000000 : ℝ)] ![(82824651623519/100000000000000 : ℝ), (2995518890233/25000000000000 : ℝ), (5193272806027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168927081/2500000000 : ℝ)|^65 ≤ (82824651623519/100000000000000 : ℝ)^49
        have hw : |(2168927081/2500000000 : ℝ)|=(2168927081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80800663/400000000 : ℝ)|^65 ≤ (2995518890233/25000000000000 : ℝ)^49
        have hw : |(80800663/400000000 : ℝ)|=(80800663/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075573867/10000000000 : ℝ)|^65 ≤ (5193272806027/100000000000000 : ℝ)^49
        have hw : |(1075573867/10000000000 : ℝ)|=(1075573867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1136715931/10000000000 : ℝ)*x 0 + (6214410049/10000000000 : ℝ)*x 1 + (640718149/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1136715931/10000000000 : ℝ)^65 ≤ (5588476108623/100000000000000 : ℝ)^49 := by
    have hnat : (1136715931 : ℕ)^65*100000000000000^49 ≤ 5588476108623^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136715931 10000000000 5588476108623 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6214410049/10000000000 : ℝ)^65 ≤ (26601654916109/50000000000000 : ℝ)^49 := by
    have hnat : (6214410049 : ℕ)^65*50000000000000^49 ≤ 26601654916109^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6214410049 10000000000 26601654916109 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640718149/1250000000 : ℝ)^65 ≤ (1287756689039/3125000000000 : ℝ)^49 := by
    have hnat : (640718149 : ℕ)^65*3125000000000^49 ≤ 1287756689039^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640718149 1250000000 1287756689039 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1136715931/10000000000 : ℝ), (6214410049/10000000000 : ℝ), (640718149/1250000000 : ℝ)] ![(5588476108623/100000000000000 : ℝ), (26601654916109/50000000000000 : ℝ), (1287756689039/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1136715931/10000000000 : ℝ)|^65 ≤ (5588476108623/100000000000000 : ℝ)^49
        have hw : |(-1136715931/10000000000 : ℝ)|=(1136715931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6214410049/10000000000 : ℝ)|^65 ≤ (26601654916109/50000000000000 : ℝ)^49
        have hw : |(6214410049/10000000000 : ℝ)|=(6214410049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(640718149/1250000000 : ℝ)|^65 ≤ (1287756689039/3125000000000 : ℝ)^49
        have hw : |(640718149/1250000000 : ℝ)|=(640718149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1125544/1953125 : ℝ)*x 0 + (-328261593/5000000000 : ℝ)*x 1 + (365966573/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1125544/1953125 : ℝ)^65 ≤ (24068088845979/50000000000000 : ℝ)^49 := by
    have hnat : (1125544 : ℕ)^65*50000000000000^49 ≤ 24068088845979^49*1953125^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125544 1953125 24068088845979 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328261593/5000000000 : ℝ)^65 ≤ (1349012622839/50000000000000 : ℝ)^49 := by
    have hnat : (328261593 : ℕ)^65*50000000000000^49 ≤ 1349012622839^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328261593 5000000000 1349012622839 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365966573/625000000 : ℝ)^65 ≤ (2458289852473/5000000000000 : ℝ)^49 := by
    have hnat : (365966573 : ℕ)^65*5000000000000^49 ≤ 2458289852473^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365966573 625000000 2458289852473 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1125544/1953125 : ℝ), (-328261593/5000000000 : ℝ), (365966573/625000000 : ℝ)] ![(24068088845979/50000000000000 : ℝ), (1349012622839/50000000000000 : ℝ), (2458289852473/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1125544/1953125 : ℝ)|^65 ≤ (24068088845979/50000000000000 : ℝ)^49
        have hw : |(1125544/1953125 : ℝ)|=(1125544/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-328261593/5000000000 : ℝ)|^65 ≤ (1349012622839/50000000000000 : ℝ)^49
        have hw : |(-328261593/5000000000 : ℝ)|=(328261593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(365966573/625000000 : ℝ)|^65 ≤ (2458289852473/5000000000000 : ℝ)^49
        have hw : |(365966573/625000000 : ℝ)|=(365966573/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1866691671/5000000000 : ℝ)*x 0 + (3719169821/5000000000 : ℝ)*x 1 + (-1108433823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1866691671/5000000000 : ℝ)^65 ≤ (1691457141153/6250000000000 : ℝ)^49 := by
    have hnat : (1866691671 : ℕ)^65*6250000000000^49 ≤ 1691457141153^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866691671 5000000000 1691457141153 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3719169821/5000000000 : ℝ)^65 ≤ (16882975670543/25000000000000 : ℝ)^49 := by
    have hnat : (3719169821 : ℕ)^65*25000000000000^49 ≤ 16882975670543^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3719169821 5000000000 16882975670543 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108433823/10000000000 : ℝ)^65 ≤ (540478304663/10000000000000 : ℝ)^49 := by
    have hnat : (1108433823 : ℕ)^65*10000000000000^49 ≤ 540478304663^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108433823 10000000000 540478304663 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1866691671/5000000000 : ℝ), (3719169821/5000000000 : ℝ), (-1108433823/10000000000 : ℝ)] ![(1691457141153/6250000000000 : ℝ), (16882975670543/25000000000000 : ℝ), (540478304663/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1866691671/5000000000 : ℝ)|^65 ≤ (1691457141153/6250000000000 : ℝ)^49
        have hw : |(1866691671/5000000000 : ℝ)|=(1866691671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3719169821/5000000000 : ℝ)|^65 ≤ (16882975670543/25000000000000 : ℝ)^49
        have hw : |(3719169821/5000000000 : ℝ)|=(3719169821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1108433823/10000000000 : ℝ)|^65 ≤ (540478304663/10000000000000 : ℝ)^49
        have hw : |(-1108433823/10000000000 : ℝ)|=(1108433823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301053_s6_s6_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8760508721/10000000000 : ℝ)*x 0 + (1560369889/10000000000 : ℝ)*x 1 + (1432119181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8760508721/10000000000 : ℝ)^65 ≤ (41950138244257/50000000000000 : ℝ)^49 := by
    have hnat : (8760508721 : ℕ)^65*50000000000000^49 ≤ 41950138244257^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8760508721 10000000000 41950138244257 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560369889/10000000000 : ℝ)^65 ≤ (4253649163303/50000000000000 : ℝ)^49 := by
    have hnat : (1560369889 : ℕ)^65*50000000000000^49 ≤ 4253649163303^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560369889 10000000000 4253649163303 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1432119181/10000000000 : ℝ)^65 ≤ (949053146393/12500000000000 : ℝ)^49 := by
    have hnat : (1432119181 : ℕ)^65*12500000000000^49 ≤ 949053146393^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1432119181 10000000000 949053146393 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8760508721/10000000000 : ℝ), (1560369889/10000000000 : ℝ), (1432119181/10000000000 : ℝ)] ![(41950138244257/50000000000000 : ℝ), (4253649163303/50000000000000 : ℝ), (949053146393/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8760508721/10000000000 : ℝ)|^65 ≤ (41950138244257/50000000000000 : ℝ)^49
        have hw : |(8760508721/10000000000 : ℝ)|=(8760508721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560369889/10000000000 : ℝ)|^65 ≤ (4253649163303/50000000000000 : ℝ)^49
        have hw : |(1560369889/10000000000 : ℝ)|=(1560369889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1432119181/10000000000 : ℝ)|^65 ≤ (949053146393/12500000000000 : ℝ)^49
        have hw : |(1432119181/10000000000 : ℝ)|=(1432119181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301053_s6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((51/80 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(51/80 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36449/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36449/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72187/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72187/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((49051/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(49051/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28519/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28519/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55833/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(55833/100000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (51/80 : ℝ) ^ (129/32 : ℝ) ≤ (81429312231607519/500000000000000000 : ℝ) := by
    have hpowers : (51/80 : ℝ)^129 ≤ (81429312231607519/500000000000000000 : ℝ)^32 := by
      have hnat : (51 : ℕ)^129*500000000000000000^32 ≤ 81429312231607519^32*80^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51 80 81429312231607519 500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (51/80 : ℝ)) (X := (81429312231607519/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner0a : (581429312231607519/500000000000000000 : ℝ) ≤ (5190685830595163/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (581429312231607519/500000000000000000 : ℝ)^32 ≤ (5190685830595163/5000000000000000 : ℝ)^129 := by
      have hnat : (581429312231607519 : ℕ)^32*5000000000000000^129 ≤ 5190685830595163^129*500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        581429312231607519 500000000000000000 5190685830595163 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5190685830595163/5000000000000000 : ℝ)) (X := (581429312231607519/500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner0b : (331429312231607519/250000000000000000 : ℝ) ≤ (10724459630640387/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (331429312231607519/250000000000000000 : ℝ)^32 ≤ (10724459630640387/10000000000000000 : ℝ)^129 := by
      have hnat : (331429312231607519 : ℕ)^32*10000000000000000^129 ≤ 10724459630640387^129*250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        331429312231607519 250000000000000000 10724459630640387 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10724459630640387/10000000000000000 : ℝ)) (X := (331429312231607519/250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(63561943531721/1062500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(343087969450061/6375000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (51/80 : ℝ)) (alpha := (63561943531721/1062500000000000 : ℝ)) (beta := (343087969450061/6375000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (51/80 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(63561943531721/1062500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(343087969450061/6375000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (36449/50000 : ℝ) ^ (129/32 : ℝ) ≤ (27962263010709281641/100000000000000000000 : ℝ) := by
    have hpowers : (36449/50000 : ℝ)^129 ≤ (27962263010709281641/100000000000000000000 : ℝ)^32 := by
      have hnat : (36449 : ℕ)^129*100000000000000000000^32 ≤ 27962263010709281641^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36449 50000 27962263010709281641 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36449/50000 : ℝ)) (X := (27962263010709281641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner1a : (127962263010709281641/100000000000000000000 : ℝ) ≤ (531536337046309/500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (127962263010709281641/100000000000000000000 : ℝ)^32 ≤ (531536337046309/500000000000000 : ℝ)^129 := by
      have hnat : (127962263010709281641 : ℕ)^32*500000000000000^129 ≤ 531536337046309^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127962263010709281641 100000000000000000000 531536337046309 500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (531536337046309/500000000000000 : ℝ)) (X := (127962263010709281641/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner1b : (77962263010709281641/50000000000000000000 : ℝ) ≤ (2232979513371947/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (77962263010709281641/50000000000000000000 : ℝ)^32 ≤ (2232979513371947/2000000000000000 : ℝ)^129 := by
      have hnat : (77962263010709281641 : ℕ)^32*2000000000000000^129 ≤ 2232979513371947^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77962263010709281641 50000000000000000000 2232979513371947 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2232979513371947/2000000000000000 : ℝ)) (X := (77962263010709281641/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(769178952349/8890000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(106834165186711/1457960000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (36449/50000 : ℝ)) (alpha := (769178952349/8890000000000 : ℝ)) (beta := (106834165186711/1457960000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (36449/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(769178952349/8890000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(106834165186711/1457960000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (72187/100000 : ℝ) ^ (129/32 : ℝ) ≤ (209992047325816983/781250000000000000 : ℝ) := by
    have hpowers : (72187/100000 : ℝ)^129 ≤ (209992047325816983/781250000000000000 : ℝ)^32 := by
      have hnat : (72187 : ℕ)^129*781250000000000000^32 ≤ 209992047325816983^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72187 100000 209992047325816983 781250000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72187/100000 : ℝ)) (X := (209992047325816983/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner2a : (991242047325816983/781250000000000000 : ℝ) ≤ (5304165398969017/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (991242047325816983/781250000000000000 : ℝ)^32 ≤ (5304165398969017/5000000000000000 : ℝ)^129 := by
      have hnat : (991242047325816983 : ℕ)^32*5000000000000000^129 ≤ 5304165398969017^129*781250000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        991242047325816983 781250000000000000 5304165398969017 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5304165398969017/5000000000000000 : ℝ)) (X := (991242047325816983/781250000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s6_corner2b : (600617047325816983/390625000000000000 : ℝ) ≤ (11126211636161377/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (600617047325816983/390625000000000000 : ℝ)^32 ≤ (11126211636161377/10000000000000000 : ℝ)^129 := by
      have hnat : (600617047325816983 : ℕ)^32*10000000000000000^129 ≤ 11126211636161377^129*390625000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        600617047325816983 390625000000000000 11126211636161377 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11126211636161377/10000000000000000 : ℝ)) (X := (600617047325816983/390625000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(304165398969017/3609350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(517880838223343/7218700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (72187/100000 : ℝ)) (alpha := (304165398969017/3609350000000000 : ℝ)) (beta := (517880838223343/7218700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (72187/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(304165398969017/3609350000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(517880838223343/7218700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-2171162899/10000000000 : ℝ)*X 0 0+(5295336213/10000000000 : ℝ)*X 0 1+(1341452947/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((1150793543/2500000000 : ℝ)*X 1 0+(-1676998601/10000000000 : ℝ)*X 1 1+(6364005889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((4619862327/10000000000 : ℝ)*X 2 0+(6365723391/10000000000 : ℝ)*X 2 1+(-330211657/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((1371437269/2000000000 : ℝ)*X 0 0+(744959591/2500000000 : ℝ)*X 0 1+(361803979/1250000000 : ℝ)*X 0 2+(1371437269/2000000000 : ℝ)*X 1 0+(744959591/2500000000 : ℝ)*X 1 1+(361803979/1250000000 : ℝ)*X 1 2+(1371437269/2000000000 : ℝ)*X 2 0+(744959591/2500000000 : ℝ)*X 2 1+(361803979/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-2012578129/10000000000 : ℝ)*X 0 0+(4234635949/10000000000 : ℝ)*X 0 1+(3233483357/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((3904651423/10000000000 : ℝ)*X 1 0+(-107990241/1250000000 : ℝ)*X 1 1+(7426907713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((1960824163/5000000000 : ℝ)*X 2 0+(7500979027/10000000000 : ℝ)*X 2 1+(-679547383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((6468039183/10000000000 : ℝ)*X 0 0+(2454428181/5000000000 : ℝ)*X 0 1+(1043040991/10000000000 : ℝ)*X 0 2+(6468039183/10000000000 : ℝ)*X 1 0+(2454428181/5000000000 : ℝ)*X 1 1+(1043040991/10000000000 : ℝ)*X 1 2+(6468039183/10000000000 : ℝ)*X 2 0+(2454428181/5000000000 : ℝ)*X 2 1+(1043040991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-1164868351/10000000000 : ℝ)*X 0 0+(2426631/5000000 : ℝ)*X 0 1+(806294401/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((3759686603/10000000000 : ℝ)*X 1 0+(-224288309/2000000000 : ℝ)*X 1 1+(3705148519/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((2875814503/5000000000 : ℝ)*X 2 0+(5846969887/10000000000 : ℝ)*X 2 1+(-696159521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((2168927081/2500000000 : ℝ)*X 0 0+(80800663/400000000 : ℝ)*X 0 1+(1075573867/10000000000 : ℝ)*X 0 2+(2168927081/2500000000 : ℝ)*X 1 0+(80800663/400000000 : ℝ)*X 1 1+(1075573867/10000000000 : ℝ)*X 1 2+(2168927081/2500000000 : ℝ)*X 2 0+(80800663/400000000 : ℝ)*X 2 1+(1075573867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-1136715931/10000000000 : ℝ)*X 0 0+(6214410049/10000000000 : ℝ)*X 0 1+(640718149/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((1125544/1953125 : ℝ)*X 1 0+(-328261593/5000000000 : ℝ)*X 1 1+(365966573/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((1866691671/5000000000 : ℝ)*X 2 0+(3719169821/5000000000 : ℝ)*X 2 1+(-1108433823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((8760508721/10000000000 : ℝ)*X 0 0+(1560369889/10000000000 : ℝ)*X 0 1+(1432119181/10000000000 : ℝ)*X 0 2+(8760508721/10000000000 : ℝ)*X 1 0+(1560369889/10000000000 : ℝ)*X 1 1+(1432119181/10000000000 : ℝ)*X 1 2+(8760508721/10000000000 : ℝ)*X 2 0+(1560369889/10000000000 : ℝ)*X 2 1+(1432119181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301053_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((49051/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(49051/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40037897206903954515101493/2420441406250000000000000000000 : ℝ) := by norm_num
    linear_combination (1260537/500000000000 : ℝ)*(base5) + (5739417/1000000000000 : ℝ)*(base49) + (67423602109/500000000000 : ℝ)*(base59) + (117863798469/31250000000 : ℝ)*(major_s6_0) + (117863798469/31250000000 : ℝ)*(major_s6_1) + (117863798469/31250000000 : ℝ)*(major_s6_2) + (67739697/1000000000000 : ℝ)*(sp_s6_0) + (144021/5000000000 : ℝ)*(sp_s6_6) + (4993494081569/1000000000000 : ℝ)*(sp_s6_7) + (2496644297183/500000000000 : ℝ)*(sp_s6_8) + (156040366309/31250000000 : ℝ)*(sp_s6_9) + (637421110403/250000000000 : ℝ)*(sp_s6_13) + (2732269/10000000000 : ℝ)*(sp_s6_15) + (68155113/250000000000 : ℝ)*(sp_s6_23) + (509943153377/200000000000 : ℝ)*(f.failure) + (2496780910633/500000000000 : ℝ)*(f.sum) + (139416150800931607/401089018750000000000000000000 : ℝ)*base62 + (233110487845109/1804675000000000000000000000 : ℝ)*base65 + (144825219614711/182245000000000000000000000 : ℝ)*base67 + (154626713436773/1804675000000000000000000000 : ℝ)*base69 + (2862745166273890923/9587335937500000000000000000000 : ℝ)*base70 + (102465747743187/265625000000000000000000000 : ℝ)*base73 + (41366773967/444500000000000000000000 : ℝ)*base75 + (9078319616399/33203125000000000000000000 : ℝ)*base77 + (673355861202890897/2420441406250000000000000000000 : ℝ)*base79 + (5163/5000000000000000 : ℝ)*base86 + (5163/5000000000000000 : ℝ)*base88 + (5163/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28519/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28519/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3144207864854826609862936195979/279559046068750000000000000000000000 : ℝ) := by norm_num
    linear_combination (495451/500000000000 : ℝ)*(base39) + (1238091/250000000000 : ℝ)*(base59) + (3824428326953/1000000000000 : ℝ)*(major_s6_0) + (3824428326953/1000000000000 : ℝ)*(major_s6_1) + (3824428326953/1000000000000 : ℝ)*(major_s6_2) + (17376787/1000000000000 : ℝ)*(sp_s6_0) + (252341/250000000000 : ℝ)*(sp_s6_1) + (3792379/100000000000 : ℝ)*(sp_s6_2) + (12284359/200000000000 : ℝ)*(sp_s6_7) + (1265843318539/250000000000 : ℝ)*(sp_s6_14) + (2531725531687/500000000000 : ℝ)*(sp_s6_15) + (5063414148947/1000000000000 : ℝ)*(sp_s6_16) + (2585286057137/1000000000000 : ℝ)*(sp_s6_20) + (22955003/200000000000 : ℝ)*(sp_s6_27) + (2585400832153/1000000000000 : ℝ)*(f.failure) + (2531726036369/500000000000 : ℝ)*(f.sum) + (1507595571546321399/3208712150000000000000000000000 : ℝ)*base63 + (1467606084659601/7218700000000000000000000000 : ℝ)*base65 + (616036937253071/1457960000000000000000000000 : ℝ)*base66 + (69292470179423/1804675000000000000000000000 : ℝ)*base69 + (11886198057653069939/19174671875000000000000000000000 : ℝ)*base71 + (4222938628730867/6375000000000000000000000000 : ℝ)*base72 + (2248923000731/4445000000000000000000000 : ℝ)*base75 + (225579740944863/1062500000000000000000000000 : ℝ)*base77 + (5483299970428028051/29045296875000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (25093/25000000000000000 : ℝ)*base87 + (25093/25000000000000000 : ℝ)*base89 + (25093/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55833/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(55833/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4559645871764750025334089022311/1397795230343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (2894449/1000000000000 : ℝ)*(base15) + (112502696449/1000000000000 : ℝ)*(base40) + (3690884044179/1000000000000 : ℝ)*(major_s6_0) + (3690884044179/1000000000000 : ℝ)*(major_s6_1) + (3690884044179/1000000000000 : ℝ)*(major_s6_2) + (19170081/1000000000000 : ℝ)*(sp_s6_0) + (22189313/1000000000000 : ℝ)*(sp_s6_1) + (1409983/250000000000 : ℝ)*(sp_s6_2) + (4934483/200000000000 : ℝ)*(sp_s6_9) + (2639373/40000000000 : ℝ)*(sp_s6_20) + (4886625981751/1000000000000 : ℝ)*(sp_s6_21) + (488662006807/100000000000 : ℝ)*(sp_s6_22) + (977322967897/200000000000 : ℝ)*(sp_s6_23) + (1247527932427/500000000000 : ℝ)*(sp_s6_27) + (2495121849179/1000000000000 : ℝ)*(f.failure) + (610830643979/125000000000 : ℝ)*(f.sum) + (155054479754744849/1604356075000000000000000000000 : ℝ)*base62 + (4230296639569107/7218700000000000000000000000 : ℝ)*base64 + (823756856483993/1457960000000000000000000000 : ℝ)*base66 + (2752975416447407/3609350000000000000000000000 : ℝ)*base68 + (2672076722119159977/19174671875000000000000000000000 : ℝ)*base71 + (1431385070860027/2125000000000000000000000000 : ℝ)*base72 + (5977804585191/8890000000000000000000000 : ℝ)*base74 + (528292692822941/1062500000000000000000000000 : ℝ)*base76 + (524152153678939203/4840882812500000000000000000000 : ℝ)*base78 + (13599/25000000000000000 : ℝ)*base87 + (13599/25000000000000000 : ℝ)*base89 + (13599/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((51/80 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(51/80 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36449/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36449/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72187/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72187/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((49051/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(49051/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28519/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28519/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55833/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(55833/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301053_s6 p hpa hpb X hX hprev5

#print axioms solution
