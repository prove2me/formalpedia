-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301039_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:25:17.041621+00:00
-- url     : https://prove2.me/submissions/bbb555e9-6f81-49ed-bd49-ec95236ac1bf

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
theorem collision_support_c301039_s1_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-338064849/2000000000 : ℝ)*x 0 + (-6138564421/10000000000 : ℝ)*x 1 + (4840731373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338064849/2000000000 : ℝ)^65 ≤ (9459726908183/100000000000000 : ℝ)^49 := by
    have hnat : (338064849 : ℕ)^65*100000000000000^49 ≤ 9459726908183^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338064849 2000000000 9459726908183 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6138564421/10000000000 : ℝ)^65 ≤ (26171833607423/50000000000000 : ℝ)^49 := by
    have hnat : (6138564421 : ℕ)^65*50000000000000^49 ≤ 26171833607423^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6138564421 10000000000 26171833607423 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4840731373/10000000000 : ℝ)^65 ≤ (381966058603/1000000000000 : ℝ)^49 := by
    have hnat : (4840731373 : ℕ)^65*1000000000000^49 ≤ 381966058603^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4840731373 10000000000 381966058603 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-338064849/2000000000 : ℝ), (-6138564421/10000000000 : ℝ), (4840731373/10000000000 : ℝ)] ![(9459726908183/100000000000000 : ℝ), (26171833607423/50000000000000 : ℝ), (381966058603/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-338064849/2000000000 : ℝ)|^65 ≤ (9459726908183/100000000000000 : ℝ)^49
        have hw : |(-338064849/2000000000 : ℝ)|=(338064849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6138564421/10000000000 : ℝ)|^65 ≤ (26171833607423/50000000000000 : ℝ)^49
        have hw : |(-6138564421/10000000000 : ℝ)|=(6138564421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4840731373/10000000000 : ℝ)|^65 ≤ (381966058603/1000000000000 : ℝ)^49
        have hw : |(4840731373/10000000000 : ℝ)|=(4840731373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4818240643/10000000000 : ℝ)*x 0 + (4128632003/10000000000 : ℝ)*x 1 + (829389987/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4818240643/10000000000 : ℝ)^65 ≤ (37961369357873/100000000000000 : ℝ)^49 := by
    have hnat : (4818240643 : ℕ)^65*100000000000000^49 ≤ 37961369357873^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4818240643 10000000000 37961369357873 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128632003/10000000000 : ℝ)^65 ≤ (30928234508047/100000000000000 : ℝ)^49 := by
    have hnat : (4128632003 : ℕ)^65*100000000000000^49 ≤ 30928234508047^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128632003 10000000000 30928234508047 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (829389987/2000000000 : ℝ)^65 ≤ (31110396111427/100000000000000 : ℝ)^49 := by
    have hnat : (829389987 : ℕ)^65*100000000000000^49 ≤ 31110396111427^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829389987 2000000000 31110396111427 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4818240643/10000000000 : ℝ), (4128632003/10000000000 : ℝ), (829389987/2000000000 : ℝ)] ![(37961369357873/100000000000000 : ℝ), (30928234508047/100000000000000 : ℝ), (31110396111427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4818240643/10000000000 : ℝ)|^65 ≤ (37961369357873/100000000000000 : ℝ)^49
        have hw : |(4818240643/10000000000 : ℝ)|=(4818240643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128632003/10000000000 : ℝ)|^65 ≤ (30928234508047/100000000000000 : ℝ)^49
        have hw : |(4128632003/10000000000 : ℝ)|=(4128632003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(829389987/2000000000 : ℝ)|^65 ≤ (31110396111427/100000000000000 : ℝ)^49
        have hw : |(829389987/2000000000 : ℝ)|=(829389987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1498469549/10000000000 : ℝ)*x 0 + (-6667092339/10000000000 : ℝ)*x 1 + (4388123083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1498469549/10000000000 : ℝ)^65 ≤ (4031268615579/50000000000000 : ℝ)^49 := by
    have hnat : (1498469549 : ℕ)^65*50000000000000^49 ≤ 4031268615579^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498469549 10000000000 4031268615579 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6667092339/10000000000 : ℝ)^65 ≤ (58404503716189/100000000000000 : ℝ)^49 := by
    have hnat : (6667092339 : ℕ)^65*100000000000000^49 ≤ 58404503716189^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6667092339 10000000000 58404503716189 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4388123083/10000000000 : ℝ)^65 ≤ (33532959037227/100000000000000 : ℝ)^49 := by
    have hnat : (4388123083 : ℕ)^65*100000000000000^49 ≤ 33532959037227^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388123083 10000000000 33532959037227 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1498469549/10000000000 : ℝ), (-6667092339/10000000000 : ℝ), (4388123083/10000000000 : ℝ)] ![(4031268615579/50000000000000 : ℝ), (58404503716189/100000000000000 : ℝ), (33532959037227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1498469549/10000000000 : ℝ)|^65 ≤ (4031268615579/50000000000000 : ℝ)^49
        have hw : |(-1498469549/10000000000 : ℝ)|=(1498469549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6667092339/10000000000 : ℝ)|^65 ≤ (58404503716189/100000000000000 : ℝ)^49
        have hw : |(-6667092339/10000000000 : ℝ)|=(6667092339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4388123083/10000000000 : ℝ)|^65 ≤ (33532959037227/100000000000000 : ℝ)^49
        have hw : |(4388123083/10000000000 : ℝ)|=(4388123083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (295008129/625000000 : ℝ)*x 0 + (4158164251/10000000000 : ℝ)*x 1 + (4219909917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (295008129/625000000 : ℝ)^65 ≤ (36939410012429/100000000000000 : ℝ)^49 := by
    have hnat : (295008129 : ℕ)^65*100000000000000^49 ≤ 36939410012429^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295008129 625000000 36939410012429 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4158164251/10000000000 : ℝ)^65 ≤ (31222046027351/100000000000000 : ℝ)^49 := by
    have hnat : (4158164251 : ℕ)^65*100000000000000^49 ≤ 31222046027351^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158164251 10000000000 31222046027351 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4219909917/10000000000 : ℝ)^65 ≤ (6367708788261/20000000000000 : ℝ)^49 := by
    have hnat : (4219909917 : ℕ)^65*20000000000000^49 ≤ 6367708788261^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219909917 10000000000 6367708788261 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(295008129/625000000 : ℝ), (4158164251/10000000000 : ℝ), (4219909917/10000000000 : ℝ)] ![(36939410012429/100000000000000 : ℝ), (31222046027351/100000000000000 : ℝ), (6367708788261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(295008129/625000000 : ℝ)|^65 ≤ (36939410012429/100000000000000 : ℝ)^49
        have hw : |(295008129/625000000 : ℝ)|=(295008129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4158164251/10000000000 : ℝ)|^65 ≤ (31222046027351/100000000000000 : ℝ)^49
        have hw : |(4158164251/10000000000 : ℝ)|=(4158164251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4219909917/10000000000 : ℝ)|^65 ≤ (6367708788261/20000000000000 : ℝ)^49
        have hw : |(4219909917/10000000000 : ℝ)|=(4219909917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4533174807/10000000000 : ℝ)*x 0 + (-4227008939/10000000000 : ℝ)*x 1 + (-4343281339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4533174807/10000000000 : ℝ)^65 ≤ (8752807198963/25000000000000 : ℝ)^49 := by
    have hnat : (4533174807 : ℕ)^65*25000000000000^49 ≤ 8752807198963^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533174807 10000000000 8752807198963 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227008939/10000000000 : ℝ)^65 ≤ (15954806866041/50000000000000 : ℝ)^49 := by
    have hnat : (4227008939 : ℕ)^65*50000000000000^49 ≤ 15954806866041^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227008939 10000000000 15954806866041 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4343281339/10000000000 : ℝ)^65 ≤ (33079157461543/100000000000000 : ℝ)^49 := by
    have hnat : (4343281339 : ℕ)^65*100000000000000^49 ≤ 33079157461543^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343281339 10000000000 33079157461543 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4533174807/10000000000 : ℝ), (-4227008939/10000000000 : ℝ), (-4343281339/10000000000 : ℝ)] ![(8752807198963/25000000000000 : ℝ), (15954806866041/50000000000000 : ℝ), (33079157461543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4533174807/10000000000 : ℝ)|^65 ≤ (8752807198963/25000000000000 : ℝ)^49
        have hw : |(4533174807/10000000000 : ℝ)|=(4533174807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4227008939/10000000000 : ℝ)|^65 ≤ (15954806866041/50000000000000 : ℝ)^49
        have hw : |(-4227008939/10000000000 : ℝ)|=(4227008939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4343281339/10000000000 : ℝ)|^65 ≤ (33079157461543/100000000000000 : ℝ)^49
        have hw : |(-4343281339/10000000000 : ℝ)|=(4343281339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (374433099/500000000 : ℝ)*x 0 + (-4496067/2500000000 : ℝ)*x 1 + (4219909917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (374433099/500000000 : ℝ)^65 ≤ (17034656180143/25000000000000 : ℝ)^49 := by
    have hnat : (374433099 : ℕ)^65*25000000000000^49 ≤ 17034656180143^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374433099 500000000 17034656180143 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496067/2500000000 : ℝ)^65 ≤ (22831330451/100000000000000 : ℝ)^49 := by
    have hnat : (4496067 : ℕ)^65*100000000000000^49 ≤ 22831330451^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496067 2500000000 22831330451 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4219909917/10000000000 : ℝ)^65 ≤ (6367708788261/20000000000000 : ℝ)^49 := by
    have hnat : (4219909917 : ℕ)^65*20000000000000^49 ≤ 6367708788261^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219909917 10000000000 6367708788261 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(374433099/500000000 : ℝ), (-4496067/2500000000 : ℝ), (4219909917/10000000000 : ℝ)] ![(17034656180143/25000000000000 : ℝ), (22831330451/100000000000000 : ℝ), (6367708788261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(374433099/500000000 : ℝ)|^65 ≤ (17034656180143/25000000000000 : ℝ)^49
        have hw : |(374433099/500000000 : ℝ)|=(374433099/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4496067/2500000000 : ℝ)|^65 ≤ (22831330451/100000000000000 : ℝ)^49
        have hw : |(-4496067/2500000000 : ℝ)|=(4496067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4219909917/10000000000 : ℝ)|^65 ≤ (6367708788261/20000000000000 : ℝ)^49
        have hw : |(4219909917/10000000000 : ℝ)|=(4219909917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-394128119/5000000000 : ℝ)*x 0 + (-5893526741/10000000000 : ℝ)*x 1 + (5657321703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (394128119/5000000000 : ℝ)^65 ≤ (1719355002509/50000000000000 : ℝ)^49 := by
    have hnat : (394128119 : ℕ)^65*50000000000000^49 ≤ 1719355002509^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394128119 5000000000 1719355002509 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5893526741/10000000000 : ℝ)^65 ≤ (49590187569201/100000000000000 : ℝ)^49 := by
    have hnat : (5893526741 : ℕ)^65*100000000000000^49 ≤ 49590187569201^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5893526741 10000000000 49590187569201 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5657321703/10000000000 : ℝ)^65 ≤ (46971102421443/100000000000000 : ℝ)^49 := by
    have hnat : (5657321703 : ℕ)^65*100000000000000^49 ≤ 46971102421443^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5657321703 10000000000 46971102421443 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-394128119/5000000000 : ℝ), (-5893526741/10000000000 : ℝ), (5657321703/10000000000 : ℝ)] ![(1719355002509/50000000000000 : ℝ), (49590187569201/100000000000000 : ℝ), (46971102421443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-394128119/5000000000 : ℝ)|^65 ≤ (1719355002509/50000000000000 : ℝ)^49
        have hw : |(-394128119/5000000000 : ℝ)|=(394128119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5893526741/10000000000 : ℝ)|^65 ≤ (49590187569201/100000000000000 : ℝ)^49
        have hw : |(-5893526741/10000000000 : ℝ)|=(5893526741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5657321703/10000000000 : ℝ)|^65 ≤ (46971102421443/100000000000000 : ℝ)^49
        have hw : |(5657321703/10000000000 : ℝ)|=(5657321703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1080689837/2500000000 : ℝ)*x 0 + (4305787133/10000000000 : ℝ)*x 1 + (4476045423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080689837/2500000000 : ℝ)^65 ≤ (3287198227707/10000000000000 : ℝ)^49 := by
    have hnat : (1080689837 : ℕ)^65*10000000000000^49 ≤ 3287198227707^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080689837 2500000000 3287198227707 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4305787133/10000000000 : ℝ)^65 ≤ (16350442733971/50000000000000 : ℝ)^49 := by
    have hnat : (4305787133 : ℕ)^65*50000000000000^49 ≤ 16350442733971^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305787133 10000000000 16350442733971 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476045423/10000000000 : ℝ)^65 ≤ (6885426445739/20000000000000 : ℝ)^49 := by
    have hnat : (4476045423 : ℕ)^65*20000000000000^49 ≤ 6885426445739^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476045423 10000000000 6885426445739 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080689837/2500000000 : ℝ), (4305787133/10000000000 : ℝ), (4476045423/10000000000 : ℝ)] ![(3287198227707/10000000000000 : ℝ), (16350442733971/50000000000000 : ℝ), (6885426445739/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080689837/2500000000 : ℝ)|^65 ≤ (3287198227707/10000000000000 : ℝ)^49
        have hw : |(1080689837/2500000000 : ℝ)|=(1080689837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4305787133/10000000000 : ℝ)|^65 ≤ (16350442733971/50000000000000 : ℝ)^49
        have hw : |(4305787133/10000000000 : ℝ)|=(4305787133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476045423/10000000000 : ℝ)|^65 ≤ (6885426445739/20000000000000 : ℝ)^49
        have hw : |(4476045423/10000000000 : ℝ)|=(4476045423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (276177077/500000000 : ℝ)*x 0 + (-3664812221/10000000000 : ℝ)*x 1 + (-959932909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276177077/500000000 : ℝ)^65 ≤ (45503393646681/100000000000000 : ℝ)^49 := by
    have hnat : (276177077 : ℕ)^65*100000000000000^49 ≤ 45503393646681^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276177077 500000000 45503393646681 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3664812221/10000000000 : ℝ)^65 ≤ (6601479503233/25000000000000 : ℝ)^49 := by
    have hnat : (3664812221 : ℕ)^65*25000000000000^49 ≤ 6601479503233^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3664812221 10000000000 6601479503233 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (959932909/2500000000 : ℝ)^65 ≤ (28090688330699/100000000000000 : ℝ)^49 := by
    have hnat : (959932909 : ℕ)^65*100000000000000^49 ≤ 28090688330699^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959932909 2500000000 28090688330699 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(276177077/500000000 : ℝ), (-3664812221/10000000000 : ℝ), (-959932909/2500000000 : ℝ)] ![(45503393646681/100000000000000 : ℝ), (6601479503233/25000000000000 : ℝ), (28090688330699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(276177077/500000000 : ℝ)|^65 ≤ (45503393646681/100000000000000 : ℝ)^49
        have hw : |(276177077/500000000 : ℝ)|=(276177077/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3664812221/10000000000 : ℝ)|^65 ≤ (6601479503233/25000000000000 : ℝ)^49
        have hw : |(-3664812221/10000000000 : ℝ)|=(3664812221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-959932909/2500000000 : ℝ)|^65 ≤ (28090688330699/100000000000000 : ℝ)^49
        have hw : |(-959932909/2500000000 : ℝ)|=(959932909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2189308189/2500000000 : ℝ)*x 0 + (-316525001/5000000000 : ℝ)*x 1 + (1109382523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189308189/2500000000 : ℝ)^65 ≤ (41929330064929/50000000000000 : ℝ)^49 := by
    have hnat : (2189308189 : ℕ)^65*50000000000000^49 ≤ 41929330064929^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189308189 2500000000 41929330064929 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316525001/5000000000 : ℝ)^65 ≤ (2570815061097/100000000000000 : ℝ)^49 := by
    have hnat : (316525001 : ℕ)^65*100000000000000^49 ≤ 2570815061097^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316525001 5000000000 2570815061097 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1109382523/5000000000 : ℝ)^65 ≤ (13570524797703/100000000000000 : ℝ)^49 := by
    have hnat : (1109382523 : ℕ)^65*100000000000000^49 ≤ 13570524797703^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109382523 5000000000 13570524797703 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189308189/2500000000 : ℝ), (-316525001/5000000000 : ℝ), (1109382523/5000000000 : ℝ)] ![(41929330064929/50000000000000 : ℝ), (2570815061097/100000000000000 : ℝ), (13570524797703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189308189/2500000000 : ℝ)|^65 ≤ (41929330064929/50000000000000 : ℝ)^49
        have hw : |(2189308189/2500000000 : ℝ)|=(2189308189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-316525001/5000000000 : ℝ)|^65 ≤ (2570815061097/100000000000000 : ℝ)^49
        have hw : |(-316525001/5000000000 : ℝ)|=(316525001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1109382523/5000000000 : ℝ)|^65 ≤ (13570524797703/100000000000000 : ℝ)^49
        have hw : |(1109382523/5000000000 : ℝ)|=(1109382523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076670237/10000000000 : ℝ)*x 0 + (-3323625429/5000000000 : ℝ)*x 1 + (2344937787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076670237/10000000000 : ℝ)^65 ≤ (2600148104353/50000000000000 : ℝ)^49 := by
    have hnat : (1076670237 : ℕ)^65*50000000000000^49 ≤ 2600148104353^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076670237 10000000000 2600148104353 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3323625429/5000000000 : ℝ)^65 ≤ (58174046654077/100000000000000 : ℝ)^49 := by
    have hnat : (3323625429 : ℕ)^65*100000000000000^49 ≤ 58174046654077^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3323625429 5000000000 58174046654077 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2344937787/5000000000 : ℝ)^65 ≤ (18312828563591/50000000000000 : ℝ)^49 := by
    have hnat : (2344937787 : ℕ)^65*50000000000000^49 ≤ 18312828563591^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2344937787 5000000000 18312828563591 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076670237/10000000000 : ℝ), (-3323625429/5000000000 : ℝ), (2344937787/5000000000 : ℝ)] ![(2600148104353/50000000000000 : ℝ), (58174046654077/100000000000000 : ℝ), (18312828563591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076670237/10000000000 : ℝ)|^65 ≤ (2600148104353/50000000000000 : ℝ)^49
        have hw : |(-1076670237/10000000000 : ℝ)|=(1076670237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3323625429/5000000000 : ℝ)|^65 ≤ (58174046654077/100000000000000 : ℝ)^49
        have hw : |(-3323625429/5000000000 : ℝ)|=(3323625429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2344937787/5000000000 : ℝ)|^65 ≤ (18312828563591/50000000000000 : ℝ)^49
        have hw : |(2344937787/5000000000 : ℝ)|=(2344937787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (342054759/625000000 : ℝ)*x 0 + (1934177823/5000000000 : ℝ)*x 1 + (3693518133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342054759/625000000 : ℝ)^65 ≤ (22475274785543/50000000000000 : ℝ)^49 := by
    have hnat : (342054759 : ℕ)^65*50000000000000^49 ≤ 22475274785543^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342054759 625000000 22475274785543 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1934177823/5000000000 : ℝ)^65 ≤ (1418440557883/5000000000000 : ℝ)^49 := by
    have hnat : (1934177823 : ℕ)^65*5000000000000^49 ≤ 1418440557883^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934177823 5000000000 1418440557883 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3693518133/10000000000 : ℝ)^65 ≤ (13340319624549/50000000000000 : ℝ)^49 := by
    have hnat : (3693518133 : ℕ)^65*50000000000000^49 ≤ 13340319624549^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3693518133 10000000000 13340319624549 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(342054759/625000000 : ℝ), (1934177823/5000000000 : ℝ), (3693518133/10000000000 : ℝ)] ![(22475274785543/50000000000000 : ℝ), (1418440557883/5000000000000 : ℝ), (13340319624549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(342054759/625000000 : ℝ)|^65 ≤ (22475274785543/50000000000000 : ℝ)^49
        have hw : |(342054759/625000000 : ℝ)|=(342054759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1934177823/5000000000 : ℝ)|^65 ≤ (1418440557883/5000000000000 : ℝ)^49
        have hw : |(1934177823/5000000000 : ℝ)|=(1934177823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3693518133/10000000000 : ℝ)|^65 ≤ (13340319624549/50000000000000 : ℝ)^49
        have hw : |(3693518133/10000000000 : ℝ)|=(3693518133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (431764047/1000000000 : ℝ)*x 0 + (-1140390779/2500000000 : ℝ)*x 1 + (-4223779013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431764047/1000000000 : ℝ)^65 ≤ (16410177875837/50000000000000 : ℝ)^49 := by
    have hnat : (431764047 : ℕ)^65*50000000000000^49 ≤ 16410177875837^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431764047 1000000000 16410177875837 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140390779/2500000000 : ℝ)^65 ≤ (35302370802939/100000000000000 : ℝ)^49 := by
    have hnat : (1140390779 : ℕ)^65*100000000000000^49 ≤ 35302370802939^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140390779 2500000000 35302370802939 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223779013/10000000000 : ℝ)^65 ≤ (7969318358149/25000000000000 : ℝ)^49 := by
    have hnat : (4223779013 : ℕ)^65*25000000000000^49 ≤ 7969318358149^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223779013 10000000000 7969318358149 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431764047/1000000000 : ℝ), (-1140390779/2500000000 : ℝ), (-4223779013/10000000000 : ℝ)] ![(16410177875837/50000000000000 : ℝ), (35302370802939/100000000000000 : ℝ), (7969318358149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431764047/1000000000 : ℝ)|^65 ≤ (16410177875837/50000000000000 : ℝ)^49
        have hw : |(431764047/1000000000 : ℝ)|=(431764047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1140390779/2500000000 : ℝ)|^65 ≤ (35302370802939/100000000000000 : ℝ)^49
        have hw : |(-1140390779/2500000000 : ℝ)|=(1140390779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4223779013/10000000000 : ℝ)|^65 ≤ (7969318358149/25000000000000 : ℝ)^49
        have hw : |(-4223779013/10000000000 : ℝ)|=(4223779013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301039_s1_s1_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (830163187/1000000000 : ℝ)*x 0 + (-56463701/10000000000 : ℝ)*x 1 + (3168982709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (830163187/1000000000 : ℝ)^65 ≤ (19530253407469/25000000000000 : ℝ)^49 := by
    have hnat : (830163187 : ℕ)^65*25000000000000^49 ≤ 19530253407469^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830163187 1000000000 19530253407469 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56463701/10000000000 : ℝ)^65 ≤ (4165941807/4000000000000 : ℝ)^49 := by
    have hnat : (56463701 : ℕ)^65*4000000000000^49 ≤ 4165941807^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56463701 10000000000 4165941807 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3168982709/10000000000 : ℝ)^65 ≤ (544370945427/2500000000000 : ℝ)^49 := by
    have hnat : (3168982709 : ℕ)^65*2500000000000^49 ≤ 544370945427^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168982709 10000000000 544370945427 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(830163187/1000000000 : ℝ), (-56463701/10000000000 : ℝ), (3168982709/10000000000 : ℝ)] ![(19530253407469/25000000000000 : ℝ), (4165941807/4000000000000 : ℝ), (544370945427/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(830163187/1000000000 : ℝ)|^65 ≤ (19530253407469/25000000000000 : ℝ)^49
        have hw : |(830163187/1000000000 : ℝ)|=(830163187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56463701/10000000000 : ℝ)|^65 ≤ (4165941807/4000000000000 : ℝ)^49
        have hw : |(-56463701/10000000000 : ℝ)|=(56463701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3168982709/10000000000 : ℝ)|^65 ≤ (544370945427/2500000000000 : ℝ)^49
        have hw : |(3168982709/10000000000 : ℝ)|=(3168982709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301039_s1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((71767/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71767/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-689/800 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-689/800 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4711/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4711/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1147/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1147/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3193/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-3193/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23999/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23999/50000 : ℝ)*X 1 2) := by
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
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (71767/100000 : ℝ) ^ (129/32 : ℝ) ≤ (13127040439060269573/50000000000000000000 : ℝ) := by
    have hpowers : (71767/100000 : ℝ)^129 ≤ (13127040439060269573/50000000000000000000 : ℝ)^32 := by
      have hnat : (71767 : ℕ)^129*50000000000000000000^32 ≤ 13127040439060269573^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71767 100000 13127040439060269573 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71767/100000 : ℝ)) (X := (13127040439060269573/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (63127040439060269573/50000000000000000000 : ℝ) ≤ (2119069202711603/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (63127040439060269573/50000000000000000000 : ℝ)^32 ≤ (2119069202711603/2000000000000000 : ℝ)^129 := by
      have hnat : (63127040439060269573 : ℕ)^32*2000000000000000^129 ≤ 2119069202711603^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63127040439060269573 50000000000000000000 2119069202711603 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2119069202711603/2000000000000000 : ℝ)) (X := (63127040439060269573/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (38127040439060269573/25000000000000000000 : ℝ) ≤ (2775927128105333/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (38127040439060269573/25000000000000000000 : ℝ)^32 ≤ (2775927128105333/2500000000000000 : ℝ)^129 := by
      have hnat : (38127040439060269573 : ℕ)^32*2500000000000000^129 ≤ 2775927128105333^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38127040439060269573 25000000000000000000 2775927128105333 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2775927128105333/2500000000000000 : ℝ)) (X := (38127040439060269573/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(119069202711603/1435340000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(508362498863317/7176700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (71767/100000 : ℝ)) (alpha := (119069202711603/1435340000000000 : ℝ)) (beta := (508362498863317/7176700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (71767/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(119069202711603/1435340000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(508362498863317/7176700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (689/800 : ℝ) ^ (129/32 : ℝ) ≤ (10952662968504153301/20000000000000000000 : ℝ) := by
    have hpowers : (689/800 : ℝ)^129 ≤ (10952662968504153301/20000000000000000000 : ℝ)^32 := by
      have hnat : (689 : ℕ)^129*20000000000000000000^32 ≤ 10952662968504153301^32*800^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        689 800 10952662968504153301 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (689/800 : ℝ)) (X := (10952662968504153301/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (30952662968504153301/20000000000000000000 : ℝ) ≤ (5572106858256889/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (30952662968504153301/20000000000000000000 : ℝ)^32 ≤ (5572106858256889/5000000000000000 : ℝ)^129 := by
      have hnat : (30952662968504153301 : ℕ)^32*5000000000000000^129 ≤ 5572106858256889^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30952662968504153301 20000000000000000000 5572106858256889 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5572106858256889/5000000000000000 : ℝ)) (X := (30952662968504153301/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (20952662968504153301/10000000000000000000 : ℝ) ≤ (12013989558804177/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (20952662968504153301/10000000000000000000 : ℝ)^32 ≤ (12013989558804177/10000000000000000 : ℝ)^129 := by
      have hnat : (20952662968504153301 : ℕ)^32*10000000000000000^129 ≤ 12013989558804177^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20952662968504153301 10000000000000000000 12013989558804177 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12013989558804177/10000000000000000 : ℝ)) (X := (20952662968504153301/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(572106858256889/4306250000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(869775842290399/8612500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (689/800 : ℝ)) (alpha := (572106858256889/4306250000000000 : ℝ)) (beta := (869775842290399/8612500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (689/800 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(572106858256889/4306250000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(869775842290399/8612500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (4711/5000 : ℝ) ^ (129/32 : ℝ) ≤ (1229092015795350251/1562500000000000000 : ℝ) := by
    have hpowers : (4711/5000 : ℝ)^129 ≤ (1229092015795350251/1562500000000000000 : ℝ)^32 := by
      have hnat : (4711 : ℕ)^129*1562500000000000000^32 ≤ 1229092015795350251^32*5000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4711 5000 1229092015795350251 1562500000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4711/5000 : ℝ)) (X := (1229092015795350251/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (2791592015795350251/1562500000000000000 : ℝ) ≤ (5774169797405857/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2791592015795350251/1562500000000000000 : ℝ)^32 ≤ (5774169797405857/5000000000000000 : ℝ)^129 := by
      have hnat : (2791592015795350251 : ℕ)^32*5000000000000000^129 ≤ 5774169797405857^129*1562500000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2791592015795350251 1562500000000000000 5774169797405857 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5774169797405857/5000000000000000 : ℝ)) (X := (2791592015795350251/1562500000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2010342015795350251/781250000000000000 : ℝ) ≤ (3160563240969433/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2010342015795350251/781250000000000000 : ℝ)^32 ≤ (3160563240969433/2500000000000000 : ℝ)^129 := by
      have hnat : (2010342015795350251 : ℕ)^32*2500000000000000^129 ≤ 3160563240969433^129*781250000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2010342015795350251 781250000000000000 3160563240969433 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160563240969433/2500000000000000 : ℝ)) (X := (2010342015795350251/781250000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(774169797405857/4711000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(546956684533009/4711000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (4711/5000 : ℝ)) (alpha := (774169797405857/4711000000000000 : ℝ)) (beta := (546956684533009/4711000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (4711/5000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(774169797405857/4711000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(546956684533009/4711000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-338064849/2000000000 : ℝ)*X 0 0+(-6138564421/10000000000 : ℝ)*X 0 1+(4840731373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4818240643/10000000000 : ℝ)*X 1 0+(4128632003/10000000000 : ℝ)*X 1 1+(829389987/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1498469549/10000000000 : ℝ)*X 0 0+(-6667092339/10000000000 : ℝ)*X 0 1+(4388123083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((295008129/625000000 : ℝ)*X 1 0+(4158164251/10000000000 : ℝ)*X 1 1+(4219909917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4533174807/10000000000 : ℝ)*X 2 0+(-4227008939/10000000000 : ℝ)*X 2 1+(-4343281339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((374433099/500000000 : ℝ)*X 0 0+(-4496067/2500000000 : ℝ)*X 0 1+(4219909917/10000000000 : ℝ)*X 0 2+(374433099/500000000 : ℝ)*X 1 0+(-4496067/2500000000 : ℝ)*X 1 1+(4219909917/10000000000 : ℝ)*X 1 2+(374433099/500000000 : ℝ)*X 2 0+(-4496067/2500000000 : ℝ)*X 2 1+(4219909917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-394128119/5000000000 : ℝ)*X 0 0+(-5893526741/10000000000 : ℝ)*X 0 1+(5657321703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1080689837/2500000000 : ℝ)*X 1 0+(4305787133/10000000000 : ℝ)*X 1 1+(4476045423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((276177077/500000000 : ℝ)*X 2 0+(-3664812221/10000000000 : ℝ)*X 2 1+(-959932909/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2189308189/2500000000 : ℝ)*X 0 0+(-316525001/5000000000 : ℝ)*X 0 1+(1109382523/5000000000 : ℝ)*X 0 2+(2189308189/2500000000 : ℝ)*X 1 0+(-316525001/5000000000 : ℝ)*X 1 1+(1109382523/5000000000 : ℝ)*X 1 2+(2189308189/2500000000 : ℝ)*X 2 0+(-316525001/5000000000 : ℝ)*X 2 1+(1109382523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1076670237/10000000000 : ℝ)*X 0 0+(-3323625429/5000000000 : ℝ)*X 0 1+(2344937787/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((342054759/625000000 : ℝ)*X 1 0+(1934177823/5000000000 : ℝ)*X 1 1+(3693518133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((431764047/1000000000 : ℝ)*X 2 0+(-1140390779/2500000000 : ℝ)*X 2 1+(-4223779013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((830163187/1000000000 : ℝ)*X 0 0+(-56463701/10000000000 : ℝ)*X 0 1+(3168982709/10000000000 : ℝ)*X 0 2+(830163187/1000000000 : ℝ)*X 1 0+(-56463701/10000000000 : ℝ)*X 1 1+(3168982709/10000000000 : ℝ)*X 1 2+(830163187/1000000000 : ℝ)*X 2 0+(-56463701/10000000000 : ℝ)*X 2 1+(3168982709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301039_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((1147/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1147/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15083474279781532405535318793231/1455918738706250000000000000000000000 : ℝ) := by norm_num
    linear_combination (110148406413/1000000000000 : ℝ)*(base3) + (1316031/500000000000 : ℝ)*(base10) + (876860636503/500000000000 : ℝ)*(base40) + (59942814547/200000000000 : ℝ)*(base49) + (1669717/1000000000000 : ℝ)*(base59) + (7730648814701/1000000000000 : ℝ)*(major_s1_0) + (7730648814701/1000000000000 : ℝ)*(major_s1_1) + (7730648814701/1000000000000 : ℝ)*(major_s1_2) + (10235083870503/1000000000000 : ℝ)*(sp_s1_7) + (10345261026043/1000000000000 : ℝ)*(sp_s1_8) + (10235199144321/1000000000000 : ℝ)*(sp_s1_9) + (5115946625293/1000000000000 : ℝ)*(sp_s1_13) + (86524691/1000000000000 : ℝ)*(sp_s1_15) + (112641757/1000000000000 : ℝ)*(sp_s1_21) + (2613047515853/500000000000 : ℝ)*(f.failure) + (10235199144321/1000000000000 : ℝ)*(f.sum) + (24231817795542335841/81146975000000000000000000000000 : ℝ)*base63 + (3498937555057009/4711000000000000000000000000 : ℝ)*base65 + (710607968679301/8612500000000000000000000000 : ℝ)*base67 + (2387836099707757/4711000000000000000000000000 : ℝ)*base69 + (99422867423076276253/338094337000000000000000000000000 : ℝ)*base71 + (4309200958106867/7176700000000000000000000000 : ℝ)*base73 + (1311969147036657/2153125000000000000000000000 : ℝ)*base75 + (167706888264347/287068000000000000000000000 : ℝ)*base76 + (17804948375592932873/154523321875000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (2707/12500000000000000 : ℝ)*base86 + (2707/12500000000000000 : ℝ)*base88 + (2707/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3193/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-3193/10000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (166113024071924730237/73609375000000000000000000 : ℝ) := by norm_num
    linear_combination (6597/10000000000 : ℝ)*(base24) + (1723336720221/1000000000000 : ℝ)*(base40) + (119733/1000000000000 : ℝ)*(base50) + (92919/50000000000 : ℝ)*(base53) + (1312625676471/250000000000 : ℝ)*(major_s1_0) + (1312625676471/250000000000 : ℝ)*(major_s1_1) + (328156302969/62500000000 : ℝ)*(major_s1_2) + (7412703/500000000000 : ℝ)*(sp_s1_0) + (14589091/500000000000 : ℝ)*(sp_s1_8) + (434470519801/62500000000 : ℝ)*(sp_s1_14) + (173787849101/25000000000 : ℝ)*(sp_s1_15) + (3475772170451/500000000000 : ℝ)*(sp_s1_16) + (3549449732467/1000000000000 : ℝ)*(sp_s1_20) + (9926469/1000000000000 : ℝ)*(sp_s1_27) + (443682457367/125000000000 : ℝ)*(f.failure) + (3475772500301/500000000000 : ℝ)*(f.sum) + (893403641939571991/5071685937500000000000000000000 : ℝ)*base62 + (362649533044241/1177750000000000000000000000 : ℝ)*base64 + (1923994856545517/4306250000000000000000000000 : ℝ)*base67 + (22655620535509/588875000000000000000000000 : ℝ)*base68 + (25141644395922723103/84523584250000000000000000000000 : ℝ)*base71 + (588647288340419/3588350000000000000000000000 : ℝ)*base73 + (16379717974313/2153125000000000000000000000 : ℝ)*base75 + (30315070124459/717670000000000000000000000 : ℝ)*base76 + (114080205983457279461/309046643750000000000000000000000 : ℝ)*base78 + (1527/3125000000000000 : ℝ)*base87 + (1527/3125000000000000 : ℝ)*base89 + (1527/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23999/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23999/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5752896629076370071741881298153/1455918738706250000000000000000000000 : ℝ) := by norm_num
    linear_combination (787813/1000000000000 : ℝ)*(base3) + (636534640421/250000000000 : ℝ)*(base40) + (11415784049/250000000000 : ℝ)*(base49) + (8232287977763/1000000000000 : ℝ)*(major_s1_0) + (8232287977763/1000000000000 : ℝ)*(major_s1_1) + (8232287977763/1000000000000 : ℝ)*(major_s1_2) + (3753343/500000000000 : ℝ)*(sp_s1_0) + (40319299/1000000000000 : ℝ)*(sp_s1_1) + (7821203/125000000000 : ℝ)*(sp_s1_7) + (26521369/1000000000000 : ℝ)*(sp_s1_20) + (10899290007473/1000000000000 : ℝ)*(sp_s1_21) + (1362415069037/125000000000 : ℝ)*(sp_s1_22) + (5449680041891/500000000000 : ℝ)*(sp_s1_23) + (5565187245429/1000000000000 : ℝ)*(sp_s1_27) + (5565214554611/1000000000000 : ℝ)*(f.failure) + (5449680041891/500000000000 : ℝ)*(f.sum) + (20147664138611471083/81146975000000000000000000000000 : ℝ)*base63 + (1334883265996167/4711000000000000000000000000 : ℝ)*base65 + (246403472698813/8612500000000000000000000000 : ℝ)*base67 + (1948544827525391/4711000000000000000000000000 : ℝ)*base69 + (22364011259561741739/338094337000000000000000000000000 : ℝ)*base71 + (2422228130838311/7176700000000000000000000000 : ℝ)*base73 + (1827357071230557/4306250000000000000000000000 : ℝ)*base75 + (20133470964933/57413600000000000000000000 : ℝ)*base76 + (38902304944373859973/309046643750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (5609/25000000000000000 : ℝ)*base86 + (5609/25000000000000000 : ℝ)*base88 + (5609/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((71767/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71767/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-689/800 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-689/800 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4711/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4711/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1147/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1147/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3193/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-3193/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23999/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23999/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301039_s1 p hpa hpb X hX hprev0

#print axioms solution
