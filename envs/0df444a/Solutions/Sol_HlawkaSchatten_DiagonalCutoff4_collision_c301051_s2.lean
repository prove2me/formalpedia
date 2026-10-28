-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301051_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:29:20.181331+00:00
-- url     : https://prove2.me/submissions/c6f55159-c113-42f3-9354-a0b3cbddd326

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
theorem collision_support_c301051_s2_s2_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1955871417/5000000000 : ℝ)*x 0 + (1954923667/5000000000 : ℝ)*x 1 + (2620189773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1955871417/5000000000 : ℝ)^65 ≤ (1799478806387/6250000000000 : ℝ)^49 := by
    have hnat : (1955871417 : ℕ)^65*6250000000000^49 ≤ 1799478806387^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955871417 5000000000 1799478806387 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1954923667/5000000000 : ℝ)^65 ≤ (5754631060827/20000000000000 : ℝ)^49 := by
    have hnat : (1954923667 : ℕ)^65*20000000000000^49 ≤ 5754631060827^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954923667 5000000000 5754631060827 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620189773/5000000000 : ℝ)^65 ≤ (42435183788169/100000000000000 : ℝ)^49 := by
    have hnat : (2620189773 : ℕ)^65*100000000000000^49 ≤ 42435183788169^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620189773 5000000000 42435183788169 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1955871417/5000000000 : ℝ), (1954923667/5000000000 : ℝ), (2620189773/5000000000 : ℝ)] ![(1799478806387/6250000000000 : ℝ), (5754631060827/20000000000000 : ℝ), (42435183788169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1955871417/5000000000 : ℝ)|^65 ≤ (1799478806387/6250000000000 : ℝ)^49
        have hw : |(-1955871417/5000000000 : ℝ)|=(1955871417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1954923667/5000000000 : ℝ)|^65 ≤ (5754631060827/20000000000000 : ℝ)^49
        have hw : |(1954923667/5000000000 : ℝ)|=(1954923667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620189773/5000000000 : ℝ)|^65 ≤ (42435183788169/100000000000000 : ℝ)^49
        have hw : |(2620189773/5000000000 : ℝ)|=(2620189773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3101822523/10000000000 : ℝ)*x 0 + (-3100319483/10000000000 : ℝ)*x 1 + (3302497151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3101822523/10000000000 : ℝ)^65 ≤ (21164807120401/100000000000000 : ℝ)^49 := by
    have hnat : (3101822523 : ℕ)^65*100000000000000^49 ≤ 21164807120401^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3101822523 10000000000 21164807120401 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3100319483/10000000000 : ℝ)^65 ≤ (2115120361537/10000000000000 : ℝ)^49 := by
    have hnat : (3100319483 : ℕ)^65*10000000000000^49 ≤ 2115120361537^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3100319483 10000000000 2115120361537 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3302497151/5000000000 : ℝ)^65 ≤ (2307359569919/4000000000000 : ℝ)^49 := by
    have hnat : (3302497151 : ℕ)^65*4000000000000^49 ≤ 2307359569919^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3302497151 5000000000 2307359569919 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3101822523/10000000000 : ℝ), (-3100319483/10000000000 : ℝ), (3302497151/5000000000 : ℝ)] ![(21164807120401/100000000000000 : ℝ), (2115120361537/10000000000000 : ℝ), (2307359569919/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3101822523/10000000000 : ℝ)|^65 ≤ (21164807120401/100000000000000 : ℝ)^49
        have hw : |(3101822523/10000000000 : ℝ)|=(3101822523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3100319483/10000000000 : ℝ)|^65 ≤ (2115120361537/10000000000000 : ℝ)^49
        have hw : |(-3100319483/10000000000 : ℝ)|=(3100319483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3302497151/5000000000 : ℝ)|^65 ≤ (2307359569919/4000000000000 : ℝ)^49
        have hw : |(3302497151/5000000000 : ℝ)|=(3302497151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1090388159/2000000000 : ℝ)*x 0 + (681780147/1250000000 : ℝ)*x 1 + (-458135923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090388159/2000000000 : ℝ)^65 ≤ (22361298284413/50000000000000 : ℝ)^49 := by
    have hnat : (1090388159 : ℕ)^65*50000000000000^49 ≤ 22361298284413^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090388159 2000000000 22361298284413 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681780147/1250000000 : ℝ)^65 ≤ (22373815070959/50000000000000 : ℝ)^49 := by
    have hnat : (681780147 : ℕ)^65*50000000000000^49 ≤ 22373815070959^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681780147 1250000000 22373815070959 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458135923/2500000000 : ℝ)^65 ≤ (2105954653333/20000000000000 : ℝ)^49 := by
    have hnat : (458135923 : ℕ)^65*20000000000000^49 ≤ 2105954653333^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458135923 2500000000 2105954653333 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090388159/2000000000 : ℝ), (681780147/1250000000 : ℝ), (-458135923/2500000000 : ℝ)] ![(22361298284413/50000000000000 : ℝ), (22373815070959/50000000000000 : ℝ), (2105954653333/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090388159/2000000000 : ℝ)|^65 ≤ (22361298284413/50000000000000 : ℝ)^49
        have hw : |(1090388159/2000000000 : ℝ)|=(1090388159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681780147/1250000000 : ℝ)|^65 ≤ (22373815070959/50000000000000 : ℝ)^49
        have hw : |(681780147/1250000000 : ℝ)|=(681780147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-458135923/2500000000 : ℝ)|^65 ≤ (2105954653333/20000000000000 : ℝ)^49
        have hw : |(-458135923/2500000000 : ℝ)|=(458135923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5111074621/10000000000 : ℝ)*x 0 + (2556615589/5000000000 : ℝ)*x 1 + (682682063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5111074621/10000000000 : ℝ)^65 ≤ (5131478952481/12500000000000 : ℝ)^49 := by
    have hnat : (5111074621 : ℕ)^65*12500000000000^49 ≤ 5131478952481^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5111074621 10000000000 5131478952481 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2556615589/5000000000 : ℝ)^65 ≤ (41074810478257/100000000000000 : ℝ)^49 := by
    have hnat : (2556615589 : ℕ)^65*100000000000000^49 ≤ 41074810478257^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556615589 5000000000 41074810478257 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682682063/2500000000 : ℝ)^65 ≤ (4468339472717/25000000000000 : ℝ)^49 := by
    have hnat : (682682063 : ℕ)^65*25000000000000^49 ≤ 4468339472717^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682682063 2500000000 4468339472717 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5111074621/10000000000 : ℝ), (2556615589/5000000000 : ℝ), (682682063/2500000000 : ℝ)] ![(5131478952481/12500000000000 : ℝ), (41074810478257/100000000000000 : ℝ), (4468339472717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5111074621/10000000000 : ℝ)|^65 ≤ (5131478952481/12500000000000 : ℝ)^49
        have hw : |(5111074621/10000000000 : ℝ)|=(5111074621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2556615589/5000000000 : ℝ)|^65 ≤ (41074810478257/100000000000000 : ℝ)^49
        have hw : |(2556615589/5000000000 : ℝ)|=(2556615589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682682063/2500000000 : ℝ)|^65 ≤ (4468339472717/25000000000000 : ℝ)^49
        have hw : |(682682063/2500000000 : ℝ)|=(682682063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3781726267/10000000000 : ℝ)*x 0 + (3451987267/10000000000 : ℝ)*x 1 + (5757674529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3781726267/10000000000 : ℝ)^65 ≤ (6882290264707/25000000000000 : ℝ)^49 := by
    have hnat : (3781726267 : ℕ)^65*25000000000000^49 ≤ 6882290264707^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3781726267 10000000000 6882290264707 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3451987267/10000000000 : ℝ)^65 ≤ (24391282335701/100000000000000 : ℝ)^49 := by
    have hnat : (3451987267 : ℕ)^65*100000000000000^49 ≤ 24391282335701^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3451987267 10000000000 24391282335701 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5757674529/10000000000 : ℝ)^65 ≤ (24039778298561/50000000000000 : ℝ)^49 := by
    have hnat : (5757674529 : ℕ)^65*50000000000000^49 ≤ 24039778298561^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5757674529 10000000000 24039778298561 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3781726267/10000000000 : ℝ), (3451987267/10000000000 : ℝ), (5757674529/10000000000 : ℝ)] ![(6882290264707/25000000000000 : ℝ), (24391282335701/100000000000000 : ℝ), (24039778298561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3781726267/10000000000 : ℝ)|^65 ≤ (6882290264707/25000000000000 : ℝ)^49
        have hw : |(-3781726267/10000000000 : ℝ)|=(3781726267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3451987267/10000000000 : ℝ)|^65 ≤ (24391282335701/100000000000000 : ℝ)^49
        have hw : |(3451987267/10000000000 : ℝ)|=(3451987267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5757674529/10000000000 : ℝ)|^65 ≤ (24039778298561/50000000000000 : ℝ)^49
        have hw : |(5757674529/10000000000 : ℝ)|=(5757674529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2968933591/10000000000 : ℝ)*x 0 + (-542012839/2000000000 : ℝ)*x 1 + (7002633143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2968933591/10000000000 : ℝ)^65 ≤ (19970475075341/100000000000000 : ℝ)^49 := by
    have hnat : (2968933591 : ℕ)^65*100000000000000^49 ≤ 19970475075341^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2968933591 10000000000 19970475075341 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542012839/2000000000 : ℝ)^65 ≤ (707766567711/4000000000000 : ℝ)^49 := by
    have hnat : (542012839 : ℕ)^65*4000000000000^49 ≤ 707766567711^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542012839 2000000000 707766567711 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7002633143/10000000000 : ℝ)^65 ≤ (62335360716339/100000000000000 : ℝ)^49 := by
    have hnat : (7002633143 : ℕ)^65*100000000000000^49 ≤ 62335360716339^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7002633143 10000000000 62335360716339 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2968933591/10000000000 : ℝ), (-542012839/2000000000 : ℝ), (7002633143/10000000000 : ℝ)] ![(19970475075341/100000000000000 : ℝ), (707766567711/4000000000000 : ℝ), (62335360716339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2968933591/10000000000 : ℝ)|^65 ≤ (19970475075341/100000000000000 : ℝ)^49
        have hw : |(2968933591/10000000000 : ℝ)|=(2968933591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-542012839/2000000000 : ℝ)|^65 ≤ (707766567711/4000000000000 : ℝ)^49
        have hw : |(-542012839/2000000000 : ℝ)|=(542012839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7002633143/10000000000 : ℝ)|^65 ≤ (62335360716339/100000000000000 : ℝ)^49
        have hw : |(7002633143/10000000000 : ℝ)|=(7002633143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (653654601/1250000000 : ℝ)*x 0 + (1500021369/2500000000 : ℝ)*x 1 + (-666356553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653654601/1250000000 : ℝ)^65 ≤ (21157765658201/50000000000000 : ℝ)^49 := by
    have hnat : (653654601 : ℕ)^65*50000000000000^49 ≤ 21157765658201^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653654601 1250000000 21157765658201 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1500021369/2500000000 : ℝ)^65 ≤ (5078308141817/10000000000000 : ℝ)^49 := by
    have hnat : (1500021369 : ℕ)^65*10000000000000^49 ≤ 5078308141817^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500021369 2500000000 5078308141817 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (666356553/5000000000 : ℝ)^65 ≤ (6901387249599/100000000000000 : ℝ)^49 := by
    have hnat : (666356553 : ℕ)^65*100000000000000^49 ≤ 6901387249599^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666356553 5000000000 6901387249599 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653654601/1250000000 : ℝ), (1500021369/2500000000 : ℝ), (-666356553/5000000000 : ℝ)] ![(21157765658201/50000000000000 : ℝ), (5078308141817/10000000000000 : ℝ), (6901387249599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653654601/1250000000 : ℝ)|^65 ≤ (21157765658201/50000000000000 : ℝ)^49
        have hw : |(653654601/1250000000 : ℝ)|=(653654601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1500021369/2500000000 : ℝ)|^65 ≤ (5078308141817/10000000000000 : ℝ)^49
        have hw : |(1500021369/2500000000 : ℝ)|=(1500021369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-666356553/5000000000 : ℝ)|^65 ≤ (6901387249599/100000000000000 : ℝ)^49
        have hw : |(-666356553/5000000000 : ℝ)|=(666356553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_12 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (502478799/1000000000 : ℝ)*x 0 + (5765498589/10000000000 : ℝ)*x 1 + (1983900889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502478799/1000000000 : ℝ)^65 ≤ (4013502481153/10000000000000 : ℝ)^49 := by
    have hnat : (502478799 : ℕ)^65*10000000000000^49 ≤ 4013502481153^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502478799 1000000000 4013502481153 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5765498589/10000000000 : ℝ)^65 ≤ (24083122310587/50000000000000 : ℝ)^49 := by
    have hnat : (5765498589 : ℕ)^65*50000000000000^49 ≤ 24083122310587^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5765498589 10000000000 24083122310587 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1983900889/10000000000 : ℝ)^65 ≤ (5849365277347/50000000000000 : ℝ)^49 := by
    have hnat : (1983900889 : ℕ)^65*50000000000000^49 ≤ 5849365277347^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983900889 10000000000 5849365277347 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(502478799/1000000000 : ℝ), (5765498589/10000000000 : ℝ), (1983900889/10000000000 : ℝ)] ![(4013502481153/10000000000000 : ℝ), (24083122310587/50000000000000 : ℝ), (5849365277347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(502478799/1000000000 : ℝ)|^65 ≤ (4013502481153/10000000000000 : ℝ)^49
        have hw : |(502478799/1000000000 : ℝ)|=(502478799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5765498589/10000000000 : ℝ)|^65 ≤ (24083122310587/50000000000000 : ℝ)^49
        have hw : |(5765498589/10000000000 : ℝ)|=(5765498589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1983900889/10000000000 : ℝ)|^65 ≤ (5849365277347/50000000000000 : ℝ)^49
        have hw : |(1983900889/10000000000 : ℝ)|=(1983900889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3453877909/10000000000 : ℝ)*x 0 + (755977509/2000000000 : ℝ)*x 1 + (5757677371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3453877909/10000000000 : ℝ)^65 ≤ (24409005075211/100000000000000 : ℝ)^49 := by
    have hnat : (3453877909 : ℕ)^65*100000000000000^49 ≤ 24409005075211^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3453877909 10000000000 24409005075211 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (755977509/2000000000 : ℝ)^65 ≤ (27511406832357/100000000000000 : ℝ)^49 := by
    have hnat : (755977509 : ℕ)^65*100000000000000^49 ≤ 27511406832357^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755977509 2000000000 27511406832357 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5757677371/10000000000 : ℝ)^65 ≤ (12019897019643/25000000000000 : ℝ)^49 := by
    have hnat : (5757677371 : ℕ)^65*25000000000000^49 ≤ 12019897019643^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5757677371 10000000000 12019897019643 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3453877909/10000000000 : ℝ), (755977509/2000000000 : ℝ), (5757677371/10000000000 : ℝ)] ![(24409005075211/100000000000000 : ℝ), (27511406832357/100000000000000 : ℝ), (12019897019643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3453877909/10000000000 : ℝ)|^65 ≤ (24409005075211/100000000000000 : ℝ)^49
        have hw : |(-3453877909/10000000000 : ℝ)|=(3453877909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(755977509/2000000000 : ℝ)|^65 ≤ (27511406832357/100000000000000 : ℝ)^49
        have hw : |(755977509/2000000000 : ℝ)|=(755977509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5757677371/10000000000 : ℝ)|^65 ≤ (12019897019643/25000000000000 : ℝ)^49
        have hw : |(5757677371/10000000000 : ℝ)|=(5757677371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (338943533/1250000000 : ℝ)*x 0 + (-1483744907/5000000000 : ℝ)*x 1 + (7002635427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338943533/1250000000 : ℝ)^65 ≤ (17707018854923/100000000000000 : ℝ)^49 := by
    have hnat : (338943533 : ℕ)^65*100000000000000^49 ≤ 17707018854923^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338943533 1250000000 17707018854923 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1483744907/5000000000 : ℝ)^65 ≤ (3991518689057/20000000000000 : ℝ)^49 := by
    have hnat : (1483744907 : ℕ)^65*20000000000000^49 ≤ 3991518689057^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483744907 5000000000 3991518689057 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7002635427/10000000000 : ℝ)^65 ≤ (15583846921671/25000000000000 : ℝ)^49 := by
    have hnat : (7002635427 : ℕ)^65*25000000000000^49 ≤ 15583846921671^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7002635427 10000000000 15583846921671 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338943533/1250000000 : ℝ), (-1483744907/5000000000 : ℝ), (7002635427/10000000000 : ℝ)] ![(17707018854923/100000000000000 : ℝ), (3991518689057/20000000000000 : ℝ), (15583846921671/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338943533/1250000000 : ℝ)|^65 ≤ (17707018854923/100000000000000 : ℝ)^49
        have hw : |(338943533/1250000000 : ℝ)|=(338943533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1483744907/5000000000 : ℝ)|^65 ≤ (3991518689057/20000000000000 : ℝ)^49
        have hw : |(-1483744907/5000000000 : ℝ)|=(1483744907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7002635427/10000000000 : ℝ)|^65 ≤ (15583846921671/25000000000000 : ℝ)^49
        have hw : |(7002635427/10000000000 : ℝ)|=(7002635427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1499455267/2500000000 : ℝ)*x 0 + (5231606627/10000000000 : ℝ)*x 1 + (-266542077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1499455267/2500000000 : ℝ)^65 ≤ (50757659588363/100000000000000 : ℝ)^49 := by
    have hnat : (1499455267 : ℕ)^65*100000000000000^49 ≤ 50757659588363^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499455267 2500000000 50757659588363 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231606627/10000000000 : ℝ)^65 ≤ (42340971841521/100000000000000 : ℝ)^49 := by
    have hnat : (5231606627 : ℕ)^65*100000000000000^49 ≤ 42340971841521^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231606627 10000000000 42340971841521 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266542077/2000000000 : ℝ)^65 ≤ (1380273711609/20000000000000 : ℝ)^49 := by
    have hnat : (266542077 : ℕ)^65*20000000000000^49 ≤ 1380273711609^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266542077 2000000000 1380273711609 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1499455267/2500000000 : ℝ), (5231606627/10000000000 : ℝ), (-266542077/2000000000 : ℝ)] ![(50757659588363/100000000000000 : ℝ), (42340971841521/100000000000000 : ℝ), (1380273711609/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1499455267/2500000000 : ℝ)|^65 ≤ (50757659588363/100000000000000 : ℝ)^49
        have hw : |(1499455267/2500000000 : ℝ)|=(1499455267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231606627/10000000000 : ℝ)|^65 ≤ (42340971841521/100000000000000 : ℝ)^49
        have hw : |(5231606627/10000000000 : ℝ)|=(5231606627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266542077/2000000000 : ℝ)|^65 ≤ (1380273711609/20000000000000 : ℝ)^49
        have hw : |(-266542077/2000000000 : ℝ)|=(266542077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_18 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5763323377/10000000000 : ℝ)*x 0 + (2513532867/5000000000 : ℝ)*x 1 + (1983896897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5763323377/10000000000 : ℝ)^65 ≤ (48142140126599/100000000000000 : ℝ)^49 := by
    have hnat : (5763323377 : ℕ)^65*100000000000000^49 ≤ 48142140126599^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5763323377 10000000000 48142140126599 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2513532867/5000000000 : ℝ)^65 ≤ (40159160523717/100000000000000 : ℝ)^49 := by
    have hnat : (2513532867 : ℕ)^65*100000000000000^49 ≤ 40159160523717^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513532867 5000000000 40159160523717 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1983896897/10000000000 : ℝ)^65 ≤ (11698699327969/100000000000000 : ℝ)^49 := by
    have hnat : (1983896897 : ℕ)^65*100000000000000^49 ≤ 11698699327969^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983896897 10000000000 11698699327969 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5763323377/10000000000 : ℝ), (2513532867/5000000000 : ℝ), (1983896897/10000000000 : ℝ)] ![(48142140126599/100000000000000 : ℝ), (40159160523717/100000000000000 : ℝ), (11698699327969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5763323377/10000000000 : ℝ)|^65 ≤ (48142140126599/100000000000000 : ℝ)^49
        have hw : |(5763323377/10000000000 : ℝ)|=(5763323377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2513532867/5000000000 : ℝ)|^65 ≤ (40159160523717/100000000000000 : ℝ)^49
        have hw : |(2513532867/5000000000 : ℝ)|=(2513532867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1983896897/10000000000 : ℝ)|^65 ≤ (11698699327969/100000000000000 : ℝ)^49
        have hw : |(1983896897/10000000000 : ℝ)|=(1983896897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_19 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3999316343/10000000000 : ℝ)*x 0 + (3997460339/10000000000 : ℝ)*x 1 + (79371411/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3999316343/10000000000 : ℝ)^65 ≤ (29649810615233/100000000000000 : ℝ)^49 := by
    have hnat : (3999316343 : ℕ)^65*100000000000000^49 ≤ 29649810615233^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3999316343 10000000000 29649810615233 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3997460339/10000000000 : ℝ)^65 ≤ (2963155907837/10000000000000 : ℝ)^49 := by
    have hnat : (3997460339 : ℕ)^65*10000000000000^49 ≤ 2963155907837^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3997460339 10000000000 2963155907837 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79371411/156250000 : ℝ)^65 ≤ (50898287859/125000000000 : ℝ)^49 := by
    have hnat : (79371411 : ℕ)^65*125000000000^49 ≤ 50898287859^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79371411 156250000 50898287859 125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3999316343/10000000000 : ℝ), (3997460339/10000000000 : ℝ), (79371411/156250000 : ℝ)] ![(29649810615233/100000000000000 : ℝ), (2963155907837/10000000000000 : ℝ), (50898287859/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3999316343/10000000000 : ℝ)|^65 ≤ (29649810615233/100000000000000 : ℝ)^49
        have hw : |(-3999316343/10000000000 : ℝ)|=(3999316343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3997460339/10000000000 : ℝ)|^65 ≤ (2963155907837/10000000000000 : ℝ)^49
        have hw : |(3997460339/10000000000 : ℝ)|=(3997460339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79371411/156250000 : ℝ)|^65 ≤ (50898287859/125000000000 : ℝ)^49
        have hw : |(79371411/156250000 : ℝ)|=(79371411/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3031566313/10000000000 : ℝ)*x 0 + (-757503901/2500000000 : ℝ)*x 1 + (6714102797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3031566313/10000000000 : ℝ)^65 ≤ (20531255347067/100000000000000 : ℝ)^49 := by
    have hnat : (3031566313 : ℕ)^65*100000000000000^49 ≤ 20531255347067^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3031566313 10000000000 20531255347067 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (757503901/2500000000 : ℝ)^65 ≤ (512933126761/2500000000000 : ℝ)^49 := by
    have hnat : (757503901 : ℕ)^65*2500000000000^49 ≤ 512933126761^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757503901 2500000000 512933126761 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6714102797/10000000000 : ℝ)^65 ≤ (58951419569251/100000000000000 : ℝ)^49 := by
    have hnat : (6714102797 : ℕ)^65*100000000000000^49 ≤ 58951419569251^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6714102797 10000000000 58951419569251 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3031566313/10000000000 : ℝ), (-757503901/2500000000 : ℝ), (6714102797/10000000000 : ℝ)] ![(20531255347067/100000000000000 : ℝ), (512933126761/2500000000000 : ℝ), (58951419569251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3031566313/10000000000 : ℝ)|^65 ≤ (20531255347067/100000000000000 : ℝ)^49
        have hw : |(3031566313/10000000000 : ℝ)|=(3031566313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-757503901/2500000000 : ℝ)|^65 ≤ (512933126761/2500000000000 : ℝ)^49
        have hw : |(-757503901/2500000000 : ℝ)|=(757503901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6714102797/10000000000 : ℝ)|^65 ≤ (58951419569251/100000000000000 : ℝ)^49
        have hw : |(6714102797/10000000000 : ℝ)|=(6714102797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5743941767/10000000000 : ℝ)*x 0 + (253816731/500000000 : ℝ)*x 1 + (-1944355281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5743941767/10000000000 : ℝ)^65 ≤ (748867110887/1562500000000 : ℝ)^49 := by
    have hnat : (5743941767 : ℕ)^65*1562500000000^49 ≤ 748867110887^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5743941767 10000000000 748867110887 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253816731/500000000 : ℝ)^65 ≤ (4068210180659/10000000000000 : ℝ)^49 := by
    have hnat : (253816731 : ℕ)^65*10000000000000^49 ≤ 4068210180659^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253816731 500000000 4068210180659 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1944355281/10000000000 : ℝ)^65 ≤ (2847600770273/25000000000000 : ℝ)^49 := by
    have hnat : (1944355281 : ℕ)^65*25000000000000^49 ≤ 2847600770273^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944355281 10000000000 2847600770273 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5743941767/10000000000 : ℝ), (253816731/500000000 : ℝ), (-1944355281/10000000000 : ℝ)] ![(748867110887/1562500000000 : ℝ), (4068210180659/10000000000000 : ℝ), (2847600770273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5743941767/10000000000 : ℝ)|^65 ≤ (748867110887/1562500000000 : ℝ)^49
        have hw : |(5743941767/10000000000 : ℝ)|=(5743941767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(253816731/500000000 : ℝ)|^65 ≤ (4068210180659/10000000000000 : ℝ)^49
        have hw : |(253816731/500000000 : ℝ)|=(253816731/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1944355281/10000000000 : ℝ)|^65 ≤ (2847600770273/25000000000000 : ℝ)^49
        have hw : |(-1944355281/10000000000 : ℝ)|=(1944355281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301051_s2_s2_25 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (182622483/400000000 : ℝ)*x 0 + (1469932391/2500000000 : ℝ)*x 1 + (60480231/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182622483/400000000 : ℝ)^65 ≤ (35343430577017/100000000000000 : ℝ)^49 := by
    have hnat : (182622483 : ℕ)^65*100000000000000^49 ≤ 35343430577017^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182622483 400000000 35343430577017 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1469932391/2500000000 : ℝ)^65 ≤ (24718121939737/50000000000000 : ℝ)^49 := by
    have hnat : (1469932391 : ℕ)^65*50000000000000^49 ≤ 24718121939737^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469932391 2500000000 24718121939737 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60480231/250000000 : ℝ)^65 ≤ (380508138269/2500000000000 : ℝ)^49 := by
    have hnat : (60480231 : ℕ)^65*2500000000000^49 ≤ 380508138269^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60480231 250000000 380508138269 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(182622483/400000000 : ℝ), (1469932391/2500000000 : ℝ), (60480231/250000000 : ℝ)] ![(35343430577017/100000000000000 : ℝ), (24718121939737/50000000000000 : ℝ), (380508138269/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(182622483/400000000 : ℝ)|^65 ≤ (35343430577017/100000000000000 : ℝ)^49
        have hw : |(182622483/400000000 : ℝ)|=(182622483/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1469932391/2500000000 : ℝ)|^65 ≤ (24718121939737/50000000000000 : ℝ)^49
        have hw : |(1469932391/2500000000 : ℝ)|=(1469932391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(60480231/250000000 : ℝ)|^65 ≤ (380508138269/2500000000000 : ℝ)^49
        have hw : |(60480231/250000000 : ℝ)|=(60480231/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301051_s2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((67297/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67297/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(67139/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(67139/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18989/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(18989/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((32381/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32381/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6473/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6473/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(411/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(411/10000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (67297/100000 : ℝ) ^ (129/32 : ℝ) ≤ (506462963940427513/2500000000000000000 : ℝ) := by
    have hpowers : (67297/100000 : ℝ)^129 ≤ (506462963940427513/2500000000000000000 : ℝ)^32 := by
      have hnat : (67297 : ℕ)^129*2500000000000000000^32 ≤ 506462963940427513^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67297 100000 506462963940427513 2500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67297/100000 : ℝ)) (X := (506462963940427513/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (3006462963940427513/2500000000000000000 : ℝ) ≤ (83745925434569/80000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3006462963940427513/2500000000000000000 : ℝ)^32 ≤ (83745925434569/80000000000000 : ℝ)^129 := by
      have hnat : (3006462963940427513 : ℕ)^32*80000000000000^129 ≤ 83745925434569^129*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3006462963940427513 2500000000000000000 83745925434569 80000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (83745925434569/80000000000000 : ℝ)) (X := (3006462963940427513/2500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (1756462963940427513/1250000000000000000 : ℝ) ≤ (10880427250415497/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (1756462963940427513/1250000000000000000 : ℝ)^32 ≤ (10880427250415497/10000000000000000 : ℝ)^129 := by
      have hnat : (1756462963940427513 : ℕ)^32*10000000000000000^129 ≤ 10880427250415497^129*1250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1756462963940427513 1250000000000000000 10880427250415497 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10880427250415497/10000000000000000 : ℝ)) (X := (1756462963940427513/1250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3745925434569/53837600000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(103046642773593/1682425000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (67297/100000 : ℝ)) (alpha := (3745925434569/53837600000000 : ℝ)) (beta := (103046642773593/1682425000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (67297/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3745925434569/53837600000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(103046642773593/1682425000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (67139/100000 : ℝ) ^ (129/32 : ℝ) ≤ (20067461485443280427/100000000000000000000 : ℝ) := by
    have hpowers : (67139/100000 : ℝ)^129 ≤ (20067461485443280427/100000000000000000000 : ℝ)^32 := by
      have hnat : (67139 : ℕ)^129*100000000000000000000^32 ≤ 20067461485443280427^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67139 100000 20067461485443280427 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67139/100000 : ℝ)) (X := (20067461485443280427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (120067461485443280427/100000000000000000000 : ℝ) ≤ (10464112668688367/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (120067461485443280427/100000000000000000000 : ℝ)^32 ≤ (10464112668688367/10000000000000000 : ℝ)^129 := by
      have hnat : (120067461485443280427 : ℕ)^32*10000000000000000^129 ≤ 10464112668688367^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        120067461485443280427 100000000000000000000 10464112668688367 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10464112668688367/10000000000000000 : ℝ)) (X := (120067461485443280427/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (70067461485443280427/50000000000000000000 : ℝ) ≤ (1087308016913811/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (70067461485443280427/50000000000000000000 : ℝ)^32 ≤ (1087308016913811/1000000000000000 : ℝ)^129 := by
      have hnat : (70067461485443280427 : ℕ)^32*1000000000000000^129 ≤ 1087308016913811^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70067461485443280427 50000000000000000000 1087308016913811 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1087308016913811/1000000000000000 : ℝ)) (X := (70067461485443280427/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(464112668688367/6713900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(408967500449743/6713900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (67139/100000 : ℝ)) (alpha := (464112668688367/6713900000000000 : ℝ)) (beta := (408967500449743/6713900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (67139/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(464112668688367/6713900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(408967500449743/6713900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (18989/100000 : ℝ) ^ (129/32 : ℝ) ≤ (123441607443482947/100000000000000000000 : ℝ) := by
    have hpowers : (18989/100000 : ℝ)^129 ≤ (123441607443482947/100000000000000000000 : ℝ)^32 := by
      have hnat : (18989 : ℕ)^129*100000000000000000000^32 ≤ 123441607443482947^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18989 100000 123441607443482947 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18989/100000 : ℝ)) (X := (123441607443482947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (100123441607443482947/100000000000000000000 : ℝ) ≤ (10003060697282217/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (100123441607443482947/100000000000000000000 : ℝ)^32 ≤ (10003060697282217/10000000000000000 : ℝ)^129 := by
      have hnat : (100123441607443482947 : ℕ)^32*10000000000000000^129 ≤ 10003060697282217^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100123441607443482947 100000000000000000000 10003060697282217 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003060697282217/10000000000000000 : ℝ)) (X := (100123441607443482947/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (50123441607443482947/50000000000000000000 : ℝ) ≤ (10006118558428391/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (50123441607443482947/50000000000000000000 : ℝ)^32 ≤ (10006118558428391/10000000000000000 : ℝ)^129 := by
      have hnat : (50123441607443482947 : ℕ)^32*10000000000000000^129 ≤ 10006118558428391^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50123441607443482947 50000000000000000000 10006118558428391 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006118558428391/10000000000000000 : ℝ)) (X := (50123441607443482947/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(180041016601/111700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1528930573087/949450000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (18989/100000 : ℝ)) (alpha := (180041016601/111700000000000 : ℝ)) (beta := (1528930573087/949450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (18989/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(180041016601/111700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1528930573087/949450000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1955871417/5000000000 : ℝ)*X 0 0+(1954923667/5000000000 : ℝ)*X 0 1+(2620189773/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((3101822523/10000000000 : ℝ)*X 1 0+(-3100319483/10000000000 : ℝ)*X 1 1+(3302497151/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1090388159/2000000000 : ℝ)*X 2 0+(681780147/1250000000 : ℝ)*X 2 1+(-458135923/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((5111074621/10000000000 : ℝ)*X 0 0+(2556615589/5000000000 : ℝ)*X 0 1+(682682063/2500000000 : ℝ)*X 0 2+(5111074621/10000000000 : ℝ)*X 1 0+(2556615589/5000000000 : ℝ)*X 1 1+(682682063/2500000000 : ℝ)*X 1 2+(5111074621/10000000000 : ℝ)*X 2 0+(2556615589/5000000000 : ℝ)*X 2 1+(682682063/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-3781726267/10000000000 : ℝ)*X 0 0+(3451987267/10000000000 : ℝ)*X 0 1+(5757674529/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2968933591/10000000000 : ℝ)*X 1 0+(-542012839/2000000000 : ℝ)*X 1 1+(7002633143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((653654601/1250000000 : ℝ)*X 2 0+(1500021369/2500000000 : ℝ)*X 2 1+(-666356553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((502478799/1000000000 : ℝ)*X 0 0+(5765498589/10000000000 : ℝ)*X 0 1+(1983900889/10000000000 : ℝ)*X 0 2+(502478799/1000000000 : ℝ)*X 1 0+(5765498589/10000000000 : ℝ)*X 1 1+(1983900889/10000000000 : ℝ)*X 1 2+(502478799/1000000000 : ℝ)*X 2 0+(5765498589/10000000000 : ℝ)*X 2 1+(1983900889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-3453877909/10000000000 : ℝ)*X 0 0+(755977509/2000000000 : ℝ)*X 0 1+(5757677371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((338943533/1250000000 : ℝ)*X 1 0+(-1483744907/5000000000 : ℝ)*X 1 1+(7002635427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1499455267/2500000000 : ℝ)*X 2 0+(5231606627/10000000000 : ℝ)*X 2 1+(-266542077/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_18 : ((5763323377/10000000000 : ℝ)*X 0 0+(2513532867/5000000000 : ℝ)*X 0 1+(1983896897/10000000000 : ℝ)*X 0 2+(5763323377/10000000000 : ℝ)*X 1 0+(2513532867/5000000000 : ℝ)*X 1 1+(1983896897/10000000000 : ℝ)*X 1 2+(5763323377/10000000000 : ℝ)*X 2 0+(2513532867/5000000000 : ℝ)*X 2 1+(1983896897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((-3999316343/10000000000 : ℝ)*X 0 0+(3997460339/10000000000 : ℝ)*X 0 1+(79371411/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3031566313/10000000000 : ℝ)*X 1 0+(-757503901/2500000000 : ℝ)*X 1 1+(6714102797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((5743941767/10000000000 : ℝ)*X 2 0+(253816731/500000000 : ℝ)*X 2 1+(-1944355281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((182622483/400000000 : ℝ)*X 0 0+(1469932391/2500000000 : ℝ)*X 0 1+(60480231/250000000 : ℝ)*X 0 2+(182622483/400000000 : ℝ)*X 1 0+(1469932391/2500000000 : ℝ)*X 1 1+(60480231/250000000 : ℝ)*X 1 2+(182622483/400000000 : ℝ)*X 2 0+(1469932391/2500000000 : ℝ)*X 2 1+(60480231/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301051_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((32381/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32381/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4522770818733461579356391774493/252344445855550000000000000000000000 : ℝ) := by norm_num
    linear_combination (372377290883/1000000000000 : ℝ)*(base49) + (321638824459/500000000000 : ℝ)*(base59) + (498607139479/250000000000 : ℝ)*(base60) + (2181890360341/250000000000 : ℝ)*(major_s2_0) + (2181890360341/250000000000 : ℝ)*(major_s2_1) + (2181890360341/250000000000 : ℝ)*(major_s2_2) + (20386671/250000000000 : ℝ)*(sp_s2_2) + (180548221703/15625000000 : ℝ)*(sp_s2_7) + (11554742222189/1000000000000 : ℝ)*(sp_s2_8) + (2888751160577/250000000000 : ℝ)*(sp_s2_9) + (368741559491/62500000000 : ℝ)*(sp_s2_12) + (239869691/1000000000000 : ℝ)*(sp_s2_14) + (13012139/125000000000 : ℝ)*(sp_s2_20) + (165767543/1000000000000 : ℝ)*(sp_s2_25) + (5900030719399/1000000000000 : ℝ)*(f.failure) + (180548221703/15625000000 : ℝ)*(f.sum) + (18430503134214203/749942630000000000000000000000 : ℝ)*base62 + (11136983559729/118681250000000000000000000 : ℝ)*base64 + (399536244422383/1678475000000000000000000000 : ℝ)*base66 + (4288339436561/27925000000000000000000000 : ℝ)*base68 + (1112100657898752411/63895136650000000000000000000000 : ℝ)*base71 + (100430043276629/841212500000000000000000000 : ℝ)*base72 + (146175537835961/3356950000000000000000000000 : ℝ)*base74 + (16365177874333/336485000000000000000000000 : ℝ)*base76 + (8308635471219974943/112956332075000000000000000000000 : ℝ)*base78 + (5581/25000000000000000 : ℝ)*base86 + (5581/25000000000000000 : ℝ)*base88 + (5581/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6473/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6473/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (193269047189170240148343/15599398596191406250000000000 : ℝ) := by norm_num
    linear_combination (186188442853/500000000000 : ℝ)*(base49) + (109558466821/100000000000 : ℝ)*(base59) + (2179823034759/1000000000000 : ℝ)*(base60) + (8727269403781/1000000000000 : ℝ)*(major_s2_0) + (8727269403781/1000000000000 : ℝ)*(major_s2_1) + (8727269403781/1000000000000 : ℝ)*(major_s2_2) + (183007869/1000000000000 : ℝ)*(sp_s2_0) + (3531/100000000 : ℝ)*(sp_s2_6) + (31592339/200000000000 : ℝ)*(sp_s2_8) + (11554518374519/1000000000000 : ℝ)*(sp_s2_13) + (5777271710347/500000000000 : ℝ)*(sp_s2_14) + (2888625908059/250000000000 : ℝ)*(sp_s2_15) + (368737374083/62500000000 : ℝ)*(sp_s2_18) + (24718769/125000000000 : ℝ)*(sp_s2_21) + (184369790479/31250000000 : ℝ)*(f.failure) + (11554701382389/1000000000000 : ℝ)*(f.sum) + (443023869409543217/749942630000000000000000000000 : ℝ)*base62 + (243293023169431/474725000000000000000000000 : ℝ)*base65 + (2036560897299507/6713900000000000000000000000 : ℝ)*base67 + (31630440040271/111700000000000000000000000 : ℝ)*base68 + (26512786538556710013/127790273300000000000000000000000 : ℝ)*base71 + (285915004199149/3364850000000000000000000000 : ℝ)*base72 + (3276444871245307/6713900000000000000000000000 : ℝ)*base75 + (620183026006109/1345940000000000000000000000 : ℝ)*base77 + (142553123112475745623/451825328300000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (29/3125000000000000 : ℝ)*base86 + (29/3125000000000000 : ℝ)*base88 + (29/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(411/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(411/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (58400763216593540244135252099891/4289855579544350000000000000000000000 : ℝ) := by norm_num
    linear_combination (220651908153/500000000000 : ℝ)*(base49) + (175346882761/500000000000 : ℝ)*(base60) + (4683847974589/1000000000000 : ℝ)*(major_s2_0) + (4683847974589/1000000000000 : ℝ)*(major_s2_1) + (4683847974589/1000000000000 : ℝ)*(major_s2_2) + (496690981/1000000000000 : ℝ)*(sp_s2_1) + (878997/31250000000 : ℝ)*(sp_s2_2) + (11812843/1000000000000 : ℝ)*(sp_s2_8) + (19056311/1000000000000 : ℝ)*(sp_s2_12) + (17811123/200000000000 : ℝ)*(sp_s2_15) + (775162910399/125000000000 : ℝ)*(sp_s2_19) + (775099347421/125000000000 : ℝ)*(sp_s2_20) + (6201186099673/1000000000000 : ℝ)*(sp_s2_21) + (1583184535887/500000000000 : ℝ)*(sp_s2_25) + (633277625617/200000000000 : ℝ)*(f.failure) + (775162910399/125000000000 : ℝ)*(f.sum) + (1689350328131919/5858926796875000000000000000 : ℝ)*base62 + (4890838479949/118681250000000000000000000 : ℝ)*base64 + (1020189300905643/6713900000000000000000000000 : ℝ)*base67 + (15475072219989/111700000000000000000000000 : ℝ)*base68 + (24828115233884196083/127790273300000000000000000000000 : ℝ)*base70 + (89221753297843/420606250000000000000000000 : ℝ)*base73 + (1979637328639073/6713900000000000000000000000 : ℝ)*base75 + (441631518232229/1345940000000000000000000000 : ℝ)*base77 + (10002095646870946903/451825328300000000000000000000000 : ℝ)*base79 + (2723/5000000000000000 : ℝ)*base86 + (2723/5000000000000000 : ℝ)*base88 + (2723/5000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((67297/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67297/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(67139/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(67139/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18989/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(18989/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((32381/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32381/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6473/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6473/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(411/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(411/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301051_s2 p hpa hpb X hX hprev1

#print axioms solution
