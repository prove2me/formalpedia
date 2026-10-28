-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301045_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:26:12.494695+00:00
-- url     : https://prove2.me/submissions/a58a75dd-4f61-47c2-bb0c-b258d01acd54

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
theorem collision_support_c301045_s1_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8196501/1000000000 : ℝ)*x 0 + (-6963622723/10000000000 : ℝ)*x 1 + (481754683/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8196501/1000000000 : ℝ)^65 ≤ (17075142301/10000000000000 : ℝ)^49 := by
    have hnat : (8196501 : ℕ)^65*10000000000000^49 ≤ 17075142301^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8196501 1000000000 17075142301 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6963622723/10000000000 : ℝ)^65 ≤ (61875130287773/100000000000000 : ℝ)^49 := by
    have hnat : (6963622723 : ℕ)^65*100000000000000^49 ≤ 61875130287773^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6963622723 10000000000 61875130287773 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481754683/1000000000 : ℝ)^65 ≤ (37954118274771/100000000000000 : ℝ)^49 := by
    have hnat : (481754683 : ℕ)^65*100000000000000^49 ≤ 37954118274771^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481754683 1000000000 37954118274771 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8196501/1000000000 : ℝ), (-6963622723/10000000000 : ℝ), (481754683/1000000000 : ℝ)] ![(17075142301/10000000000000 : ℝ), (61875130287773/100000000000000 : ℝ), (37954118274771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8196501/1000000000 : ℝ)|^65 ≤ (17075142301/10000000000000 : ℝ)^49
        have hw : |(8196501/1000000000 : ℝ)|=(8196501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6963622723/10000000000 : ℝ)|^65 ≤ (61875130287773/100000000000000 : ℝ)^49
        have hw : |(-6963622723/10000000000 : ℝ)|=(6963622723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(481754683/1000000000 : ℝ)|^65 ≤ (37954118274771/100000000000000 : ℝ)^49
        have hw : |(481754683/1000000000 : ℝ)|=(481754683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (618751499/1000000000 : ℝ)*x 0 + (-3066923957/10000000000 : ℝ)*x 1 + (-3648739717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (618751499/1000000000 : ℝ)^65 ≤ (826532562923/1562500000000 : ℝ)^49 := by
    have hnat : (618751499 : ℕ)^65*1562500000000^49 ≤ 826532562923^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618751499 1000000000 826532562923 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3066923957/10000000000 : ℝ)^65 ≤ (2606188594953/12500000000000 : ℝ)^49 := by
    have hnat : (3066923957 : ℕ)^65*12500000000000^49 ≤ 2606188594953^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3066923957 10000000000 2606188594953 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3648739717/10000000000 : ℝ)^65 ≤ (26252407196877/100000000000000 : ℝ)^49 := by
    have hnat : (3648739717 : ℕ)^65*100000000000000^49 ≤ 26252407196877^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3648739717 10000000000 26252407196877 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(618751499/1000000000 : ℝ), (-3066923957/10000000000 : ℝ), (-3648739717/10000000000 : ℝ)] ![(826532562923/1562500000000 : ℝ), (2606188594953/12500000000000 : ℝ), (26252407196877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(618751499/1000000000 : ℝ)|^65 ≤ (826532562923/1562500000000 : ℝ)^49
        have hw : |(618751499/1000000000 : ℝ)|=(618751499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3066923957/10000000000 : ℝ)|^65 ≤ (2606188594953/12500000000000 : ℝ)^49
        have hw : |(-3066923957/10000000000 : ℝ)|=(3066923957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3648739717/10000000000 : ℝ)|^65 ≤ (26252407196877/100000000000000 : ℝ)^49
        have hw : |(-3648739717/10000000000 : ℝ)|=(3648739717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5658220159/10000000000 : ℝ)*x 0 + (-250981089/1000000000 : ℝ)*x 1 + (2364809411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5658220159/10000000000 : ℝ)^65 ≤ (46980998091983/100000000000000 : ℝ)^49 := by
    have hnat : (5658220159 : ℕ)^65*100000000000000^49 ≤ 46980998091983^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5658220159 10000000000 46980998091983 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250981089/1000000000 : ℝ)^65 ≤ (799052678521/5000000000000 : ℝ)^49 := by
    have hnat : (250981089 : ℕ)^65*5000000000000^49 ≤ 799052678521^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250981089 1000000000 799052678521 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2364809411/5000000000 : ℝ)^65 ≤ (185189741587/500000000000 : ℝ)^49 := by
    have hnat : (2364809411 : ℕ)^65*500000000000^49 ≤ 185189741587^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364809411 5000000000 185189741587 500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5658220159/10000000000 : ℝ), (-250981089/1000000000 : ℝ), (2364809411/5000000000 : ℝ)] ![(46980998091983/100000000000000 : ℝ), (799052678521/5000000000000 : ℝ), (185189741587/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5658220159/10000000000 : ℝ)|^65 ≤ (46980998091983/100000000000000 : ℝ)^49
        have hw : |(5658220159/10000000000 : ℝ)|=(5658220159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-250981089/1000000000 : ℝ)|^65 ≤ (799052678521/5000000000000 : ℝ)^49
        have hw : |(-250981089/1000000000 : ℝ)|=(250981089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2364809411/5000000000 : ℝ)|^65 ≤ (185189741587/500000000000 : ℝ)^49
        have hw : |(2364809411/5000000000 : ℝ)|=(2364809411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (263672447/10000000000 : ℝ)*x 0 + (-4382998763/5000000000 : ℝ)*x 1 + (2419834507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263672447/10000000000 : ℝ)^65 ≤ (804440737839/100000000000000 : ℝ)^49 := by
    have hnat : (263672447 : ℕ)^65*100000000000000^49 ≤ 804440737839^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263672447 10000000000 804440737839 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4382998763/5000000000 : ℝ)^65 ≤ (83970015142469/100000000000000 : ℝ)^49 := by
    have hnat : (4382998763 : ℕ)^65*100000000000000^49 ≤ 83970015142469^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382998763 5000000000 83970015142469 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2419834507/10000000000 : ℝ)^65 ≤ (761277205101/5000000000000 : ℝ)^49 := by
    have hnat : (2419834507 : ℕ)^65*5000000000000^49 ≤ 761277205101^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2419834507 10000000000 761277205101 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263672447/10000000000 : ℝ), (-4382998763/5000000000 : ℝ), (2419834507/10000000000 : ℝ)] ![(804440737839/100000000000000 : ℝ), (83970015142469/100000000000000 : ℝ), (761277205101/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263672447/10000000000 : ℝ)|^65 ≤ (804440737839/100000000000000 : ℝ)^49
        have hw : |(263672447/10000000000 : ℝ)|=(263672447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4382998763/5000000000 : ℝ)|^65 ≤ (83970015142469/100000000000000 : ℝ)^49
        have hw : |(-4382998763/5000000000 : ℝ)|=(4382998763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2419834507/10000000000 : ℝ)|^65 ≤ (761277205101/5000000000000 : ℝ)^49
        have hw : |(2419834507/10000000000 : ℝ)|=(2419834507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3404687299/10000000000 : ℝ)*x 0 + (1266679269/2500000000 : ℝ)*x 1 + (2288998341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3404687299/10000000000 : ℝ)^65 ≤ (4789786084439/20000000000000 : ℝ)^49 := by
    have hnat : (3404687299 : ℕ)^65*20000000000000^49 ≤ 4789786084439^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3404687299 10000000000 4789786084439 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1266679269/2500000000 : ℝ)^65 ≤ (10144972551757/25000000000000 : ℝ)^49 := by
    have hnat : (1266679269 : ℕ)^65*25000000000000^49 ≤ 10144972551757^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266679269 2500000000 10144972551757 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2288998341/5000000000 : ℝ)^65 ≤ (35471179351993/100000000000000 : ℝ)^49 := by
    have hnat : (2288998341 : ℕ)^65*100000000000000^49 ≤ 35471179351993^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288998341 5000000000 35471179351993 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3404687299/10000000000 : ℝ), (1266679269/2500000000 : ℝ), (2288998341/5000000000 : ℝ)] ![(4789786084439/20000000000000 : ℝ), (10144972551757/25000000000000 : ℝ), (35471179351993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3404687299/10000000000 : ℝ)|^65 ≤ (4789786084439/20000000000000 : ℝ)^49
        have hw : |(3404687299/10000000000 : ℝ)|=(3404687299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1266679269/2500000000 : ℝ)|^65 ≤ (10144972551757/25000000000000 : ℝ)^49
        have hw : |(1266679269/2500000000 : ℝ)|=(1266679269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2288998341/5000000000 : ℝ)|^65 ≤ (35471179351993/100000000000000 : ℝ)^49
        have hw : |(2288998341/5000000000 : ℝ)|=(2288998341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5025055351/10000000000 : ℝ)*x 0 + (-1292296659/5000000000 : ℝ)*x 1 + (-2657860153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5025055351/10000000000 : ℝ)^65 ≤ (39197126631/97656250000 : ℝ)^49 := by
    have hnat : (5025055351 : ℕ)^65*97656250000^49 ≤ 39197126631^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025055351 10000000000 39197126631 97656250000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292296659/5000000000 : ℝ)^65 ≤ (16615762967061/100000000000000 : ℝ)^49 := by
    have hnat : (1292296659 : ℕ)^65*100000000000000^49 ≤ 16615762967061^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292296659 5000000000 16615762967061 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2657860153/5000000000 : ℝ)^65 ≤ (21623189671991/50000000000000 : ℝ)^49 := by
    have hnat : (2657860153 : ℕ)^65*50000000000000^49 ≤ 21623189671991^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2657860153 5000000000 21623189671991 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5025055351/10000000000 : ℝ), (-1292296659/5000000000 : ℝ), (-2657860153/5000000000 : ℝ)] ![(39197126631/97656250000 : ℝ), (16615762967061/100000000000000 : ℝ), (21623189671991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5025055351/10000000000 : ℝ)|^65 ≤ (39197126631/97656250000 : ℝ)^49
        have hw : |(5025055351/10000000000 : ℝ)|=(5025055351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1292296659/5000000000 : ℝ)|^65 ≤ (16615762967061/100000000000000 : ℝ)^49
        have hw : |(-1292296659/5000000000 : ℝ)|=(1292296659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2657860153/5000000000 : ℝ)|^65 ≤ (21623189671991/50000000000000 : ℝ)^49
        have hw : |(-2657860153/5000000000 : ℝ)|=(2657860153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2620163677/5000000000 : ℝ)*x 0 + (-72640657/625000000 : ℝ)*x 1 + (3045652177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620163677/5000000000 : ℝ)^65 ≤ (42434623148461/100000000000000 : ℝ)^49 := by
    have hnat : (2620163677 : ℕ)^65*100000000000000^49 ≤ 42434623148461^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620163677 5000000000 42434623148461 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72640657/625000000 : ℝ)^65 ≤ (5755611875897/100000000000000 : ℝ)^49 := by
    have hnat : (72640657 : ℕ)^65*100000000000000^49 ≤ 5755611875897^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72640657 625000000 5755611875897 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3045652177/5000000000 : ℝ)^65 ≤ (12952441239683/25000000000000 : ℝ)^49 := by
    have hnat : (3045652177 : ℕ)^65*25000000000000^49 ≤ 12952441239683^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3045652177 5000000000 12952441239683 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620163677/5000000000 : ℝ), (-72640657/625000000 : ℝ), (3045652177/5000000000 : ℝ)] ![(42434623148461/100000000000000 : ℝ), (5755611875897/100000000000000 : ℝ), (12952441239683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620163677/5000000000 : ℝ)|^65 ≤ (42434623148461/100000000000000 : ℝ)^49
        have hw : |(2620163677/5000000000 : ℝ)|=(2620163677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-72640657/625000000 : ℝ)|^65 ≤ (5755611875897/100000000000000 : ℝ)^49
        have hw : |(-72640657/625000000 : ℝ)|=(72640657/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3045652177/5000000000 : ℝ)|^65 ≤ (12952441239683/25000000000000 : ℝ)^49
        have hw : |(3045652177/5000000000 : ℝ)|=(3045652177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (64500341/5000000000 : ℝ)*x 0 + (-632366901/1250000000 : ℝ)*x 1 + (67346737/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64500341/5000000000 : ℝ)^65 ≤ (77908073633/25000000000000 : ℝ)^49 := by
    have hnat : (64500341 : ℕ)^65*25000000000000^49 ≤ 77908073633^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64500341 5000000000 77908073633 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (632366901/1250000000 : ℝ)^65 ≤ (20248616912013/50000000000000 : ℝ)^49 := by
    have hnat : (632366901 : ℕ)^65*50000000000000^49 ≤ 20248616912013^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632366901 1250000000 20248616912013 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67346737/100000000 : ℝ)^65 ≤ (59191133874899/100000000000000 : ℝ)^49 := by
    have hnat : (67346737 : ℕ)^65*100000000000000^49 ≤ 59191133874899^49*100000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67346737 100000000 59191133874899 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64500341/5000000000 : ℝ), (-632366901/1250000000 : ℝ), (67346737/100000000 : ℝ)] ![(77908073633/25000000000000 : ℝ), (20248616912013/50000000000000 : ℝ), (59191133874899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64500341/5000000000 : ℝ)|^65 ≤ (77908073633/25000000000000 : ℝ)^49
        have hw : |(64500341/5000000000 : ℝ)|=(64500341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-632366901/1250000000 : ℝ)|^65 ≤ (20248616912013/50000000000000 : ℝ)^49
        have hw : |(-632366901/1250000000 : ℝ)|=(632366901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67346737/100000000 : ℝ)|^65 ≤ (59191133874899/100000000000000 : ℝ)^49
        have hw : |(67346737/100000000 : ℝ)|=(67346737/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3632792029/10000000000 : ℝ)*x 0 + (3452052083/10000000000 : ℝ)*x 1 + (5886144399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3632792029/10000000000 : ℝ)^65 ≤ (326253832443/1250000000000 : ℝ)^49 := by
    have hnat : (3632792029 : ℕ)^65*1250000000000^49 ≤ 326253832443^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3632792029 10000000000 326253832443 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3452052083/10000000000 : ℝ)^65 ≤ (12195944931839/50000000000000 : ℝ)^49 := by
    have hnat : (3452052083 : ℕ)^65*50000000000000^49 ≤ 12195944931839^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3452052083 10000000000 12195944931839 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5886144399/10000000000 : ℝ)^65 ≤ (4950780353047/10000000000000 : ℝ)^49 := by
    have hnat : (5886144399 : ℕ)^65*10000000000000^49 ≤ 4950780353047^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5886144399 10000000000 4950780353047 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3632792029/10000000000 : ℝ), (3452052083/10000000000 : ℝ), (5886144399/10000000000 : ℝ)] ![(326253832443/1250000000000 : ℝ), (12195944931839/50000000000000 : ℝ), (4950780353047/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3632792029/10000000000 : ℝ)|^65 ≤ (326253832443/1250000000000 : ℝ)^49
        have hw : |(3632792029/10000000000 : ℝ)|=(3632792029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3452052083/10000000000 : ℝ)|^65 ≤ (12195944931839/50000000000000 : ℝ)^49
        have hw : |(3452052083/10000000000 : ℝ)|=(3452052083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5886144399/10000000000 : ℝ)|^65 ≤ (4950780353047/10000000000000 : ℝ)^49
        have hw : |(5886144399/10000000000 : ℝ)|=(5886144399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (319617847/400000000 : ℝ)*x 0 + (-301368057/2000000000 : ℝ)*x 1 + (-1350588173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (319617847/400000000 : ℝ)^65 ≤ (74260435063879/100000000000000 : ℝ)^49 := by
    have hnat : (319617847 : ℕ)^65*100000000000000^49 ≤ 74260435063879^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319617847 400000000 74260435063879 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301368057/2000000000 : ℝ)^65 ≤ (4061168544217/50000000000000 : ℝ)^49 := by
    have hnat : (301368057 : ℕ)^65*50000000000000^49 ≤ 4061168544217^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301368057 2000000000 4061168544217 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350588173/5000000000 : ℝ)^65 ≤ (2202153478853/12500000000000 : ℝ)^49 := by
    have hnat : (1350588173 : ℕ)^65*12500000000000^49 ≤ 2202153478853^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350588173 5000000000 2202153478853 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(319617847/400000000 : ℝ), (-301368057/2000000000 : ℝ), (-1350588173/5000000000 : ℝ)] ![(74260435063879/100000000000000 : ℝ), (4061168544217/50000000000000 : ℝ), (2202153478853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(319617847/400000000 : ℝ)|^65 ≤ (74260435063879/100000000000000 : ℝ)^49
        have hw : |(319617847/400000000 : ℝ)|=(319617847/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-301368057/2000000000 : ℝ)|^65 ≤ (4061168544217/50000000000000 : ℝ)^49
        have hw : |(-301368057/2000000000 : ℝ)|=(301368057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1350588173/5000000000 : ℝ)|^65 ≤ (2202153478853/12500000000000 : ℝ)^49
        have hw : |(-1350588173/5000000000 : ℝ)|=(1350588173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (884501637/1250000000 : ℝ)*x 0 + (-2049542759/10000000000 : ℝ)*x 1 + (3472283759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (884501637/1250000000 : ℝ)^65 ≤ (63203338171761/100000000000000 : ℝ)^49 := by
    have hnat : (884501637 : ℕ)^65*100000000000000^49 ≤ 63203338171761^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884501637 1250000000 63203338171761 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2049542759/10000000000 : ℝ)^65 ≤ (38171738353/312500000000 : ℝ)^49 := by
    have hnat : (2049542759 : ℕ)^65*312500000000^49 ≤ 38171738353^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049542759 10000000000 38171738353 312500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3472283759/10000000000 : ℝ)^65 ≤ (6145426383651/25000000000000 : ℝ)^49 := by
    have hnat : (3472283759 : ℕ)^65*25000000000000^49 ≤ 6145426383651^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3472283759 10000000000 6145426383651 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(884501637/1250000000 : ℝ), (-2049542759/10000000000 : ℝ), (3472283759/10000000000 : ℝ)] ![(63203338171761/100000000000000 : ℝ), (38171738353/312500000000 : ℝ), (6145426383651/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(884501637/1250000000 : ℝ)|^65 ≤ (63203338171761/100000000000000 : ℝ)^49
        have hw : |(884501637/1250000000 : ℝ)|=(884501637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2049542759/10000000000 : ℝ)|^65 ≤ (38171738353/312500000000 : ℝ)^49
        have hw : |(-2049542759/10000000000 : ℝ)|=(2049542759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3472283759/10000000000 : ℝ)|^65 ≤ (6145426383651/25000000000000 : ℝ)^49
        have hw : |(3472283759/10000000000 : ℝ)|=(3472283759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (43772841/5000000000 : ℝ)*x 0 + (-2237840267/2500000000 : ℝ)*x 1 + (2207616947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43772841/5000000000 : ℝ)^65 ≤ (186342267959/100000000000000 : ℝ)^49 := by
    have hnat : (43772841 : ℕ)^65*100000000000000^49 ≤ 186342267959^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43772841 5000000000 186342267959 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237840267/2500000000 : ℝ)^65 ≤ (21583376891521/25000000000000 : ℝ)^49 := by
    have hnat : (2237840267 : ℕ)^65*25000000000000^49 ≤ 21583376891521^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237840267 2500000000 21583376891521 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207616947/10000000000 : ℝ)^65 ≤ (3370037537823/25000000000000 : ℝ)^49 := by
    have hnat : (2207616947 : ℕ)^65*25000000000000^49 ≤ 3370037537823^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207616947 10000000000 3370037537823 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43772841/5000000000 : ℝ), (-2237840267/2500000000 : ℝ), (2207616947/10000000000 : ℝ)] ![(186342267959/100000000000000 : ℝ), (21583376891521/25000000000000 : ℝ), (3370037537823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43772841/5000000000 : ℝ)|^65 ≤ (186342267959/100000000000000 : ℝ)^49
        have hw : |(43772841/5000000000 : ℝ)|=(43772841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2237840267/2500000000 : ℝ)|^65 ≤ (21583376891521/25000000000000 : ℝ)^49
        have hw : |(-2237840267/2500000000 : ℝ)|=(2237840267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2207616947/10000000000 : ℝ)|^65 ≤ (3370037537823/25000000000000 : ℝ)^49
        have hw : |(2207616947/10000000000 : ℝ)|=(2207616947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3932950083/5000000000 : ℝ)*x 0 + (2304932037/10000000000 : ℝ)*x 1 + (2147709581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3932950083/5000000000 : ℝ)^65 ≤ (72728913734427/100000000000000 : ℝ)^49 := by
    have hnat : (3932950083 : ℕ)^65*100000000000000^49 ≤ 72728913734427^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3932950083 5000000000 72728913734427 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2304932037/10000000000 : ℝ)^65 ≤ (3568506565733/25000000000000 : ℝ)^49 := by
    have hnat : (2304932037 : ℕ)^65*25000000000000^49 ≤ 3568506565733^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2304932037 10000000000 3568506565733 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2147709581/10000000000 : ℝ)^65 ≤ (6498529993147/50000000000000 : ℝ)^49 := by
    have hnat : (2147709581 : ℕ)^65*50000000000000^49 ≤ 6498529993147^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147709581 10000000000 6498529993147 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3932950083/5000000000 : ℝ), (2304932037/10000000000 : ℝ), (2147709581/10000000000 : ℝ)] ![(72728913734427/100000000000000 : ℝ), (3568506565733/25000000000000 : ℝ), (6498529993147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3932950083/5000000000 : ℝ)|^65 ≤ (72728913734427/100000000000000 : ℝ)^49
        have hw : |(3932950083/5000000000 : ℝ)|=(3932950083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2304932037/10000000000 : ℝ)|^65 ≤ (3568506565733/25000000000000 : ℝ)^49
        have hw : |(2304932037/10000000000 : ℝ)|=(2304932037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2147709581/10000000000 : ℝ)|^65 ≤ (6498529993147/50000000000000 : ℝ)^49
        have hw : |(2147709581/10000000000 : ℝ)|=(2147709581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1027119349/2500000000 : ℝ)*x 0 + (-610141049/1250000000 : ℝ)*x 1 + (-2050394763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027119349/2500000000 : ℝ)^65 ≤ (6145622586661/20000000000000 : ℝ)^49 := by
    have hnat : (1027119349 : ℕ)^65*20000000000000^49 ≤ 6145622586661^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027119349 2500000000 6145622586661 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610141049/1250000000 : ℝ)^65 ≤ (38620025111759/100000000000000 : ℝ)^49 := by
    have hnat : (610141049 : ℕ)^65*100000000000000^49 ≤ 38620025111759^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610141049 1250000000 38620025111759 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2050394763/5000000000 : ℝ)^65 ≤ (1532593096693/5000000000000 : ℝ)^49 := by
    have hnat : (2050394763 : ℕ)^65*5000000000000^49 ≤ 1532593096693^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050394763 5000000000 1532593096693 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1027119349/2500000000 : ℝ), (-610141049/1250000000 : ℝ), (-2050394763/5000000000 : ℝ)] ![(6145622586661/20000000000000 : ℝ), (38620025111759/100000000000000 : ℝ), (1532593096693/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1027119349/2500000000 : ℝ)|^65 ≤ (6145622586661/20000000000000 : ℝ)^49
        have hw : |(1027119349/2500000000 : ℝ)|=(1027119349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-610141049/1250000000 : ℝ)|^65 ≤ (38620025111759/100000000000000 : ℝ)^49
        have hw : |(-610141049/1250000000 : ℝ)|=(610141049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2050394763/5000000000 : ℝ)|^65 ≤ (1532593096693/5000000000000 : ℝ)^49
        have hw : |(-2050394763/5000000000 : ℝ)|=(2050394763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301045_s1_s1_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3767459319/5000000000 : ℝ)*x 0 + (-1320666163/10000000000 : ℝ)*x 1 + (1730923499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3767459319/5000000000 : ℝ)^65 ≤ (34348751874031/50000000000000 : ℝ)^49 := by
    have hnat : (3767459319 : ℕ)^65*50000000000000^49 ≤ 34348751874031^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3767459319 5000000000 34348751874031 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320666163/10000000000 : ℝ)^65 ≤ (3409377351407/50000000000000 : ℝ)^49 := by
    have hnat : (1320666163 : ℕ)^65*50000000000000^49 ≤ 3409377351407^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320666163 10000000000 3409377351407 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1730923499/5000000000 : ℝ)^65 ≤ (12241870768471/50000000000000 : ℝ)^49 := by
    have hnat : (1730923499 : ℕ)^65*50000000000000^49 ≤ 12241870768471^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730923499 5000000000 12241870768471 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3767459319/5000000000 : ℝ), (-1320666163/10000000000 : ℝ), (1730923499/5000000000 : ℝ)] ![(34348751874031/50000000000000 : ℝ), (3409377351407/50000000000000 : ℝ), (12241870768471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3767459319/5000000000 : ℝ)|^65 ≤ (34348751874031/50000000000000 : ℝ)^49
        have hw : |(3767459319/5000000000 : ℝ)|=(3767459319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1320666163/10000000000 : ℝ)|^65 ≤ (3409377351407/50000000000000 : ℝ)^49
        have hw : |(-1320666163/10000000000 : ℝ)|=(1320666163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1730923499/5000000000 : ℝ)|^65 ≤ (12241870768471/50000000000000 : ℝ)^49
        have hw : |(1730923499/5000000000 : ℝ)|=(1730923499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301045_s1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((727/800 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(727/800 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-83911/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-83911/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48183/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48183/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((63451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-35371/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-35371/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2746/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2746/3125 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (727/800 : ℝ) ^ (129/32 : ℝ) ≤ (67995329662510464749/100000000000000000000 : ℝ) := by
    have hpowers : (727/800 : ℝ)^129 ≤ (67995329662510464749/100000000000000000000 : ℝ)^32 := by
      have hnat : (727 : ℕ)^129*100000000000000000000^32 ≤ 67995329662510464749^32*800^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        727 800 67995329662510464749 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (727/800 : ℝ)) (X := (67995329662510464749/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (167995329662510464749/100000000000000000000 : ℝ) ≤ (5686665511912683/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (167995329662510464749/100000000000000000000 : ℝ)^32 ≤ (5686665511912683/5000000000000000 : ℝ)^129 := by
      have hnat : (167995329662510464749 : ℕ)^32*5000000000000000^129 ≤ 5686665511912683^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        167995329662510464749 100000000000000000000 5686665511912683 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5686665511912683/5000000000000000 : ℝ)) (X := (167995329662510464749/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (117995329662510464749/50000000000000000000 : ℝ) ≤ (309343537580853/250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (117995329662510464749/50000000000000000000 : ℝ)^32 ≤ (309343537580853/250000000000000 : ℝ)^129 := by
      have hnat : (117995329662510464749 : ℕ)^32*250000000000000^129 ≤ 309343537580853^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117995329662510464749 50000000000000000000 309343537580853 250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (309343537580853/250000000000000 : ℝ)) (X := (117995329662510464749/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(686665511912683/4543750000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(500205239704377/4543750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (727/800 : ℝ)) (alpha := (686665511912683/4543750000000000 : ℝ)) (beta := (500205239704377/4543750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (727/800 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(686665511912683/4543750000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(500205239704377/4543750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (83911/100000 : ℝ) ^ (129/32 : ℝ) ≤ (24652725043785470487/50000000000000000000 : ℝ) := by
    have hpowers : (83911/100000 : ℝ)^129 ≤ (24652725043785470487/50000000000000000000 : ℝ)^32 := by
      have hnat : (83911 : ℕ)^129*50000000000000000000^32 ≤ 24652725043785470487^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83911 100000 24652725043785470487 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83911/100000 : ℝ)) (X := (24652725043785470487/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (74652725043785470487/50000000000000000000 : ℝ) ≤ (11045402828675239/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (74652725043785470487/50000000000000000000 : ℝ)^32 ≤ (11045402828675239/10000000000000000 : ℝ)^129 := by
      have hnat : (74652725043785470487 : ℕ)^32*10000000000000000^129 ≤ 11045402828675239^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74652725043785470487 50000000000000000000 11045402828675239 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11045402828675239/10000000000000000 : ℝ)) (X := (74652725043785470487/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (49652725043785470487/25000000000000000000 : ℝ) ≤ (2963897997115587/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (49652725043785470487/25000000000000000000 : ℝ)^32 ≤ (2963897997115587/2500000000000000 : ℝ)^129 := by
      have hnat : (49652725043785470487 : ℕ)^32*2500000000000000^129 ≤ 2963897997115587^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        49652725043785470487 25000000000000000000 2963897997115587 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2963897997115587/2500000000000000 : ℝ)) (X := (49652725043785470487/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1045402828675239/8391100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(810189159787109/8391100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (83911/100000 : ℝ)) (alpha := (1045402828675239/8391100000000000 : ℝ)) (beta := (810189159787109/8391100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (83911/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1045402828675239/8391100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(810189159787109/8391100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (48183/50000 : ℝ) ^ (129/32 : ℝ) ≤ (43068818106721871467/50000000000000000000 : ℝ) := by
    have hpowers : (48183/50000 : ℝ)^129 ≤ (43068818106721871467/50000000000000000000 : ℝ)^32 := by
      have hnat : (48183 : ℕ)^129*50000000000000000000^32 ≤ 43068818106721871467^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48183 50000 43068818106721871467 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48183/50000 : ℝ)) (X := (43068818106721871467/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (93068818106721871467/50000000000000000000 : ℝ) ≤ (11666366457462959/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (93068818106721871467/50000000000000000000 : ℝ)^32 ≤ (11666366457462959/10000000000000000 : ℝ)^129 := by
      have hnat : (93068818106721871467 : ℕ)^32*10000000000000000^129 ≤ 11666366457462959^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93068818106721871467 50000000000000000000 11666366457462959 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11666366457462959/10000000000000000 : ℝ)) (X := (93068818106721871467/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (68068818106721871467/25000000000000000000 : ℝ) ≤ (801288718942257/625000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (68068818106721871467/25000000000000000000 : ℝ)^32 ≤ (801288718942257/625000000000000 : ℝ)^129 := by
      have hnat : (68068818106721871467 : ℕ)^32*625000000000000^129 ≤ 801288718942257^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68068818106721871467 25000000000000000000 801288718942257 625000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (801288718942257/625000000000000 : ℝ)) (X := (68068818106721871467/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1666366457462959/9636600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1154253045613153/9636600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (48183/50000 : ℝ)) (alpha := (1666366457462959/9636600000000000 : ℝ)) (beta := (1154253045613153/9636600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (48183/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1666366457462959/9636600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1154253045613153/9636600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((8196501/1000000000 : ℝ)*X 0 0+(-6963622723/10000000000 : ℝ)*X 0 1+(481754683/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((618751499/1000000000 : ℝ)*X 2 0+(-3066923957/10000000000 : ℝ)*X 2 1+(-3648739717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5658220159/10000000000 : ℝ)*X 0 0+(-250981089/1000000000 : ℝ)*X 0 1+(2364809411/5000000000 : ℝ)*X 0 2+(5658220159/10000000000 : ℝ)*X 1 0+(-250981089/1000000000 : ℝ)*X 1 1+(2364809411/5000000000 : ℝ)*X 1 2+(5658220159/10000000000 : ℝ)*X 2 0+(-250981089/1000000000 : ℝ)*X 2 1+(2364809411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((263672447/10000000000 : ℝ)*X 0 0+(-4382998763/5000000000 : ℝ)*X 0 1+(2419834507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3404687299/10000000000 : ℝ)*X 1 0+(1266679269/2500000000 : ℝ)*X 1 1+(2288998341/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5025055351/10000000000 : ℝ)*X 2 0+(-1292296659/5000000000 : ℝ)*X 2 1+(-2657860153/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2620163677/5000000000 : ℝ)*X 0 0+(-72640657/625000000 : ℝ)*X 0 1+(3045652177/5000000000 : ℝ)*X 0 2+(2620163677/5000000000 : ℝ)*X 1 0+(-72640657/625000000 : ℝ)*X 1 1+(3045652177/5000000000 : ℝ)*X 1 2+(2620163677/5000000000 : ℝ)*X 2 0+(-72640657/625000000 : ℝ)*X 2 1+(3045652177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((64500341/5000000000 : ℝ)*X 0 0+(-632366901/1250000000 : ℝ)*X 0 1+(67346737/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3632792029/10000000000 : ℝ)*X 1 0+(3452052083/10000000000 : ℝ)*X 1 1+(5886144399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((319617847/400000000 : ℝ)*X 2 0+(-301368057/2000000000 : ℝ)*X 2 1+(-1350588173/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((884501637/1250000000 : ℝ)*X 0 0+(-2049542759/10000000000 : ℝ)*X 0 1+(3472283759/10000000000 : ℝ)*X 0 2+(884501637/1250000000 : ℝ)*X 1 0+(-2049542759/10000000000 : ℝ)*X 1 1+(3472283759/10000000000 : ℝ)*X 1 2+(884501637/1250000000 : ℝ)*X 2 0+(-2049542759/10000000000 : ℝ)*X 2 1+(3472283759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((43772841/5000000000 : ℝ)*X 0 0+(-2237840267/2500000000 : ℝ)*X 0 1+(2207616947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3932950083/5000000000 : ℝ)*X 1 0+(2304932037/10000000000 : ℝ)*X 1 1+(2147709581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1027119349/2500000000 : ℝ)*X 2 0+(-610141049/1250000000 : ℝ)*X 2 1+(-2050394763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3767459319/5000000000 : ℝ)*X 0 0+(-1320666163/10000000000 : ℝ)*X 0 1+(1730923499/5000000000 : ℝ)*X 0 2+(3767459319/5000000000 : ℝ)*X 1 0+(-1320666163/10000000000 : ℝ)*X 1 1+(1730923499/5000000000 : ℝ)*X 1 2+(3767459319/5000000000 : ℝ)*X 2 0+(-1320666163/10000000000 : ℝ)*X 2 1+(1730923499/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301045_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((63451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (31415520510685979737362023021451/6123587206981250000000000000000000000 : ℝ) := by norm_num
    linear_combination (80010296413/125000000000 : ℝ)*(base7) + (533245186437/1000000000000 : ℝ)*(base50) + (7345759/500000000000 : ℝ)*(base54) + (70987585321/31250000000 : ℝ)*(major_s1_0) + (70987585321/31250000000 : ℝ)*(major_s1_1) + (1135794019377/500000000000 : ℝ)*(major_s1_2) + (10006719/500000000000 : ℝ)*(sp_s1_0) + (55713093/1000000000000 : ℝ)*(sp_s1_2) + (16498609/500000000000 : ℝ)*(sp_s1_6) + (2613276111847/1000000000000 : ℝ)*(sp_s1_7) + (1306648062643/500000000000 : ℝ)*(sp_s1_8) + (2613210479877/1000000000000 : ℝ)*(sp_s1_9) + (435137994391/200000000000 : ℝ)*(sp_s1_13) + (7620399/500000000000 : ℝ)*(sp_s1_23) + (767827644693/500000000000 : ℝ)*(f.failure) + (1306648062643/500000000000 : ℝ)*(f.sum) + (89021787665930913531/134769457100000000000000000000000 : ℝ)*base62 + (947749159517867/1606100000000000000000000000 : ℝ)*base64 + (1371869480811399/4195550000000000000000000000 : ℝ)*base67 + (259884562627879/1606100000000000000000000000 : ℝ)*base68 + (2428296414240883953/145954337500000000000000000000000 : ℝ)*base70 + (1221786432220353/2271875000000000000000000000 : ℝ)*base72 + (1621852172349031/4195550000000000000000000000 : ℝ)*base74 + (703122666072099/4543750000000000000000000000 : ℝ)*base76 + (104241611572784406709/381270606250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (8167/12500000000000000 : ℝ)*base86 + (8167/12500000000000000 : ℝ)*base88 + (8167/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-35371/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-35371/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (57528961576885021581802899/7297716875000000000000000000000 : ℝ) := by norm_num
    linear_combination (174213093077/200000000000 : ℝ)*(base7) + (202852495349/1000000000000 : ℝ)*(base40) + (7041477/1000000000000 : ℝ)*(base53) + (2812327/1000000000000 : ℝ)*(base60) + (394638604413/200000000000 : ℝ)*(major_s1_0) + (394638604413/200000000000 : ℝ)*(major_s1_1) + (493296495147/250000000000 : ℝ)*(major_s1_2) + (257823/100000000000 : ℝ)*(sp_s1_0) + (2075926217779/1000000000000 : ℝ)*(sp_s1_14) + (1037963006431/500000000000 : ℝ)*(sp_s1_15) + (1037967918743/500000000000 : ℝ)*(sp_s1_16) + (551223981339/250000000000 : ℝ)*(sp_s1_20) + (1391573/500000000000 : ℝ)*(sp_s1_22) + (46528101/500000000000 : ℝ)*(sp_s1_27) + (666961758087/500000000000 : ℝ)*(f.failure) + (1037967918743/500000000000 : ℝ)*(f.sum) + (91826335754414032937/134769457100000000000000000000000 : ℝ)*base63 + (692857330773363/803050000000000000000000000 : ℝ)*base65 + (74922125043983/1678220000000000000000000000 : ℝ)*base66 + (629701407582761/803050000000000000000000000 : ℝ)*base69 + (64232935428512453/7297716875000000000000000000000 : ℝ)*base70 + (493642877362201/908750000000000000000000000 : ℝ)*base73 + (163303995250137/1678220000000000000000000000 : ℝ)*base74 + (32915288494921/908750000000000000000000000 : ℝ)*base76 + (63795060576651901097/152508242500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (2847/12500000000000000 : ℝ)*base87 + (2847/12500000000000000 : ℝ)*base89 + (2847/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2746/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2746/3125 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (96592826020277792322641991115213/6123587206981250000000000000000000000 : ℝ) := by norm_num
    linear_combination (865321080717/1000000000000 : ℝ)*(base7) + (5502126793/40000000000 : ℝ)*(base40) + (465873152759/1000000000000 : ℝ)*(base43) + (31004087873/200000000000 : ℝ)*(base50) + (1015169204257/500000000000 : ℝ)*(major_s1_0) + (312893051151/200000000000 : ℝ)*(major_s1_1) + (1015169204257/500000000000 : ℝ)*(major_s1_2) + (12833659/1000000000000 : ℝ)*(sp_s1_0) + (43806769/500000000000 : ℝ)*(sp_s1_2) + (170016259/500000000000 : ℝ)*(sp_s1_7) + (1688904572049/1000000000000 : ℝ)*(sp_s1_21) + (431026118197/200000000000 : ℝ)*(sp_s1_22) + (1689169824689/1000000000000 : ℝ)*(sp_s1_23) + (559469045583/250000000000 : ℝ)*(sp_s1_27) + (85784693851/62500000000 : ℝ)*(f.failure) + (431026118197/200000000000 : ℝ)*(f.sum) + (13824857213587225633/25269273206250000000000000000000 : ℝ)*base63 + (122971587749731/4818300000000000000000000000 : ℝ)*base64 + (210610734273911/1678220000000000000000000000 : ℝ)*base66 + (1126646811729883/4818300000000000000000000000 : ℝ)*base69 + (65408323313963770567/437863012500000000000000000000000 : ℝ)*base71 + (91676436448903/4543750000000000000000000000 : ℝ)*base73 + (527904662863929/1678220000000000000000000000 : ℝ)*base75 + (23779135145229/35498046875000000000000000 : ℝ)*base77 + (300485037079863436359/762541212500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (353/781250000000000 : ℝ)*base87 + (353/781250000000000 : ℝ)*base89 + (353/781250000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((727/800 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(727/800 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-83911/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-83911/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48183/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48183/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((63451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-35371/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-35371/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2746/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2746/3125 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301045_s1 p hpa hpb X hX hprev0

#print axioms solution
