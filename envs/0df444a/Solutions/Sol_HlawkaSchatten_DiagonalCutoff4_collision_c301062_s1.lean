-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:39:00.211087+00:00
-- url     : https://prove2.me/submissions/c888b033-e45c-47c5-bf55-a923f4e7efd2

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
theorem collision_support_c301062_s1_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-19548933/200000000 : ℝ)*x 0 + (5024470951/10000000000 : ℝ)*x 1 + (-6397625727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19548933/200000000 : ℝ)^65 ≤ (4574330418489/100000000000000 : ℝ)^49 := by
    have hnat : (19548933 : ℕ)^65*100000000000000^49 ≤ 4574330418489^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19548933 200000000 4574330418489 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5024470951/10000000000 : ℝ)^65 ≤ (10032916411731/25000000000000 : ℝ)^49 := by
    have hnat : (5024470951 : ℕ)^65*25000000000000^49 ≤ 10032916411731^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024470951 10000000000 10032916411731 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6397625727/10000000000 : ℝ)^65 ≤ (11058800786461/20000000000000 : ℝ)^49 := by
    have hnat : (6397625727 : ℕ)^65*20000000000000^49 ≤ 11058800786461^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6397625727 10000000000 11058800786461 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19548933/200000000 : ℝ), (5024470951/10000000000 : ℝ), (-6397625727/10000000000 : ℝ)] ![(4574330418489/100000000000000 : ℝ), (10032916411731/25000000000000 : ℝ), (11058800786461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19548933/200000000 : ℝ)|^65 ≤ (4574330418489/100000000000000 : ℝ)^49
        have hw : |(-19548933/200000000 : ℝ)|=(19548933/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5024470951/10000000000 : ℝ)|^65 ≤ (10032916411731/25000000000000 : ℝ)^49
        have hw : |(5024470951/10000000000 : ℝ)|=(5024470951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6397625727/10000000000 : ℝ)|^65 ≤ (11058800786461/20000000000000 : ℝ)^49
        have hw : |(-6397625727/10000000000 : ℝ)|=(6397625727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1261522461/2500000000 : ℝ)*x 0 + (-19315411/200000000 : ℝ)*x 1 + (-6383937951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1261522461/2500000000 : ℝ)^65 ≤ (40360885515161/100000000000000 : ℝ)^49 := by
    have hnat : (1261522461 : ℕ)^65*100000000000000^49 ≤ 40360885515161^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261522461 2500000000 40360885515161 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19315411/200000000 : ℝ)^65 ≤ (1125496732861/25000000000000 : ℝ)^49 := by
    have hnat : (19315411 : ℕ)^65*25000000000000^49 ≤ 1125496732861^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19315411 200000000 1125496732861 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6383937951/10000000000 : ℝ)^65 ≤ (6892140943379/12500000000000 : ℝ)^49 := by
    have hnat : (6383937951 : ℕ)^65*12500000000000^49 ≤ 6892140943379^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6383937951 10000000000 6892140943379 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1261522461/2500000000 : ℝ), (-19315411/200000000 : ℝ), (-6383937951/10000000000 : ℝ)] ![(40360885515161/100000000000000 : ℝ), (1125496732861/25000000000000 : ℝ), (6892140943379/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1261522461/2500000000 : ℝ)|^65 ≤ (40360885515161/100000000000000 : ℝ)^49
        have hw : |(1261522461/2500000000 : ℝ)|=(1261522461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19315411/200000000 : ℝ)|^65 ≤ (1125496732861/25000000000000 : ℝ)^49
        have hw : |(-19315411/200000000 : ℝ)|=(19315411/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6383937951/10000000000 : ℝ)|^65 ≤ (6892140943379/12500000000000 : ℝ)^49
        have hw : |(-6383937951/10000000000 : ℝ)|=(6383937951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5352268367/10000000000 : ℝ)*x 0 + (2795587383/5000000000 : ℝ)*x 1 + (888915117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352268367/10000000000 : ℝ)^65 ≤ (43641250792609/100000000000000 : ℝ)^49 := by
    have hnat : (5352268367 : ℕ)^65*100000000000000^49 ≤ 43641250792609^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352268367 10000000000 43641250792609 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2795587383/5000000000 : ℝ)^65 ≤ (578049596597/1250000000000 : ℝ)^49 := by
    have hnat : (2795587383 : ℕ)^65*1250000000000^49 ≤ 578049596597^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2795587383 5000000000 578049596597 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888915117/5000000000 : ℝ)^65 ≤ (5057390731261/50000000000000 : ℝ)^49 := by
    have hnat : (888915117 : ℕ)^65*50000000000000^49 ≤ 5057390731261^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888915117 5000000000 5057390731261 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352268367/10000000000 : ℝ), (2795587383/5000000000 : ℝ), (888915117/5000000000 : ℝ)] ![(43641250792609/100000000000000 : ℝ), (578049596597/1250000000000 : ℝ), (5057390731261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352268367/10000000000 : ℝ)|^65 ≤ (43641250792609/100000000000000 : ℝ)^49
        have hw : |(5352268367/10000000000 : ℝ)|=(5352268367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2795587383/5000000000 : ℝ)|^65 ≤ (578049596597/1250000000000 : ℝ)^49
        have hw : |(2795587383/5000000000 : ℝ)|=(2795587383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(888915117/5000000000 : ℝ)|^65 ≤ (5057390731261/50000000000000 : ℝ)^49
        have hw : |(888915117/5000000000 : ℝ)|=(888915117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-932449313/10000000000 : ℝ)*x 0 + (37952787/200000000 : ℝ)*x 1 + (-8821349271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (932449313/10000000000 : ℝ)^65 ≤ (2148554301203/50000000000000 : ℝ)^49 := by
    have hnat : (932449313 : ℕ)^65*50000000000000^49 ≤ 2148554301203^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932449313 10000000000 2148554301203 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37952787/200000000 : ℝ)^65 ≤ (1102880219579/10000000000000 : ℝ)^49 := by
    have hnat : (37952787 : ℕ)^65*10000000000000^49 ≤ 1102880219579^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37952787 200000000 1102880219579 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8821349271/10000000000 : ℝ)^65 ≤ (84674089195967/100000000000000 : ℝ)^49 := by
    have hnat : (8821349271 : ℕ)^65*100000000000000^49 ≤ 84674089195967^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8821349271 10000000000 84674089195967 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-932449313/10000000000 : ℝ), (37952787/200000000 : ℝ), (-8821349271/10000000000 : ℝ)] ![(2148554301203/50000000000000 : ℝ), (1102880219579/10000000000000 : ℝ), (84674089195967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-932449313/10000000000 : ℝ)|^65 ≤ (2148554301203/50000000000000 : ℝ)^49
        have hw : |(-932449313/10000000000 : ℝ)|=(932449313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(37952787/200000000 : ℝ)|^65 ≤ (1102880219579/10000000000000 : ℝ)^49
        have hw : |(37952787/200000000 : ℝ)|=(37952787/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8821349271/10000000000 : ℝ)|^65 ≤ (84674089195967/100000000000000 : ℝ)^49
        have hw : |(-8821349271/10000000000 : ℝ)|=(8821349271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2113666919/10000000000 : ℝ)*x 0 + (-682596779/10000000000 : ℝ)*x 1 + (-1760504239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113666919/10000000000 : ℝ)^65 ≤ (12724488156899/100000000000000 : ℝ)^49 := by
    have hnat : (2113666919 : ℕ)^65*100000000000000^49 ≤ 12724488156899^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113666919 10000000000 12724488156899 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682596779/10000000000 : ℝ)^65 ≤ (1420539036667/50000000000000 : ℝ)^49 := by
    have hnat : (682596779 : ℕ)^65*50000000000000^49 ≤ 1420539036667^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682596779 10000000000 1420539036667 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1760504239/2000000000 : ℝ)^65 ≤ (42217216876237/50000000000000 : ℝ)^49 := by
    have hnat : (1760504239 : ℕ)^65*50000000000000^49 ≤ 42217216876237^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760504239 2000000000 42217216876237 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2113666919/10000000000 : ℝ), (-682596779/10000000000 : ℝ), (-1760504239/2000000000 : ℝ)] ![(12724488156899/100000000000000 : ℝ), (1420539036667/50000000000000 : ℝ), (42217216876237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2113666919/10000000000 : ℝ)|^65 ≤ (12724488156899/100000000000000 : ℝ)^49
        have hw : |(2113666919/10000000000 : ℝ)|=(2113666919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-682596779/10000000000 : ℝ)|^65 ≤ (1420539036667/50000000000000 : ℝ)^49
        have hw : |(-682596779/10000000000 : ℝ)|=(682596779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1760504239/2000000000 : ℝ)|^65 ≤ (42217216876237/50000000000000 : ℝ)^49
        have hw : |(-1760504239/2000000000 : ℝ)|=(1760504239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2358833991/10000000000 : ℝ)*x 0 + (3878972471/5000000000 : ℝ)*x 1 + (90241199/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2358833991/10000000000 : ℝ)^65 ≤ (3679627675217/25000000000000 : ℝ)^49 := by
    have hnat : (2358833991 : ℕ)^65*25000000000000^49 ≤ 3679627675217^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2358833991 10000000000 3679627675217 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3878972471/5000000000 : ℝ)^65 ≤ (71407793450867/100000000000000 : ℝ)^49 := by
    have hnat : (3878972471 : ℕ)^65*100000000000000^49 ≤ 71407793450867^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3878972471 5000000000 71407793450867 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90241199/400000000 : ℝ)^65 ≤ (13873695830779/100000000000000 : ℝ)^49 := by
    have hnat : (90241199 : ℕ)^65*100000000000000^49 ≤ 13873695830779^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90241199 400000000 13873695830779 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2358833991/10000000000 : ℝ), (3878972471/5000000000 : ℝ), (90241199/400000000 : ℝ)] ![(3679627675217/25000000000000 : ℝ), (71407793450867/100000000000000 : ℝ), (13873695830779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2358833991/10000000000 : ℝ)|^65 ≤ (3679627675217/25000000000000 : ℝ)^49
        have hw : |(2358833991/10000000000 : ℝ)|=(2358833991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3878972471/5000000000 : ℝ)|^65 ≤ (71407793450867/100000000000000 : ℝ)^49
        have hw : |(3878972471/5000000000 : ℝ)|=(3878972471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90241199/400000000 : ℝ)|^65 ≤ (13873695830779/100000000000000 : ℝ)^49
        have hw : |(90241199/400000000 : ℝ)|=(90241199/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3516275989/10000000000 : ℝ)*x 0 + (31448087/39062500 : ℝ)*x 1 + (35929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3516275989/10000000000 : ℝ)^65 ≤ (24995690842969/100000000000000 : ℝ)^49 := by
    have hnat : (3516275989 : ℕ)^65*100000000000000^49 ≤ 24995690842969^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3516275989 10000000000 24995690842969 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31448087/39062500 : ℝ)^65 ≤ (75004303150539/100000000000000 : ℝ)^49 := by
    have hnat : (31448087 : ℕ)^65*100000000000000^49 ≤ 75004303150539^49*39062500^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31448087 39062500 75004303150539 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35929/10000000000 : ℝ)^65 ≤ (5992821/100000000000000 : ℝ)^49 := by
    have hnat : (35929 : ℕ)^65*100000000000000^49 ≤ 5992821^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35929 10000000000 5992821 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3516275989/10000000000 : ℝ), (31448087/39062500 : ℝ), (35929/10000000000 : ℝ)] ![(24995690842969/100000000000000 : ℝ), (75004303150539/100000000000000 : ℝ), (5992821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3516275989/10000000000 : ℝ)|^65 ≤ (24995690842969/100000000000000 : ℝ)^49
        have hw : |(3516275989/10000000000 : ℝ)|=(3516275989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31448087/39062500 : ℝ)|^65 ≤ (75004303150539/100000000000000 : ℝ)^49
        have hw : |(31448087/39062500 : ℝ)|=(31448087/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35929/10000000000 : ℝ)|^65 ≤ (5992821/100000000000000 : ℝ)^49
        have hw : |(35929/10000000000 : ℝ)|=(35929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-104706381/1250000000 : ℝ)*x 0 + (37649809/200000000 : ℝ)*x 1 + (-4437597817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104706381/1250000000 : ℝ)^65 ≤ (465929593693/12500000000000 : ℝ)^49 := by
    have hnat : (104706381 : ℕ)^65*12500000000000^49 ≤ 465929593693^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104706381 1250000000 465929593693 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37649809/200000000 : ℝ)^65 ≤ (10912162703879/100000000000000 : ℝ)^49 := by
    have hnat : (37649809 : ℕ)^65*100000000000000^49 ≤ 10912162703879^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37649809 200000000 10912162703879 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4437597817/5000000000 : ℝ)^65 ≤ (21340100133273/25000000000000 : ℝ)^49 := by
    have hnat : (4437597817 : ℕ)^65*25000000000000^49 ≤ 21340100133273^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4437597817 5000000000 21340100133273 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104706381/1250000000 : ℝ), (37649809/200000000 : ℝ), (-4437597817/5000000000 : ℝ)] ![(465929593693/12500000000000 : ℝ), (10912162703879/100000000000000 : ℝ), (21340100133273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104706381/1250000000 : ℝ)|^65 ≤ (465929593693/12500000000000 : ℝ)^49
        have hw : |(-104706381/1250000000 : ℝ)|=(104706381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(37649809/200000000 : ℝ)|^65 ≤ (10912162703879/100000000000000 : ℝ)^49
        have hw : |(37649809/200000000 : ℝ)|=(37649809/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4437597817/5000000000 : ℝ)|^65 ≤ (21340100133273/25000000000000 : ℝ)^49
        have hw : |(-4437597817/5000000000 : ℝ)|=(4437597817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (427991501/2500000000 : ℝ)*x 0 + (-543024277/5000000000 : ℝ)*x 1 + (-8856252801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427991501/2500000000 : ℝ)^65 ≤ (9620725729267/100000000000000 : ℝ)^49 := by
    have hnat : (427991501 : ℕ)^65*100000000000000^49 ≤ 9620725729267^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427991501 2500000000 9620725729267 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543024277/5000000000 : ℝ)^65 ≤ (5260469468213/100000000000000 : ℝ)^49 := by
    have hnat : (543024277 : ℕ)^65*100000000000000^49 ≤ 5260469468213^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543024277 5000000000 5260469468213 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8856252801/10000000000 : ℝ)^65 ≤ (42559402394239/50000000000000 : ℝ)^49 := by
    have hnat : (8856252801 : ℕ)^65*50000000000000^49 ≤ 42559402394239^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8856252801 10000000000 42559402394239 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427991501/2500000000 : ℝ), (-543024277/5000000000 : ℝ), (-8856252801/10000000000 : ℝ)] ![(9620725729267/100000000000000 : ℝ), (5260469468213/100000000000000 : ℝ), (42559402394239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427991501/2500000000 : ℝ)|^65 ≤ (9620725729267/100000000000000 : ℝ)^49
        have hw : |(427991501/2500000000 : ℝ)|=(427991501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-543024277/5000000000 : ℝ)|^65 ≤ (5260469468213/100000000000000 : ℝ)^49
        have hw : |(-543024277/5000000000 : ℝ)|=(543024277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8856252801/10000000000 : ℝ)|^65 ≤ (42559402394239/50000000000000 : ℝ)^49
        have hw : |(-8856252801/10000000000 : ℝ)|=(8856252801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7455006253/10000000000 : ℝ)*x 0 + (2709935621/10000000000 : ℝ)*x 1 + (117069211/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7455006253/10000000000 : ℝ)^65 ≤ (16933174816607/25000000000000 : ℝ)^49 := by
    have hnat : (7455006253 : ℕ)^65*25000000000000^49 ≤ 16933174816607^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7455006253 10000000000 16933174816607 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709935621/10000000000 : ℝ)^65 ≤ (4423262655681/25000000000000 : ℝ)^49 := by
    have hnat : (2709935621 : ℕ)^65*25000000000000^49 ≤ 4423262655681^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709935621 10000000000 4423262655681 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117069211/500000000 : ℝ)^65 ≤ (14574250086649/100000000000000 : ℝ)^49 := by
    have hnat : (117069211 : ℕ)^65*100000000000000^49 ≤ 14574250086649^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117069211 500000000 14574250086649 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7455006253/10000000000 : ℝ), (2709935621/10000000000 : ℝ), (117069211/500000000 : ℝ)] ![(16933174816607/25000000000000 : ℝ), (4423262655681/25000000000000 : ℝ), (14574250086649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7455006253/10000000000 : ℝ)|^65 ≤ (16933174816607/25000000000000 : ℝ)^49
        have hw : |(7455006253/10000000000 : ℝ)|=(7455006253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709935621/10000000000 : ℝ)|^65 ≤ (4423262655681/25000000000000 : ℝ)^49
        have hw : |(2709935621/10000000000 : ℝ)|=(2709935621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117069211/500000000 : ℝ)|^65 ≤ (14574250086649/100000000000000 : ℝ)^49
        have hw : |(117069211/500000000 : ℝ)|=(117069211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4160353899/5000000000 : ℝ)*x 0 + (1577130289/5000000000 : ℝ)*x 1 + (2391/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4160353899/5000000000 : ℝ)^65 ≤ (19589807302871/25000000000000 : ℝ)^49 := by
    have hnat : (4160353899 : ℕ)^65*25000000000000^49 ≤ 19589807302871^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160353899 5000000000 19589807302871 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1577130289/5000000000 : ℝ)^65 ≤ (21640748820667/100000000000000 : ℝ)^49 := by
    have hnat : (1577130289 : ℕ)^65*100000000000000^49 ≤ 21640748820667^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577130289 5000000000 21640748820667 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2391/250000000 : ℝ)^65 ≤ (21961639/100000000000000 : ℝ)^49 := by
    have hnat : (2391 : ℕ)^65*100000000000000^49 ≤ 21961639^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391 250000000 21961639 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4160353899/5000000000 : ℝ), (1577130289/5000000000 : ℝ), (2391/250000000 : ℝ)] ![(19589807302871/25000000000000 : ℝ), (21640748820667/100000000000000 : ℝ), (21961639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4160353899/5000000000 : ℝ)|^65 ≤ (19589807302871/25000000000000 : ℝ)^49
        have hw : |(4160353899/5000000000 : ℝ)|=(4160353899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1577130289/5000000000 : ℝ)|^65 ≤ (21640748820667/100000000000000 : ℝ)^49
        have hw : |(1577130289/5000000000 : ℝ)|=(1577130289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2391/250000000 : ℝ)|^65 ≤ (21961639/100000000000000 : ℝ)^49
        have hw : |(2391/250000000 : ℝ)|=(2391/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-227652969/5000000000 : ℝ)*x 0 + (6698075853/10000000000 : ℝ)*x 1 + (-31073913/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227652969/5000000000 : ℝ)^65 ≤ (1660344753167/100000000000000 : ℝ)^49 := by
    have hnat : (227652969 : ℕ)^65*100000000000000^49 ≤ 1660344753167^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227652969 5000000000 1660344753167 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6698075853/10000000000 : ℝ)^65 ≤ (3672801404091/6250000000000 : ℝ)^49 := by
    have hnat : (6698075853 : ℕ)^65*6250000000000^49 ≤ 3672801404091^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6698075853 10000000000 3672801404091 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31073913/62500000 : ℝ)^65 ≤ (19787416384227/50000000000000 : ℝ)^49 := by
    have hnat : (31073913 : ℕ)^65*50000000000000^49 ≤ 19787416384227^49*62500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31073913 62500000 19787416384227 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-227652969/5000000000 : ℝ), (6698075853/10000000000 : ℝ), (-31073913/62500000 : ℝ)] ![(1660344753167/100000000000000 : ℝ), (3672801404091/6250000000000 : ℝ), (19787416384227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-227652969/5000000000 : ℝ)|^65 ≤ (1660344753167/100000000000000 : ℝ)^49
        have hw : |(-227652969/5000000000 : ℝ)|=(227652969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6698075853/10000000000 : ℝ)|^65 ≤ (3672801404091/6250000000000 : ℝ)^49
        have hw : |(6698075853/10000000000 : ℝ)|=(6698075853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31073913/62500000 : ℝ)|^65 ≤ (19787416384227/50000000000000 : ℝ)^49
        have hw : |(-31073913/62500000 : ℝ)|=(31073913/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1988678521/2500000000 : ℝ)*x 0 + (-75664407/2000000000 : ℝ)*x 1 + (-1752059373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988678521/2500000000 : ℝ)^65 ≤ (73820240521/100000000000 : ℝ)^49 := by
    have hnat : (1988678521 : ℕ)^65*100000000000^49 ≤ 73820240521^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988678521 2500000000 73820240521 100000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75664407/2000000000 : ℝ)^65 ≤ (649321721041/50000000000000 : ℝ)^49 := by
    have hnat : (75664407 : ℕ)^65*50000000000000^49 ≤ 649321721041^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75664407 2000000000 649321721041 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1752059373/5000000000 : ℝ)^65 ≤ (3110139503831/12500000000000 : ℝ)^49 := by
    have hnat : (1752059373 : ℕ)^65*12500000000000^49 ≤ 3110139503831^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752059373 5000000000 3110139503831 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1988678521/2500000000 : ℝ), (-75664407/2000000000 : ℝ), (-1752059373/5000000000 : ℝ)] ![(73820240521/100000000000 : ℝ), (649321721041/50000000000000 : ℝ), (3110139503831/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1988678521/2500000000 : ℝ)|^65 ≤ (73820240521/100000000000 : ℝ)^49
        have hw : |(1988678521/2500000000 : ℝ)|=(1988678521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-75664407/2000000000 : ℝ)|^65 ≤ (649321721041/50000000000000 : ℝ)^49
        have hw : |(-75664407/2000000000 : ℝ)|=(75664407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1752059373/5000000000 : ℝ)|^65 ≤ (3110139503831/12500000000000 : ℝ)^49
        have hw : |(-1752059373/5000000000 : ℝ)|=(1752059373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (544109521/2500000000 : ℝ)*x 0 + (3779309951/5000000000 : ℝ)*x 1 + (2720835627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544109521/2500000000 : ℝ)^65 ≤ (6614091830537/50000000000000 : ℝ)^49 := by
    have hnat : (544109521 : ℕ)^65*50000000000000^49 ≤ 6614091830537^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544109521 2500000000 6614091830537 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3779309951/5000000000 : ℝ)^65 ≤ (34492150172321/50000000000000 : ℝ)^49 := by
    have hnat : (3779309951 : ℕ)^65*50000000000000^49 ≤ 34492150172321^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3779309951 5000000000 34492150172321 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720835627/10000000000 : ℝ)^65 ≤ (17787515987789/100000000000000 : ℝ)^49 := by
    have hnat : (2720835627 : ℕ)^65*100000000000000^49 ≤ 17787515987789^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720835627 10000000000 17787515987789 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544109521/2500000000 : ℝ), (3779309951/5000000000 : ℝ), (2720835627/10000000000 : ℝ)] ![(6614091830537/50000000000000 : ℝ), (34492150172321/50000000000000 : ℝ), (17787515987789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544109521/2500000000 : ℝ)|^65 ≤ (6614091830537/50000000000000 : ℝ)^49
        have hw : |(544109521/2500000000 : ℝ)|=(544109521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3779309951/5000000000 : ℝ)|^65 ≤ (34492150172321/50000000000000 : ℝ)^49
        have hw : |(3779309951/5000000000 : ℝ)|=(3779309951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720835627/10000000000 : ℝ)|^65 ≤ (17787515987789/100000000000000 : ℝ)^49
        have hw : |(2720835627/10000000000 : ℝ)|=(2720835627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s1_s1_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4247443641/5000000000 : ℝ)*x 0 + (2901375601/10000000000 : ℝ)*x 1 + (-990561/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247443641/5000000000 : ℝ)^65 ≤ (40271278684749/50000000000000 : ℝ)^49 := by
    have hnat : (4247443641 : ℕ)^65*50000000000000^49 ≤ 40271278684749^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247443641 5000000000 40271278684749 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2901375601/10000000000 : ℝ)^65 ≤ (9684957051211/50000000000000 : ℝ)^49 := by
    have hnat : (2901375601 : ℕ)^65*50000000000000^49 ≤ 9684957051211^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2901375601 10000000000 9684957051211 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (990561/200000000 : ℝ)^65 ≤ (43764260497/50000000000000 : ℝ)^49 := by
    have hnat : (990561 : ℕ)^65*50000000000000^49 ≤ 43764260497^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990561 200000000 43764260497 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247443641/5000000000 : ℝ), (2901375601/10000000000 : ℝ), (-990561/200000000 : ℝ)] ![(40271278684749/50000000000000 : ℝ), (9684957051211/50000000000000 : ℝ), (43764260497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247443641/5000000000 : ℝ)|^65 ≤ (40271278684749/50000000000000 : ℝ)^49
        have hw : |(4247443641/5000000000 : ℝ)|=(4247443641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2901375601/10000000000 : ℝ)|^65 ≤ (9684957051211/50000000000000 : ℝ)^49
        have hw : |(2901375601/10000000000 : ℝ)|=(2901375601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-990561/200000000 : ℝ)|^65 ≤ (43764260497/50000000000000 : ℝ)^49
        have hw : |(-990561/200000000 : ℝ)|=(990561/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301062_s1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((48813/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48813/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24123/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(24123/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42871/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42871/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((46289/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46289/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18393/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18393/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38441/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38441/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  have s1_pow0 : (48813/50000 : ℝ) ^ (129/32 : ℝ) ≤ (90768655713679265549/100000000000000000000 : ℝ) := by
    have hpowers : (48813/50000 : ℝ)^129 ≤ (90768655713679265549/100000000000000000000 : ℝ)^32 := by
      have hnat : (48813 : ℕ)^129*100000000000000000000^32 ≤ 90768655713679265549^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48813 50000 90768655713679265549 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48813/50000 : ℝ)) (X := (90768655713679265549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (190768655713679265549/100000000000000000000 : ℝ) ≤ (11737703547568463/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (190768655713679265549/100000000000000000000 : ℝ)^32 ≤ (11737703547568463/10000000000000000 : ℝ)^129 := by
      have hnat : (190768655713679265549 : ℕ)^32*10000000000000000^129 ≤ 11737703547568463^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        190768655713679265549 100000000000000000000 11737703547568463 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11737703547568463/10000000000000000 : ℝ)) (X := (190768655713679265549/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (140768655713679265549/50000000000000000000 : ℝ) ≤ (12927447895769801/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (140768655713679265549/50000000000000000000 : ℝ)^32 ≤ (12927447895769801/10000000000000000 : ℝ)^129 := by
      have hnat : (140768655713679265549 : ℕ)^32*10000000000000000^129 ≤ 12927447895769801^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        140768655713679265549 50000000000000000000 12927447895769801 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12927447895769801/10000000000000000 : ℝ)) (X := (140768655713679265549/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1737703547568463/9762600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(198290724700223/1627100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (48813/50000 : ℝ)) (alpha := (1737703547568463/9762600000000000 : ℝ)) (beta := (198290724700223/1627100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (48813/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1737703547568463/9762600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(198290724700223/1627100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (24123/25000 : ℝ) ^ (129/32 : ℝ) ≤ (86592561362267525159/100000000000000000000 : ℝ) := by
    have hpowers : (24123/25000 : ℝ)^129 ≤ (86592561362267525159/100000000000000000000 : ℝ)^32 := by
      have hnat : (24123 : ℕ)^129*100000000000000000000^32 ≤ 86592561362267525159^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24123 25000 86592561362267525159 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24123/25000 : ℝ)) (X := (86592561362267525159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (186592561362267525159/100000000000000000000 : ℝ) ≤ (729589558409909/625000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (186592561362267525159/100000000000000000000 : ℝ)^32 ≤ (729589558409909/625000000000000 : ℝ)^129 := by
      have hnat : (186592561362267525159 : ℕ)^32*625000000000000^129 ≤ 729589558409909^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        186592561362267525159 100000000000000000000 729589558409909 625000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (729589558409909/625000000000000 : ℝ)) (X := (186592561362267525159/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (136592561362267525159/50000000000000000000 : ℝ) ≤ (2566246734962773/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (136592561362267525159/50000000000000000000 : ℝ)^32 ≤ (2566246734962773/2000000000000000 : ℝ)^129 := by
      have hnat : (136592561362267525159 : ℕ)^32*2000000000000000^129 ≤ 2566246734962773^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        136592561362267525159 50000000000000000000 2566246734962773 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2566246734962773/2000000000000000 : ℝ)) (X := (136592561362267525159/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(104589558409909/603075000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(385933580085107/3216400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (24123/25000 : ℝ)) (alpha := (104589558409909/603075000000000 : ℝ)) (beta := (385933580085107/3216400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (24123/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(104589558409909/603075000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(385933580085107/3216400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (42871/50000 : ℝ) ^ (129/32 : ℝ) ≤ (53788166247984009983/100000000000000000000 : ℝ) := by
    have hpowers : (42871/50000 : ℝ)^129 ≤ (53788166247984009983/100000000000000000000 : ℝ)^32 := by
      have hnat : (42871 : ℕ)^129*100000000000000000000^32 ≤ 53788166247984009983^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42871 50000 53788166247984009983 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42871/50000 : ℝ)) (X := (53788166247984009983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (153788166247984009983/100000000000000000000 : ℝ) ≤ (11126753731289197/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (153788166247984009983/100000000000000000000 : ℝ)^32 ≤ (11126753731289197/10000000000000000 : ℝ)^129 := by
      have hnat : (153788166247984009983 : ℕ)^32*10000000000000000^129 ≤ 11126753731289197^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        153788166247984009983 100000000000000000000 11126753731289197 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11126753731289197/10000000000000000 : ℝ)) (X := (153788166247984009983/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (103788166247984009983/50000000000000000000 : ℝ) ≤ (2996537945341487/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (103788166247984009983/50000000000000000000 : ℝ)^32 ≤ (2996537945341487/2500000000000000 : ℝ)^129 := by
      have hnat : (103788166247984009983 : ℕ)^32*2500000000000000^129 ≤ 2996537945341487^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103788166247984009983 50000000000000000000 2996537945341487 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2996537945341487/2500000000000000 : ℝ)) (X := (103788166247984009983/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1126753731289197/8574200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(861984002083/8600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (42871/50000 : ℝ)) (alpha := (1126753731289197/8574200000000000 : ℝ)) (beta := (861984002083/8600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (42871/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1126753731289197/8574200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(861984002083/8600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-19548933/200000000 : ℝ)*X 0 0+(5024470951/10000000000 : ℝ)*X 0 1+(-6397625727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1261522461/2500000000 : ℝ)*X 1 0+(-19315411/200000000 : ℝ)*X 1 1+(-6383937951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5352268367/10000000000 : ℝ)*X 2 0+(2795587383/5000000000 : ℝ)*X 2 1+(888915117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-932449313/10000000000 : ℝ)*X 0 0+(37952787/200000000 : ℝ)*X 0 1+(-8821349271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2113666919/10000000000 : ℝ)*X 1 0+(-682596779/10000000000 : ℝ)*X 1 1+(-1760504239/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2358833991/10000000000 : ℝ)*X 2 0+(3878972471/5000000000 : ℝ)*X 2 1+(90241199/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3516275989/10000000000 : ℝ)*X 0 0+(31448087/39062500 : ℝ)*X 0 1+(35929/10000000000 : ℝ)*X 0 2+(3516275989/10000000000 : ℝ)*X 1 0+(31448087/39062500 : ℝ)*X 1 1+(35929/10000000000 : ℝ)*X 1 2+(3516275989/10000000000 : ℝ)*X 2 0+(31448087/39062500 : ℝ)*X 2 1+(35929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-104706381/1250000000 : ℝ)*X 0 0+(37649809/200000000 : ℝ)*X 0 1+(-4437597817/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((427991501/2500000000 : ℝ)*X 1 0+(-543024277/5000000000 : ℝ)*X 1 1+(-8856252801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((7455006253/10000000000 : ℝ)*X 2 0+(2709935621/10000000000 : ℝ)*X 2 1+(117069211/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((4160353899/5000000000 : ℝ)*X 0 0+(1577130289/5000000000 : ℝ)*X 0 1+(2391/250000000 : ℝ)*X 0 2+(4160353899/5000000000 : ℝ)*X 1 0+(1577130289/5000000000 : ℝ)*X 1 1+(2391/250000000 : ℝ)*X 1 2+(4160353899/5000000000 : ℝ)*X 2 0+(1577130289/5000000000 : ℝ)*X 2 1+(2391/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-227652969/5000000000 : ℝ)*X 0 0+(6698075853/10000000000 : ℝ)*X 0 1+(-31073913/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1988678521/2500000000 : ℝ)*X 1 0+(-75664407/2000000000 : ℝ)*X 1 1+(-1752059373/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((544109521/2500000000 : ℝ)*X 2 0+(3779309951/5000000000 : ℝ)*X 2 1+(2720835627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((4247443641/5000000000 : ℝ)*X 0 0+(2901375601/10000000000 : ℝ)*X 0 1+(-990561/200000000 : ℝ)*X 0 2+(4247443641/5000000000 : ℝ)*X 1 0+(2901375601/10000000000 : ℝ)*X 1 1+(-990561/200000000 : ℝ)*X 1 2+(4247443641/5000000000 : ℝ)*X 2 0+(2901375601/10000000000 : ℝ)*X 2 1+(-990561/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((46289/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46289/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (428151181599615176383689797/65221302833500000000000000000000 : ℝ) := by norm_num
    linear_combination (131828170967/1000000000000 : ℝ)*(base5) + (469260472139/500000000000 : ℝ)*(base7) + (44279243081/25000000000 : ℝ)*(major_s1_0) + (44279243081/25000000000 : ℝ)*(major_s1_1) + (44279243081/25000000000 : ℝ)*(major_s1_2) + (3940431/1000000000000 : ℝ)*(sp_s1_0) + (141833/40000000000 : ℝ)*(sp_s1_1) + (883422902531/500000000000 : ℝ)*(sp_s1_7) + (883430323867/500000000000 : ℝ)*(sp_s1_8) + (474682467013/250000000000 : ℝ)*(sp_s1_9) + (2004043928797/1000000000000 : ℝ)*(sp_s1_13) + (398543/6250000000 : ℝ)*(sp_s1_14) + (24659407/500000000000 : ℝ)*(sp_s1_15) + (11815287/1000000000000 : ℝ)*(sp_s1_23) + (239470231097/200000000000 : ℝ)*(f.failure) + (1766913512373/1000000000000 : ℝ)*(f.sum) + (9378642174143237/48101262000000000000000000000 : ℝ)*base62 + (240204984249/430000000000000000000000 : ℝ)*base64 + (20388454301153/80410000000000000000000000 : ℝ)*base67 + (127483178626871/428710000000000000000000000 : ℝ)*base68 + (2147913176789543/5247397500000000000000000000 : ℝ)*base70 + (23491470487089/81355000000000000000000000 : ℝ)*base73 + (11311063625063/48246000000000000000000000 : ℝ)*base74 + (5933880560497/24406500000000000000000000 : ℝ)*base76 + (85061446768728207/1308351110000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (1843/5000000000000000 : ℝ)*base86 + (1843/5000000000000000 : ℝ)*base88 + (1843/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18393/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18393/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (88339258300409831456342148593/6522130283350000000000000000000000 : ℝ) := by norm_num
    linear_combination (72092154943/1000000000000 : ℝ)*(base5) + (940631956523/1000000000000 : ℝ)*(base7) + (77317/250000000000 : ℝ)*(base40) + (5399183569/200000000000 : ℝ)*(base60) + (435721315477/250000000000 : ℝ)*(major_s1_0) + (435721315477/250000000000 : ℝ)*(major_s1_1) + (435721315477/250000000000 : ℝ)*(major_s1_2) + (1334281/1000000000000 : ℝ)*(sp_s1_1) + (10842351/50000000000 : ℝ)*(sp_s1_7) + (47593453/500000000000 : ℝ)*(sp_s1_8) + (1727946100543/1000000000000 : ℝ)*(sp_s1_14) + (216008303297/125000000000 : ℝ)*(sp_s1_15) + (900127551253/500000000000 : ℝ)*(sp_s1_16) + (2046770015681/1000000000000 : ℝ)*(sp_s1_20) + (589115107051/500000000000 : ℝ)*(f.failure) + (1728162947563/1000000000000 : ℝ)*(f.sum) + (70233989599890707/1202531550000000000000000000000 : ℝ)*base63 + (1375338020471/2150000000000000000000000 : ℝ)*base65 + (74432363793741/804100000000000000000000000 : ℝ)*base66 + (313580212536369/2143550000000000000000000000 : ℝ)*base69 + (16669273499492513/52473975000000000000000000000 : ℝ)*base71 + (16122468471123/813550000000000000000000000 : ℝ)*base72 + (8396983994411/18846093750000000000000000 : ℝ)*base75 + (582888624225991/2440650000000000000000000000 : ℝ)*base77 + (2114215512112664813/13083511100000000000000000000000 : ℝ)*base79 + (3031/12500000000000000 : ℝ)*base87 + (3031/12500000000000000 : ℝ)*base89 + (3031/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38441/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38441/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (942858795250692501835571/100210962500000000000000000000 : ℝ) := by norm_num
    linear_combination (341974270463/500000000000 : ℝ)*(base7) + (7868757/1000000000000 : ℝ)*(base11) + (257447/1000000000000 : ℝ)*(base40) + (373842144963/1000000000000 : ℝ)*(base43) + (6723235403/500000000000 : ℝ)*(base59) + (380059987663/250000000000 : ℝ)*(major_s1_0) + (1146397805689/1000000000000 : ℝ)*(major_s1_1) + (380059987663/250000000000 : ℝ)*(major_s1_2) + (5660683/200000000000 : ℝ)*(sp_s1_2) + (360772793/1000000000000 : ℝ)*(sp_s1_20) + (1217638584671/1000000000000 : ℝ)*(sp_s1_21) + (1591488598391/1000000000000 : ℝ)*(sp_s1_22) + (1217618150013/1000000000000 : ℝ)*(sp_s1_23) + (53478270953/31250000000 : ℝ)*(sp_s1_27) + (1027716902363/1000000000000 : ℝ)*(f.failure) + (1591488598391/1000000000000 : ℝ)*(f.sum) + (11262623896800533/48101262000000000000000000000 : ℝ)*base63 + (748674431117/1075000000000000000000000 : ℝ)*base65 + (822204707691877/3216400000000000000000000000 : ℝ)*base66 + (810559519018461/2143550000000000000000000000 : ℝ)*base69 + (30018987050998069/104947950000000000000000000000 : ℝ)*base71 + (13058957032093/203387500000000000000000000 : ℝ)*base72 + (872926535733557/1206150000000000000000000000 : ℝ)*base75 + (10432888691321/2440650000000000000000000000 : ℝ)*base76 + (14152322049509768237/52334044400000000000000000000000 : ℝ)*base79 + (13897/25000000000000000 : ℝ)*base86 + (13897/25000000000000000 : ℝ)*base88 + (13897/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((48813/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48813/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24123/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(24123/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42871/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42871/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((46289/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46289/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18393/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18393/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38441/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38441/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301062_s1 p hpa hpb X hX hprev0

#print axioms solution
