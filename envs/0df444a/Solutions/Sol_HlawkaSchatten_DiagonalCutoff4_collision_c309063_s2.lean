-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:05:23.229396+00:00
-- url     : https://prove2.me/submissions/4c95c5f2-99c2-49c3-bd4b-a05278d6f8a1

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
theorem collision_support_c309063_s2_s2_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-731442107/10000000000 : ℝ)*x 0 + (5608649099/10000000000 : ℝ)*x 1 + (2900904543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (731442107/10000000000 : ℝ)^35 ≤ (1685041845383/50000000000000 : ℝ)^27 := by
    have hnat : (731442107 : ℕ)^35*50000000000000^27 ≤ 1685041845383^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731442107 10000000000 1685041845383 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5608649099/10000000000 : ℝ)^35 ≤ (1476712416887/3125000000000 : ℝ)^27 := by
    have hnat : (5608649099 : ℕ)^35*3125000000000^27 ≤ 1476712416887^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608649099 10000000000 1476712416887 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2900904543/5000000000 : ℝ)^35 ≤ (4937511895791/10000000000000 : ℝ)^27 := by
    have hnat : (2900904543 : ℕ)^35*10000000000000^27 ≤ 4937511895791^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2900904543 5000000000 4937511895791 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-731442107/10000000000 : ℝ), (5608649099/10000000000 : ℝ), (2900904543/5000000000 : ℝ)] ![(1685041845383/50000000000000 : ℝ), (1476712416887/3125000000000 : ℝ), (4937511895791/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-731442107/10000000000 : ℝ)|^35 ≤ (1685041845383/50000000000000 : ℝ)^27
        have hw : |(-731442107/10000000000 : ℝ)|=(731442107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5608649099/10000000000 : ℝ)|^35 ≤ (1476712416887/3125000000000 : ℝ)^27
        have hw : |(5608649099/10000000000 : ℝ)|=(5608649099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2900904543/5000000000 : ℝ)|^35 ≤ (4937511895791/10000000000000 : ℝ)^27
        have hw : |(2900904543/5000000000 : ℝ)|=(2900904543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5608563957/10000000000 : ℝ)*x 0 + (-729541537/10000000000 : ℝ)*x 1 + (5802921913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5608563957/10000000000 : ℝ)^35 ≤ (5906733430439/12500000000000 : ℝ)^27 := by
    have hnat : (5608563957 : ℕ)^35*12500000000000^27 ≤ 5906733430439^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608563957 10000000000 5906733430439 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (729541537/10000000000 : ℝ)^35 ≤ (3358736677467/100000000000000 : ℝ)^27 := by
    have hnat : (729541537 : ℕ)^35*100000000000000^27 ≤ 3358736677467^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729541537 10000000000 3358736677467 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5802921913/10000000000 : ℝ)^35 ≤ (12346848966437/25000000000000 : ℝ)^27 := by
    have hnat : (5802921913 : ℕ)^35*25000000000000^27 ≤ 12346848966437^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5802921913 10000000000 12346848966437 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5608563957/10000000000 : ℝ), (-729541537/10000000000 : ℝ), (5802921913/10000000000 : ℝ)] ![(5906733430439/12500000000000 : ℝ), (3358736677467/100000000000000 : ℝ), (12346848966437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5608563957/10000000000 : ℝ)|^35 ≤ (5906733430439/12500000000000 : ℝ)^27
        have hw : |(5608563957/10000000000 : ℝ)|=(5608563957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-729541537/10000000000 : ℝ)|^35 ≤ (3358736677467/100000000000000 : ℝ)^27
        have hw : |(-729541537/10000000000 : ℝ)|=(729541537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5802921913/10000000000 : ℝ)|^35 ≤ (12346848966437/25000000000000 : ℝ)^27
        have hw : |(5802921913/10000000000 : ℝ)|=(5802921913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2835205653/5000000000 : ℝ)*x 0 + (722059449/1250000000 : ℝ)*x 1 + (-13282847/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2835205653/5000000000 : ℝ)^35 ≤ (11982611467053/25000000000000 : ℝ)^27 := by
    have hnat : (2835205653 : ℕ)^35*25000000000000^27 ≤ 11982611467053^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835205653 5000000000 11982611467053 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (722059449/1250000000 : ℝ)^35 ≤ (1963832968251/4000000000000 : ℝ)^27 := by
    have hnat : (722059449 : ℕ)^35*4000000000000^27 ≤ 1963832968251^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722059449 1250000000 1963832968251 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13282847/200000000 : ℝ)^35 ≤ (2973729920363/100000000000000 : ℝ)^27 := by
    have hnat : (13282847 : ℕ)^35*100000000000000^27 ≤ 2973729920363^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13282847 200000000 2973729920363 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2835205653/5000000000 : ℝ), (722059449/1250000000 : ℝ), (-13282847/200000000 : ℝ)] ![(11982611467053/25000000000000 : ℝ), (1963832968251/4000000000000 : ℝ), (2973729920363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2835205653/5000000000 : ℝ)|^35 ≤ (11982611467053/25000000000000 : ℝ)^27
        have hw : |(2835205653/5000000000 : ℝ)|=(2835205653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(722059449/1250000000 : ℝ)|^35 ≤ (1963832968251/4000000000000 : ℝ)^27
        have hw : |(722059449/1250000000 : ℝ)|=(722059449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13282847/200000000 : ℝ)|^35 ≤ (2973729920363/100000000000000 : ℝ)^27
        have hw : |(-13282847/200000000 : ℝ)|=(13282847/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (36460421/80000000 : ℝ)*x 0 + (4320663973/10000000000 : ℝ)*x 1 + (3970255079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36460421/80000000 : ℝ)^35 ≤ (36108974648693/100000000000000 : ℝ)^27 := by
    have hnat : (36460421 : ℕ)^35*100000000000000^27 ≤ 36108974648693^27*80000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36460421 80000000 36108974648693 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4320663973/10000000000 : ℝ)^35 ≤ (33694999334359/100000000000000 : ℝ)^27 := by
    have hnat : (4320663973 : ℕ)^35*100000000000000^27 ≤ 33694999334359^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320663973 10000000000 33694999334359 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3970255079/10000000000 : ℝ)^35 ≤ (30196026006517/100000000000000 : ℝ)^27 := by
    have hnat : (3970255079 : ℕ)^35*100000000000000^27 ≤ 30196026006517^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3970255079 10000000000 30196026006517 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(36460421/80000000 : ℝ), (4320663973/10000000000 : ℝ), (3970255079/10000000000 : ℝ)] ![(36108974648693/100000000000000 : ℝ), (33694999334359/100000000000000 : ℝ), (30196026006517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(36460421/80000000 : ℝ)|^35 ≤ (36108974648693/100000000000000 : ℝ)^27
        have hw : |(36460421/80000000 : ℝ)|=(36460421/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4320663973/10000000000 : ℝ)|^35 ≤ (33694999334359/100000000000000 : ℝ)^27
        have hw : |(4320663973/10000000000 : ℝ)|=(4320663973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3970255079/10000000000 : ℝ)|^35 ≤ (30196026006517/100000000000000 : ℝ)^27
        have hw : |(3970255079/10000000000 : ℝ)|=(3970255079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-524527827/5000000000 : ℝ)*x 0 + (3150142207/10000000000 : ℝ)*x 1 + (389112481/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524527827/5000000000 : ℝ)^35 ≤ (537854441801/10000000000000 : ℝ)^27 := by
    have hnat : (524527827 : ℕ)^35*10000000000000^27 ≤ 537854441801^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524527827 5000000000 537854441801 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3150142207/10000000000 : ℝ)^35 ≤ (223710950961/1000000000000 : ℝ)^27 := by
    have hnat : (3150142207 : ℕ)^35*1000000000000^27 ≤ 223710950961^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3150142207 10000000000 223710950961 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389112481/500000000 : ℝ)^35 ≤ (72250360475711/100000000000000 : ℝ)^27 := by
    have hnat : (389112481 : ℕ)^35*100000000000000^27 ≤ 72250360475711^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389112481 500000000 72250360475711 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-524527827/5000000000 : ℝ), (3150142207/10000000000 : ℝ), (389112481/500000000 : ℝ)] ![(537854441801/10000000000000 : ℝ), (223710950961/1000000000000 : ℝ), (72250360475711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-524527827/5000000000 : ℝ)|^35 ≤ (537854441801/10000000000000 : ℝ)^27
        have hw : |(-524527827/5000000000 : ℝ)|=(524527827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3150142207/10000000000 : ℝ)|^35 ≤ (223710950961/1000000000000 : ℝ)^27
        have hw : |(3150142207/10000000000 : ℝ)|=(3150142207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(389112481/500000000 : ℝ)|^35 ≤ (72250360475711/100000000000000 : ℝ)^27
        have hw : |(389112481/500000000 : ℝ)|=(389112481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1831518469/5000000000 : ℝ)*x 0 + (-17579391/1000000000 : ℝ)*x 1 + (3891799171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1831518469/5000000000 : ℝ)^35 ≤ (13601258492307/50000000000000 : ℝ)^27 := by
    have hnat : (1831518469 : ℕ)^35*50000000000000^27 ≤ 13601258492307^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831518469 5000000000 13601258492307 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17579391/1000000000 : ℝ)^35 ≤ (530890506641/100000000000000 : ℝ)^27 := by
    have hnat : (17579391 : ℕ)^35*100000000000000^27 ≤ 530890506641^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17579391 1000000000 530890506641 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3891799171/5000000000 : ℝ)^35 ≤ (36133296250921/50000000000000 : ℝ)^27 := by
    have hnat : (3891799171 : ℕ)^35*50000000000000^27 ≤ 36133296250921^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3891799171 5000000000 36133296250921 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1831518469/5000000000 : ℝ), (-17579391/1000000000 : ℝ), (3891799171/5000000000 : ℝ)] ![(13601258492307/50000000000000 : ℝ), (530890506641/100000000000000 : ℝ), (36133296250921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1831518469/5000000000 : ℝ)|^35 ≤ (13601258492307/50000000000000 : ℝ)^27
        have hw : |(1831518469/5000000000 : ℝ)|=(1831518469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17579391/1000000000 : ℝ)|^35 ≤ (530890506641/100000000000000 : ℝ)^27
        have hw : |(-17579391/1000000000 : ℝ)|=(17579391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3891799171/5000000000 : ℝ)|^35 ≤ (36133296250921/50000000000000 : ℝ)^27
        have hw : |(3891799171/5000000000 : ℝ)|=(3891799171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3479225289/10000000000 : ℝ)*x 0 + (1991061671/2500000000 : ℝ)*x 1 + (-25259999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3479225289/10000000000 : ℝ)^35 ≤ (508927038901/2000000000000 : ℝ)^27 := by
    have hnat : (3479225289 : ℕ)^35*2000000000000^27 ≤ 508927038901^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3479225289 10000000000 508927038901 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1991061671/2500000000 : ℝ)^35 ≤ (37224103704069/50000000000000 : ℝ)^27 := by
    have hnat : (1991061671 : ℕ)^35*50000000000000^27 ≤ 37224103704069^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991061671 2500000000 37224103704069 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25259999/5000000000 : ℝ)^35 ≤ (21088127037/20000000000000 : ℝ)^27 := by
    have hnat : (25259999 : ℕ)^35*20000000000000^27 ≤ 21088127037^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25259999 5000000000 21088127037 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3479225289/10000000000 : ℝ), (1991061671/2500000000 : ℝ), (-25259999/5000000000 : ℝ)] ![(508927038901/2000000000000 : ℝ), (37224103704069/50000000000000 : ℝ), (21088127037/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3479225289/10000000000 : ℝ)|^35 ≤ (508927038901/2000000000000 : ℝ)^27
        have hw : |(3479225289/10000000000 : ℝ)|=(3479225289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1991061671/2500000000 : ℝ)|^35 ≤ (37224103704069/50000000000000 : ℝ)^27
        have hw : |(1991061671/2500000000 : ℝ)|=(1991061671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25259999/5000000000 : ℝ)|^35 ≤ (21088127037/20000000000000 : ℝ)^27
        have hw : |(-25259999/5000000000 : ℝ)|=(25259999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (443434927/1250000000 : ℝ)*x 0 + (442345729/625000000 : ℝ)*x 1 + (1695167877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443434927/1250000000 : ℝ)^35 ≤ (81547909917/312500000000 : ℝ)^27 := by
    have hnat : (443434927 : ℕ)^35*312500000000^27 ≤ 81547909917^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443434927 1250000000 81547909917 312500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442345729/625000000 : ℝ)^35 ≤ (63885509184101/100000000000000 : ℝ)^27 := by
    have hnat : (442345729 : ℕ)^35*100000000000000^27 ≤ 63885509184101^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442345729 625000000 63885509184101 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1695167877/10000000000 : ℝ)^35 ≤ (10019159627547/100000000000000 : ℝ)^27 := by
    have hnat : (1695167877 : ℕ)^35*100000000000000^27 ≤ 10019159627547^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1695167877 10000000000 10019159627547 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(443434927/1250000000 : ℝ), (442345729/625000000 : ℝ), (1695167877/10000000000 : ℝ)] ![(81547909917/312500000000 : ℝ), (63885509184101/100000000000000 : ℝ), (10019159627547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(443434927/1250000000 : ℝ)|^35 ≤ (81547909917/312500000000 : ℝ)^27
        have hw : |(443434927/1250000000 : ℝ)|=(443434927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(442345729/625000000 : ℝ)|^35 ≤ (63885509184101/100000000000000 : ℝ)^27
        have hw : |(442345729/625000000 : ℝ)|=(442345729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1695167877/10000000000 : ℝ)|^35 ≤ (10019159627547/100000000000000 : ℝ)^27
        have hw : |(1695167877/10000000000 : ℝ)|=(1695167877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-7223181/500000000 : ℝ)*x 0 + (3576449889/10000000000 : ℝ)*x 1 + (157248061/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7223181/500000000 : ℝ)^35 ≤ (411625006501/100000000000000 : ℝ)^27 := by
    have hnat : (7223181 : ℕ)^35*100000000000000^27 ≤ 411625006501^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7223181 500000000 411625006501 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3576449889/10000000000 : ℝ)^35 ≤ (3296489385049/12500000000000 : ℝ)^27 := by
    have hnat : (3576449889 : ℕ)^35*12500000000000^27 ≤ 3296489385049^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3576449889 10000000000 3296489385049 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157248061/200000000 : ℝ)^35 ≤ (73216459908189/100000000000000 : ℝ)^27 := by
    have hnat : (157248061 : ℕ)^35*100000000000000^27 ≤ 73216459908189^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157248061 200000000 73216459908189 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7223181/500000000 : ℝ), (3576449889/10000000000 : ℝ), (157248061/200000000 : ℝ)] ![(411625006501/100000000000000 : ℝ), (3296489385049/12500000000000 : ℝ), (73216459908189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7223181/500000000 : ℝ)|^35 ≤ (411625006501/100000000000000 : ℝ)^27
        have hw : |(-7223181/500000000 : ℝ)|=(7223181/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3576449889/10000000000 : ℝ)|^35 ≤ (3296489385049/12500000000000 : ℝ)^27
        have hw : |(3576449889/10000000000 : ℝ)|=(3576449889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157248061/200000000 : ℝ)|^35 ≤ (73216459908189/100000000000000 : ℝ)^27
        have hw : |(157248061/200000000 : ℝ)|=(157248061/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (121616033/400000000 : ℝ)*x 0 + (-131553369/1250000000 : ℝ)*x 1 + (7863768501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121616033/400000000 : ℝ)^35 ≤ (10683047748643/50000000000000 : ℝ)^27 := by
    have hnat : (121616033 : ℕ)^35*50000000000000^27 ≤ 10683047748643^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121616033 400000000 10683047748643 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131553369/1250000000 : ℝ)^35 ≤ (1350240312219/25000000000000 : ℝ)^27 := by
    have hnat : (131553369 : ℕ)^35*25000000000000^27 ≤ 1350240312219^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131553369 1250000000 1350240312219 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7863768501/10000000000 : ℝ)^35 ≤ (73232943239823/100000000000000 : ℝ)^27 := by
    have hnat : (7863768501 : ℕ)^35*100000000000000^27 ≤ 73232943239823^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7863768501 10000000000 73232943239823 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(121616033/400000000 : ℝ), (-131553369/1250000000 : ℝ), (7863768501/10000000000 : ℝ)] ![(10683047748643/50000000000000 : ℝ), (1350240312219/25000000000000 : ℝ), (73232943239823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(121616033/400000000 : ℝ)|^35 ≤ (10683047748643/50000000000000 : ℝ)^27
        have hw : |(121616033/400000000 : ℝ)|=(121616033/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-131553369/1250000000 : ℝ)|^35 ≤ (1350240312219/25000000000000 : ℝ)^27
        have hw : |(-131553369/1250000000 : ℝ)|=(131553369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7863768501/10000000000 : ℝ)|^35 ≤ (73232943239823/100000000000000 : ℝ)^27
        have hw : |(7863768501/10000000000 : ℝ)|=(7863768501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7716416307/10000000000 : ℝ)*x 0 + (118203909/312500000 : ℝ)*x 1 + (-15436409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7716416307/10000000000 : ℝ)^35 ≤ (8932383019103/12500000000000 : ℝ)^27 := by
    have hnat : (7716416307 : ℕ)^35*12500000000000^27 ≤ 8932383019103^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7716416307 10000000000 8932383019103 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118203909/312500000 : ℝ)^35 ≤ (14179148069013/50000000000000 : ℝ)^27 := by
    have hnat : (118203909 : ℕ)^35*50000000000000^27 ≤ 14179148069013^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118203909 312500000 14179148069013 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15436409/2000000000 : ℝ)^35 ≤ (91319848829/50000000000000 : ℝ)^27 := by
    have hnat : (15436409 : ℕ)^35*50000000000000^27 ≤ 91319848829^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15436409 2000000000 91319848829 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7716416307/10000000000 : ℝ), (118203909/312500000 : ℝ), (-15436409/2000000000 : ℝ)] ![(8932383019103/12500000000000 : ℝ), (14179148069013/50000000000000 : ℝ), (91319848829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7716416307/10000000000 : ℝ)|^35 ≤ (8932383019103/12500000000000 : ℝ)^27
        have hw : |(7716416307/10000000000 : ℝ)|=(7716416307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(118203909/312500000 : ℝ)|^35 ≤ (14179148069013/50000000000000 : ℝ)^27
        have hw : |(118203909/312500000 : ℝ)|=(118203909/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15436409/2000000000 : ℝ)|^35 ≤ (91319848829/50000000000000 : ℝ)^27
        have hw : |(-15436409/2000000000 : ℝ)|=(15436409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7536642847/10000000000 : ℝ)*x 0 + (744020961/2500000000 : ℝ)*x 1 + (420209477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7536642847/10000000000 : ℝ)^35 ≤ (69308454085209/100000000000000 : ℝ)^27 := by
    have hnat : (7536642847 : ℕ)^35*100000000000000^27 ≤ 69308454085209^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7536642847 10000000000 69308454085209 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744020961/2500000000 : ℝ)^35 ≤ (20782039851373/100000000000000 : ℝ)^27 := by
    have hnat : (744020961 : ℕ)^35*100000000000000^27 ≤ 20782039851373^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744020961 2500000000 20782039851373 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420209477/2500000000 : ℝ)^35 ≤ (4954753026211/50000000000000 : ℝ)^27 := by
    have hnat : (420209477 : ℕ)^35*50000000000000^27 ≤ 4954753026211^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420209477 2500000000 4954753026211 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7536642847/10000000000 : ℝ), (744020961/2500000000 : ℝ), (420209477/2500000000 : ℝ)] ![(69308454085209/100000000000000 : ℝ), (20782039851373/100000000000000 : ℝ), (4954753026211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7536642847/10000000000 : ℝ)|^35 ≤ (69308454085209/100000000000000 : ℝ)^27
        have hw : |(7536642847/10000000000 : ℝ)|=(7536642847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(744020961/2500000000 : ℝ)|^35 ≤ (20782039851373/100000000000000 : ℝ)^27
        have hw : |(744020961/2500000000 : ℝ)|=(744020961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(420209477/2500000000 : ℝ)|^35 ≤ (4954753026211/50000000000000 : ℝ)^27
        have hw : |(420209477/2500000000 : ℝ)|=(420209477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-142431579/10000000000 : ℝ)*x 0 + (284956827/400000000 : ℝ)*x 1 + (558195217/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (142431579/10000000000 : ℝ)^35 ≤ (40413519243/10000000000000 : ℝ)^27 := by
    have hnat : (142431579 : ℕ)^35*10000000000000^27 ≤ 40413519243^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142431579 10000000000 40413519243 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284956827/400000000 : ℝ)^35 ≤ (64428835565337/100000000000000 : ℝ)^27 := by
    have hnat : (284956827 : ℕ)^35*100000000000000^27 ≤ 64428835565337^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284956827 400000000 64428835565337 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (558195217/1250000000 : ℝ)^35 ≤ (7033405845403/20000000000000 : ℝ)^27 := by
    have hnat : (558195217 : ℕ)^35*20000000000000^27 ≤ 7033405845403^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558195217 1250000000 7033405845403 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-142431579/10000000000 : ℝ), (284956827/400000000 : ℝ), (558195217/1250000000 : ℝ)] ![(40413519243/10000000000000 : ℝ), (64428835565337/100000000000000 : ℝ), (7033405845403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-142431579/10000000000 : ℝ)|^35 ≤ (40413519243/10000000000000 : ℝ)^27
        have hw : |(-142431579/10000000000 : ℝ)|=(142431579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284956827/400000000 : ℝ)|^35 ≤ (64428835565337/100000000000000 : ℝ)^27
        have hw : |(284956827/400000000 : ℝ)|=(284956827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(558195217/1250000000 : ℝ)|^35 ≤ (7033405845403/20000000000000 : ℝ)^27
        have hw : |(558195217/1250000000 : ℝ)|=(558195217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1536670249/2000000000 : ℝ)*x 0 + (-60912879/10000000000 : ℝ)*x 1 + (3828226071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1536670249/2000000000 : ℝ)^35 ≤ (35531192566263/50000000000000 : ℝ)^27 := by
    have hnat : (1536670249 : ℕ)^35*50000000000000^27 ≤ 35531192566263^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536670249 2000000000 35531192566263 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60912879/10000000000 : ℝ)^35 ≤ (67188763689/50000000000000 : ℝ)^27 := by
    have hnat : (60912879 : ℕ)^35*50000000000000^27 ≤ 67188763689^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60912879 10000000000 67188763689 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3828226071/10000000000 : ℝ)^35 ≤ (5760647467011/20000000000000 : ℝ)^27 := by
    have hnat : (3828226071 : ℕ)^35*20000000000000^27 ≤ 5760647467011^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3828226071 10000000000 5760647467011 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1536670249/2000000000 : ℝ), (-60912879/10000000000 : ℝ), (3828226071/10000000000 : ℝ)] ![(35531192566263/50000000000000 : ℝ), (67188763689/50000000000000 : ℝ), (5760647467011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1536670249/2000000000 : ℝ)|^35 ≤ (35531192566263/50000000000000 : ℝ)^27
        have hw : |(1536670249/2000000000 : ℝ)|=(1536670249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-60912879/10000000000 : ℝ)|^35 ≤ (67188763689/50000000000000 : ℝ)^27
        have hw : |(-60912879/10000000000 : ℝ)|=(60912879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3828226071/10000000000 : ℝ)|^35 ≤ (5760647467011/20000000000000 : ℝ)^27
        have hw : |(3828226071/10000000000 : ℝ)|=(3828226071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1474617407/5000000000 : ℝ)*x 0 + (1593957181/2000000000 : ℝ)*x 1 + (-245813343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1474617407/5000000000 : ℝ)^35 ≤ (10269663207379/50000000000000 : ℝ)^27 := by
    have hnat : (1474617407 : ℕ)^35*50000000000000^27 ≤ 10269663207379^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1474617407 5000000000 10269663207379 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1593957181/2000000000 : ℝ)^35 ≤ (18628833989061/25000000000000 : ℝ)^27 := by
    have hnat : (1593957181 : ℕ)^35*25000000000000^27 ≤ 18628833989061^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593957181 2000000000 18628833989061 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245813343/2500000000 : ℝ)^35 ≤ (2472668810821/50000000000000 : ℝ)^27 := by
    have hnat : (245813343 : ℕ)^35*50000000000000^27 ≤ 2472668810821^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245813343 2500000000 2472668810821 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1474617407/5000000000 : ℝ), (1593957181/2000000000 : ℝ), (-245813343/2500000000 : ℝ)] ![(10269663207379/50000000000000 : ℝ), (18628833989061/25000000000000 : ℝ), (2472668810821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1474617407/5000000000 : ℝ)|^35 ≤ (10269663207379/50000000000000 : ℝ)^27
        have hw : |(1474617407/5000000000 : ℝ)|=(1474617407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1593957181/2000000000 : ℝ)|^35 ≤ (18628833989061/25000000000000 : ℝ)^27
        have hw : |(1593957181/2000000000 : ℝ)|=(1593957181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245813343/2500000000 : ℝ)|^35 ≤ (2472668810821/50000000000000 : ℝ)^27
        have hw : |(-245813343/2500000000 : ℝ)|=(245813343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s2_s2_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7676041121/10000000000 : ℝ)*x 0 + (631105891/2500000000 : ℝ)*x 1 + (1977814019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7676041121/10000000000 : ℝ)^35 ≤ (70974754310809/100000000000000 : ℝ)^27 := by
    have hnat : (7676041121 : ℕ)^35*100000000000000^27 ≤ 70974754310809^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7676041121 10000000000 70974754310809 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (631105891/2500000000 : ℝ)^35 ≤ (16789010742919/100000000000000 : ℝ)^27 := by
    have hnat : (631105891 : ℕ)^35*100000000000000^27 ≤ 16789010742919^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631105891 2500000000 16789010742919 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1977814019/10000000000 : ℝ)^35 ≤ (382382341633/3125000000000 : ℝ)^27 := by
    have hnat : (1977814019 : ℕ)^35*3125000000000^27 ≤ 382382341633^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977814019 10000000000 382382341633 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7676041121/10000000000 : ℝ), (631105891/2500000000 : ℝ), (1977814019/10000000000 : ℝ)] ![(70974754310809/100000000000000 : ℝ), (16789010742919/100000000000000 : ℝ), (382382341633/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7676041121/10000000000 : ℝ)|^35 ≤ (70974754310809/100000000000000 : ℝ)^27
        have hw : |(7676041121/10000000000 : ℝ)|=(7676041121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(631105891/2500000000 : ℝ)|^35 ≤ (16789010742919/100000000000000 : ℝ)^27
        have hw : |(631105891/2500000000 : ℝ)|=(631105891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1977814019/10000000000 : ℝ)|^35 ≤ (382382341633/3125000000000 : ℝ)^27
        have hw : |(1977814019/10000000000 : ℝ)|=(1977814019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309063_s2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((79473/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79473/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79397/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19187/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19187/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((68201/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68201/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68561/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(68561/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32961/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32961/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (79473/100000 : ℝ) ^ (69/16 : ℝ) ≤ (18563807705397555477/50000000000000000000 : ℝ) := by
    have hpowers : (79473/100000 : ℝ)^69 ≤ (18563807705397555477/50000000000000000000 : ℝ)^16 := by
      have hnat : (79473 : ℕ)^69*50000000000000000000^16 ≤ 18563807705397555477^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79473 100000 18563807705397555477 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79473/100000 : ℝ)) (X := (18563807705397555477/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (68563807705397555477/50000000000000000000 : ℝ) ≤ (21014890084191/19531250000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (68563807705397555477/50000000000000000000 : ℝ)^16 ≤ (21014890084191/19531250000000 : ℝ)^69 := by
      have hnat : (68563807705397555477 : ℕ)^16*19531250000000^69 ≤ 21014890084191^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68563807705397555477 50000000000000000000 21014890084191 19531250000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (21014890084191/19531250000000 : ℝ)) (X := (68563807705397555477/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (43563807705397555477/25000000000000000000 : ℝ) ≤ (1137436465954577/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (43563807705397555477/25000000000000000000 : ℝ)^16 ≤ (1137436465954577/1000000000000000 : ℝ)^69 := by
      have hnat : (43563807705397555477 : ℕ)^16*1000000000000000^69 ≤ 1137436465954577^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43563807705397555477 25000000000000000000 1137436465954577 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1137436465954577/1000000000000000 : ℝ)) (X := (43563807705397555477/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1483640084191/15522070312500 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(307370468219989/3973650000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (79473/100000 : ℝ)) (alpha := (1483640084191/15522070312500 : ℝ)) (beta := (307370468219989/3973650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (79473/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1483640084191/15522070312500 : ℝ)*((1 : ℝ)*pair X 0 1)+(307370468219989/3973650000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (79397/100000 : ℝ) ^ (69/16 : ℝ) ≤ (36974741897826064797/100000000000000000000 : ℝ) := by
    have hpowers : (79397/100000 : ℝ)^69 ≤ (36974741897826064797/100000000000000000000 : ℝ)^16 := by
      have hnat : (79397 : ℕ)^69*100000000000000000000^16 ≤ 36974741897826064797^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79397 100000 36974741897826064797 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79397/100000 : ℝ)) (X := (36974741897826064797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (136974741897826064797/100000000000000000000 : ℝ) ≤ (1344605131942079/1250000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (136974741897826064797/100000000000000000000 : ℝ)^16 ≤ (1344605131942079/1250000000000000 : ℝ)^69 := by
      have hnat : (136974741897826064797 : ℕ)^16*1250000000000000^69 ≤ 1344605131942079^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        136974741897826064797 100000000000000000000 1344605131942079 1250000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1344605131942079/1250000000000000 : ℝ)) (X := (136974741897826064797/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (86974741897826064797/50000000000000000000 : ℝ) ≤ (28424334347831/25000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (86974741897826064797/50000000000000000000 : ℝ)^16 ≤ (28424334347831/25000000000000 : ℝ)^69 := by
      have hnat : (86974741897826064797 : ℕ)^16*25000000000000^69 ≤ 28424334347831^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86974741897826064797 50000000000000000000 28424334347831 25000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (28424334347831/25000000000000 : ℝ)) (X := (86974741897826064797/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(94605131942079/992462500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(76611585449471/992462500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (79397/100000 : ℝ)) (alpha := (94605131942079/992462500000000 : ℝ)) (beta := (76611585449471/992462500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (79397/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(94605131942079/992462500000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(76611585449471/992462500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (19187/25000 : ℝ) ^ (69/16 : ℝ) ≤ (3992654576436399223/12500000000000000000 : ℝ) := by
    have hpowers : (19187/25000 : ℝ)^69 ≤ (3992654576436399223/12500000000000000000 : ℝ)^16 := by
      have hnat : (19187 : ℕ)^69*12500000000000000000^16 ≤ 3992654576436399223^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19187 25000 3992654576436399223 12500000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19187/25000 : ℝ)) (X := (3992654576436399223/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (16492654576436399223/12500000000000000000 : ℝ) ≤ (2132771487522623/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (16492654576436399223/12500000000000000000 : ℝ)^16 ≤ (2132771487522623/2000000000000000 : ℝ)^69 := by
      have hnat : (16492654576436399223 : ℕ)^16*2000000000000000^69 ≤ 2132771487522623^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16492654576436399223 12500000000000000000 2132771487522623 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2132771487522623/2000000000000000 : ℝ)) (X := (16492654576436399223/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (10242654576436399223/6250000000000000000 : ℝ) ≤ (11213641532690607/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (10242654576436399223/6250000000000000000 : ℝ)^16 ≤ (11213641532690607/10000000000000000 : ℝ)^69 := by
      have hnat : (10242654576436399223 : ℕ)^16*10000000000000000^69 ≤ 11213641532690607^69*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10242654576436399223 6250000000000000000 11213641532690607 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11213641532690607/10000000000000000 : ℝ)) (X := (10242654576436399223/6250000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(132771487522623/1534960000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(137446023769373/1918700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (19187/25000 : ℝ)) (alpha := (132771487522623/1534960000000000 : ℝ)) (beta := (137446023769373/1918700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (19187/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(132771487522623/1534960000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(137446023769373/1918700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-731442107/10000000000 : ℝ)*X 0 0+(5608649099/10000000000 : ℝ)*X 0 1+(2900904543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((5608563957/10000000000 : ℝ)*X 1 0+(-729541537/10000000000 : ℝ)*X 1 1+(5802921913/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2835205653/5000000000 : ℝ)*X 2 0+(722059449/1250000000 : ℝ)*X 2 1+(-13282847/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((36460421/80000000 : ℝ)*X 0 0+(4320663973/10000000000 : ℝ)*X 0 1+(3970255079/10000000000 : ℝ)*X 0 2+(36460421/80000000 : ℝ)*X 1 0+(4320663973/10000000000 : ℝ)*X 1 1+(3970255079/10000000000 : ℝ)*X 1 2+(36460421/80000000 : ℝ)*X 2 0+(4320663973/10000000000 : ℝ)*X 2 1+(3970255079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-524527827/5000000000 : ℝ)*X 0 0+(3150142207/10000000000 : ℝ)*X 0 1+(389112481/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1831518469/5000000000 : ℝ)*X 1 0+(-17579391/1000000000 : ℝ)*X 1 1+(3891799171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((3479225289/10000000000 : ℝ)*X 2 0+(1991061671/2500000000 : ℝ)*X 2 1+(-25259999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((443434927/1250000000 : ℝ)*X 0 0+(442345729/625000000 : ℝ)*X 0 1+(1695167877/10000000000 : ℝ)*X 0 2+(443434927/1250000000 : ℝ)*X 1 0+(442345729/625000000 : ℝ)*X 1 1+(1695167877/10000000000 : ℝ)*X 1 2+(443434927/1250000000 : ℝ)*X 2 0+(442345729/625000000 : ℝ)*X 2 1+(1695167877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-7223181/500000000 : ℝ)*X 0 0+(3576449889/10000000000 : ℝ)*X 0 1+(157248061/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((121616033/400000000 : ℝ)*X 1 0+(-131553369/1250000000 : ℝ)*X 1 1+(7863768501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((7716416307/10000000000 : ℝ)*X 2 0+(118203909/312500000 : ℝ)*X 2 1+(-15436409/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7536642847/10000000000 : ℝ)*X 0 0+(744020961/2500000000 : ℝ)*X 0 1+(420209477/2500000000 : ℝ)*X 0 2+(7536642847/10000000000 : ℝ)*X 1 0+(744020961/2500000000 : ℝ)*X 1 1+(420209477/2500000000 : ℝ)*X 1 2+(7536642847/10000000000 : ℝ)*X 2 0+(744020961/2500000000 : ℝ)*X 2 1+(420209477/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-142431579/10000000000 : ℝ)*X 0 0+(284956827/400000000 : ℝ)*X 0 1+(558195217/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1536670249/2000000000 : ℝ)*X 1 0+(-60912879/10000000000 : ℝ)*X 1 1+(3828226071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1474617407/5000000000 : ℝ)*X 2 0+(1593957181/2000000000 : ℝ)*X 2 1+(-245813343/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((7676041121/10000000000 : ℝ)*X 0 0+(631105891/2500000000 : ℝ)*X 0 1+(1977814019/10000000000 : ℝ)*X 0 2+(7676041121/10000000000 : ℝ)*X 1 0+(631105891/2500000000 : ℝ)*X 1 1+(1977814019/10000000000 : ℝ)*X 1 2+(7676041121/10000000000 : ℝ)*X 2 0+(631105891/2500000000 : ℝ)*X 2 1+(1977814019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((68201/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68201/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16398281884980744202741029826807/1008903270533725000000000000000000000 : ℝ) := by norm_num
    linear_combination (621929244907/1000000000000 : ℝ)*(base7) + (2022769/1000000000000 : ℝ)*(base50) + (59453275443/1000000000000 : ℝ)*(base60) + (487671108703/250000000000 : ℝ)*(major_s2_0) + (487671108703/250000000000 : ℝ)*(major_s2_1) + (487671108703/250000000000 : ℝ)*(major_s2_2) + (12413191/1000000000000 : ℝ)*(sp_s2_0) + (1555811/1000000000000 : ℝ)*(sp_s2_6) + (574420041163/250000000000 : ℝ)*(sp_s2_7) + (1148888915367/500000000000 : ℝ)*(sp_s2_8) + (1148888438883/500000000000 : ℝ)*(sp_s2_9) + (1846870347239/1000000000000 : ℝ)*(sp_s2_13) + (85252891/1000000000000 : ℝ)*(sp_s2_14) + (119121/125000000000 : ℝ)*(sp_s2_23) + (1224942658143/1000000000000 : ℝ)*(f.failure) + (1148888915367/500000000000 : ℝ)*(f.sum) + (9932796524877756387/152339023900000000000000000000000 : ℝ)*base62 + (66379446764447/959350000000000000000000000 : ℝ)*base64 + (486769198826859/496231250000000000000000000 : ℝ)*base66 + (78279379655573/76748000000000000000000000 : ℝ)*base68 + (37299119380795236353/76242422550000000000000000000000 : ℝ)*base71 + (164860343160527/248353125000000000000000000 : ℝ)*base72 + (488243144529033/3969850000000000000000000000 : ℝ)*base74 + (2550075058661243/3973650000000000000000000000 : ℝ)*base76 + (2931816337772359339/7887397226250000000000000000000 : ℝ)*base78 + (98321/100000000000000000 : ℝ)*base87 + (98321/100000000000000000 : ℝ)*base89 + (98321/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68561/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(68561/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (122089414040246013832016274133/14412903864767500000000000000000000 : ℝ) := by norm_num
    linear_combination (645120318527/1000000000000 : ℝ)*(base7) + (14047/1000000000000 : ℝ)*(base39) + (12141/20000000000 : ℝ)*(base49) + (374135061503/200000000000 : ℝ)*(major_s2_0) + (374135061503/200000000000 : ℝ)*(major_s2_1) + (374135061503/200000000000 : ℝ)*(major_s2_2) + (642599/500000000000 : ℝ)*(sp_s2_1) + (39529467/1000000000000 : ℝ)*(sp_s2_8) + (1086942402383/500000000000 : ℝ)*(sp_s2_14) + (2173844322989/1000000000000 : ℝ)*(sp_s2_15) + (434777027531/200000000000 : ℝ)*(sp_s2_16) + (363954889609/200000000000 : ℝ)*(sp_s2_20) + (332889/1000000000000 : ℝ)*(sp_s2_21) + (23185957/500000000000 : ℝ)*(sp_s2_27) + (146837562679/125000000000 : ℝ)*(f.failure) + (434777027531/200000000000 : ℝ)*(f.sum) + (1157625689556555889/17410174160000000000000000000000 : ℝ)*base62 + (12331568079533/54820000000000000000000000 : ℝ)*base64 + (208292053585429/396985000000000000000000000 : ℝ)*base66 + (61070029010787/219280000000000000000000000 : ℝ)*base69 + (45659500728841943/871341972000000000000000000000 : ℝ)*base70 + (10314618699181/99341250000000000000000000 : ℝ)*base73 + (28074614610527/79397000000000000000000000 : ℝ)*base74 + (5876906653559/39736500000000000000000000 : ℝ)*base76 + (4921311924140175967/7887397226250000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (5213/12500000000000000 : ℝ)*base87 + (5213/12500000000000000 : ℝ)*base89 + (5213/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32961/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32961/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6186527730989139195460184415359/1614245232853960000000000000000000000 : ℝ) := by norm_num
    linear_combination (638058739929/1000000000000 : ℝ)*(base7) + (132774352159/1000000000000 : ℝ)*(base40) + (321729/1000000000000 : ℝ)*(base49) + (359649551749/200000000000 : ℝ)*(major_s2_0) + (359649551749/200000000000 : ℝ)*(major_s2_1) + (359649551749/200000000000 : ℝ)*(major_s2_2) + (4529139/1000000000000 : ℝ)*(sp_s2_1) + (6044393/1000000000000 : ℝ)*(sp_s2_2) + (25064547/1000000000000 : ℝ)*(sp_s2_9) + (94309/31250000000 : ℝ)*(sp_s2_20) + (1039406040353/500000000000 : ℝ)*(sp_s2_21) + (2078807551567/1000000000000 : ℝ)*(sp_s2_22) + (1039390485883/500000000000 : ℝ)*(sp_s2_23) + (441818739823/250000000000 : ℝ)*(sp_s2_27) + (1129219237251/1000000000000 : ℝ)*(f.failure) + (1039406040353/500000000000 : ℝ)*(f.sum) + (29099893928946333069/121871219120000000000000000000000 : ℝ)*base62 + (169578104858163/383740000000000000000000000 : ℝ)*base64 + (3123606200617/19849250000000000000000000 : ℝ)*base66 + (752309326883241/1534960000000000000000000000 : ℝ)*base68 + (5182479189719545369/30496969020000000000000000000000 : ℝ)*base71 + (621641727407807/794730000000000000000000000 : ℝ)*base72 + (508521274081517/793970000000000000000000000 : ℝ)*base74 + (57881291717329/397365000000000000000000000 : ℝ)*base76 + (7606352856359960779/63099177810000000000000000000000 : ℝ)*base78 + (9997/100000000000000000 : ℝ)*base87 + (9997/100000000000000000 : ℝ)*base89 + (9997/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((79473/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79473/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79397/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19187/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19187/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((68201/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68201/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68561/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(68561/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32961/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32961/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309063_s2 p hpa hpb X hX hprev1

#print axioms solution
