-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:20:53.835467+00:00
-- url     : https://prove2.me/submissions/794cf922-b8a3-4946-b877-e23c9a01e969

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
theorem collision_support_c312062_s1_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-22919551/200000000 : ℝ)*x 0 + (505147793/1000000000 : ℝ)*x 1 + (-750827003/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22919551/200000000 : ℝ)^73 ≤ (6238572021983/100000000000000 : ℝ)^57 := by
    have hnat : (22919551 : ℕ)^73*100000000000000^57 ≤ 6238572021983^57*200000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22919551 200000000 6238572021983 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505147793/1000000000 : ℝ)^73 ≤ (8340603902519/20000000000000 : ℝ)^57 := by
    have hnat : (505147793 : ℕ)^73*20000000000000^57 ≤ 8340603902519^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505147793 1000000000 8340603902519 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (750827003/1250000000 : ℝ)^73 ≤ (26029204226049/50000000000000 : ℝ)^57 := by
    have hnat : (750827003 : ℕ)^73*50000000000000^57 ≤ 26029204226049^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750827003 1250000000 26029204226049 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22919551/200000000 : ℝ), (505147793/1000000000 : ℝ), (-750827003/1250000000 : ℝ)] ![(6238572021983/100000000000000 : ℝ), (8340603902519/20000000000000 : ℝ), (26029204226049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22919551/200000000 : ℝ)|^73 ≤ (6238572021983/100000000000000 : ℝ)^57
        have hw : |(-22919551/200000000 : ℝ)|=(22919551/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(505147793/1000000000 : ℝ)|^73 ≤ (8340603902519/20000000000000 : ℝ)^57
        have hw : |(505147793/1000000000 : ℝ)|=(505147793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-750827003/1250000000 : ℝ)|^73 ≤ (26029204226049/50000000000000 : ℝ)^57
        have hw : |(-750827003/1250000000 : ℝ)|=(750827003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5094037393/10000000000 : ℝ)*x 0 + (-1168074217/10000000000 : ℝ)*x 1 + (-1488010369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5094037393/10000000000 : ℝ)^73 ≤ (1686141220231/4000000000000 : ℝ)^57 := by
    have hnat : (5094037393 : ℕ)^73*4000000000000^57 ≤ 1686141220231^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5094037393 10000000000 1686141220231 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1168074217/10000000000 : ℝ)^73 ≤ (6393044886623/100000000000000 : ℝ)^57 := by
    have hnat : (1168074217 : ℕ)^73*100000000000000^57 ≤ 6393044886623^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168074217 10000000000 6393044886623 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1488010369/2500000000 : ℝ)^73 ≤ (51453424585339/100000000000000 : ℝ)^57 := by
    have hnat : (1488010369 : ℕ)^73*100000000000000^57 ≤ 51453424585339^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1488010369 2500000000 51453424585339 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5094037393/10000000000 : ℝ), (-1168074217/10000000000 : ℝ), (-1488010369/2500000000 : ℝ)] ![(1686141220231/4000000000000 : ℝ), (6393044886623/100000000000000 : ℝ), (51453424585339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5094037393/10000000000 : ℝ)|^73 ≤ (1686141220231/4000000000000 : ℝ)^57
        have hw : |(5094037393/10000000000 : ℝ)|=(5094037393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1168074217/10000000000 : ℝ)|^73 ≤ (6393044886623/100000000000000 : ℝ)^57
        have hw : |(-1168074217/10000000000 : ℝ)|=(1168074217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1488010369/2500000000 : ℝ)|^73 ≤ (51453424585339/100000000000000 : ℝ)^57
        have hw : |(-1488010369/2500000000 : ℝ)|=(1488010369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1334795347/2500000000 : ℝ)*x 0 + (5389177523/10000000000 : ℝ)*x 1 + (1646691709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1334795347/2500000000 : ℝ)^73 ≤ (44768891241607/100000000000000 : ℝ)^57 := by
    have hnat : (1334795347 : ℕ)^73*100000000000000^57 ≤ 44768891241607^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334795347 2500000000 44768891241607 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389177523/10000000000 : ℝ)^73 ≤ (353956923759/781250000000 : ℝ)^57 := by
    have hnat : (5389177523 : ℕ)^73*781250000000^57 ≤ 353956923759^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389177523 10000000000 353956923759 781250000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1646691709/10000000000 : ℝ)^73 ≤ (1984924500769/20000000000000 : ℝ)^57 := by
    have hnat : (1646691709 : ℕ)^73*20000000000000^57 ≤ 1984924500769^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1646691709 10000000000 1984924500769 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1334795347/2500000000 : ℝ), (5389177523/10000000000 : ℝ), (1646691709/10000000000 : ℝ)] ![(44768891241607/100000000000000 : ℝ), (353956923759/781250000000 : ℝ), (1984924500769/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1334795347/2500000000 : ℝ)|^73 ≤ (44768891241607/100000000000000 : ℝ)^57
        have hw : |(1334795347/2500000000 : ℝ)|=(1334795347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389177523/10000000000 : ℝ)|^73 ≤ (353956923759/781250000000 : ℝ)^57
        have hw : |(5389177523/10000000000 : ℝ)|=(5389177523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1646691709/10000000000 : ℝ)|^73 ≤ (1984924500769/20000000000000 : ℝ)^57
        have hw : |(1646691709/10000000000 : ℝ)|=(1646691709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-148438829/1000000000 : ℝ)*x 0 + (3020980189/10000000000 : ℝ)*x 1 + (-3772843583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (148438829/1000000000 : ℝ)^73 ≤ (1086199173471/12500000000000 : ℝ)^57 := by
    have hnat : (148438829 : ℕ)^73*12500000000000^57 ≤ 1086199173471^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148438829 1000000000 1086199173471 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3020980189/10000000000 : ℝ)^73 ≤ (5397149934431/25000000000000 : ℝ)^57 := by
    have hnat : (3020980189 : ℕ)^73*25000000000000^57 ≤ 5397149934431^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3020980189 10000000000 5397149934431 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3772843583/5000000000 : ℝ)^73 ≤ (17430451714851/25000000000000 : ℝ)^57 := by
    have hnat : (3772843583 : ℕ)^73*25000000000000^57 ≤ 17430451714851^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3772843583 5000000000 17430451714851 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-148438829/1000000000 : ℝ), (3020980189/10000000000 : ℝ), (-3772843583/5000000000 : ℝ)] ![(1086199173471/12500000000000 : ℝ), (5397149934431/25000000000000 : ℝ), (17430451714851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-148438829/1000000000 : ℝ)|^73 ≤ (1086199173471/12500000000000 : ℝ)^57
        have hw : |(-148438829/1000000000 : ℝ)|=(148438829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3020980189/10000000000 : ℝ)|^73 ≤ (5397149934431/25000000000000 : ℝ)^57
        have hw : |(3020980189/10000000000 : ℝ)|=(3020980189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3772843583/5000000000 : ℝ)|^73 ≤ (17430451714851/25000000000000 : ℝ)^57
        have hw : |(-3772843583/5000000000 : ℝ)|=(3772843583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3545753329/10000000000 : ℝ)*x 0 + (-399579267/5000000000 : ℝ)*x 1 + (-7532361313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3545753329/10000000000 : ℝ)^73 ≤ (1656498046449/6250000000000 : ℝ)^57 := by
    have hnat : (3545753329 : ℕ)^73*6250000000000^57 ≤ 1656498046449^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3545753329 10000000000 1656498046449 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399579267/5000000000 : ℝ)^73 ≤ (1965939222357/50000000000000 : ℝ)^57 := by
    have hnat : (399579267 : ℕ)^73*50000000000000^57 ≤ 1965939222357^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399579267 5000000000 1965939222357 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7532361313/10000000000 : ℝ)^73 ≤ (6956415280077/10000000000000 : ℝ)^57 := by
    have hnat : (7532361313 : ℕ)^73*10000000000000^57 ≤ 6956415280077^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7532361313 10000000000 6956415280077 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3545753329/10000000000 : ℝ), (-399579267/5000000000 : ℝ), (-7532361313/10000000000 : ℝ)] ![(1656498046449/6250000000000 : ℝ), (1965939222357/50000000000000 : ℝ), (6956415280077/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3545753329/10000000000 : ℝ)|^73 ≤ (1656498046449/6250000000000 : ℝ)^57
        have hw : |(3545753329/10000000000 : ℝ)|=(3545753329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-399579267/5000000000 : ℝ)|^73 ≤ (1965939222357/50000000000000 : ℝ)^57
        have hw : |(-399579267/5000000000 : ℝ)|=(399579267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7532361313/10000000000 : ℝ)|^73 ≤ (6956415280077/10000000000000 : ℝ)^57
        have hw : |(-7532361313/10000000000 : ℝ)|=(7532361313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3694286379/10000000000 : ℝ)*x 0 + (7078130769/10000000000 : ℝ)*x 1 + (171021719/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3694286379/10000000000 : ℝ)^73 ≤ (27934160734837/100000000000000 : ℝ)^57 := by
    have hnat : (3694286379 : ℕ)^73*100000000000000^57 ≤ 27934160734837^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3694286379 10000000000 27934160734837 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7078130769/10000000000 : ℝ)^73 ≤ (64237771267619/100000000000000 : ℝ)^57 := by
    have hnat : (7078130769 : ℕ)^73*100000000000000^57 ≤ 64237771267619^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7078130769 10000000000 64237771267619 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171021719/1250000000 : ℝ)^73 ≤ (1565613597597/20000000000000 : ℝ)^57 := by
    have hnat : (171021719 : ℕ)^73*20000000000000^57 ≤ 1565613597597^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171021719 1250000000 1565613597597 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3694286379/10000000000 : ℝ), (7078130769/10000000000 : ℝ), (171021719/1250000000 : ℝ)] ![(27934160734837/100000000000000 : ℝ), (64237771267619/100000000000000 : ℝ), (1565613597597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3694286379/10000000000 : ℝ)|^73 ≤ (27934160734837/100000000000000 : ℝ)^57
        have hw : |(3694286379/10000000000 : ℝ)|=(3694286379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7078130769/10000000000 : ℝ)|^73 ≤ (64237771267619/100000000000000 : ℝ)^57
        have hw : |(7078130769/10000000000 : ℝ)|=(7078130769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171021719/1250000000 : ℝ)|^73 ≤ (1565613597597/20000000000000 : ℝ)^57
        have hw : |(171021719/1250000000 : ℝ)|=(171021719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2045571283/5000000000 : ℝ)*x 0 + (7411984007/10000000000 : ℝ)*x 1 + (-14238789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2045571283/5000000000 : ℝ)^73 ≤ (15916908521823/50000000000000 : ℝ)^57 := by
    have hnat : (2045571283 : ℕ)^73*50000000000000^57 ≤ 15916908521823^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045571283 5000000000 15916908521823 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7411984007/10000000000 : ℝ)^73 ≤ (34071782634967/50000000000000 : ℝ)^57 := by
    have hnat : (7411984007 : ℕ)^73*50000000000000^57 ≤ 34071782634967^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7411984007 10000000000 34071782634967 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14238789/10000000000 : ℝ)^73 ≤ (11308837177/50000000000000 : ℝ)^57 := by
    have hnat : (14238789 : ℕ)^73*50000000000000^57 ≤ 11308837177^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14238789 10000000000 11308837177 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2045571283/5000000000 : ℝ), (7411984007/10000000000 : ℝ), (-14238789/10000000000 : ℝ)] ![(15916908521823/50000000000000 : ℝ), (34071782634967/50000000000000 : ℝ), (11308837177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2045571283/5000000000 : ℝ)|^73 ≤ (15916908521823/50000000000000 : ℝ)^57
        have hw : |(2045571283/5000000000 : ℝ)|=(2045571283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7411984007/10000000000 : ℝ)|^73 ≤ (34071782634967/50000000000000 : ℝ)^57
        have hw : |(7411984007/10000000000 : ℝ)|=(7411984007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14238789/10000000000 : ℝ)|^73 ≤ (11308837177/50000000000000 : ℝ)^57
        have hw : |(-14238789/10000000000 : ℝ)|=(14238789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-157380681/2000000000 : ℝ)*x 0 + (697022463/2000000000 : ℝ)*x 1 + (-237118177/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (157380681/2000000000 : ℝ)^73 ≤ (1927412342667/50000000000000 : ℝ)^57 := by
    have hnat : (157380681 : ℕ)^73*50000000000000^57 ≤ 1927412342667^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157380681 2000000000 1927412342667 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (697022463/2000000000 : ℝ)^73 ≤ (2592484839403/10000000000000 : ℝ)^57 := by
    have hnat : (697022463 : ℕ)^73*10000000000000^57 ≤ 2592484839403^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697022463 2000000000 2592484839403 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237118177/312500000 : ℝ)^73 ≤ (7022032690609/10000000000000 : ℝ)^57 := by
    have hnat : (237118177 : ℕ)^73*10000000000000^57 ≤ 7022032690609^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237118177 312500000 7022032690609 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-157380681/2000000000 : ℝ), (697022463/2000000000 : ℝ), (-237118177/312500000 : ℝ)] ![(1927412342667/50000000000000 : ℝ), (2592484839403/10000000000000 : ℝ), (7022032690609/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-157380681/2000000000 : ℝ)|^73 ≤ (1927412342667/50000000000000 : ℝ)^57
        have hw : |(-157380681/2000000000 : ℝ)|=(157380681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(697022463/2000000000 : ℝ)|^73 ≤ (2592484839403/10000000000000 : ℝ)^57
        have hw : |(697022463/2000000000 : ℝ)|=(697022463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-237118177/312500000 : ℝ)|^73 ≤ (7022032690609/10000000000000 : ℝ)^57
        have hw : |(-237118177/312500000 : ℝ)|=(237118177/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2983091351/10000000000 : ℝ)*x 0 + (-148524021/1000000000 : ℝ)*x 1 + (-1893595937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2983091351/10000000000 : ℝ)^73 ≤ (21242446478943/100000000000000 : ℝ)^57 := by
    have hnat : (2983091351 : ℕ)^73*100000000000000^57 ≤ 21242446478943^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2983091351 10000000000 21242446478943 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148524021/1000000000 : ℝ)^73 ≤ (8695980929199/100000000000000 : ℝ)^57 := by
    have hnat : (148524021 : ℕ)^73*100000000000000^57 ≤ 8695980929199^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148524021 1000000000 8695980929199 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1893595937/2500000000 : ℝ)^73 ≤ (13683900893/19531250000 : ℝ)^57 := by
    have hnat : (1893595937 : ℕ)^73*19531250000^57 ≤ 13683900893^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893595937 2500000000 13683900893 19531250000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2983091351/10000000000 : ℝ), (-148524021/1000000000 : ℝ), (-1893595937/2500000000 : ℝ)] ![(21242446478943/100000000000000 : ℝ), (8695980929199/100000000000000 : ℝ), (13683900893/19531250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2983091351/10000000000 : ℝ)|^73 ≤ (21242446478943/100000000000000 : ℝ)^57
        have hw : |(2983091351/10000000000 : ℝ)|=(2983091351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-148524021/1000000000 : ℝ)|^73 ≤ (8695980929199/100000000000000 : ℝ)^57
        have hw : |(-148524021/1000000000 : ℝ)|=(148524021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1893595937/2500000000 : ℝ)|^73 ≤ (13683900893/19531250000 : ℝ)^57
        have hw : |(-1893595937/2500000000 : ℝ)|=(1893595937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6909987781/10000000000 : ℝ)*x 0 + (1942951953/5000000000 : ℝ)*x 1 + (1378918391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6909987781/10000000000 : ℝ)^73 ≤ (31144995642973/50000000000000 : ℝ)^57 := by
    have hnat : (6909987781 : ℕ)^73*50000000000000^57 ≤ 31144995642973^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6909987781 10000000000 31144995642973 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942951953/5000000000 : ℝ)^73 ≤ (29803121748731/100000000000000 : ℝ)^57 := by
    have hnat : (1942951953 : ℕ)^73*100000000000000^57 ≤ 29803121748731^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942951953 5000000000 29803121748731 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378918391/10000000000 : ℝ)^73 ≤ (1976721736621/25000000000000 : ℝ)^57 := by
    have hnat : (1378918391 : ℕ)^73*25000000000000^57 ≤ 1976721736621^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378918391 10000000000 1976721736621 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6909987781/10000000000 : ℝ), (1942951953/5000000000 : ℝ), (1378918391/10000000000 : ℝ)] ![(31144995642973/50000000000000 : ℝ), (29803121748731/100000000000000 : ℝ), (1976721736621/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6909987781/10000000000 : ℝ)|^73 ≤ (31144995642973/50000000000000 : ℝ)^57
        have hw : |(6909987781/10000000000 : ℝ)|=(6909987781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1942951953/5000000000 : ℝ)|^73 ≤ (29803121748731/100000000000000 : ℝ)^57
        have hw : |(1942951953/5000000000 : ℝ)|=(1942951953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1378918391/10000000000 : ℝ)|^73 ≤ (1976721736621/25000000000000 : ℝ)^57
        have hw : |(1378918391/10000000000 : ℝ)|=(1378918391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7685343467/10000000000 : ℝ)*x 0 + (940506343/2500000000 : ℝ)*x 1 + (-17500283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7685343467/10000000000 : ℝ)^73 ≤ (7137872134761/10000000000000 : ℝ)^57 := by
    have hnat : (7685343467 : ℕ)^73*10000000000000^57 ≤ 7137872134761^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7685343467 10000000000 7137872134761 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (940506343/2500000000 : ℝ)^73 ≤ (28591823366333/100000000000000 : ℝ)^57 := by
    have hnat : (940506343 : ℕ)^73*100000000000000^57 ≤ 28591823366333^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940506343 2500000000 28591823366333 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17500283/10000000000 : ℝ)^73 ≤ (29455268553/100000000000000 : ℝ)^57 := by
    have hnat : (17500283 : ℕ)^73*100000000000000^57 ≤ 29455268553^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17500283 10000000000 29455268553 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7685343467/10000000000 : ℝ), (940506343/2500000000 : ℝ), (-17500283/10000000000 : ℝ)] ![(7137872134761/10000000000000 : ℝ), (28591823366333/100000000000000 : ℝ), (29455268553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7685343467/10000000000 : ℝ)|^73 ≤ (7137872134761/10000000000000 : ℝ)^57
        have hw : |(7685343467/10000000000 : ℝ)|=(7685343467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(940506343/2500000000 : ℝ)|^73 ≤ (28591823366333/100000000000000 : ℝ)^57
        have hw : |(940506343/2500000000 : ℝ)|=(940506343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17500283/10000000000 : ℝ)|^73 ≤ (29455268553/100000000000000 : ℝ)^57
        have hw : |(-17500283/10000000000 : ℝ)|=(17500283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-82749021/5000000000 : ℝ)*x 0 + (252961871/400000000 : ℝ)*x 1 + (-5255200541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82749021/5000000000 : ℝ)^73 ≤ (32710328697/6250000000000 : ℝ)^57 := by
    have hnat : (82749021 : ℕ)^73*6250000000000^57 ≤ 32710328697^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82749021 5000000000 32710328697 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252961871/400000000 : ℝ)^73 ≤ (55607585908991/100000000000000 : ℝ)^57 := by
    have hnat : (252961871 : ℕ)^73*100000000000000^57 ≤ 55607585908991^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252961871 400000000 55607585908991 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255200541/10000000000 : ℝ)^73 ≤ (43869048825707/100000000000000 : ℝ)^57 := by
    have hnat : (5255200541 : ℕ)^73*100000000000000^57 ≤ 43869048825707^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255200541 10000000000 43869048825707 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82749021/5000000000 : ℝ), (252961871/400000000 : ℝ), (-5255200541/10000000000 : ℝ)] ![(32710328697/6250000000000 : ℝ), (55607585908991/100000000000000 : ℝ), (43869048825707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82749021/5000000000 : ℝ)|^73 ≤ (32710328697/6250000000000 : ℝ)^57
        have hw : |(-82749021/5000000000 : ℝ)|=(82749021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(252961871/400000000 : ℝ)|^73 ≤ (55607585908991/100000000000000 : ℝ)^57
        have hw : |(252961871/400000000 : ℝ)|=(252961871/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5255200541/10000000000 : ℝ)|^73 ≤ (43869048825707/100000000000000 : ℝ)^57
        have hw : |(-5255200541/10000000000 : ℝ)|=(5255200541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (845617297/1250000000 : ℝ)*x 0 + (-583658377/10000000000 : ℝ)*x 1 + (-4576649911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845617297/1250000000 : ℝ)^73 ≤ (60620373559533/100000000000000 : ℝ)^57 := by
    have hnat : (845617297 : ℕ)^73*100000000000000^57 ≤ 60620373559533^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845617297 1250000000 60620373559533 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (583658377/10000000000 : ℝ)^73 ≤ (2629161790689/100000000000000 : ℝ)^57 := by
    have hnat : (583658377 : ℕ)^73*100000000000000^57 ≤ 2629161790689^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583658377 10000000000 2629161790689 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4576649911/10000000000 : ℝ)^73 ≤ (18375232319513/50000000000000 : ℝ)^57 := by
    have hnat : (4576649911 : ℕ)^73*50000000000000^57 ≤ 18375232319513^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4576649911 10000000000 18375232319513 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(845617297/1250000000 : ℝ), (-583658377/10000000000 : ℝ), (-4576649911/10000000000 : ℝ)] ![(60620373559533/100000000000000 : ℝ), (2629161790689/100000000000000 : ℝ), (18375232319513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(845617297/1250000000 : ℝ)|^73 ≤ (60620373559533/100000000000000 : ℝ)^57
        have hw : |(845617297/1250000000 : ℝ)|=(845617297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-583658377/10000000000 : ℝ)|^73 ≤ (2629161790689/100000000000000 : ℝ)^57
        have hw : |(-583658377/10000000000 : ℝ)|=(583658377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4576649911/10000000000 : ℝ)|^73 ≤ (18375232319513/50000000000000 : ℝ)^57
        have hw : |(-4576649911/10000000000 : ℝ)|=(4576649911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9006929/25000000 : ℝ)*x 0 + (1674777523/2500000000 : ℝ)*x 1 + (1021589361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9006929/25000000 : ℝ)^73 ≤ (13525517399327/50000000000000 : ℝ)^57 := by
    have hnat : (9006929 : ℕ)^73*50000000000000^57 ≤ 13525517399327^57*25000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9006929 25000000 13525517399327 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1674777523/2500000000 : ℝ)^73 ≤ (29932970539759/50000000000000 : ℝ)^57 := by
    have hnat : (1674777523 : ℕ)^73*50000000000000^57 ≤ 29932970539759^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674777523 2500000000 29932970539759 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021589361/5000000000 : ℝ)^73 ≤ (6541512052801/50000000000000 : ℝ)^57 := by
    have hnat : (1021589361 : ℕ)^73*50000000000000^57 ≤ 6541512052801^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021589361 5000000000 6541512052801 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9006929/25000000 : ℝ), (1674777523/2500000000 : ℝ), (1021589361/5000000000 : ℝ)] ![(13525517399327/50000000000000 : ℝ), (29932970539759/50000000000000 : ℝ), (6541512052801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9006929/25000000 : ℝ)|^73 ≤ (13525517399327/50000000000000 : ℝ)^57
        have hw : |(9006929/25000000 : ℝ)|=(9006929/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1674777523/2500000000 : ℝ)|^73 ≤ (29932970539759/50000000000000 : ℝ)^57
        have hw : |(1674777523/2500000000 : ℝ)|=(1674777523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1021589361/5000000000 : ℝ)|^73 ≤ (6541512052801/50000000000000 : ℝ)^57
        have hw : |(1021589361/5000000000 : ℝ)|=(1021589361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s1_s1_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1633042661/2000000000 : ℝ)*x 0 + (155185593/500000000 : ℝ)*x 1 + (-163531259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1633042661/2000000000 : ℝ)^73 ≤ (15427184119353/20000000000000 : ℝ)^57 := by
    have hnat : (1633042661 : ℕ)^73*20000000000000^57 ≤ 15427184119353^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633042661 2000000000 15427184119353 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155185593/500000000 : ℝ)^73 ≤ (2793583295483/12500000000000 : ℝ)^57 := by
    have hnat : (155185593 : ℕ)^73*12500000000000^57 ≤ 2793583295483^57*500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155185593 500000000 2793583295483 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163531259/10000000000 : ℝ)^73 ≤ (257706510077/50000000000000 : ℝ)^57 := by
    have hnat : (163531259 : ℕ)^73*50000000000000^57 ≤ 257706510077^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163531259 10000000000 257706510077 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1633042661/2000000000 : ℝ), (155185593/500000000 : ℝ), (-163531259/10000000000 : ℝ)] ![(15427184119353/20000000000000 : ℝ), (2793583295483/12500000000000 : ℝ), (257706510077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1633042661/2000000000 : ℝ)|^73 ≤ (15427184119353/20000000000000 : ℝ)^57
        have hw : |(1633042661/2000000000 : ℝ)|=(1633042661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(155185593/500000000 : ℝ)|^73 ≤ (2793583295483/12500000000000 : ℝ)^57
        have hw : |(155185593/500000000 : ℝ)|=(155185593/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-163531259/10000000000 : ℝ)|^73 ≤ (257706510077/50000000000000 : ℝ)^57
        have hw : |(-163531259/10000000000 : ℝ)|=(163531259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312062_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((21309/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21309/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(84429/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(84429/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-36901/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-36901/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16573/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16573/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66319/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66319/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-25603/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-25603/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (178281/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (21309/25000 : ℝ) ^ (9/2 : ℝ) ≤ (24365413021993218289/50000000000000000000 : ℝ) := by
    have hpowers : (21309/25000 : ℝ)^9 ≤ (24365413021993218289/50000000000000000000 : ℝ)^2 := by
      have hnat : (21309 : ℕ)^9*50000000000000000000^2 ≤ 24365413021993218289^2*25000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21309 25000 24365413021993218289 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21309/25000 : ℝ)) (X := (24365413021993218289/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (74365413021993218289/50000000000000000000 : ℝ) ≤ (10922230338362987/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (74365413021993218289/50000000000000000000 : ℝ)^2 ≤ (10922230338362987/10000000000000000 : ℝ)^9 := by
      have hnat : (74365413021993218289 : ℕ)^2*10000000000000000^9 ≤ 10922230338362987^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74365413021993218289 50000000000000000000 10922230338362987 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10922230338362987/10000000000000000 : ℝ)) (X := (74365413021993218289/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (49365413021993218289/25000000000000000000 : ℝ) ≤ (5816113074181593/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (49365413021993218289/25000000000000000000 : ℝ)^2 ≤ (5816113074181593/5000000000000000 : ℝ)^9 := by
      have hnat : (49365413021993218289 : ℕ)^2*5000000000000000^9 ≤ 5816113074181593^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        49365413021993218289 25000000000000000000 5816113074181593 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5816113074181593/5000000000000000 : ℝ)) (X := (49365413021993218289/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(922230338362987/8523600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(709995810000199/8523600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (21309/25000 : ℝ)) (alpha := (922230338362987/8523600000000000 : ℝ)) (beta := (709995810000199/8523600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (21309/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(922230338362987/8523600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(709995810000199/8523600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (84429/100000 : ℝ) ^ (9/2 : ℝ) ≤ (23344383471803414867/50000000000000000000 : ℝ) := by
    have hpowers : (84429/100000 : ℝ)^9 ≤ (23344383471803414867/50000000000000000000 : ℝ)^2 := by
      have hnat : (84429 : ℕ)^9*50000000000000000000^2 ≤ 23344383471803414867^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84429 100000 23344383471803414867 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (84429/100000 : ℝ)) (X := (23344383471803414867/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (73344383471803414867/50000000000000000000 : ℝ) ≤ (1361090781428953/1250000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (73344383471803414867/50000000000000000000 : ℝ)^2 ≤ (1361090781428953/1250000000000000 : ℝ)^9 := by
      have hnat : (73344383471803414867 : ℕ)^2*1250000000000000^9 ≤ 1361090781428953^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73344383471803414867 50000000000000000000 1361090781428953 1250000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1361090781428953/1250000000000000 : ℝ)) (X := (73344383471803414867/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (48344383471803414867/25000000000000000000 : ℝ) ≤ (22613918397351/19531250000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (48344383471803414867/25000000000000000000 : ℝ)^2 ≤ (22613918397351/19531250000000 : ℝ)^9 := by
      have hnat : (48344383471803414867 : ℕ)^2*19531250000000^9 ≤ 22613918397351^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48344383471803414867 25000000000000000000 22613918397351 19531250000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (22613918397351/19531250000000 : ℝ)) (X := (48344383471803414867/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(111090781428953/1055362500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(86199996001511/1055362500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (84429/100000 : ℝ)) (alpha := (111090781428953/1055362500000000 : ℝ)) (beta := (86199996001511/1055362500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (84429/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(111090781428953/1055362500000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(86199996001511/1055362500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (36901/50000 : ℝ) ^ (9/2 : ℝ) ≤ (25486288224016898981/100000000000000000000 : ℝ) := by
    have hpowers : (36901/50000 : ℝ)^9 ≤ (25486288224016898981/100000000000000000000 : ℝ)^2 := by
      have hnat : (36901 : ℕ)^9*100000000000000000000^2 ≤ 25486288224016898981^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36901 50000 25486288224016898981 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36901/50000 : ℝ)) (X := (25486288224016898981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (125486288224016898981/100000000000000000000 : ℝ) ≤ (10517445808691363/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (125486288224016898981/100000000000000000000 : ℝ)^2 ≤ (10517445808691363/10000000000000000 : ℝ)^9 := by
      have hnat : (125486288224016898981 : ℕ)^2*10000000000000000^9 ≤ 10517445808691363^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125486288224016898981 100000000000000000000 10517445808691363 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10517445808691363/10000000000000000 : ℝ)) (X := (125486288224016898981/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (75486288224016898981/50000000000000000000 : ℝ) ≤ (1369825160505219/1250000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (75486288224016898981/50000000000000000000 : ℝ)^2 ≤ (1369825160505219/1250000000000000 : ℝ)^9 := by
      have hnat : (75486288224016898981 : ℕ)^2*1250000000000000^9 ≤ 1369825160505219^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75486288224016898981 50000000000000000000 1369825160505219 1250000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1369825160505219/1250000000000000 : ℝ)) (X := (75486288224016898981/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(517445808691363/7380200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(441155475350389/7380200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (36901/50000 : ℝ)) (alpha := (517445808691363/7380200000000000 : ℝ)) (beta := (441155475350389/7380200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (36901/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(517445808691363/7380200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(441155475350389/7380200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-22919551/200000000 : ℝ)*X 0 0+(505147793/1000000000 : ℝ)*X 0 1+(-750827003/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5094037393/10000000000 : ℝ)*X 1 0+(-1168074217/10000000000 : ℝ)*X 1 1+(-1488010369/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1334795347/2500000000 : ℝ)*X 2 0+(5389177523/10000000000 : ℝ)*X 2 1+(1646691709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-148438829/1000000000 : ℝ)*X 0 0+(3020980189/10000000000 : ℝ)*X 0 1+(-3772843583/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3545753329/10000000000 : ℝ)*X 1 0+(-399579267/5000000000 : ℝ)*X 1 1+(-7532361313/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3694286379/10000000000 : ℝ)*X 2 0+(7078130769/10000000000 : ℝ)*X 2 1+(171021719/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2045571283/5000000000 : ℝ)*X 0 0+(7411984007/10000000000 : ℝ)*X 0 1+(-14238789/10000000000 : ℝ)*X 0 2+(2045571283/5000000000 : ℝ)*X 1 0+(7411984007/10000000000 : ℝ)*X 1 1+(-14238789/10000000000 : ℝ)*X 1 2+(2045571283/5000000000 : ℝ)*X 2 0+(7411984007/10000000000 : ℝ)*X 2 1+(-14238789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-157380681/2000000000 : ℝ)*X 0 0+(697022463/2000000000 : ℝ)*X 0 1+(-237118177/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2983091351/10000000000 : ℝ)*X 1 0+(-148524021/1000000000 : ℝ)*X 1 1+(-1893595937/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6909987781/10000000000 : ℝ)*X 2 0+(1942951953/5000000000 : ℝ)*X 2 1+(1378918391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7685343467/10000000000 : ℝ)*X 0 0+(940506343/2500000000 : ℝ)*X 0 1+(-17500283/10000000000 : ℝ)*X 0 2+(7685343467/10000000000 : ℝ)*X 1 0+(940506343/2500000000 : ℝ)*X 1 1+(-17500283/10000000000 : ℝ)*X 1 2+(7685343467/10000000000 : ℝ)*X 2 0+(940506343/2500000000 : ℝ)*X 2 1+(-17500283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-82749021/5000000000 : ℝ)*X 0 0+(252961871/400000000 : ℝ)*X 0 1+(-5255200541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((845617297/1250000000 : ℝ)*X 1 0+(-583658377/10000000000 : ℝ)*X 1 1+(-4576649911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((9006929/25000000 : ℝ)*X 2 0+(1674777523/2500000000 : ℝ)*X 2 1+(1021589361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1633042661/2000000000 : ℝ)*X 0 0+(155185593/500000000 : ℝ)*X 0 1+(-163531259/10000000000 : ℝ)*X 0 2+(1633042661/2000000000 : ℝ)*X 1 0+(155185593/500000000 : ℝ)*X 1 1+(-163531259/10000000000 : ℝ)*X 1 2+(1633042661/2000000000 : ℝ)*X 2 0+(155185593/500000000 : ℝ)*X 2 1+(-163531259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((16573/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16573/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (101258227519187338985339762057/27835848678600000000000000000000000 : ℝ) := by norm_num
    linear_combination (182612208717/250000000000 : ℝ)*(base7) + (29289/125000000000 : ℝ)*(base49) + (19997197767/500000000000 : ℝ)*(base60) + (2338949939687/1000000000000 : ℝ)*(major_s1_0) + (2338949939687/1000000000000 : ℝ)*(major_s1_1) + (2338949939687/1000000000000 : ℝ)*(major_s1_2) + (1052167/500000000000 : ℝ)*(sp_s1_0) + (1239279/1000000000000 : ℝ)*(sp_s1_1) + (284249874407/100000000000 : ℝ)*(sp_s1_7) + (1421255921553/500000000000 : ℝ)*(sp_s1_8) + (2842515993583/1000000000000 : ℝ)*(sp_s1_9) + (2131747678989/1000000000000 : ℝ)*(sp_s1_13) + (757259/50000000000 : ℝ)*(sp_s1_14) + (2911199/1000000000000 : ℝ)*(sp_s1_15) + (35032471103/25000000000 : ℝ)*(f.failure) + (2842515993583/1000000000000 : ℝ)*(f.sum) + (35706082905586813061/124620581160000000000000000000000 : ℝ)*base63 + (2993066899055217/7380200000000000000000000000 : ℝ)*base64 + (780024709696393/4221450000000000000000000000 : ℝ)*base67 + (928115306648501/7380200000000000000000000000 : ℝ)*base69 + (98871050630886899617/314529363600000000000000000000000 : ℝ)*base70 + (1502217765233513/8523600000000000000000000000 : ℝ)*base73 + (1300239414247849/4221450000000000000000000000 : ℝ)*base75 + (3242526139835069/8523600000000000000000000000 : ℝ)*base77 + (21107681115492394231/239879674800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (2461/2500000000000000 : ℝ)*base86 + (2461/2500000000000000 : ℝ)*base88 + (2461/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66319/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66319/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7583853328503992472095099/1384673124000000000000000000000 : ℝ) := by norm_num
    linear_combination (73838263523/100000000000 : ℝ)*(base7) + (73/625000000 : ℝ)*(base12) + (890671/1000000000000 : ℝ)*(base59) + (2276509553139/1000000000000 : ℝ)*(major_s1_0) + (2276509553139/1000000000000 : ℝ)*(major_s1_1) + (2276509553139/1000000000000 : ℝ)*(major_s1_2) + (5787127/500000000000 : ℝ)*(sp_s1_1) + (1246387/250000000000 : ℝ)*(sp_s1_2) + (7333649/200000000000 : ℝ)*(sp_s1_8) + (2750328612561/1000000000000 : ℝ)*(sp_s1_14) + (1375140243431/500000000000 : ℝ)*(sp_s1_15) + (2750323743813/1000000000000 : ℝ)*(sp_s1_16) + (2102262938451/1000000000000 : ℝ)*(sp_s1_20) + (9599387/1000000000000 : ℝ)*(sp_s1_27) + (1363889902607/1000000000000 : ℝ)*(f.failure) + (2750328729361/1000000000000 : ℝ)*(f.sum) + (19462791170741072729/41540193720000000000000000000000 : ℝ)*base62 + (277256991308931/7380200000000000000000000000 : ℝ)*base65 + (171561593331539/703575000000000000000000000 : ℝ)*base66 + (1455705811052363/7380200000000000000000000000 : ℝ)*base68 + (15854610451000365623/104843121200000000000000000000000 : ℝ)*base70 + (488247504983393/2841200000000000000000000000 : ℝ)*base72 + (366335342990779/1407150000000000000000000000 : ℝ)*base74 + (162729575699851/2841200000000000000000000000 : ℝ)*base77 + (4247046374676892529/79959891600000000000000000000000 : ℝ)*base79 + (57809/100000000000000000 : ℝ)*base86 + (57809/100000000000000000 : ℝ)*base88 + (57809/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-25603/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-25603/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14460208475846546827299/1845050000000000000000000000 : ℝ) := by norm_num
    linear_combination (83386435537/200000000000 : ℝ)*(base7) + (2576113/250000000000 : ℝ)*(base11) + (96957909609/500000000000 : ℝ)*(base39) + (107329/500000000000 : ℝ)*(base59) + (1127666560353/500000000000 : ℝ)*(major_s1_0) + (1127666560353/500000000000 : ℝ)*(major_s1_1) + (1127666560353/500000000000 : ℝ)*(major_s1_2) + (6120151/500000000000 : ℝ)*(sp_s1_0) + (2464357/1000000000000 : ℝ)*(sp_s1_2) + (437109/6250000000 : ℝ)*(sp_s1_9) + (363958500537/125000000000 : ℝ)*(sp_s1_21) + (58233810981/20000000000 : ℝ)*(sp_s1_22) + (2911618147253/1000000000000 : ℝ)*(sp_s1_23) + (884067486189/500000000000 : ℝ)*(sp_s1_27) + (1351202794693/1000000000000 : ℝ)*(f.failure) + (58233810981/20000000000 : ℝ)*(f.sum) + (4725340431569098997/20770096860000000000000000000000 : ℝ)*base63 + (1165951883233917/3690100000000000000000000000 : ℝ)*base65 + (371130428982589/703575000000000000000000000 : ℝ)*base67 + (838240136199761/3690100000000000000000000000 : ℝ)*base68 + (29388348269467384939/52421560600000000000000000000000 : ℝ)*base71 + (299294063927869/1420600000000000000000000000 : ℝ)*base73 + (142327012291133/703575000000000000000000000 : ℝ)*base74 + (445700524181483/1420600000000000000000000000 : ℝ)*base76 + (7716631445081202497/39979945800000000000000000000000 : ℝ)*base78 + (7291/100000000000000000 : ℝ)*base86 + (7291/100000000000000000 : ℝ)*base88 + (7291/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((21309/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21309/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(84429/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(84429/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-36901/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-36901/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16573/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16573/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66319/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66319/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-25603/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-25603/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312062_s1 p hpa hpb X hX hprev0

#print axioms solution
