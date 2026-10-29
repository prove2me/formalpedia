-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316051_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:06:33.648862+00:00
-- url     : https://prove2.me/submissions/bc05c7d5-238f-476f-8b31-f08a36ee843c

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
theorem collision_support_c316051_s1_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-913705631/2500000000 : ℝ)*x 0 + (91177319/250000000 : ℝ)*x 1 + (647347721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (913705631/2500000000 : ℝ)^39 ≤ (28187567166203/100000000000000 : ℝ)^31 := by
    have hnat : (913705631 : ℕ)^39*100000000000000^31 ≤ 28187567166203^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913705631 2500000000 28187567166203 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91177319/250000000 : ℝ)^39 ≤ (14056293892379/50000000000000 : ℝ)^31 := by
    have hnat : (91177319 : ℕ)^39*50000000000000^31 ≤ 14056293892379^31*250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91177319 250000000 14056293892379 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647347721/1250000000 : ℝ)^39 ≤ (10924961259527/25000000000000 : ℝ)^31 := by
    have hnat : (647347721 : ℕ)^39*25000000000000^31 ≤ 10924961259527^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647347721 1250000000 10924961259527 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-913705631/2500000000 : ℝ), (91177319/250000000 : ℝ), (647347721/1250000000 : ℝ)] ![(28187567166203/100000000000000 : ℝ), (14056293892379/50000000000000 : ℝ), (10924961259527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-913705631/2500000000 : ℝ)|^39 ≤ (28187567166203/100000000000000 : ℝ)^31
        have hw : |(-913705631/2500000000 : ℝ)|=(913705631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91177319/250000000 : ℝ)|^39 ≤ (14056293892379/50000000000000 : ℝ)^31
        have hw : |(91177319/250000000 : ℝ)|=(91177319/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647347721/1250000000 : ℝ)|^39 ≤ (10924961259527/25000000000000 : ℝ)^31
        have hw : |(647347721/1250000000 : ℝ)|=(647347721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (57912939/200000000 : ℝ)*x 0 + (-722380701/2500000000 : ℝ)*x 1 + (6485303141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57912939/200000000 : ℝ)^39 ≤ (21030095790247/100000000000000 : ℝ)^31 := by
    have hnat : (57912939 : ℕ)^39*100000000000000^31 ≤ 21030095790247^31*200000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57912939 200000000 21030095790247 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (722380701/2500000000 : ℝ)^39 ≤ (20974155399657/100000000000000 : ℝ)^31 := by
    have hnat : (722380701 : ℕ)^39*100000000000000^31 ≤ 20974155399657^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722380701 2500000000 20974155399657 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6485303141/10000000000 : ℝ)^39 ≤ (57995748784489/100000000000000 : ℝ)^31 := by
    have hnat : (6485303141 : ℕ)^39*100000000000000^31 ≤ 57995748784489^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6485303141 10000000000 57995748784489 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(57912939/200000000 : ℝ), (-722380701/2500000000 : ℝ), (6485303141/10000000000 : ℝ)] ![(21030095790247/100000000000000 : ℝ), (20974155399657/100000000000000 : ℝ), (57995748784489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(57912939/200000000 : ℝ)|^39 ≤ (21030095790247/100000000000000 : ℝ)^31
        have hw : |(57912939/200000000 : ℝ)|=(57912939/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-722380701/2500000000 : ℝ)|^39 ≤ (20974155399657/100000000000000 : ℝ)^31
        have hw : |(-722380701/2500000000 : ℝ)|=(722380701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6485303141/10000000000 : ℝ)|^39 ≤ (57995748784489/100000000000000 : ℝ)^31
        have hw : |(6485303141/10000000000 : ℝ)|=(6485303141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5363695723/10000000000 : ℝ)*x 0 + (2686893849/5000000000 : ℝ)*x 1 + (-1415720051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363695723/10000000000 : ℝ)^39 ≤ (45671831226273/100000000000000 : ℝ)^31 := by
    have hnat : (5363695723 : ℕ)^39*100000000000000^31 ≤ 45671831226273^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363695723 10000000000 45671831226273 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2686893849/5000000000 : ℝ)^39 ≤ (22889983419711/50000000000000 : ℝ)^31 := by
    have hnat : (2686893849 : ℕ)^39*50000000000000^31 ≤ 22889983419711^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686893849 5000000000 22889983419711 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1415720051/10000000000 : ℝ)^39 ≤ (2137050480069/25000000000000 : ℝ)^31 := by
    have hnat : (1415720051 : ℕ)^39*25000000000000^31 ≤ 2137050480069^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415720051 10000000000 2137050480069 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363695723/10000000000 : ℝ), (2686893849/5000000000 : ℝ), (-1415720051/10000000000 : ℝ)] ![(45671831226273/100000000000000 : ℝ), (22889983419711/50000000000000 : ℝ), (2137050480069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363695723/10000000000 : ℝ)|^39 ≤ (45671831226273/100000000000000 : ℝ)^31
        have hw : |(5363695723/10000000000 : ℝ)|=(5363695723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2686893849/5000000000 : ℝ)|^39 ≤ (22889983419711/50000000000000 : ℝ)^31
        have hw : |(2686893849/5000000000 : ℝ)|=(2686893849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1415720051/10000000000 : ℝ)|^39 ≤ (2137050480069/25000000000000 : ℝ)^31
        have hw : |(-1415720051/10000000000 : ℝ)|=(1415720051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5095824423/10000000000 : ℝ)*x 0 + (5105412389/10000000000 : ℝ)*x 1 + (2125940277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5095824423/10000000000 : ℝ)^39 ≤ (42821008973609/100000000000000 : ℝ)^31 := by
    have hnat : (5095824423 : ℕ)^39*100000000000000^31 ≤ 42821008973609^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5095824423 10000000000 42821008973609 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5105412389/10000000000 : ℝ)^39 ≤ (42922394792739/100000000000000 : ℝ)^31 := by
    have hnat : (5105412389 : ℕ)^39*100000000000000^31 ≤ 42922394792739^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5105412389 10000000000 42922394792739 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125940277/10000000000 : ℝ)^39 ≤ (3564149055417/25000000000000 : ℝ)^31 := by
    have hnat : (2125940277 : ℕ)^39*25000000000000^31 ≤ 3564149055417^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125940277 10000000000 3564149055417 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5095824423/10000000000 : ℝ), (5105412389/10000000000 : ℝ), (2125940277/10000000000 : ℝ)] ![(42821008973609/100000000000000 : ℝ), (42922394792739/100000000000000 : ℝ), (3564149055417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5095824423/10000000000 : ℝ)|^39 ≤ (42821008973609/100000000000000 : ℝ)^31
        have hw : |(5095824423/10000000000 : ℝ)|=(5095824423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5105412389/10000000000 : ℝ)|^39 ≤ (42922394792739/100000000000000 : ℝ)^31
        have hw : |(5105412389/10000000000 : ℝ)|=(5105412389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125940277/10000000000 : ℝ)|^39 ≤ (3564149055417/25000000000000 : ℝ)^31
        have hw : |(2125940277/10000000000 : ℝ)|=(2125940277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-890538367/2500000000 : ℝ)*x 0 + (3331813473/10000000000 : ℝ)*x 1 + (1386160433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (890538367/2500000000 : ℝ)^39 ≤ (5458276823177/20000000000000 : ℝ)^31 := by
    have hnat : (890538367 : ℕ)^39*20000000000000^31 ≤ 5458276823177^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890538367 2500000000 5458276823177 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3331813473/10000000000 : ℝ)^39 ≤ (5018009698461/20000000000000 : ℝ)^31 := by
    have hnat : (3331813473 : ℕ)^39*20000000000000^31 ≤ 5018009698461^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3331813473 10000000000 5018009698461 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1386160433/2500000000 : ℝ)^39 ≤ (9523713475351/20000000000000 : ℝ)^31 := by
    have hnat : (1386160433 : ℕ)^39*20000000000000^31 ≤ 9523713475351^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386160433 2500000000 9523713475351 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-890538367/2500000000 : ℝ), (3331813473/10000000000 : ℝ), (1386160433/2500000000 : ℝ)] ![(5458276823177/20000000000000 : ℝ), (5018009698461/20000000000000 : ℝ), (9523713475351/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-890538367/2500000000 : ℝ)|^39 ≤ (5458276823177/20000000000000 : ℝ)^31
        have hw : |(-890538367/2500000000 : ℝ)|=(890538367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3331813473/10000000000 : ℝ)|^39 ≤ (5018009698461/20000000000000 : ℝ)^31
        have hw : |(3331813473/10000000000 : ℝ)|=(3331813473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1386160433/2500000000 : ℝ)|^39 ≤ (9523713475351/20000000000000 : ℝ)^31
        have hw : |(1386160433/2500000000 : ℝ)|=(1386160433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (568018713/2000000000 : ℝ)*x 0 + (-41506941/156250000 : ℝ)*x 1 + (6716432997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (568018713/2000000000 : ℝ)^39 ≤ (2565471622289/12500000000000 : ℝ)^31 := by
    have hnat : (568018713 : ℕ)^39*12500000000000^31 ≤ 2565471622289^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568018713 2000000000 2565471622289 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41506941/156250000 : ℝ)^39 ≤ (9434157995193/50000000000000 : ℝ)^31 := by
    have hnat : (41506941 : ℕ)^39*50000000000000^31 ≤ 9434157995193^31*156250000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41506941 156250000 9434157995193 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6716432997/10000000000 : ℝ)^39 ≤ (7575988877569/12500000000000 : ℝ)^31 := by
    have hnat : (6716432997 : ℕ)^39*12500000000000^31 ≤ 7575988877569^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6716432997 10000000000 7575988877569 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(568018713/2000000000 : ℝ), (-41506941/156250000 : ℝ), (6716432997/10000000000 : ℝ)] ![(2565471622289/12500000000000 : ℝ), (9434157995193/50000000000000 : ℝ), (7575988877569/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(568018713/2000000000 : ℝ)|^39 ≤ (2565471622289/12500000000000 : ℝ)^31
        have hw : |(568018713/2000000000 : ℝ)|=(568018713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41506941/156250000 : ℝ)|^39 ≤ (9434157995193/50000000000000 : ℝ)^31
        have hw : |(-41506941/156250000 : ℝ)|=(41506941/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6716432997/10000000000 : ℝ)|^39 ≤ (7575988877569/12500000000000 : ℝ)^31
        have hw : |(6716432997/10000000000 : ℝ)|=(6716432997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5227141711/10000000000 : ℝ)*x 0 + (2875932677/5000000000 : ℝ)*x 1 + (-1056897251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5227141711/10000000000 : ℝ)^39 ≤ (8842768920489/20000000000000 : ℝ)^31 := by
    have hnat : (5227141711 : ℕ)^39*20000000000000^31 ≤ 8842768920489^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227141711 10000000000 8842768920489 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2875932677/5000000000 : ℝ)^39 ≤ (6233527435897/12500000000000 : ℝ)^31 := by
    have hnat : (2875932677 : ℕ)^39*12500000000000^31 ≤ 6233527435897^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2875932677 5000000000 6233527435897 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056897251/10000000000 : ℝ)^39 ≤ (2958967950633/50000000000000 : ℝ)^31 := by
    have hnat : (1056897251 : ℕ)^39*50000000000000^31 ≤ 2958967950633^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056897251 10000000000 2958967950633 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5227141711/10000000000 : ℝ), (2875932677/5000000000 : ℝ), (-1056897251/10000000000 : ℝ)] ![(8842768920489/20000000000000 : ℝ), (6233527435897/12500000000000 : ℝ), (2958967950633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5227141711/10000000000 : ℝ)|^39 ≤ (8842768920489/20000000000000 : ℝ)^31
        have hw : |(5227141711/10000000000 : ℝ)|=(5227141711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2875932677/5000000000 : ℝ)|^39 ≤ (6233527435897/12500000000000 : ℝ)^31
        have hw : |(2875932677/5000000000 : ℝ)|=(2875932677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1056897251/10000000000 : ℝ)|^39 ≤ (2958967950633/50000000000000 : ℝ)^31
        have hw : |(-1056897251/10000000000 : ℝ)|=(1056897251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_12 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (101258107/200000000 : ℝ)*x 0 + (278557111/500000000 : ℝ)*x 1 + (311059503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101258107/200000000 : ℝ)^39 ≤ (8494657707921/20000000000000 : ℝ)^31 := by
    have hnat : (101258107 : ℕ)^39*20000000000000^31 ≤ 8494657707921^31*200000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101258107 200000000 8494657707921 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278557111/500000000 : ℝ)^39 ≤ (47905068978709/100000000000000 : ℝ)^31 := by
    have hnat : (278557111 : ℕ)^39*100000000000000^31 ≤ 47905068978709^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278557111 500000000 47905068978709 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311059503/2000000000 : ℝ)^39 ≤ (1924328491503/20000000000000 : ℝ)^31 := by
    have hnat : (311059503 : ℕ)^39*20000000000000^31 ≤ 1924328491503^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311059503 2000000000 1924328491503 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(101258107/200000000 : ℝ), (278557111/500000000 : ℝ), (311059503/2000000000 : ℝ)] ![(8494657707921/20000000000000 : ℝ), (47905068978709/100000000000000 : ℝ), (1924328491503/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(101258107/200000000 : ℝ)|^39 ≤ (8494657707921/20000000000000 : ℝ)^31
        have hw : |(101258107/200000000 : ℝ)|=(101258107/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(278557111/500000000 : ℝ)|^39 ≤ (47905068978709/100000000000000 : ℝ)^31
        have hw : |(278557111/500000000 : ℝ)|=(278557111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(311059503/2000000000 : ℝ)|^39 ≤ (1924328491503/20000000000000 : ℝ)^31
        have hw : |(311059503/2000000000 : ℝ)|=(311059503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-417437243/1250000000 : ℝ)*x 0 + (3554594371/10000000000 : ℝ)*x 1 + (5544643283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417437243/1250000000 : ℝ)^39 ≤ (6290717801667/25000000000000 : ℝ)^31 := by
    have hnat : (417437243 : ℕ)^39*25000000000000^31 ≤ 6290717801667^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417437243 1250000000 6290717801667 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3554594371/10000000000 : ℝ)^39 ≤ (27218544646627/100000000000000 : ℝ)^31 := by
    have hnat : (3554594371 : ℕ)^39*100000000000000^31 ≤ 27218544646627^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3554594371 10000000000 27218544646627 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5544643283/10000000000 : ℝ)^39 ≤ (47618584134577/100000000000000 : ℝ)^31 := by
    have hnat : (5544643283 : ℕ)^39*100000000000000^31 ≤ 47618584134577^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5544643283 10000000000 47618584134577 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417437243/1250000000 : ℝ), (3554594371/10000000000 : ℝ), (5544643283/10000000000 : ℝ)] ![(6290717801667/25000000000000 : ℝ), (27218544646627/100000000000000 : ℝ), (47618584134577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417437243/1250000000 : ℝ)|^39 ≤ (6290717801667/25000000000000 : ℝ)^31
        have hw : |(-417437243/1250000000 : ℝ)|=(417437243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3554594371/10000000000 : ℝ)|^39 ≤ (27218544646627/100000000000000 : ℝ)^31
        have hw : |(3554594371/10000000000 : ℝ)|=(3554594371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5544643283/10000000000 : ℝ)|^39 ≤ (47618584134577/100000000000000 : ℝ)^31
        have hw : |(5544643283/10000000000 : ℝ)|=(5544643283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2662571283/10000000000 : ℝ)*x 0 + (-2834066993/10000000000 : ℝ)*x 1 + (839554211/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2662571283/10000000000 : ℝ)^39 ≤ (18923082690361/100000000000000 : ℝ)^31 := by
    have hnat : (2662571283 : ℕ)^39*100000000000000^31 ≤ 18923082690361^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2662571283 10000000000 18923082690361 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2834066993/10000000000 : ℝ)^39 ≤ (20468998427131/100000000000000 : ℝ)^31 := by
    have hnat : (2834066993 : ℕ)^39*100000000000000^31 ≤ 20468998427131^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2834066993 10000000000 20468998427131 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (839554211/1250000000 : ℝ)^39 ≤ (60607918865167/100000000000000 : ℝ)^31 := by
    have hnat : (839554211 : ℕ)^39*100000000000000^31 ≤ 60607918865167^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839554211 1250000000 60607918865167 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2662571283/10000000000 : ℝ), (-2834066993/10000000000 : ℝ), (839554211/1250000000 : ℝ)] ![(18923082690361/100000000000000 : ℝ), (20468998427131/100000000000000 : ℝ), (60607918865167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2662571283/10000000000 : ℝ)|^39 ≤ (18923082690361/100000000000000 : ℝ)^31
        have hw : |(2662571283/10000000000 : ℝ)|=(2662571283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2834066993/10000000000 : ℝ)|^39 ≤ (20468998427131/100000000000000 : ℝ)^31
        have hw : |(-2834066993/10000000000 : ℝ)|=(2834066993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(839554211/1250000000 : ℝ)|^39 ≤ (60607918865167/100000000000000 : ℝ)^31
        have hw : |(839554211/1250000000 : ℝ)|=(839554211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5741861561/10000000000 : ℝ)*x 0 + (5237391851/10000000000 : ℝ)*x 1 + (-528447711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5741861561/10000000000 : ℝ)^39 ≤ (6219891176361/12500000000000 : ℝ)^31 := by
    have hnat : (5741861561 : ℕ)^39*12500000000000^31 ≤ 6219891176361^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5741861561 10000000000 6219891176361 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237391851/10000000000 : ℝ)^39 ≤ (22161473781681/50000000000000 : ℝ)^31 := by
    have hnat : (5237391851 : ℕ)^39*50000000000000^31 ≤ 22161473781681^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237391851 10000000000 22161473781681 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528447711/5000000000 : ℝ)^39 ≤ (5917923017169/100000000000000 : ℝ)^31 := by
    have hnat : (528447711 : ℕ)^39*100000000000000^31 ≤ 5917923017169^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528447711 5000000000 5917923017169 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5741861561/10000000000 : ℝ), (5237391851/10000000000 : ℝ), (-528447711/5000000000 : ℝ)] ![(6219891176361/12500000000000 : ℝ), (22161473781681/50000000000000 : ℝ), (5917923017169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5741861561/10000000000 : ℝ)|^39 ≤ (6219891176361/12500000000000 : ℝ)^31
        have hw : |(5741861561/10000000000 : ℝ)|=(5741861561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237391851/10000000000 : ℝ)|^39 ≤ (22161473781681/50000000000000 : ℝ)^31
        have hw : |(5237391851/10000000000 : ℝ)|=(5237391851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-528447711/5000000000 : ℝ)|^39 ≤ (5917923017169/100000000000000 : ℝ)^31
        have hw : |(-528447711/5000000000 : ℝ)|=(528447711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_18 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (556145327/1000000000 : ℝ)*x 0 + (5072833911/10000000000 : ℝ)*x 1 + (777647273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (556145327/1000000000 : ℝ)^39 ≤ (1195006977473/2500000000000 : ℝ)^31 := by
    have hnat : (556145327 : ℕ)^39*2500000000000^31 ≤ 1195006977473^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556145327 1000000000 1195006977473 2500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5072833911/10000000000 : ℝ)^39 ≤ (21289050766799/50000000000000 : ℝ)^31 := by
    have hnat : (5072833911 : ℕ)^39*50000000000000^31 ≤ 21289050766799^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072833911 10000000000 21289050766799 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (777647273/5000000000 : ℝ)^39 ≤ (60135120939/625000000000 : ℝ)^31 := by
    have hnat : (777647273 : ℕ)^39*625000000000^31 ≤ 60135120939^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777647273 5000000000 60135120939 625000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(556145327/1000000000 : ℝ), (5072833911/10000000000 : ℝ), (777647273/5000000000 : ℝ)] ![(1195006977473/2500000000000 : ℝ), (21289050766799/50000000000000 : ℝ), (60135120939/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(556145327/1000000000 : ℝ)|^39 ≤ (1195006977473/2500000000000 : ℝ)^31
        have hw : |(556145327/1000000000 : ℝ)|=(556145327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5072833911/10000000000 : ℝ)|^39 ≤ (21289050766799/50000000000000 : ℝ)^31
        have hw : |(5072833911/10000000000 : ℝ)|=(5072833911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(777647273/5000000000 : ℝ)|^39 ≤ (60135120939/625000000000 : ℝ)^31
        have hw : |(777647273/5000000000 : ℝ)|=(777647273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_19 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-924294363/2500000000 : ℝ)*x 0 + (3689535047/10000000000 : ℝ)*x 1 + (1275258159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (924294363/2500000000 : ℝ)^39 ≤ (28599138615447/100000000000000 : ℝ)^31 := by
    have hnat : (924294363 : ℕ)^39*100000000000000^31 ≤ 28599138615447^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924294363 2500000000 28599138615447 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3689535047/10000000000 : ℝ)^39 ≤ (28524785407869/100000000000000 : ℝ)^31 := by
    have hnat : (3689535047 : ℕ)^39*100000000000000^31 ≤ 28524785407869^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3689535047 10000000000 28524785407869 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1275258159/2500000000 : ℝ)^39 ≤ (42876075964631/100000000000000 : ℝ)^31 := by
    have hnat : (1275258159 : ℕ)^39*100000000000000^31 ≤ 42876075964631^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275258159 2500000000 42876075964631 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-924294363/2500000000 : ℝ), (3689535047/10000000000 : ℝ), (1275258159/2500000000 : ℝ)] ![(28599138615447/100000000000000 : ℝ), (28524785407869/100000000000000 : ℝ), (42876075964631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-924294363/2500000000 : ℝ)|^39 ≤ (28599138615447/100000000000000 : ℝ)^31
        have hw : |(-924294363/2500000000 : ℝ)|=(924294363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3689535047/10000000000 : ℝ)|^39 ≤ (28524785407869/100000000000000 : ℝ)^31
        have hw : |(3689535047/10000000000 : ℝ)|=(3689535047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1275258159/2500000000 : ℝ)|^39 ≤ (42876075964631/100000000000000 : ℝ)^31
        have hw : |(1275258159/2500000000 : ℝ)|=(1275258159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2860280661/10000000000 : ℝ)*x 0 + (-2854056701/10000000000 : ℝ)*x 1 + (3271328319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2860280661/10000000000 : ℝ)^39 ≤ (10353734287957/50000000000000 : ℝ)^31 := by
    have hnat : (2860280661 : ℕ)^39*50000000000000^31 ≤ 10353734287957^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2860280661 10000000000 10353734287957 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2854056701/10000000000 : ℝ)^39 ≤ (1290674806331/6250000000000 : ℝ)^31 := by
    have hnat : (2854056701 : ℕ)^39*6250000000000^31 ≤ 1290674806331^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2854056701 10000000000 1290674806331 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3271328319/5000000000 : ℝ)^39 ≤ (29320867248401/50000000000000 : ℝ)^31 := by
    have hnat : (3271328319 : ℕ)^39*50000000000000^31 ≤ 29320867248401^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3271328319 5000000000 29320867248401 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2860280661/10000000000 : ℝ), (-2854056701/10000000000 : ℝ), (3271328319/5000000000 : ℝ)] ![(10353734287957/50000000000000 : ℝ), (1290674806331/6250000000000 : ℝ), (29320867248401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2860280661/10000000000 : ℝ)|^39 ≤ (10353734287957/50000000000000 : ℝ)^31
        have hw : |(2860280661/10000000000 : ℝ)|=(2860280661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2854056701/10000000000 : ℝ)|^39 ≤ (1290674806331/6250000000000 : ℝ)^31
        have hw : |(-2854056701/10000000000 : ℝ)|=(2854056701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3271328319/5000000000 : ℝ)|^39 ≤ (29320867248401/50000000000000 : ℝ)^31
        have hw : |(3271328319/5000000000 : ℝ)|=(3271328319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (86407053/156250000 : ℝ)*x 0 + (5163635449/10000000000 : ℝ)*x 1 + (-294973679/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86407053/156250000 : ℝ)^39 ≤ (47460979218353/100000000000000 : ℝ)^31 := by
    have hnat : (86407053 : ℕ)^39*100000000000000^31 ≤ 47460979218353^31*156250000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86407053 156250000 47460979218353 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5163635449/10000000000 : ℝ)^39 ≤ (43539114552883/100000000000000 : ℝ)^31 := by
    have hnat : (5163635449 : ℕ)^39*100000000000000^31 ≤ 43539114552883^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5163635449 10000000000 43539114552883 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (294973679/2000000000 : ℝ)^39 ≤ (2249976553863/25000000000000 : ℝ)^31 := by
    have hnat : (294973679 : ℕ)^39*25000000000000^31 ≤ 2249976553863^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294973679 2000000000 2249976553863 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86407053/156250000 : ℝ), (5163635449/10000000000 : ℝ), (-294973679/2000000000 : ℝ)] ![(47460979218353/100000000000000 : ℝ), (43539114552883/100000000000000 : ℝ), (2249976553863/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86407053/156250000 : ℝ)|^39 ≤ (47460979218353/100000000000000 : ℝ)^31
        have hw : |(86407053/156250000 : ℝ)|=(86407053/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5163635449/10000000000 : ℝ)|^39 ≤ (43539114552883/100000000000000 : ℝ)^31
        have hw : |(5163635449/10000000000 : ℝ)|=(5163635449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-294973679/2000000000 : ℝ)|^39 ≤ (2249976553863/25000000000000 : ℝ)^31
        have hw : |(-294973679/2000000000 : ℝ)|=(294973679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316051_s1_s1_25 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2343498711/5000000000 : ℝ)*x 0 + (2827433073/5000000000 : ℝ)*x 1 + (1932326811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2343498711/5000000000 : ℝ)^39 ≤ (38544668811647/100000000000000 : ℝ)^31 := by
    have hnat : (2343498711 : ℕ)^39*100000000000000^31 ≤ 38544668811647^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2343498711 5000000000 38544668811647 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2827433073/5000000000 : ℝ)^39 ≤ (48812529940119/100000000000000 : ℝ)^31 := by
    have hnat : (2827433073 : ℕ)^39*100000000000000^31 ≤ 48812529940119^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827433073 5000000000 48812529940119 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1932326811/10000000000 : ℝ)^39 ≤ (2528560245909/20000000000000 : ℝ)^31 := by
    have hnat : (1932326811 : ℕ)^39*20000000000000^31 ≤ 2528560245909^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932326811 10000000000 2528560245909 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2343498711/5000000000 : ℝ), (2827433073/5000000000 : ℝ), (1932326811/10000000000 : ℝ)] ![(38544668811647/100000000000000 : ℝ), (48812529940119/100000000000000 : ℝ), (2528560245909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2343498711/5000000000 : ℝ)|^39 ≤ (38544668811647/100000000000000 : ℝ)^31
        have hw : |(2343498711/5000000000 : ℝ)|=(2343498711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2827433073/5000000000 : ℝ)|^39 ≤ (48812529940119/100000000000000 : ℝ)^31
        have hw : |(2827433073/5000000000 : ℝ)|=(2827433073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1932326811/10000000000 : ℝ)|^39 ≤ (2528560245909/20000000000000 : ℝ)^31
        have hw : |(1932326811/10000000000 : ℝ)|=(1932326811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316051_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((4581/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4581/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2268/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2268/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(34041/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(34041/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((559/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(559/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3487/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3487/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1107/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1107/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (4581/6250 : ℝ) ^ (19/4 : ℝ) ≤ (11431449651536957119/50000000000000000000 : ℝ) := by
    have hpowers : (4581/6250 : ℝ)^19 ≤ (11431449651536957119/50000000000000000000 : ℝ)^4 := by
      have hnat : (4581 : ℕ)^19*50000000000000000000^4 ≤ 11431449651536957119^4*6250^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4581 6250 11431449651536957119 50000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4581/6250 : ℝ)) (X := (11431449651536957119/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (61431449651536957119/50000000000000000000 : ℝ) ≤ (10443003487980109/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (61431449651536957119/50000000000000000000 : ℝ)^4 ≤ (10443003487980109/10000000000000000 : ℝ)^19 := by
      have hnat : (61431449651536957119 : ℕ)^4*10000000000000000^19 ≤ 10443003487980109^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61431449651536957119 50000000000000000000 10443003487980109 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10443003487980109/10000000000000000 : ℝ)) (X := (61431449651536957119/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (36431449651536957119/25000000000000000000 : ℝ) ≤ (2706255109921611/2500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (36431449651536957119/25000000000000000000 : ℝ)^4 ≤ (2706255109921611/2500000000000000 : ℝ)^19 := by
      have hnat : (36431449651536957119 : ℕ)^4*2500000000000000^19 ≤ 2706255109921611^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36431449651536957119 25000000000000000000 2706255109921611 2500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2706255109921611/2500000000000000 : ℝ)) (X := (36431449651536957119/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(147667829326703/2443200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(76403390341267/1465920000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (4581/6250 : ℝ)) (alpha := (147667829326703/2443200000000000 : ℝ)) (beta := (76403390341267/1465920000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4581/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(147667829326703/2443200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(76403390341267/1465920000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2268/3125 : ℝ) ^ (19/4 : ℝ) ≤ (872623444571653459/4000000000000000000 : ℝ) := by
    have hpowers : (2268/3125 : ℝ)^19 ≤ (872623444571653459/4000000000000000000 : ℝ)^4 := by
      have hnat : (2268 : ℕ)^19*4000000000000000000^4 ≤ 872623444571653459^4*3125^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2268 3125 872623444571653459 4000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2268/3125 : ℝ)) (X := (872623444571653459/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (4872623444571653459/4000000000000000000 : ℝ) ≤ (2084839865478669/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (4872623444571653459/4000000000000000000 : ℝ)^4 ≤ (2084839865478669/2000000000000000 : ℝ)^19 := by
      have hnat : (4872623444571653459 : ℕ)^4*2000000000000000^19 ≤ 2084839865478669^19*4000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4872623444571653459 4000000000000000000 2084839865478669 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2084839865478669/2000000000000000 : ℝ)) (X := (4872623444571653459/4000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (2872623444571653459/2000000000000000000 : ℝ) ≤ (10792075886861223/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2872623444571653459/2000000000000000000 : ℝ)^4 ≤ (10792075886861223/10000000000000000 : ℝ)^19 := by
      have hnat : (2872623444571653459 : ℕ)^4*10000000000000000^19 ≤ 10792075886861223^19*2000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2872623444571653459 2000000000000000000 10792075886861223 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10792075886861223/10000000000000000 : ℝ)) (X := (2872623444571653459/2000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(12119980782667/207360000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(61312759911313/1209600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (2268/3125 : ℝ)) (alpha := (12119980782667/207360000000000 : ℝ)) (beta := (61312759911313/1209600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (2268/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(12119980782667/207360000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(61312759911313/1209600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (34041/100000 : ℝ) ^ (19/4 : ℝ) ≤ (1496066778640009/250000000000000000 : ℝ) := by
    have hpowers : (34041/100000 : ℝ)^19 ≤ (1496066778640009/250000000000000000 : ℝ)^4 := by
      have hnat : (34041 : ℕ)^19*250000000000000000^4 ≤ 1496066778640009^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34041 100000 1496066778640009 250000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34041/100000 : ℝ)) (X := (1496066778640009/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (251496066778640009/250000000000000000 : ℝ) ≤ (5006284401331367/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (251496066778640009/250000000000000000 : ℝ)^4 ≤ (5006284401331367/5000000000000000 : ℝ)^19 := by
      have hnat : (251496066778640009 : ℕ)^4*5000000000000000^19 ≤ 5006284401331367^19*250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        251496066778640009 250000000000000000 5006284401331367 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006284401331367/5000000000000000 : ℝ)) (X := (251496066778640009/250000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (126496066778640009/125000000000000000 : ℝ) ≤ (2506269679035983/2500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (126496066778640009/125000000000000000 : ℝ)^4 ≤ (2506269679035983/2500000000000000 : ℝ)^19 := by
      have hnat : (126496066778640009 : ℕ)^4*2500000000000000^19 ≤ 2506269679035983^19*125000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        126496066778640009 125000000000000000 2506269679035983 2500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506269679035983/2500000000000000 : ℝ)) (X := (126496066778640009/125000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(2094800443789/567350000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(893565248657/243150000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (34041/100000 : ℝ)) (alpha := (2094800443789/567350000000000 : ℝ)) (beta := (893565248657/243150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (34041/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(2094800443789/567350000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(893565248657/243150000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-913705631/2500000000 : ℝ)*X 0 0+(91177319/250000000 : ℝ)*X 0 1+(647347721/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((57912939/200000000 : ℝ)*X 1 0+(-722380701/2500000000 : ℝ)*X 1 1+(6485303141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5363695723/10000000000 : ℝ)*X 2 0+(2686893849/5000000000 : ℝ)*X 2 1+(-1415720051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5095824423/10000000000 : ℝ)*X 0 0+(5105412389/10000000000 : ℝ)*X 0 1+(2125940277/10000000000 : ℝ)*X 0 2+(5095824423/10000000000 : ℝ)*X 1 0+(5105412389/10000000000 : ℝ)*X 1 1+(2125940277/10000000000 : ℝ)*X 1 2+(5095824423/10000000000 : ℝ)*X 2 0+(5105412389/10000000000 : ℝ)*X 2 1+(2125940277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-890538367/2500000000 : ℝ)*X 0 0+(3331813473/10000000000 : ℝ)*X 0 1+(1386160433/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((568018713/2000000000 : ℝ)*X 1 0+(-41506941/156250000 : ℝ)*X 1 1+(6716432997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5227141711/10000000000 : ℝ)*X 2 0+(2875932677/5000000000 : ℝ)*X 2 1+(-1056897251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((101258107/200000000 : ℝ)*X 0 0+(278557111/500000000 : ℝ)*X 0 1+(311059503/2000000000 : ℝ)*X 0 2+(101258107/200000000 : ℝ)*X 1 0+(278557111/500000000 : ℝ)*X 1 1+(311059503/2000000000 : ℝ)*X 1 2+(101258107/200000000 : ℝ)*X 2 0+(278557111/500000000 : ℝ)*X 2 1+(311059503/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-417437243/1250000000 : ℝ)*X 0 0+(3554594371/10000000000 : ℝ)*X 0 1+(5544643283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((2662571283/10000000000 : ℝ)*X 1 0+(-2834066993/10000000000 : ℝ)*X 1 1+(839554211/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((5741861561/10000000000 : ℝ)*X 2 0+(5237391851/10000000000 : ℝ)*X 2 1+(-528447711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((556145327/1000000000 : ℝ)*X 0 0+(5072833911/10000000000 : ℝ)*X 0 1+(777647273/5000000000 : ℝ)*X 0 2+(556145327/1000000000 : ℝ)*X 1 0+(5072833911/10000000000 : ℝ)*X 1 1+(777647273/5000000000 : ℝ)*X 1 2+(556145327/1000000000 : ℝ)*X 2 0+(5072833911/10000000000 : ℝ)*X 2 1+(777647273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-924294363/2500000000 : ℝ)*X 0 0+(3689535047/10000000000 : ℝ)*X 0 1+(1275258159/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2860280661/10000000000 : ℝ)*X 1 0+(-2854056701/10000000000 : ℝ)*X 1 1+(3271328319/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((86407053/156250000 : ℝ)*X 2 0+(5163635449/10000000000 : ℝ)*X 2 1+(-294973679/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((2343498711/5000000000 : ℝ)*X 0 0+(2827433073/5000000000 : ℝ)*X 0 1+(1932326811/10000000000 : ℝ)*X 0 2+(2343498711/5000000000 : ℝ)*X 1 0+(2827433073/5000000000 : ℝ)*X 1 1+(1932326811/10000000000 : ℝ)*X 1 2+(2343498711/5000000000 : ℝ)*X 2 0+(2827433073/5000000000 : ℝ)*X 2 1+(1932326811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316051_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((559/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(559/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2493068529183563090193048313/249506913600000000000000000000000 : ℝ) := by norm_num
    linear_combination (32829413669/40000000000 : ℝ)*(base49) + (436577758493/500000000000 : ℝ)*(base59) + (3519102519839/1000000000000 : ℝ)*(base60) + (3135310098049/250000000000 : ℝ)*(major_s1_0) + (3135310098049/250000000000 : ℝ)*(major_s1_1) + (3135310098049/250000000000 : ℝ)*(major_s1_2) + (60144107/1000000000000 : ℝ)*(sp_s1_2) + (2250893934517/125000000000 : ℝ)*(sp_s1_7) + (18007172569007/1000000000000 : ℝ)*(sp_s1_8) + (1800724375247/100000000000 : ℝ)*(sp_s1_9) + (7075066131427/1000000000000 : ℝ)*(sp_s1_12) + (152420441/1000000000000 : ℝ)*(sp_s1_13) + (13132757/100000000000 : ℝ)*(sp_s1_20) + (107425723/1000000000000 : ℝ)*(sp_s1_25) + (7075173557149/1000000000000 : ℝ)*(f.failure) + (18007303896577/1000000000000 : ℝ)*(f.sum) + (1143302022187689451/2941142400000000000000000000000 : ℝ)*base62 + (111128229129883/243150000000000000000000000 : ℝ)*base64 + (52174894814543/302400000000000000000000000 : ℝ)*base67 + (116617242453179/567350000000000000000000000 : ℝ)*base68 + (614544048862794629/990106800000000000000000000000 : ℝ)*base70 + (20956865006827/366480000000000000000000000 : ℝ)*base73 + (470194396733/2073600000000000000000000 : ℝ)*base74 + (168205814826673/610800000000000000000000000 : ℝ)*base76 + (3817195025093633/153921600000000000000000000000 : ℝ)*base78 + (39707/100000000000000000 : ℝ)*base86 + (39707/100000000000000000 : ℝ)*base88 + (39707/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3487/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3487/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (670816726697341585406182009/99802765440000000000000000000000 : ℝ) := by norm_num
    linear_combination (164130975201/200000000000 : ℝ)*(base49) + (180878968271/125000000000 : ℝ)*(base59) + (1882575756507/500000000000 : ℝ)*(base60) + (1253995164479/100000000000 : ℝ)*(major_s1_0) + (1253995164479/100000000000 : ℝ)*(major_s1_1) + (1253995164479/100000000000 : ℝ)*(major_s1_2) + (10292339/125000000000 : ℝ)*(sp_s1_0) + (8289567/250000000000 : ℝ)*(sp_s1_6) + (8941679/62500000000 : ℝ)*(sp_s1_7) + (1800522913659/100000000000 : ℝ)*(sp_s1_13) + (9002727271083/500000000000 : ℝ)*(sp_s1_14) + (18005336078103/1000000000000 : ℝ)*(sp_s1_15) + (3537206674331/500000000000 : ℝ)*(sp_s1_18) + (118464063/1000000000000 : ℝ)*(sp_s1_21) + (707444650693/100000000000 : ℝ)*(f.failure) + (9002727271083/500000000000 : ℝ)*(f.sum) + (127414211243189231/235291392000000000000000000000 : ℝ)*base63 + (11244215508799/24315000000000000000000000 : ℝ)*base65 + (32479096708561/120960000000000000000000000 : ℝ)*base67 + (23017622286671/28367500000000000000000000 : ℝ)*base69 + (79653174550396229/396042720000000000000000000000 : ℝ)*base71 + (285000289681249/732960000000000000000000000 : ℝ)*base73 + (58009298878921/103680000000000000000000000 : ℝ)*base75 + (131473952944369/244320000000000000000000000 : ℝ)*base77 + (2024173103065951/61568640000000000000000000000 : ℝ)*base78 + (10899/10000000000000000 : ℝ)*base86 + (10899/10000000000000000 : ℝ)*base88 + (10899/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1107/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1107/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (247077563726550645461/44537500000000000000000000 : ℝ) := by norm_num
    linear_combination (626486886101/1000000000000 : ℝ)*(base49) + (186278426377/200000000000 : ℝ)*(base60) + (375819757059/62500000000 : ℝ)*(major_s1_0) + (375819757059/62500000000 : ℝ)*(major_s1_1) + (375819757059/62500000000 : ℝ)*(major_s1_2) + (599008303/1000000000000 : ℝ)*(sp_s1_1) + (130619681/1000000000000 : ℝ)*(sp_s1_2) + (121261241/1000000000000 : ℝ)*(sp_s1_8) + (22281771/1000000000000 : ℝ)*(sp_s1_12) + (58275797/1000000000000 : ℝ)*(sp_s1_15) + (8633915199873/1000000000000 : ℝ)*(sp_s1_19) + (863319493033/100000000000 : ℝ)*(sp_s1_20) + (1726745260879/200000000000 : ℝ)*(sp_s1_21) + (3392292895031/1000000000000 : ℝ)*(sp_s1_25) + (1696157588401/500000000000 : ℝ)*(f.failure) + (8633915199873/1000000000000 : ℝ)*(f.sum) + (27147409783936747/245095200000000000000000000000 : ℝ)*base62 + (10699554699151/81050000000000000000000000 : ℝ)*base65 + (6082736831/25200000000000000000000000 : ℝ)*base67 + (110681874828411/567350000000000000000000000 : ℝ)*base68 + (17646531304587187/82508900000000000000000000000 : ℝ)*base71 + (13372370843033/30540000000000000000000000 : ℝ)*base72 + (805965944587/4320000000000000000000000 : ℝ)*base75 + (10128417594419/50900000000000000000000000 : ℝ)*base77 + (2381675803855361/12826800000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (3943/50000000000000000 : ℝ)*base86 + (3943/50000000000000000 : ℝ)*base88 + (3943/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((4581/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4581/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2268/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2268/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(34041/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(34041/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((559/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(559/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3487/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3487/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1107/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1107/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316051_s1 p hpa hpb X hX hprev0

#print axioms solution
