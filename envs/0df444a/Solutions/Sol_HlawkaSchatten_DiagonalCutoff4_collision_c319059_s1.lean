-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c319059_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:30:51.419088+00:00
-- url     : https://prove2.me/submissions/4a336d58-eb14-47c0-b554-dc847e09f434

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
theorem collision_support_c319059_s1_s1_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-3224155999/10000000000 : ℝ)*x 0 + (201276537/625000000 : ℝ)*x 1 + (587588261/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3224155999/10000000000 : ℝ)^5 ≤ (24295176496847/100000000000000 : ℝ)^4 := by
    have hnat : (3224155999 : ℕ)^5*100000000000000^4 ≤ 24295176496847^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3224155999 10000000000 24295176496847 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201276537/625000000 : ℝ)^5 ≤ (24260034713559/100000000000000 : ℝ)^4 := by
    have hnat : (201276537 : ℕ)^5*100000000000000^4 ≤ 24260034713559^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201276537 625000000 24260034713559 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587588261/1000000000 : ℝ)^5 ≤ (51444788778207/100000000000000 : ℝ)^4 := by
    have hnat : (587588261 : ℕ)^5*100000000000000^4 ≤ 51444788778207^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587588261 1000000000 51444788778207 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3224155999/10000000000 : ℝ), (201276537/625000000 : ℝ), (587588261/1000000000 : ℝ)] ![(24295176496847/100000000000000 : ℝ), (24260034713559/100000000000000 : ℝ), (51444788778207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3224155999/10000000000 : ℝ)|^5 ≤ (24295176496847/100000000000000 : ℝ)^4
        have hw : |(-3224155999/10000000000 : ℝ)|=(3224155999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201276537/625000000 : ℝ)|^5 ≤ (24260034713559/100000000000000 : ℝ)^4
        have hw : |(201276537/625000000 : ℝ)|=(201276537/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(587588261/1000000000 : ℝ)|^5 ≤ (51444788778207/100000000000000 : ℝ)^4
        have hw : |(587588261/1000000000 : ℝ)|=(587588261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (201319049/625000000 : ℝ)*x 0 + (-3217189289/10000000000 : ℝ)*x 1 + (5881291127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201319049/625000000 : ℝ)^5 ≤ (12133219946357/50000000000000 : ℝ)^4 := by
    have hnat : (201319049 : ℕ)^5*50000000000000^4 ≤ 12133219946357^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201319049 625000000 12133219946357 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3217189289/10000000000 : ℝ)^5 ≤ (3028696674341/12500000000000 : ℝ)^4 := by
    have hnat : (3217189289 : ℕ)^5*12500000000000^4 ≤ 3028696674341^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3217189289 10000000000 3028696674341 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5881291127/10000000000 : ℝ)^5 ≤ (51503986697777/100000000000000 : ℝ)^4 := by
    have hnat : (5881291127 : ℕ)^5*100000000000000^4 ≤ 51503986697777^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5881291127 10000000000 51503986697777 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(201319049/625000000 : ℝ), (-3217189289/10000000000 : ℝ), (5881291127/10000000000 : ℝ)] ![(12133219946357/50000000000000 : ℝ), (3028696674341/12500000000000 : ℝ), (51503986697777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(201319049/625000000 : ℝ)|^5 ≤ (12133219946357/50000000000000 : ℝ)^4
        have hw : |(201319049/625000000 : ℝ)|=(201319049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3217189289/10000000000 : ℝ)|^5 ≤ (3028696674341/12500000000000 : ℝ)^4
        have hw : |(-3217189289/10000000000 : ℝ)|=(3217189289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5881291127/10000000000 : ℝ)|^5 ≤ (51503986697777/100000000000000 : ℝ)^4
        have hw : |(5881291127/10000000000 : ℝ)|=(5881291127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5760482291/10000000000 : ℝ)*x 0 + (1360062161/2500000000 : ℝ)*x 1 + (-2421277/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5760482291/10000000000 : ℝ)^5 ≤ (50184957108327/100000000000000 : ℝ)^4 := by
    have hnat : (5760482291 : ℕ)^5*100000000000000^4 ≤ 50184957108327^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5760482291 10000000000 50184957108327 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360062161/2500000000 : ℝ)^5 ≤ (1460069262987/3125000000000 : ℝ)^4 := by
    have hnat : (1360062161 : ℕ)^5*3125000000000^4 ≤ 1460069262987^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360062161 2500000000 1460069262987 3125000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2421277/39062500 : ℝ)^5 ≤ (1546413230781/50000000000000 : ℝ)^4 := by
    have hnat : (2421277 : ℕ)^5*50000000000000^4 ≤ 1546413230781^4*39062500^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2421277 39062500 1546413230781 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5760482291/10000000000 : ℝ), (1360062161/2500000000 : ℝ), (-2421277/39062500 : ℝ)] ![(50184957108327/100000000000000 : ℝ), (1460069262987/3125000000000 : ℝ), (1546413230781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5760482291/10000000000 : ℝ)|^5 ≤ (50184957108327/100000000000000 : ℝ)^4
        have hw : |(5760482291/10000000000 : ℝ)|=(5760482291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360062161/2500000000 : ℝ)|^5 ≤ (1460069262987/3125000000000 : ℝ)^4
        have hw : |(1360062161/2500000000 : ℝ)|=(1360062161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2421277/39062500 : ℝ)|^5 ≤ (1546413230781/50000000000000 : ℝ)^4
        have hw : |(-2421277/39062500 : ℝ)|=(2421277/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (400185359/1000000000 : ℝ)*x 0 + (977756079/2000000000 : ℝ)*x 1 + (3538543567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (400185359/1000000000 : ℝ)^5 ≤ (1273170261651/4000000000000 : ℝ)^4 := by
    have hnat : (400185359 : ℕ)^5*4000000000000^4 ≤ 1273170261651^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400185359 1000000000 1273170261651 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977756079/2000000000 : ℝ)^5 ≤ (40879037465367/100000000000000 : ℝ)^4 := by
    have hnat : (977756079 : ℕ)^5*100000000000000^4 ≤ 40879037465367^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977756079 2000000000 40879037465367 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3538543567/10000000000 : ℝ)^5 ≤ (852865811783/3125000000000 : ℝ)^4 := by
    have hnat : (3538543567 : ℕ)^5*3125000000000^4 ≤ 852865811783^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3538543567 10000000000 852865811783 3125000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(400185359/1000000000 : ℝ), (977756079/2000000000 : ℝ), (3538543567/10000000000 : ℝ)] ![(1273170261651/4000000000000 : ℝ), (40879037465367/100000000000000 : ℝ), (852865811783/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(400185359/1000000000 : ℝ)|^5 ≤ (1273170261651/4000000000000 : ℝ)^4
        have hw : |(400185359/1000000000 : ℝ)|=(400185359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(977756079/2000000000 : ℝ)|^5 ≤ (40879037465367/100000000000000 : ℝ)^4
        have hw : |(977756079/2000000000 : ℝ)|=(977756079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3538543567/10000000000 : ℝ)|^5 ≤ (852865811783/3125000000000 : ℝ)^4
        have hw : |(3538543567/10000000000 : ℝ)|=(3538543567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-393517697/1250000000 : ℝ)*x 0 + (296565131/1000000000 : ℝ)*x 1 + (6156456333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393517697/1250000000 : ℝ)^5 ≤ (23581304085791/100000000000000 : ℝ)^4 := by
    have hnat : (393517697 : ℕ)^5*100000000000000^4 ≤ 23581304085791^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393517697 1250000000 23581304085791 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296565131/1000000000 : ℝ)^5 ≤ (4377035857151/20000000000000 : ℝ)^4 := by
    have hnat : (296565131 : ℕ)^5*20000000000000^4 ≤ 4377035857151^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296565131 1000000000 4377035857151 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6156456333/10000000000 : ℝ)^5 ≤ (13633379154923/25000000000000 : ℝ)^4 := by
    have hnat : (6156456333 : ℕ)^5*25000000000000^4 ≤ 13633379154923^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6156456333 10000000000 13633379154923 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393517697/1250000000 : ℝ), (296565131/1000000000 : ℝ), (6156456333/10000000000 : ℝ)] ![(23581304085791/100000000000000 : ℝ), (4377035857151/20000000000000 : ℝ), (13633379154923/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393517697/1250000000 : ℝ)|^5 ≤ (23581304085791/100000000000000 : ℝ)^4
        have hw : |(-393517697/1250000000 : ℝ)|=(393517697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(296565131/1000000000 : ℝ)|^5 ≤ (4377035857151/20000000000000 : ℝ)^4
        have hw : |(296565131/1000000000 : ℝ)|=(296565131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6156456333/10000000000 : ℝ)|^5 ≤ (13633379154923/25000000000000 : ℝ)^4
        have hw : |(6156456333/10000000000 : ℝ)|=(6156456333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (788138667/2500000000 : ℝ)*x 0 + (-2954666341/10000000000 : ℝ)*x 1 + (6161870577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (788138667/2500000000 : ℝ)^5 ≤ (2362263191789/10000000000000 : ℝ)^4 := by
    have hnat : (788138667 : ℕ)^5*10000000000000^4 ≤ 2362263191789^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788138667 2500000000 2362263191789 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2954666341/10000000000 : ℝ)^5 ≤ (10891948026427/50000000000000 : ℝ)^4 := by
    have hnat : (2954666341 : ℕ)^5*50000000000000^4 ≤ 10891948026427^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2954666341 10000000000 10891948026427 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6161870577/10000000000 : ℝ)^5 ≤ (54593472014443/100000000000000 : ℝ)^4 := by
    have hnat : (6161870577 : ℕ)^5*100000000000000^4 ≤ 54593472014443^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6161870577 10000000000 54593472014443 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(788138667/2500000000 : ℝ), (-2954666341/10000000000 : ℝ), (6161870577/10000000000 : ℝ)] ![(2362263191789/10000000000000 : ℝ), (10891948026427/50000000000000 : ℝ), (54593472014443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(788138667/2500000000 : ℝ)|^5 ≤ (2362263191789/10000000000000 : ℝ)^4
        have hw : |(788138667/2500000000 : ℝ)|=(788138667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2954666341/10000000000 : ℝ)|^5 ≤ (10891948026427/50000000000000 : ℝ)^4
        have hw : |(-2954666341/10000000000 : ℝ)|=(2954666341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6161870577/10000000000 : ℝ)|^5 ≤ (54593472014443/100000000000000 : ℝ)^4
        have hw : |(6161870577/10000000000 : ℝ)|=(6161870577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (113312371/200000000 : ℝ)*x 0 + (1136719383/2000000000 : ℝ)*x 1 + (-173428439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113312371/200000000 : ℝ)^5 ≤ (49154033846907/100000000000000 : ℝ)^4 := by
    have hnat : (113312371 : ℕ)^5*100000000000000^4 ≤ 49154033846907^4*200000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113312371 200000000 49154033846907 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136719383/2000000000 : ℝ)^5 ≤ (49349083029057/100000000000000 : ℝ)^4 := by
    have hnat : (1136719383 : ℕ)^5*100000000000000^4 ≤ 49349083029057^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136719383 2000000000 49349083029057 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173428439/5000000000 : ℝ)^5 ≤ (1496883111313/100000000000000 : ℝ)^4 := by
    have hnat : (173428439 : ℕ)^5*100000000000000^4 ≤ 1496883111313^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173428439 5000000000 1496883111313 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(113312371/200000000 : ℝ), (1136719383/2000000000 : ℝ), (-173428439/5000000000 : ℝ)] ![(49154033846907/100000000000000 : ℝ), (49349083029057/100000000000000 : ℝ), (1496883111313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(113312371/200000000 : ℝ)|^5 ≤ (49154033846907/100000000000000 : ℝ)^4
        have hw : |(113312371/200000000 : ℝ)|=(113312371/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1136719383/2000000000 : ℝ)|^5 ≤ (49349083029057/100000000000000 : ℝ)^4
        have hw : |(1136719383/2000000000 : ℝ)|=(1136719383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173428439/5000000000 : ℝ)|^5 ≤ (1496883111313/100000000000000 : ℝ)^4
        have hw : |(-173428439/5000000000 : ℝ)|=(173428439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (7730821/20000000 : ℝ)*x 0 + (226656163/400000000 : ℝ)*x 1 + (1399500739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7730821/20000000 : ℝ)^5 ≤ (30478565839797/100000000000000 : ℝ)^4 := by
    have hnat : (7730821 : ℕ)^5*100000000000000^4 ≤ 30478565839797^4*20000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7730821 20000000 30478565839797 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226656163/400000000 : ℝ)^5 ≤ (49162552861921/100000000000000 : ℝ)^4 := by
    have hnat : (226656163 : ℕ)^5*100000000000000^4 ≤ 49162552861921^4*400000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226656163 400000000 49162552861921 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1399500739/5000000000 : ℝ)^5 ≤ (20358881274937/100000000000000 : ℝ)^4 := by
    have hnat : (1399500739 : ℕ)^5*100000000000000^4 ≤ 20358881274937^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399500739 5000000000 20358881274937 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7730821/20000000 : ℝ), (226656163/400000000 : ℝ), (1399500739/5000000000 : ℝ)] ![(30478565839797/100000000000000 : ℝ), (49162552861921/100000000000000 : ℝ), (20358881274937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7730821/20000000 : ℝ)|^5 ≤ (30478565839797/100000000000000 : ℝ)^4
        have hw : |(7730821/20000000 : ℝ)|=(7730821/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226656163/400000000 : ℝ)|^5 ≤ (49162552861921/100000000000000 : ℝ)^4
        have hw : |(226656163/400000000 : ℝ)|=(226656163/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1399500739/5000000000 : ℝ)|^5 ≤ (20358881274937/100000000000000 : ℝ)^4
        have hw : |(1399500739/5000000000 : ℝ)|=(1399500739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-2967581949/10000000000 : ℝ)*x 0 + (3150831103/10000000000 : ℝ)*x 1 + (6152572889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2967581949/10000000000 : ℝ)^5 ≤ (21902989799349/100000000000000 : ℝ)^4 := by
    have hnat : (2967581949 : ℕ)^5*100000000000000^4 ≤ 21902989799349^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2967581949 10000000000 21902989799349 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3150831103/10000000000 : ℝ)^5 ≤ (1475405581983/6250000000000 : ℝ)^4 := by
    have hnat : (3150831103 : ℕ)^5*6250000000000^4 ≤ 1475405581983^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3150831103 10000000000 1475405581983 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6152572889/10000000000 : ℝ)^5 ≤ (54490520871539/100000000000000 : ℝ)^4 := by
    have hnat : (6152572889 : ℕ)^5*100000000000000^4 ≤ 54490520871539^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6152572889 10000000000 54490520871539 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2967581949/10000000000 : ℝ), (3150831103/10000000000 : ℝ), (6152572889/10000000000 : ℝ)] ![(21902989799349/100000000000000 : ℝ), (1475405581983/6250000000000 : ℝ), (54490520871539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2967581949/10000000000 : ℝ)|^5 ≤ (21902989799349/100000000000000 : ℝ)^4
        have hw : |(-2967581949/10000000000 : ℝ)|=(2967581949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3150831103/10000000000 : ℝ)|^5 ≤ (1475405581983/6250000000000 : ℝ)^4
        have hw : |(3150831103/10000000000 : ℝ)|=(3150831103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6152572889/10000000000 : ℝ)|^5 ≤ (54490520871539/100000000000000 : ℝ)^4
        have hw : |(6152572889/10000000000 : ℝ)|=(6152572889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1481092191/5000000000 : ℝ)*x 0 + (-629949423/2000000000 : ℝ)*x 1 + (6157986381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1481092191/5000000000 : ℝ)^5 ≤ (1092660174463/5000000000000 : ℝ)^4 := by
    have hnat : (1481092191 : ℕ)^5*5000000000000^4 ≤ 1092660174463^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1481092191 5000000000 1092660174463 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (629949423/2000000000 : ℝ)^5 ≤ (11798169000869/50000000000000 : ℝ)^4 := by
    have hnat : (629949423 : ℕ)^5*50000000000000^4 ≤ 11798169000869^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629949423 2000000000 11798169000869 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6157986381/10000000000 : ℝ)^5 ≤ (27275229243191/50000000000000 : ℝ)^4 := by
    have hnat : (6157986381 : ℕ)^5*50000000000000^4 ≤ 27275229243191^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6157986381 10000000000 27275229243191 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1481092191/5000000000 : ℝ), (-629949423/2000000000 : ℝ), (6157986381/10000000000 : ℝ)] ![(1092660174463/5000000000000 : ℝ), (11798169000869/50000000000000 : ℝ), (27275229243191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1481092191/5000000000 : ℝ)|^5 ≤ (1092660174463/5000000000000 : ℝ)^4
        have hw : |(1481092191/5000000000 : ℝ)|=(1481092191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-629949423/2000000000 : ℝ)|^5 ≤ (11798169000869/50000000000000 : ℝ)^4
        have hw : |(-629949423/2000000000 : ℝ)|=(629949423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6157986381/10000000000 : ℝ)|^5 ≤ (27275229243191/50000000000000 : ℝ)^4
        have hw : |(6157986381/10000000000 : ℝ)|=(6157986381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_16 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (749803803/1250000000 : ℝ)*x 0 + (5344135681/10000000000 : ℝ)*x 1 + (-70148023/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (749803803/1250000000 : ℝ)^5 ≤ (26394718622019/50000000000000 : ℝ)^4 := by
    have hnat : (749803803 : ℕ)^5*50000000000000^4 ≤ 26394718622019^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749803803 1250000000 26394718622019 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5344135681/10000000000 : ℝ)^5 ≤ (11423175613123/25000000000000 : ℝ)^4 := by
    have hnat : (5344135681 : ℕ)^5*25000000000000^4 ≤ 11423175613123^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344135681 10000000000 11423175613123 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70148023/2000000000 : ℝ)^5 ≤ (18973253663/1250000000000 : ℝ)^4 := by
    have hnat : (70148023 : ℕ)^5*1250000000000^4 ≤ 18973253663^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70148023 2000000000 18973253663 1250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(749803803/1250000000 : ℝ), (5344135681/10000000000 : ℝ), (-70148023/2000000000 : ℝ)] ![(26394718622019/50000000000000 : ℝ), (11423175613123/25000000000000 : ℝ), (18973253663/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(749803803/1250000000 : ℝ)|^5 ≤ (26394718622019/50000000000000 : ℝ)^4
        have hw : |(749803803/1250000000 : ℝ)|=(749803803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5344135681/10000000000 : ℝ)|^5 ≤ (11423175613123/25000000000000 : ℝ)^4
        have hw : |(5344135681/10000000000 : ℝ)|=(5344135681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-70148023/2000000000 : ℝ)|^5 ≤ (18973253663/1250000000000 : ℝ)^4
        have hw : |(-70148023/2000000000 : ℝ)|=(70148023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_19 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-27/2500000000 : ℝ)*x 0 + (27/2500000000 : ℝ)*x 1 + (4999999999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27/2500000000 : ℝ)^5 ≤ (1101/10000000000000 : ℝ)^4 := by
    have hnat : (27 : ℕ)^5*10000000000000^4 ≤ 1101^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27 2500000000 1101 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27/2500000000 : ℝ)^5 ≤ (1101/10000000000000 : ℝ)^4 := by
    have hnat : (27 : ℕ)^5*10000000000000^4 ≤ 1101^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27 2500000000 1101 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4999999999/5000000000 : ℝ)^5 ≤ (99999999975001/100000000000000 : ℝ)^4 := by
    have hnat : (4999999999 : ℕ)^5*100000000000000^4 ≤ 99999999975001^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999999999 5000000000 99999999975001 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27/2500000000 : ℝ), (27/2500000000 : ℝ), (4999999999/5000000000 : ℝ)] ![(1101/10000000000000 : ℝ), (1101/10000000000000 : ℝ), (99999999975001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27/2500000000 : ℝ)|^5 ≤ (1101/10000000000000 : ℝ)^4
        have hw : |(-27/2500000000 : ℝ)|=(27/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27/2500000000 : ℝ)|^5 ≤ (1101/10000000000000 : ℝ)^4
        have hw : |(27/2500000000 : ℝ)|=(27/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4999999999/5000000000 : ℝ)|^5 ≤ (99999999975001/100000000000000 : ℝ)^4
        have hw : |(4999999999/5000000000 : ℝ)|=(4999999999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (479024199/1000000000 : ℝ)*x 0 + (238753569/500000000 : ℝ)*x 1 + (2809491999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (479024199/1000000000 : ℝ)^5 ≤ (9962924182233/25000000000000 : ℝ)^4 := by
    have hnat : (479024199 : ℕ)^5*25000000000000^4 ≤ 9962924182233^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479024199 1000000000 9962924182233 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238753569/500000000 : ℝ)^5 ≤ (39693997226007/100000000000000 : ℝ)^4 := by
    have hnat : (238753569 : ℕ)^5*100000000000000^4 ≤ 39693997226007^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238753569 500000000 39693997226007 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2809491999/10000000000 : ℝ)^5 ≤ (20454306035491/100000000000000 : ℝ)^4 := by
    have hnat : (2809491999 : ℕ)^5*100000000000000^4 ≤ 20454306035491^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2809491999 10000000000 20454306035491 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(479024199/1000000000 : ℝ), (238753569/500000000 : ℝ), (2809491999/10000000000 : ℝ)] ![(9962924182233/25000000000000 : ℝ), (39693997226007/100000000000000 : ℝ), (20454306035491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(479024199/1000000000 : ℝ)|^5 ≤ (9962924182233/25000000000000 : ℝ)^4
        have hw : |(479024199/1000000000 : ℝ)|=(479024199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238753569/500000000 : ℝ)|^5 ≤ (39693997226007/100000000000000 : ℝ)^4
        have hw : |(238753569/500000000 : ℝ)|=(238753569/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2809491999/10000000000 : ℝ)|^5 ≤ (20454306035491/100000000000000 : ℝ)^4
        have hw : |(2809491999/10000000000 : ℝ)|=(2809491999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-3227796651/10000000000 : ℝ)*x 0 + (64486103/200000000 : ℝ)*x 1 + (2934704237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3227796651/10000000000 : ℝ)^5 ≤ (973178934621/4000000000000 : ℝ)^4 := by
    have hnat : (3227796651 : ℕ)^5*4000000000000^4 ≤ 973178934621^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3227796651 10000000000 973178934621 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64486103/200000000 : ℝ)^5 ≤ (2429658138809/10000000000000 : ℝ)^4 := by
    have hnat : (64486103 : ℕ)^5*10000000000000^4 ≤ 2429658138809^4*200000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64486103 200000000 2429658138809 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2934704237/5000000000 : ℝ)^5 ≤ (51373945234967/100000000000000 : ℝ)^4 := by
    have hnat : (2934704237 : ℕ)^5*100000000000000^4 ≤ 51373945234967^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934704237 5000000000 51373945234967 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3227796651/10000000000 : ℝ), (64486103/200000000 : ℝ), (2934704237/5000000000 : ℝ)] ![(973178934621/4000000000000 : ℝ), (2429658138809/10000000000000 : ℝ), (51373945234967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3227796651/10000000000 : ℝ)|^5 ≤ (973178934621/4000000000000 : ℝ)^4
        have hw : |(-3227796651/10000000000 : ℝ)|=(3227796651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64486103/200000000 : ℝ)|^5 ≤ (2429658138809/10000000000000 : ℝ)^4
        have hw : |(64486103/200000000 : ℝ)|=(64486103/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2934704237/5000000000 : ℝ)|^5 ≤ (51373945234967/100000000000000 : ℝ)^4
        have hw : |(2934704237/5000000000 : ℝ)|=(2934704237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (201561557/625000000 : ℝ)*x 0 + (-201301569/625000000 : ℝ)*x 1 + (5874824531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201561557/625000000 : ℝ)^5 ≤ (24302984445187/100000000000000 : ℝ)^4 := by
    have hnat : (201561557 : ℕ)^5*100000000000000^4 ≤ 24302984445187^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201561557 625000000 24302984445187 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201301569/625000000 : ℝ)^5 ≤ (6065951545723/25000000000000 : ℝ)^4 := by
    have hnat : (201301569 : ℕ)^5*25000000000000^4 ≤ 6065951545723^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201301569 625000000 6065951545723 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5874824531/10000000000 : ℝ)^5 ≤ (25716604681731/50000000000000 : ℝ)^4 := by
    have hnat : (5874824531 : ℕ)^5*50000000000000^4 ≤ 25716604681731^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5874824531 10000000000 25716604681731 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(201561557/625000000 : ℝ), (-201301569/625000000 : ℝ), (5874824531/10000000000 : ℝ)] ![(24302984445187/100000000000000 : ℝ), (6065951545723/25000000000000 : ℝ), (25716604681731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(201561557/625000000 : ℝ)|^5 ≤ (24302984445187/100000000000000 : ℝ)^4
        have hw : |(201561557/625000000 : ℝ)|=(201561557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201301569/625000000 : ℝ)|^5 ≤ (6065951545723/25000000000000 : ℝ)^4
        have hw : |(-201301569/625000000 : ℝ)|=(201301569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5874824531/10000000000 : ℝ)|^5 ≤ (25716604681731/50000000000000 : ℝ)^4
        have hw : |(5874824531/10000000000 : ℝ)|=(5874824531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_23 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (6168495021/10000000000 : ℝ)*x 0 + (2522961279/5000000000 : ℝ)*x 1 + (-114653147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6168495021/10000000000 : ℝ)^5 ≤ (546668466457/1000000000000 : ℝ)^4 := by
    have hnat : (6168495021 : ℕ)^5*1000000000000^4 ≤ 546668466457^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6168495021 10000000000 546668466457 1000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2522961279/5000000000 : ℝ)^5 ≤ (10632018774363/25000000000000 : ℝ)^4 := by
    have hnat : (2522961279 : ℕ)^5*25000000000000^4 ≤ 10632018774363^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2522961279 5000000000 10632018774363 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114653147/2000000000 : ℝ)^5 ≤ (2805078245701/100000000000000 : ℝ)^4 := by
    have hnat : (114653147 : ℕ)^5*100000000000000^4 ≤ 2805078245701^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114653147 2000000000 2805078245701 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6168495021/10000000000 : ℝ), (2522961279/5000000000 : ℝ), (-114653147/2000000000 : ℝ)] ![(546668466457/1000000000000 : ℝ), (10632018774363/25000000000000 : ℝ), (2805078245701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6168495021/10000000000 : ℝ)|^5 ≤ (546668466457/1000000000000 : ℝ)^4
        have hw : |(6168495021/10000000000 : ℝ)|=(6168495021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2522961279/5000000000 : ℝ)|^5 ≤ (10632018774363/25000000000000 : ℝ)^4
        have hw : |(2522961279/5000000000 : ℝ)|=(2522961279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114653147/2000000000 : ℝ)|^5 ≤ (2805078245701/100000000000000 : ℝ)^4
        have hw : |(-114653147/2000000000 : ℝ)|=(114653147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319059_s1_s1_27 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (729403989/2500000000 : ℝ)*x 0 + (93302603/156250000 : ℝ)*x 1 + (3410734969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (729403989/2500000000 : ℝ)^5 ≤ (10721490400813/50000000000000 : ℝ)^4 := by
    have hnat : (729403989 : ℕ)^5*50000000000000^4 ≤ 10721490400813^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729403989 2500000000 10721490400813 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93302603/156250000 : ℝ)^5 ≤ (524918848629/1000000000000 : ℝ)^4 := by
    have hnat : (93302603 : ℕ)^5*1000000000000^4 ≤ 524918848629^4*156250000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93302603 156250000 524918848629 1000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3410734969/10000000000 : ℝ)^5 ≤ (6516283580953/25000000000000 : ℝ)^4 := by
    have hnat : (3410734969 : ℕ)^5*25000000000000^4 ≤ 6516283580953^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3410734969 10000000000 6516283580953 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(729403989/2500000000 : ℝ), (93302603/156250000 : ℝ), (3410734969/10000000000 : ℝ)] ![(10721490400813/50000000000000 : ℝ), (524918848629/1000000000000 : ℝ), (6516283580953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(729403989/2500000000 : ℝ)|^5 ≤ (10721490400813/50000000000000 : ℝ)^4
        have hw : |(729403989/2500000000 : ℝ)|=(729403989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(93302603/156250000 : ℝ)|^5 ≤ (524918848629/1000000000000 : ℝ)^4
        have hw : |(93302603/156250000 : ℝ)|=(93302603/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3410734969/10000000000 : ℝ)|^5 ≤ (6516283580953/25000000000000 : ℝ)^4
        have hw : |(3410734969/10000000000 : ℝ)|=(3410734969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319059_s1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((37401/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37401/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74401/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(74401/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(29473/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(29473/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1449/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1449/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13819/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13819/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7561/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7561/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s1_pow0 : (37401/50000 : ℝ) ^ (79/16 : ℝ) ≤ (2980962321407649319/12500000000000000000 : ℝ) := by
    have hpowers : (37401/50000 : ℝ)^79 ≤ (2980962321407649319/12500000000000000000 : ℝ)^16 := by
      have hnat : (37401 : ℕ)^79*12500000000000000000^16 ≤ 2980962321407649319^16*50000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37401 50000 2980962321407649319 12500000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37401/50000 : ℝ)) (X := (2980962321407649319/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (15480962321407649319/12500000000000000000 : ℝ) ≤ (2610674674089253/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (15480962321407649319/12500000000000000000 : ℝ)^16 ≤ (2610674674089253/2500000000000000 : ℝ)^79 := by
      have hnat : (15480962321407649319 : ℕ)^16*2500000000000000^79 ≤ 2610674674089253^79*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15480962321407649319 12500000000000000000 2610674674089253 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610674674089253/2500000000000000 : ℝ)) (X := (15480962321407649319/12500000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (9230962321407649319/6250000000000000000 : ℝ) ≤ (5410933214987201/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (9230962321407649319/6250000000000000000 : ℝ)^16 ≤ (5410933214987201/5000000000000000 : ℝ)^79 := by
      have hnat : (9230962321407649319 : ℕ)^16*5000000000000000^79 ≤ 5410933214987201^79*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9230962321407649319 6250000000000000000 5410933214987201 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5410933214987201/5000000000000000 : ℝ)) (X := (9230962321407649319/6250000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(36891558029751/623350000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12638924453913/249340000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (37401/50000 : ℝ)) (alpha := (36891558029751/623350000000000 : ℝ)) (beta := (12638924453913/249340000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (37401/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(36891558029751/623350000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12638924453913/249340000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (74401/100000 : ℝ) ^ (79/16 : ℝ) ≤ (11611549957573861543/50000000000000000000 : ℝ) := by
    have hpowers : (74401/100000 : ℝ)^79 ≤ (11611549957573861543/50000000000000000000 : ℝ)^16 := by
      have hnat : (74401 : ℕ)^79*50000000000000000000^16 ≤ 11611549957573861543^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74401 100000 11611549957573861543 50000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74401/100000 : ℝ)) (X := (11611549957573861543/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (61611549957573861543/50000000000000000000 : ℝ) ≤ (2086402152070387/2000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (61611549957573861543/50000000000000000000 : ℝ)^16 ≤ (2086402152070387/2000000000000000 : ℝ)^79 := by
      have hnat : (61611549957573861543 : ℕ)^16*2000000000000000^79 ≤ 2086402152070387^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61611549957573861543 50000000000000000000 2086402152070387 2000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2086402152070387/2000000000000000 : ℝ)) (X := (61611549957573861543/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (36611549957573861543/25000000000000000000 : ℝ) ≤ (2700816438137727/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (36611549957573861543/25000000000000000000 : ℝ)^16 ≤ (2700816438137727/2500000000000000 : ℝ)^79 := by
      have hnat : (36611549957573861543 : ℕ)^16*2500000000000000^79 ≤ 2700816438137727^79*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36611549957573861543 25000000000000000000 2700816438137727 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2700816438137727/2500000000000000 : ℝ)) (X := (36611549957573861543/25000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(86402152070387/1488020000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(371254992198973/7440100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (74401/100000 : ℝ)) (alpha := (86402152070387/1488020000000000 : ℝ)) (beta := (371254992198973/7440100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (74401/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(86402152070387/1488020000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(371254992198973/7440100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (29473/50000 : ℝ) ^ (79/16 : ℝ) ≤ (7355603361248899169/100000000000000000000 : ℝ) := by
    have hpowers : (29473/50000 : ℝ)^79 ≤ (7355603361248899169/100000000000000000000 : ℝ)^16 := by
      have hnat : (29473 : ℕ)^79*100000000000000000000^16 ≤ 7355603361248899169^16*50000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29473 50000 7355603361248899169 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29473/50000 : ℝ)) (X := (7355603361248899169/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (107355603361248899169/100000000000000000000 : ℝ) ≤ (1268098514172237/1250000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (107355603361248899169/100000000000000000000 : ℝ)^16 ≤ (1268098514172237/1250000000000000 : ℝ)^79 := by
      have hnat : (107355603361248899169 : ℕ)^16*1250000000000000^79 ≤ 1268098514172237^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107355603361248899169 100000000000000000000 1268098514172237 1250000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1268098514172237/1250000000000000 : ℝ)) (X := (107355603361248899169/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (57355603361248899169/50000000000000000000 : ℝ) ≤ (10281869101572287/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (57355603361248899169/50000000000000000000 : ℝ)^16 ≤ (10281869101572287/10000000000000000 : ℝ)^79 := by
      have hnat : (57355603361248899169 : ℕ)^16*10000000000000000^79 ≤ 10281869101572287^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57355603361248899169 50000000000000000000 10281869101572287 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10281869101572287/10000000000000000 : ℝ)) (X := (57355603361248899169/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(18098514172237/736825000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(137080988194391/5894600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (29473/50000 : ℝ)) (alpha := (18098514172237/736825000000000 : ℝ)) (beta := (137080988194391/5894600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (29473/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(18098514172237/736825000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(137080988194391/5894600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3224155999/10000000000 : ℝ)*X 0 0+(201276537/625000000 : ℝ)*X 0 1+(587588261/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((201319049/625000000 : ℝ)*X 1 0+(-3217189289/10000000000 : ℝ)*X 1 1+(5881291127/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5760482291/10000000000 : ℝ)*X 2 0+(1360062161/2500000000 : ℝ)*X 2 1+(-2421277/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((400185359/1000000000 : ℝ)*X 0 0+(977756079/2000000000 : ℝ)*X 0 1+(3538543567/10000000000 : ℝ)*X 0 2+(400185359/1000000000 : ℝ)*X 1 0+(977756079/2000000000 : ℝ)*X 1 1+(3538543567/10000000000 : ℝ)*X 1 2+(400185359/1000000000 : ℝ)*X 2 0+(977756079/2000000000 : ℝ)*X 2 1+(3538543567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-393517697/1250000000 : ℝ)*X 0 0+(296565131/1000000000 : ℝ)*X 0 1+(6156456333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((788138667/2500000000 : ℝ)*X 1 0+(-2954666341/10000000000 : ℝ)*X 1 1+(6161870577/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((113312371/200000000 : ℝ)*X 2 0+(1136719383/2000000000 : ℝ)*X 2 1+(-173428439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((7730821/20000000 : ℝ)*X 0 0+(226656163/400000000 : ℝ)*X 0 1+(1399500739/5000000000 : ℝ)*X 0 2+(7730821/20000000 : ℝ)*X 1 0+(226656163/400000000 : ℝ)*X 1 1+(1399500739/5000000000 : ℝ)*X 1 2+(7730821/20000000 : ℝ)*X 2 0+(226656163/400000000 : ℝ)*X 2 1+(1399500739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-2967581949/10000000000 : ℝ)*X 0 0+(3150831103/10000000000 : ℝ)*X 0 1+(6152572889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1481092191/5000000000 : ℝ)*X 1 0+(-629949423/2000000000 : ℝ)*X 1 1+(6157986381/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((749803803/1250000000 : ℝ)*X 2 0+(5344135681/10000000000 : ℝ)*X 2 1+(-70148023/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-27/2500000000 : ℝ)*X 0 0+(27/2500000000 : ℝ)*X 0 1+(4999999999/5000000000 : ℝ)*X 0 2+(-27/2500000000 : ℝ)*X 1 0+(27/2500000000 : ℝ)*X 1 1+(4999999999/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_19 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((479024199/1000000000 : ℝ)*X 0 0+(238753569/500000000 : ℝ)*X 0 1+(2809491999/10000000000 : ℝ)*X 0 2+(479024199/1000000000 : ℝ)*X 1 0+(238753569/500000000 : ℝ)*X 1 1+(2809491999/10000000000 : ℝ)*X 1 2+(479024199/1000000000 : ℝ)*X 2 0+(238753569/500000000 : ℝ)*X 2 1+(2809491999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-3227796651/10000000000 : ℝ)*X 0 0+(64486103/200000000 : ℝ)*X 0 1+(2934704237/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((201561557/625000000 : ℝ)*X 1 0+(-201301569/625000000 : ℝ)*X 1 1+(5874824531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((6168495021/10000000000 : ℝ)*X 2 0+(2522961279/5000000000 : ℝ)*X 2 1+(-114653147/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((729403989/2500000000 : ℝ)*X 0 0+(93302603/156250000 : ℝ)*X 0 1+(3410734969/10000000000 : ℝ)*X 0 2+(729403989/2500000000 : ℝ)*X 1 0+(93302603/156250000 : ℝ)*X 1 1+(3410734969/10000000000 : ℝ)*X 1 2+(729403989/2500000000 : ℝ)*X 2 0+(93302603/156250000 : ℝ)*X 2 1+(3410734969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319059_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((1449/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1449/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12856800938614328452054922818491/2733789533029100000000000000000000000 : ℝ) := by norm_num
    linear_combination (23187332797/6250000000 : ℝ)*(base60) + (6526761214593/500000000000 : ℝ)*(major_s1_0) + (6526761214593/500000000000 : ℝ)*(major_s1_1) + (2610723184889/200000000000 : ℝ)*(major_s1_2) + (142119021/1000000000000 : ℝ)*(sp_s1_0) + (29078367/200000000000 : ℝ)*(sp_s1_1) + (34023653/500000000000 : ℝ)*(sp_s1_2) + (238181580883/12500000000 : ℝ)*(sp_s1_7) + (19054382193657/1000000000000 : ℝ)*(sp_s1_8) + (3810920108471/200000000000 : ℝ)*(sp_s1_9) + (881541871251/125000000000 : ℝ)*(sp_s1_13) + (14100417/100000000000 : ℝ)*(sp_s1_15) + (93495259/1000000000000 : ℝ)*(sp_s1_19) + (7946211/200000000000 : ℝ)*(sp_s1_27) + (7052374701063/1000000000000 : ℝ)*(f.failure) + (19054668589661/1000000000000 : ℝ)*(f.sum) + (481048579084421793/1096410336500000000000000000000 : ℝ)*base63 + (944241197105711/1178920000000000000000000000 : ℝ)*base65 + (630749876011667/1860025000000000000000000000 : ℝ)*base67 + (59463629117171/147365000000000000000000000 : ℝ)*base69 + (61705693089621392977/73487978200000000000000000000000 : ℝ)*base71 + (16414948826713/62335000000000000000000000 : ℝ)*base72 + (47016701888443/148802000000000000000000000 : ℝ)*base75 + (233021902183271/623350000000000000000000000 : ℝ)*base77 + (2802399207555277313/46377863350000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (22539/50000000000000000 : ℝ)*base86 + (22539/50000000000000000 : ℝ)*base88 + (22539/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13819/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13819/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5890459337480433390013554327117/683447383257275000000000000000000000 : ℝ) := by norm_num
    linear_combination (3722993596689/1000000000000 : ℝ)*(base60) + (13098220209163/1000000000000 : ℝ)*(major_s1_0) + (13098220209163/1000000000000 : ℝ)*(major_s1_1) + (6549163246947/500000000000 : ℝ)*(major_s1_2) + (140792427/1000000000000 : ℝ)*(sp_s1_0) + (18617583/200000000000 : ℝ)*(sp_s1_1) + (12550131/200000000000 : ℝ)*(sp_s1_6) + (73518947/1000000000000 : ℝ)*(sp_s1_7) + (9559849920483/500000000000 : ℝ)*(sp_s1_14) + (764792842577/40000000000 : ℝ)*(sp_s1_15) + (19119780638113/1000000000000 : ℝ)*(sp_s1_16) + (106284731/1000000000000 : ℝ)*(sp_s1_19) + (1769115160603/250000000000 : ℝ)*(sp_s1_20) + (33378557/250000000000 : ℝ)*(sp_s1_23) + (7076523393067/1000000000000 : ℝ)*(f.failure) + (955995707617/50000000000 : ℝ)*(f.sum) + (65781544812078667937/219282067300000000000000000000000 : ℝ)*base62 + (634431970947773/2947300000000000000000000000 : ℝ)*base64 + (45652229074539/7440100000000000000000000000 : ℝ)*base67 + (39949601211167/184206250000000000000000000 : ℝ)*base68 + (10579822786412979873/36743989100000000000000000000000 : ℝ)*base70 + (13662167089/1994720000000000000000000 : ℝ)*base73 + (940619893487979/1488020000000000000000000000 : ℝ)*base74 + (352916889560357/623350000000000000000000000 : ℝ)*base76 + (384618924541648729/11594465837500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (21649/50000000000000000 : ℝ)*base87 + (21649/50000000000000000 : ℝ)*base89 + (21649/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7561/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7561/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4518074689946022096510999/1837199455000000000000000000000 : ℝ) := by norm_num
    linear_combination (1590157/1000000000000 : ℝ)*(base39) + (1331123/1000000000000 : ℝ)*(base49) + (4240999/1000000000000 : ℝ)*(base50) + (1964545138377/1000000000000 : ℝ)*(base60) + (854223303379/100000000000 : ℝ)*(major_s1_0) + (854223303379/100000000000 : ℝ)*(major_s1_1) + (854223303379/100000000000 : ℝ)*(major_s1_2) + (6089803/500000000000 : ℝ)*(sp_s1_6) + (9333147/125000000000 : ℝ)*(sp_s1_8) + (47813737/1000000000000 : ℝ)*(sp_s1_13) + (6234693472517/500000000000 : ℝ)*(sp_s1_21) + (6234656139929/500000000000 : ℝ)*(sp_s1_22) + (6234693472517/500000000000 : ℝ)*(sp_s1_23) + (230750915473/50000000000 : ℝ)*(sp_s1_27) + (4615078302803/1000000000000 : ℝ)*(f.failure) + (6234693472517/500000000000 : ℝ)*(f.sum) + (446857862808551067/4385641346000000000000000000000 : ℝ)*base63 + (422609915932301/589460000000000000000000000 : ℝ)*base64 + (506137549846577/744010000000000000000000000 : ℝ)*base66 + (52956346755741/73682500000000000000000000 : ℝ)*base68 + (1814131605817480363/7348797820000000000000000000000 : ℝ)*base70 + (6566684148191/124670000000000000000000000 : ℝ)*base72 + (110035954096749/744010000000000000000000000 : ℝ)*base74 + (55128195437321/124670000000000000000000000 : ℝ)*base76 + (1129995701942737489/4637786335000000000000000000000 : ℝ)*base79 + (9241/50000000000000000 : ℝ)*base87 + (9241/50000000000000000 : ℝ)*base89 + (9241/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((37401/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37401/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74401/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(74401/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(29473/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(29473/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1449/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1449/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13819/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13819/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7561/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7561/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c319059_s1 p hpa hpb X hX hprev0

#print axioms solution
