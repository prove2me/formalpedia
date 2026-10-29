-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312054_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:19:21.362279+00:00
-- url     : https://prove2.me/submissions/effaddc1-7def-47ee-b493-cfceb5d1e2d4

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
theorem collision_support_c312054_s2_s2_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1149048469/10000000000 : ℝ)*x 0 + (2261171329/5000000000 : ℝ)*x 1 + (-3247813653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1149048469/10000000000 : ℝ)^73 ≤ (3129995251149/50000000000000 : ℝ)^57 := by
    have hnat : (1149048469 : ℕ)^73*50000000000000^57 ≤ 3129995251149^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149048469 10000000000 3129995251149 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261171329/5000000000 : ℝ)^73 ≤ (4524112532259/12500000000000 : ℝ)^57 := by
    have hnat : (2261171329 : ℕ)^73*12500000000000^57 ≤ 4524112532259^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261171329 5000000000 4524112532259 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3247813653/5000000000 : ℝ)^73 ≤ (28773554612067/50000000000000 : ℝ)^57 := by
    have hnat : (3247813653 : ℕ)^73*50000000000000^57 ≤ 28773554612067^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3247813653 5000000000 28773554612067 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1149048469/10000000000 : ℝ), (2261171329/5000000000 : ℝ), (-3247813653/5000000000 : ℝ)] ![(3129995251149/50000000000000 : ℝ), (4524112532259/12500000000000 : ℝ), (28773554612067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1149048469/10000000000 : ℝ)|^73 ≤ (3129995251149/50000000000000 : ℝ)^57
        have hw : |(-1149048469/10000000000 : ℝ)|=(1149048469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2261171329/5000000000 : ℝ)|^73 ≤ (4524112532259/12500000000000 : ℝ)^57
        have hw : |(2261171329/5000000000 : ℝ)|=(2261171329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3247813653/5000000000 : ℝ)|^73 ≤ (28773554612067/50000000000000 : ℝ)^57
        have hw : |(-3247813653/5000000000 : ℝ)|=(3247813653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5214650649/10000000000 : ℝ)*x 0 + (1034999457/2000000000 : ℝ)*x 1 + (1049985017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5214650649/10000000000 : ℝ)^73 ≤ (2171800084269/5000000000000 : ℝ)^57 := by
    have hnat : (5214650649 : ℕ)^73*5000000000000^57 ≤ 2171800084269^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214650649 10000000000 2171800084269 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034999457/2000000000 : ℝ)^73 ≤ (43013441997803/100000000000000 : ℝ)^57 := by
    have hnat : (1034999457 : ℕ)^73*100000000000000^57 ≤ 43013441997803^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034999457 2000000000 43013441997803 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049985017/5000000000 : ℝ)^73 ≤ (6775278148909/50000000000000 : ℝ)^57 := by
    have hnat : (1049985017 : ℕ)^73*50000000000000^57 ≤ 6775278148909^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049985017 5000000000 6775278148909 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5214650649/10000000000 : ℝ), (1034999457/2000000000 : ℝ), (1049985017/5000000000 : ℝ)] ![(2171800084269/5000000000000 : ℝ), (43013441997803/100000000000000 : ℝ), (6775278148909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5214650649/10000000000 : ℝ)|^73 ≤ (2171800084269/5000000000000 : ℝ)^57
        have hw : |(5214650649/10000000000 : ℝ)|=(5214650649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034999457/2000000000 : ℝ)|^73 ≤ (43013441997803/100000000000000 : ℝ)^57
        have hw : |(1034999457/2000000000 : ℝ)|=(1034999457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049985017/5000000000 : ℝ)|^73 ≤ (6775278148909/50000000000000 : ℝ)^57
        have hw : |(1049985017/5000000000 : ℝ)|=(1049985017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-959054557/10000000000 : ℝ)*x 0 + (2012044427/5000000000 : ℝ)*x 1 + (-7046160531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (959054557/10000000000 : ℝ)^73 ≤ (4966437163389/100000000000000 : ℝ)^57 := by
    have hnat : (959054557 : ℕ)^73*100000000000000^57 ≤ 4966437163389^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959054557 10000000000 4966437163389 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012044427/5000000000 : ℝ)^73 ≤ (155835736161/500000000000 : ℝ)^57 := by
    have hnat : (2012044427 : ℕ)^73*500000000000^57 ≤ 155835736161^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012044427 5000000000 155835736161 500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7046160531/10000000000 : ℝ)^73 ≤ (63866415599363/100000000000000 : ℝ)^57 := by
    have hnat : (7046160531 : ℕ)^73*100000000000000^57 ≤ 63866415599363^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7046160531 10000000000 63866415599363 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-959054557/10000000000 : ℝ), (2012044427/5000000000 : ℝ), (-7046160531/10000000000 : ℝ)] ![(4966437163389/100000000000000 : ℝ), (155835736161/500000000000 : ℝ), (63866415599363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-959054557/10000000000 : ℝ)|^73 ≤ (4966437163389/100000000000000 : ℝ)^57
        have hw : |(-959054557/10000000000 : ℝ)|=(959054557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012044427/5000000000 : ℝ)|^73 ≤ (155835736161/500000000000 : ℝ)^57
        have hw : |(2012044427/5000000000 : ℝ)|=(2012044427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7046160531/10000000000 : ℝ)|^73 ≤ (63866415599363/100000000000000 : ℝ)^57
        have hw : |(-7046160531/10000000000 : ℝ)|=(7046160531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1048946983/2000000000 : ℝ)*x 0 + (-655653963/5000000000 : ℝ)*x 1 + (-1142727397/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048946983/2000000000 : ℝ)^73 ≤ (2734824529199/6250000000000 : ℝ)^57 := by
    have hnat : (1048946983 : ℕ)^73*6250000000000^57 ≤ 2734824529199^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048946983 2000000000 2734824529199 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655653963/5000000000 : ℝ)^73 ≤ (7413833762479/100000000000000 : ℝ)^57 := by
    have hnat : (655653963 : ℕ)^73*100000000000000^57 ≤ 7413833762479^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655653963 5000000000 7413833762479 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1142727397/2000000000 : ℝ)^73 ≤ (24414486881227/50000000000000 : ℝ)^57 := by
    have hnat : (1142727397 : ℕ)^73*50000000000000^57 ≤ 24414486881227^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142727397 2000000000 24414486881227 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048946983/2000000000 : ℝ), (-655653963/5000000000 : ℝ), (-1142727397/2000000000 : ℝ)] ![(2734824529199/6250000000000 : ℝ), (7413833762479/100000000000000 : ℝ), (24414486881227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048946983/2000000000 : ℝ)|^73 ≤ (2734824529199/6250000000000 : ℝ)^57
        have hw : |(1048946983/2000000000 : ℝ)|=(1048946983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-655653963/5000000000 : ℝ)|^73 ≤ (7413833762479/100000000000000 : ℝ)^57
        have hw : |(-655653963/5000000000 : ℝ)|=(655653963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1142727397/2000000000 : ℝ)|^73 ≤ (24414486881227/50000000000000 : ℝ)^57
        have hw : |(-1142727397/2000000000 : ℝ)|=(1142727397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4781069561/10000000000 : ℝ)*x 0 + (6282540167/10000000000 : ℝ)*x 1 + (1110692759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4781069561/10000000000 : ℝ)^73 ≤ (38865761848211/100000000000000 : ℝ)^57 := by
    have hnat : (4781069561 : ℕ)^73*100000000000000^57 ≤ 38865761848211^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4781069561 10000000000 38865761848211 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6282540167/10000000000 : ℝ)^73 ≤ (2757030023299/5000000000000 : ℝ)^57 := by
    have hnat : (6282540167 : ℕ)^73*5000000000000^57 ≤ 2757030023299^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6282540167 10000000000 2757030023299 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110692759/10000000000 : ℝ)^73 ≤ (5993637670431/100000000000000 : ℝ)^57 := by
    have hnat : (1110692759 : ℕ)^73*100000000000000^57 ≤ 5993637670431^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110692759 10000000000 5993637670431 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4781069561/10000000000 : ℝ), (6282540167/10000000000 : ℝ), (1110692759/10000000000 : ℝ)] ![(38865761848211/100000000000000 : ℝ), (2757030023299/5000000000000 : ℝ), (5993637670431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4781069561/10000000000 : ℝ)|^73 ≤ (38865761848211/100000000000000 : ℝ)^57
        have hw : |(4781069561/10000000000 : ℝ)|=(4781069561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6282540167/10000000000 : ℝ)|^73 ≤ (2757030023299/5000000000000 : ℝ)^57
        have hw : |(6282540167/10000000000 : ℝ)|=(6282540167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1110692759/10000000000 : ℝ)|^73 ≤ (5993637670431/100000000000000 : ℝ)^57
        have hw : |(1110692759/10000000000 : ℝ)|=(1110692759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (247778577/500000000 : ℝ)*x 0 + (6216843211/10000000000 : ℝ)*x 1 + (-59361699/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (247778577/500000000 : ℝ)^73 ≤ (20345859222071/50000000000000 : ℝ)^57 := by
    have hnat : (247778577 : ℕ)^73*50000000000000^57 ≤ 20345859222071^57*500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247778577 500000000 20345859222071 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6216843211/10000000000 : ℝ)^73 ≤ (3400201423117/6250000000000 : ℝ)^57 := by
    have hnat : (6216843211 : ℕ)^73*6250000000000^57 ≤ 3400201423117^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6216843211 10000000000 3400201423117 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59361699/625000000 : ℝ)^73 ≤ (2452529385387/50000000000000 : ℝ)^57 := by
    have hnat : (59361699 : ℕ)^73*50000000000000^57 ≤ 2452529385387^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59361699 625000000 2452529385387 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(247778577/500000000 : ℝ), (6216843211/10000000000 : ℝ), (-59361699/625000000 : ℝ)] ![(20345859222071/50000000000000 : ℝ), (3400201423117/6250000000000 : ℝ), (2452529385387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(247778577/500000000 : ℝ)|^73 ≤ (20345859222071/50000000000000 : ℝ)^57
        have hw : |(247778577/500000000 : ℝ)|=(247778577/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6216843211/10000000000 : ℝ)|^73 ≤ (3400201423117/6250000000000 : ℝ)^57
        have hw : |(6216843211/10000000000 : ℝ)|=(6216843211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-59361699/625000000 : ℝ)|^73 ≤ (2452529385387/50000000000000 : ℝ)^57
        have hw : |(-59361699/625000000 : ℝ)|=(59361699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-430624097/10000000000 : ℝ)*x 0 + (1107100449/2500000000 : ℝ)*x 1 + (-3485102553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430624097/10000000000 : ℝ)^73 ≤ (356219203903/20000000000000 : ℝ)^57 := by
    have hnat : (430624097 : ℕ)^73*20000000000000^57 ≤ 356219203903^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430624097 10000000000 356219203903 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107100449/2500000000 : ℝ)^73 ≤ (8808215760531/25000000000000 : ℝ)^57 := by
    have hnat : (1107100449 : ℕ)^73*25000000000000^57 ≤ 8808215760531^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107100449 2500000000 8808215760531 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3485102553/5000000000 : ℝ)^73 ≤ (6298604091717/10000000000000 : ℝ)^57 := by
    have hnat : (3485102553 : ℕ)^73*10000000000000^57 ≤ 6298604091717^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3485102553 5000000000 6298604091717 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430624097/10000000000 : ℝ), (1107100449/2500000000 : ℝ), (-3485102553/5000000000 : ℝ)] ![(356219203903/20000000000000 : ℝ), (8808215760531/25000000000000 : ℝ), (6298604091717/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430624097/10000000000 : ℝ)|^73 ≤ (356219203903/20000000000000 : ℝ)^57
        have hw : |(-430624097/10000000000 : ℝ)|=(430624097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1107100449/2500000000 : ℝ)|^73 ≤ (8808215760531/25000000000000 : ℝ)^57
        have hw : |(1107100449/2500000000 : ℝ)|=(1107100449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3485102553/5000000000 : ℝ)|^73 ≤ (6298604091717/10000000000000 : ℝ)^57
        have hw : |(-3485102553/5000000000 : ℝ)|=(3485102553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (486546161/1000000000 : ℝ)*x 0 + (-903144289/5000000000 : ℝ)*x 1 + (-1147322263/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486546161/1000000000 : ℝ)^73 ≤ (39746530258961/100000000000000 : ℝ)^57 := by
    have hnat : (486546161 : ℕ)^73*100000000000000^57 ≤ 39746530258961^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486546161 1000000000 39746530258961 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903144289/5000000000 : ℝ)^73 ≤ (223458035527/2000000000000 : ℝ)^57 := by
    have hnat : (903144289 : ℕ)^73*2000000000000^57 ≤ 223458035527^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903144289 5000000000 223458035527 2000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147322263/2000000000 : ℝ)^73 ≤ (49080567947627/100000000000000 : ℝ)^57 := by
    have hnat : (1147322263 : ℕ)^73*100000000000000^57 ≤ 49080567947627^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147322263 2000000000 49080567947627 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(486546161/1000000000 : ℝ), (-903144289/5000000000 : ℝ), (-1147322263/2000000000 : ℝ)] ![(39746530258961/100000000000000 : ℝ), (223458035527/2000000000000 : ℝ), (49080567947627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(486546161/1000000000 : ℝ)|^73 ≤ (39746530258961/100000000000000 : ℝ)^57
        have hw : |(486546161/1000000000 : ℝ)|=(486546161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-903144289/5000000000 : ℝ)|^73 ≤ (223458035527/2000000000000 : ℝ)^57
        have hw : |(-903144289/5000000000 : ℝ)|=(903144289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1147322263/2000000000 : ℝ)|^73 ≤ (49080567947627/100000000000000 : ℝ)^57
        have hw : |(-1147322263/2000000000 : ℝ)|=(1147322263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3169518603/5000000000 : ℝ)*x 0 + (591892333/1250000000 : ℝ)*x 1 + (217543649/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3169518603/5000000000 : ℝ)^73 ≤ (55776453174057/100000000000000 : ℝ)^57 := by
    have hnat : (3169518603 : ℕ)^73*100000000000000^57 ≤ 55776453174057^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169518603 5000000000 55776453174057 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (591892333/1250000000 : ℝ)^73 ≤ (19194112036261/50000000000000 : ℝ)^57 := by
    have hnat : (591892333 : ℕ)^73*50000000000000^57 ≤ 19194112036261^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591892333 1250000000 19194112036261 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217543649/2000000000 : ℝ)^73 ≤ (5835322729019/100000000000000 : ℝ)^57 := by
    have hnat : (217543649 : ℕ)^73*100000000000000^57 ≤ 5835322729019^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217543649 2000000000 5835322729019 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3169518603/5000000000 : ℝ), (591892333/1250000000 : ℝ), (217543649/2000000000 : ℝ)] ![(55776453174057/100000000000000 : ℝ), (19194112036261/50000000000000 : ℝ), (5835322729019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3169518603/5000000000 : ℝ)|^73 ≤ (55776453174057/100000000000000 : ℝ)^57
        have hw : |(3169518603/5000000000 : ℝ)|=(3169518603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(591892333/1250000000 : ℝ)|^73 ≤ (19194112036261/50000000000000 : ℝ)^57
        have hw : |(591892333/1250000000 : ℝ)|=(591892333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217543649/2000000000 : ℝ)|^73 ≤ (5835322729019/100000000000000 : ℝ)^57
        have hw : |(217543649/2000000000 : ℝ)|=(217543649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1235331767/2000000000 : ℝ)*x 0 + (30523119/62500000 : ℝ)*x 1 + (-281848149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1235331767/2000000000 : ℝ)^73 ≤ (6744158978789/12500000000000 : ℝ)^57 := by
    have hnat : (1235331767 : ℕ)^73*12500000000000^57 ≤ 6744158978789^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235331767 2000000000 6744158978789 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30523119/62500000 : ℝ)^73 ≤ (7987486851473/20000000000000 : ℝ)^57 := by
    have hnat : (30523119 : ℕ)^73*20000000000000^57 ≤ 7987486851473^57*62500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30523119 62500000 7987486851473 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281848149/2500000000 : ℝ)^73 ≤ (6109293894353/100000000000000 : ℝ)^57 := by
    have hnat : (281848149 : ℕ)^73*100000000000000^57 ≤ 6109293894353^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281848149 2500000000 6109293894353 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1235331767/2000000000 : ℝ), (30523119/62500000 : ℝ), (-281848149/2500000000 : ℝ)] ![(6744158978789/12500000000000 : ℝ), (7987486851473/20000000000000 : ℝ), (6109293894353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1235331767/2000000000 : ℝ)|^73 ≤ (6744158978789/12500000000000 : ℝ)^57
        have hw : |(1235331767/2000000000 : ℝ)|=(1235331767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30523119/62500000 : ℝ)|^73 ≤ (7987486851473/20000000000000 : ℝ)^57
        have hw : |(30523119/62500000 : ℝ)|=(30523119/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-281848149/2500000000 : ℝ)|^73 ≤ (6109293894353/100000000000000 : ℝ)^57
        have hw : |(-281848149/2500000000 : ℝ)|=(281848149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-55703083/2500000000 : ℝ)*x 0 + (5281800983/10000000000 : ℝ)*x 1 + (-3138592391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55703083/2500000000 : ℝ)^73 ≤ (765954312909/100000000000000 : ℝ)^57 := by
    have hnat : (55703083 : ℕ)^73*100000000000000^57 ≤ 765954312909^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55703083 2500000000 765954312909 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281800983/10000000000 : ℝ)^73 ≤ (44153635021479/100000000000000 : ℝ)^57 := by
    have hnat : (5281800983 : ℕ)^73*100000000000000^57 ≤ 44153635021479^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281800983 10000000000 44153635021479 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3138592391/5000000000 : ℝ)^73 ≤ (6885051332429/12500000000000 : ℝ)^57 := by
    have hnat : (3138592391 : ℕ)^73*12500000000000^57 ≤ 6885051332429^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3138592391 5000000000 6885051332429 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55703083/2500000000 : ℝ), (5281800983/10000000000 : ℝ), (-3138592391/5000000000 : ℝ)] ![(765954312909/100000000000000 : ℝ), (44153635021479/100000000000000 : ℝ), (6885051332429/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55703083/2500000000 : ℝ)|^73 ≤ (765954312909/100000000000000 : ℝ)^57
        have hw : |(-55703083/2500000000 : ℝ)|=(55703083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281800983/10000000000 : ℝ)|^73 ≤ (44153635021479/100000000000000 : ℝ)^57
        have hw : |(5281800983/10000000000 : ℝ)|=(5281800983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3138592391/5000000000 : ℝ)|^73 ≤ (6885051332429/12500000000000 : ℝ)^57
        have hw : |(-3138592391/5000000000 : ℝ)|=(3138592391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (328360913/500000000 : ℝ)*x 0 + (-3050809/19531250 : ℝ)*x 1 + (-2072102491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328360913/500000000 : ℝ)^73 ≤ (29180323832911/50000000000000 : ℝ)^57 := by
    have hnat : (328360913 : ℕ)^73*50000000000000^57 ≤ 29180323832911^57*500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328360913 500000000 29180323832911 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3050809/19531250 : ℝ)^73 ≤ (9275790668761/100000000000000 : ℝ)^57 := by
    have hnat : (3050809 : ℕ)^73*100000000000000^57 ≤ 9275790668761^57*19531250^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3050809 19531250 9275790668761 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072102491/5000000000 : ℝ)^73 ≤ (32363561645941/100000000000000 : ℝ)^57 := by
    have hnat : (2072102491 : ℕ)^73*100000000000000^57 ≤ 32363561645941^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072102491 5000000000 32363561645941 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328360913/500000000 : ℝ), (-3050809/19531250 : ℝ), (-2072102491/5000000000 : ℝ)] ![(29180323832911/50000000000000 : ℝ), (9275790668761/100000000000000 : ℝ), (32363561645941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328360913/500000000 : ℝ)|^73 ≤ (29180323832911/50000000000000 : ℝ)^57
        have hw : |(328360913/500000000 : ℝ)|=(328360913/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3050809/19531250 : ℝ)|^73 ≤ (9275790668761/100000000000000 : ℝ)^57
        have hw : |(-3050809/19531250 : ℝ)|=(3050809/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072102491/5000000000 : ℝ)|^73 ≤ (32363561645941/100000000000000 : ℝ)^57
        have hw : |(-2072102491/5000000000 : ℝ)|=(2072102491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (983859867/2000000000 : ℝ)*x 0 + (1080452443/2000000000 : ℝ)*x 1 + (2183171273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (983859867/2000000000 : ℝ)^73 ≤ (20155331979327/50000000000000 : ℝ)^57 := by
    have hnat : (983859867 : ℕ)^73*50000000000000^57 ≤ 20155331979327^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983859867 2000000000 20155331979327 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080452443/2000000000 : ℝ)^73 ≤ (45447414239031/100000000000000 : ℝ)^57 := by
    have hnat : (1080452443 : ℕ)^73*100000000000000^57 ≤ 45447414239031^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080452443 2000000000 45447414239031 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183171273/10000000000 : ℝ)^73 ≤ (14241921784251/100000000000000 : ℝ)^57 := by
    have hnat : (2183171273 : ℕ)^73*100000000000000^57 ≤ 14241921784251^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183171273 10000000000 14241921784251 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(983859867/2000000000 : ℝ), (1080452443/2000000000 : ℝ), (2183171273/10000000000 : ℝ)] ![(20155331979327/50000000000000 : ℝ), (45447414239031/100000000000000 : ℝ), (14241921784251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(983859867/2000000000 : ℝ)|^73 ≤ (20155331979327/50000000000000 : ℝ)^57
        have hw : |(983859867/2000000000 : ℝ)|=(983859867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080452443/2000000000 : ℝ)|^73 ≤ (45447414239031/100000000000000 : ℝ)^57
        have hw : |(1080452443/2000000000 : ℝ)|=(1080452443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2183171273/10000000000 : ℝ)|^73 ≤ (14241921784251/100000000000000 : ℝ)^57
        have hw : |(2183171273/10000000000 : ℝ)|=(2183171273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312054_s2_s2_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6003140671/10000000000 : ℝ)*x 0 + (2374042549/5000000000 : ℝ)*x 1 + (-1585851733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6003140671/10000000000 : ℝ)^73 ≤ (13004959101639/25000000000000 : ℝ)^57 := by
    have hnat : (6003140671 : ℕ)^73*25000000000000^57 ≤ 13004959101639^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6003140671 10000000000 13004959101639 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2374042549/5000000000 : ℝ)^73 ≤ (9630673873767/25000000000000 : ℝ)^57 := by
    have hnat : (2374042549 : ℕ)^73*25000000000000^57 ≤ 9630673873767^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2374042549 5000000000 9630673873767 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1585851733/10000000000 : ℝ)^73 ≤ (9457468089123/100000000000000 : ℝ)^57 := by
    have hnat : (1585851733 : ℕ)^73*100000000000000^57 ≤ 9457468089123^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585851733 10000000000 9457468089123 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6003140671/10000000000 : ℝ), (2374042549/5000000000 : ℝ), (-1585851733/10000000000 : ℝ)] ![(13004959101639/25000000000000 : ℝ), (9630673873767/25000000000000 : ℝ), (9457468089123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6003140671/10000000000 : ℝ)|^73 ≤ (13004959101639/25000000000000 : ℝ)^57
        have hw : |(6003140671/10000000000 : ℝ)|=(6003140671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2374042549/5000000000 : ℝ)|^73 ≤ (9630673873767/25000000000000 : ℝ)^57
        have hw : |(2374042549/5000000000 : ℝ)|=(2374042549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1585851733/10000000000 : ℝ)|^73 ≤ (9457468089123/100000000000000 : ℝ)^57
        have hw : |(-1585851733/10000000000 : ℝ)|=(1585851733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312054_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((31307/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31307/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13179/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13179/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-27139/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-27139/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7773/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7773/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20387/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20387/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-27399/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-27399/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (31307/50000 : ℝ) ^ (9/2 : ℝ) ≤ (12162462664397219357/100000000000000000000 : ℝ) := by
    have hpowers : (31307/50000 : ℝ)^9 ≤ (12162462664397219357/100000000000000000000 : ℝ)^2 := by
      have hnat : (31307 : ℕ)^9*100000000000000000000^2 ≤ 12162462664397219357^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31307 50000 12162462664397219357 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31307/50000 : ℝ)) (X := (12162462664397219357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0a : (112162462664397219357/100000000000000000000 : ℝ) ≤ (10258343333908723/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (112162462664397219357/100000000000000000000 : ℝ)^2 ≤ (10258343333908723/10000000000000000 : ℝ)^9 := by
      have hnat : (112162462664397219357 : ℕ)^2*10000000000000000^9 ≤ 10258343333908723^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112162462664397219357 100000000000000000000 10258343333908723 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10258343333908723/10000000000000000 : ℝ)) (X := (112162462664397219357/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0b : (62162462664397219357/50000000000000000000 : ℝ) ≤ (10495736883890439/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (62162462664397219357/50000000000000000000 : ℝ)^2 ≤ (10495736883890439/10000000000000000 : ℝ)^9 := by
      have hnat : (62162462664397219357 : ℕ)^2*10000000000000000^9 ≤ 10495736883890439^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62162462664397219357 50000000000000000000 10495736883890439 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10495736883890439/10000000000000000 : ℝ)) (X := (62162462664397219357/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(258343333908723/6261400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(59348387495429/1565350000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (31307/50000 : ℝ)) (alpha := (258343333908723/6261400000000000 : ℝ)) (beta := (59348387495429/1565350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (31307/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(258343333908723/6261400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(59348387495429/1565350000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (13179/20000 : ℝ) ^ (9/2 : ℝ) ≤ (15305096790283739459/100000000000000000000 : ℝ) := by
    have hpowers : (13179/20000 : ℝ)^9 ≤ (15305096790283739459/100000000000000000000 : ℝ)^2 := by
      have hnat : (13179 : ℕ)^9*100000000000000000000^2 ≤ 15305096790283739459^2*20000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13179 20000 15305096790283739459 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13179/20000 : ℝ)) (X := (15305096790283739459/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1a : (115305096790283739459/100000000000000000000 : ℝ) ≤ (5160765391563041/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (115305096790283739459/100000000000000000000 : ℝ)^2 ≤ (5160765391563041/5000000000000000 : ℝ)^9 := by
      have hnat : (115305096790283739459 : ℕ)^2*5000000000000000^9 ≤ 5160765391563041^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115305096790283739459 100000000000000000000 5160765391563041 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5160765391563041/5000000000000000 : ℝ)) (X := (115305096790283739459/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1b : (65305096790283739459/50000000000000000000 : ℝ) ≤ (10611399931855307/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (65305096790283739459/50000000000000000000 : ℝ)^2 ≤ (10611399931855307/10000000000000000 : ℝ)^9 := by
      have hnat : (65305096790283739459 : ℕ)^2*10000000000000000^9 ≤ 10611399931855307^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65305096790283739459 50000000000000000000 10611399931855307 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10611399931855307/10000000000000000 : ℝ)) (X := (65305096790283739459/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(53588463854347/1098250000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(11594765949169/263580000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (13179/20000 : ℝ)) (alpha := (53588463854347/1098250000000000 : ℝ)) (beta := (11594765949169/263580000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (13179/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(53588463854347/1098250000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(11594765949169/263580000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (27139/50000 : ℝ) ^ (9/2 : ℝ) ≤ (1598627478699831513/25000000000000000000 : ℝ) := by
    have hpowers : (27139/50000 : ℝ)^9 ≤ (1598627478699831513/25000000000000000000 : ℝ)^2 := by
      have hnat : (27139 : ℕ)^9*25000000000000000000^2 ≤ 1598627478699831513^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27139 50000 1598627478699831513 25000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27139/50000 : ℝ)) (X := (1598627478699831513/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2a : (26598627478699831513/25000000000000000000 : ℝ) ≤ (405547790723313/400000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (26598627478699831513/25000000000000000000 : ℝ)^2 ≤ (405547790723313/400000000000000 : ℝ)^9 := by
      have hnat : (26598627478699831513 : ℕ)^2*400000000000000^9 ≤ 405547790723313^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26598627478699831513 25000000000000000000 405547790723313 400000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (405547790723313/400000000000000 : ℝ)) (X := (26598627478699831513/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2b : (14098627478699831513/12500000000000000000 : ℝ) ≤ (5135525071627383/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (14098627478699831513/12500000000000000000 : ℝ)^2 ≤ (5135525071627383/5000000000000000 : ℝ)^9 := by
      have hnat : (14098627478699831513 : ℕ)^2*5000000000000000^9 ≤ 5135525071627383^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14098627478699831513 12500000000000000000 5135525071627383 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5135525071627383/5000000000000000 : ℝ)) (X := (14098627478699831513/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(5547790723313/217112000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(132355375171941/5427800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (27139/50000 : ℝ)) (alpha := (5547790723313/217112000000000 : ℝ)) (beta := (132355375171941/5427800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (27139/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(5547790723313/217112000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(132355375171941/5427800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1149048469/10000000000 : ℝ)*X 0 0+(2261171329/5000000000 : ℝ)*X 0 1+(-3247813653/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5214650649/10000000000 : ℝ)*X 2 0+(1034999457/2000000000 : ℝ)*X 2 1+(1049985017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-959054557/10000000000 : ℝ)*X 0 0+(2012044427/5000000000 : ℝ)*X 0 1+(-7046160531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1048946983/2000000000 : ℝ)*X 1 0+(-655653963/5000000000 : ℝ)*X 1 1+(-1142727397/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4781069561/10000000000 : ℝ)*X 2 0+(6282540167/10000000000 : ℝ)*X 2 1+(1110692759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((247778577/500000000 : ℝ)*X 0 0+(6216843211/10000000000 : ℝ)*X 0 1+(-59361699/625000000 : ℝ)*X 0 2+(247778577/500000000 : ℝ)*X 1 0+(6216843211/10000000000 : ℝ)*X 1 1+(-59361699/625000000 : ℝ)*X 1 2+(247778577/500000000 : ℝ)*X 2 0+(6216843211/10000000000 : ℝ)*X 2 1+(-59361699/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-430624097/10000000000 : ℝ)*X 0 0+(1107100449/2500000000 : ℝ)*X 0 1+(-3485102553/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((486546161/1000000000 : ℝ)*X 1 0+(-903144289/5000000000 : ℝ)*X 1 1+(-1147322263/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((3169518603/5000000000 : ℝ)*X 2 0+(591892333/1250000000 : ℝ)*X 2 1+(217543649/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1235331767/2000000000 : ℝ)*X 0 0+(30523119/62500000 : ℝ)*X 0 1+(-281848149/2500000000 : ℝ)*X 0 2+(1235331767/2000000000 : ℝ)*X 1 0+(30523119/62500000 : ℝ)*X 1 1+(-281848149/2500000000 : ℝ)*X 1 2+(1235331767/2000000000 : ℝ)*X 2 0+(30523119/62500000 : ℝ)*X 2 1+(-281848149/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-55703083/2500000000 : ℝ)*X 0 0+(5281800983/10000000000 : ℝ)*X 0 1+(-3138592391/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((328360913/500000000 : ℝ)*X 1 0+(-3050809/19531250 : ℝ)*X 1 1+(-2072102491/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((983859867/2000000000 : ℝ)*X 2 0+(1080452443/2000000000 : ℝ)*X 2 1+(2183171273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((6003140671/10000000000 : ℝ)*X 0 0+(2374042549/5000000000 : ℝ)*X 0 1+(-1585851733/10000000000 : ℝ)*X 0 2+(6003140671/10000000000 : ℝ)*X 1 0+(2374042549/5000000000 : ℝ)*X 1 1+(-1585851733/10000000000 : ℝ)*X 1 2+(6003140671/10000000000 : ℝ)*X 2 0+(2374042549/5000000000 : ℝ)*X 2 1+(-1585851733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312054_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((7773/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7773/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (74897902569348374196811752259/14929885905956000000000000000000000 : ℝ) := by norm_num
    linear_combination (16173/20000000000 : ℝ)*(base23) + (495798798023/1000000000000 : ℝ)*(base39) + (22247/15625000000 : ℝ)*(base50) + (208686469177/500000000000 : ℝ)*(base60) + (37858753613/8000000000 : ℝ)*(major_s2_0) + (37858753613/8000000000 : ℝ)*(major_s2_1) + (37858753613/8000000000 : ℝ)*(major_s2_2) + (6629449214267/1000000000000 : ℝ)*(sp_s2_7) + (1325883197253/200000000000 : ℝ)*(sp_s2_8) + (6629446442347/1000000000000 : ℝ)*(sp_s2_9) + (2835216071621/1000000000000 : ℝ)*(sp_s2_13) + (21445143/1000000000000 : ℝ)*(sp_s2_14) + (10934629/200000000000 : ℝ)*(sp_s2_15) + (5852103/250000000000 : ℝ)*(sp_s2_23) + (2835216071621/1000000000000 : ℝ)*(f.failure) + (6629470659409/1000000000000 : ℝ)*(f.sum) + (457969936936492259/953773016000000000000000000000 : ℝ)*base62 + (310466725441213/1085560000000000000000000000 : ℝ)*base65 + (60101495396383/263580000000000000000000000 : ℝ)*base66 + (40680951696243/217112000000000000000000000 : ℝ)*base68 + (2494115827882239437/8496406730000000000000000000000 : ℝ)*base71 + (84425935711373/313070000000000000000000000 : ℝ)*base73 + (767738089243/5491250000000000000000000 : ℝ)*base75 + (165959055479059/250456000000000000000000000 : ℝ)*base77 + (50971979108461747/1650379812000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (24027/100000000000000000 : ℝ)*base86 + (24027/100000000000000000 : ℝ)*base88 + (24027/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20387/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20387/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (114559366828505813469045992313/6665127636587500000000000000000000 : ℝ) := by norm_num
    linear_combination (108592979523/250000000000 : ℝ)*(base39) + (4304881/1000000000000 : ℝ)*(base49) + (124686004991/1000000000000 : ℝ)*(base60) + (238911206681/50000000000 : ℝ)*(major_s2_0) + (238911206681/50000000000 : ℝ)*(major_s2_1) + (238911206681/50000000000 : ℝ)*(major_s2_2) + (53202653/500000000000 : ℝ)*(sp_s2_0) + (126544563/1000000000000 : ℝ)*(sp_s2_8) + (6693605482939/1000000000000 : ℝ)*(sp_s2_14) + (167340314721/25000000000 : ℝ)*(sp_s2_15) + (3346869566701/500000000000 : ℝ)*(sp_s2_16) + (143119049377/50000000000 : ℝ)*(sp_s2_20) + (27245157/1000000000000 : ℝ)*(sp_s2_21) + (322417001/1000000000000 : ℝ)*(sp_s2_27) + (143135170227/50000000000 : ℝ)*(f.failure) + (3346869566701/500000000000 : ℝ)*(f.sum) + (528435747186626419/851583050000000000000000000000 : ℝ)*base62 + (6169300854307/19385000000000000000000000 : ℝ)*base64 + (30011272086347/131790000000000000000000000 : ℝ)*base66 + (38075318828757/38770000000000000000000000 : ℝ)*base68 + (41173170909652461/151721548750000000000000000000 : ℝ)*base70 + (68036024851773/78267500000000000000000000 : ℝ)*base73 + (86324997613367/219650000000000000000000000 : ℝ)*base74 + (106207572688819/313070000000000000000000000 : ℝ)*base76 + (1053810993156379553/4125949530000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (749/5000000000000000 : ℝ)*base86 + (749/5000000000000000 : ℝ)*base88 + (749/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-27399/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-27399/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (327839815144505673886946502051/26660510546350000000000000000000000 : ℝ) := by norm_num
    linear_combination (853628374023/1000000000000 : ℝ)*(base39) + (1900857/500000000000 : ℝ)*(base40) + (2658151/1000000000000 : ℝ)*(base50) + (393551018399/100000000000 : ℝ)*(major_s2_0) + (393551018399/100000000000 : ℝ)*(major_s2_1) + (393551018399/100000000000 : ℝ)*(major_s2_2) + (3604531/1000000000000 : ℝ)*(sp_s2_0) + (38980741/1000000000000 : ℝ)*(sp_s2_2) + (38096937/1000000000000 : ℝ)*(sp_s2_9) + (48441131/200000000000 : ℝ)*(sp_s2_20) + (689148926739/125000000000 : ℝ)*(sp_s2_21) + (1378298754611/250000000000 : ℝ)*(sp_s2_22) + (2756558970383/500000000000 : ℝ)*(sp_s2_23) + (235757904493/100000000000 : ℝ)*(sp_s2_27) + (1178910625293/500000000000 : ℝ)*(f.failure) + (1378298754611/250000000000 : ℝ)*(f.sum) + (188981337728096729/1703166100000000000000000000000 : ℝ)*base63 + (53334564338201/77540000000000000000000000 : ℝ)*base65 + (20633369686739/26358000000000000000000000 : ℝ)*base66 + (3331327474039/15508000000000000000000000 : ℝ)*base69 + (15795811697136797/303443097500000000000000000000 : ℝ)*base70 + (7489712266009/9783437500000000000000000 : ℝ)*base73 + (24676671643491/219650000000000000000000000 : ℝ)*base75 + (136481663177639/626140000000000000000000000 : ℝ)*base76 + (128024998575135913/257871845625000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (30509/50000000000000000 : ℝ)*base87 + (30509/50000000000000000 : ℝ)*base89 + (30509/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((31307/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31307/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13179/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13179/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-27139/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-27139/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7773/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7773/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20387/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20387/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-27399/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-27399/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312054_s2 p hpa hpb X hX hprev1

#print axioms solution
