-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309086_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:06:53.531539+00:00
-- url     : https://prove2.me/submissions/7e6573f2-3082-463e-9614-ab0316b3c7bb

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
theorem collision_support_c309086_s1_s1_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6193145719/10000000000 : ℝ)*x 0 + (-3322550897/10000000000 : ℝ)*x 1 + (-1570896757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6193145719/10000000000 : ℝ)^35 ≤ (13433692279181/25000000000000 : ℝ)^27 := by
    have hnat : (6193145719 : ℕ)^35*25000000000000^27 ≤ 13433692279181^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6193145719 10000000000 13433692279181 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3322550897/10000000000 : ℝ)^35 ≤ (11985480973/50000000000 : ℝ)^27 := by
    have hnat : (3322550897 : ℕ)^35*50000000000^27 ≤ 11985480973^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3322550897 10000000000 11985480973 50000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1570896757/5000000000 : ℝ)^35 ≤ (22294268923297/100000000000000 : ℝ)^27 := by
    have hnat : (1570896757 : ℕ)^35*100000000000000^27 ≤ 22294268923297^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570896757 5000000000 22294268923297 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6193145719/10000000000 : ℝ), (-3322550897/10000000000 : ℝ), (-1570896757/5000000000 : ℝ)] ![(13433692279181/25000000000000 : ℝ), (11985480973/50000000000 : ℝ), (22294268923297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6193145719/10000000000 : ℝ)|^35 ≤ (13433692279181/25000000000000 : ℝ)^27
        have hw : |(6193145719/10000000000 : ℝ)|=(6193145719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3322550897/10000000000 : ℝ)|^35 ≤ (11985480973/50000000000 : ℝ)^27
        have hw : |(-3322550897/10000000000 : ℝ)|=(3322550897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1570896757/5000000000 : ℝ)|^35 ≤ (22294268923297/100000000000000 : ℝ)^27
        have hw : |(-1570896757/5000000000 : ℝ)|=(1570896757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3534942833/10000000000 : ℝ)*x 0 + (-1367352139/5000000000 : ℝ)*x 1 + (1268142431/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3534942833/10000000000 : ℝ)^35 ≤ (811745318621/3125000000000 : ℝ)^27 := by
    have hnat : (3534942833 : ℕ)^35*3125000000000^27 ≤ 811745318621^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3534942833 10000000000 811745318621 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367352139/5000000000 : ℝ)^35 ≤ (18623829977069/100000000000000 : ℝ)^27 := by
    have hnat : (1367352139 : ℕ)^35*100000000000000^27 ≤ 18623829977069^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367352139 5000000000 18623829977069 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1268142431/2000000000 : ℝ)^35 ≤ (6925039976737/12500000000000 : ℝ)^27 := by
    have hnat : (1268142431 : ℕ)^35*12500000000000^27 ≤ 6925039976737^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268142431 2000000000 6925039976737 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3534942833/10000000000 : ℝ), (-1367352139/5000000000 : ℝ), (1268142431/2000000000 : ℝ)] ![(811745318621/3125000000000 : ℝ), (18623829977069/100000000000000 : ℝ), (6925039976737/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3534942833/10000000000 : ℝ)|^35 ≤ (811745318621/3125000000000 : ℝ)^27
        have hw : |(3534942833/10000000000 : ℝ)|=(3534942833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1367352139/5000000000 : ℝ)|^35 ≤ (18623829977069/100000000000000 : ℝ)^27
        have hw : |(-1367352139/5000000000 : ℝ)|=(1367352139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1268142431/2000000000 : ℝ)|^35 ≤ (6925039976737/12500000000000 : ℝ)^27
        have hw : |(1268142431/2000000000 : ℝ)|=(1268142431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (860639/625000000 : ℝ)*x 0 + (-4126045359/5000000000 : ℝ)*x 1 + (3112563139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860639/625000000 : ℝ)^35 ≤ (19553289091/100000000000000 : ℝ)^27 := by
    have hnat : (860639 : ℕ)^35*100000000000000^27 ≤ 19553289091^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860639 625000000 19553289091 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4126045359/5000000000 : ℝ)^35 ≤ (19488670937609/25000000000000 : ℝ)^27 := by
    have hnat : (4126045359 : ℕ)^35*25000000000000^27 ≤ 19488670937609^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126045359 5000000000 19488670937609 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3112563139/10000000000 : ℝ)^35 ≤ (881030518367/4000000000000 : ℝ)^27 := by
    have hnat : (3112563139 : ℕ)^35*4000000000000^27 ≤ 881030518367^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3112563139 10000000000 881030518367 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860639/625000000 : ℝ), (-4126045359/5000000000 : ℝ), (3112563139/10000000000 : ℝ)] ![(19553289091/100000000000000 : ℝ), (19488670937609/25000000000000 : ℝ), (881030518367/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860639/625000000 : ℝ)|^35 ≤ (19553289091/100000000000000 : ℝ)^27
        have hw : |(860639/625000000 : ℝ)|=(860639/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4126045359/5000000000 : ℝ)|^35 ≤ (19488670937609/25000000000000 : ℝ)^27
        have hw : |(-4126045359/5000000000 : ℝ)|=(4126045359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3112563139/10000000000 : ℝ)|^35 ≤ (881030518367/4000000000000 : ℝ)^27
        have hw : |(3112563139/10000000000 : ℝ)|=(3112563139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1146191233/2500000000 : ℝ)*x 0 + (5544152053/10000000000 : ℝ)*x 1 + (1277883057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1146191233/2500000000 : ℝ)^35 ≤ (36388703049303/100000000000000 : ℝ)^27 := by
    have hnat : (1146191233 : ℕ)^35*100000000000000^27 ≤ 36388703049303^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146191233 2500000000 36388703049303 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5544152053/10000000000 : ℝ)^35 ≤ (23275790285717/50000000000000 : ℝ)^27 := by
    have hnat : (5544152053 : ℕ)^35*50000000000000^27 ≤ 23275790285717^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5544152053 10000000000 23275790285717 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1277883057/5000000000 : ℝ)^35 ≤ (17059716363019/100000000000000 : ℝ)^27 := by
    have hnat : (1277883057 : ℕ)^35*100000000000000^27 ≤ 17059716363019^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277883057 5000000000 17059716363019 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1146191233/2500000000 : ℝ), (5544152053/10000000000 : ℝ), (1277883057/5000000000 : ℝ)] ![(36388703049303/100000000000000 : ℝ), (23275790285717/50000000000000 : ℝ), (17059716363019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1146191233/2500000000 : ℝ)|^35 ≤ (36388703049303/100000000000000 : ℝ)^27
        have hw : |(1146191233/2500000000 : ℝ)|=(1146191233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5544152053/10000000000 : ℝ)|^35 ≤ (23275790285717/50000000000000 : ℝ)^27
        have hw : |(5544152053/10000000000 : ℝ)|=(5544152053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1277883057/5000000000 : ℝ)|^35 ≤ (17059716363019/100000000000000 : ℝ)^27
        have hw : |(1277883057/5000000000 : ℝ)|=(1277883057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3577317773/5000000000 : ℝ)*x 0 + (-2351535559/10000000000 : ℝ)*x 1 + (-1438911303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3577317773/5000000000 : ℝ)^35 ≤ (16197289482133/25000000000000 : ℝ)^27 := by
    have hnat : (3577317773 : ℕ)^35*25000000000000^27 ≤ 16197289482133^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3577317773 5000000000 16197289482133 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2351535559/10000000000 : ℝ)^35 ≤ (7656941823649/50000000000000 : ℝ)^27 := by
    have hnat : (2351535559 : ℕ)^35*50000000000000^27 ≤ 7656941823649^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351535559 10000000000 7656941823649 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1438911303/5000000000 : ℝ)^35 ≤ (497423960393/2500000000000 : ℝ)^27 := by
    have hnat : (1438911303 : ℕ)^35*2500000000000^27 ≤ 497423960393^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1438911303 5000000000 497423960393 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3577317773/5000000000 : ℝ), (-2351535559/10000000000 : ℝ), (-1438911303/5000000000 : ℝ)] ![(16197289482133/25000000000000 : ℝ), (7656941823649/50000000000000 : ℝ), (497423960393/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3577317773/5000000000 : ℝ)|^35 ≤ (16197289482133/25000000000000 : ℝ)^27
        have hw : |(3577317773/5000000000 : ℝ)|=(3577317773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2351535559/10000000000 : ℝ)|^35 ≤ (7656941823649/50000000000000 : ℝ)^27
        have hw : |(-2351535559/10000000000 : ℝ)|=(2351535559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1438911303/5000000000 : ℝ)|^35 ≤ (497423960393/2500000000000 : ℝ)^27
        have hw : |(-1438911303/5000000000 : ℝ)|=(1438911303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (319821871/1000000000 : ℝ)*x 0 + (-1030056027/10000000000 : ℝ)*x 1 + (7755842443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (319821871/1000000000 : ℝ)^35 ≤ (22814674709309/100000000000000 : ℝ)^27 := by
    have hnat : (319821871 : ℕ)^35*100000000000000^27 ≤ 22814674709309^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319821871 1000000000 22814674709309 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030056027/10000000000 : ℝ)^35 ≤ (5252610201089/100000000000000 : ℝ)^27 := by
    have hnat : (1030056027 : ℕ)^35*100000000000000^27 ≤ 5252610201089^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030056027 10000000000 5252610201089 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7755842443/10000000000 : ℝ)^35 ≤ (35966357539127/50000000000000 : ℝ)^27 := by
    have hnat : (7755842443 : ℕ)^35*50000000000000^27 ≤ 35966357539127^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7755842443 10000000000 35966357539127 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(319821871/1000000000 : ℝ), (-1030056027/10000000000 : ℝ), (7755842443/10000000000 : ℝ)] ![(22814674709309/100000000000000 : ℝ), (5252610201089/100000000000000 : ℝ), (35966357539127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(319821871/1000000000 : ℝ)|^35 ≤ (22814674709309/100000000000000 : ℝ)^27
        have hw : |(319821871/1000000000 : ℝ)|=(319821871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030056027/10000000000 : ℝ)|^35 ≤ (5252610201089/100000000000000 : ℝ)^27
        have hw : |(-1030056027/10000000000 : ℝ)|=(1030056027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7755842443/10000000000 : ℝ)|^35 ≤ (35966357539127/50000000000000 : ℝ)^27
        have hw : |(7755842443/10000000000 : ℝ)|=(7755842443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-202093/1250000000 : ℝ)*x 0 + (-424744603/1000000000 : ℝ)*x 1 + (1469161589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202093/1250000000 : ℝ)^35 ≤ (608479161/50000000000000 : ℝ)^27 := by
    have hnat : (202093 : ℕ)^35*50000000000000^27 ≤ 608479161^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202093 1250000000 608479161 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424744603/1000000000 : ℝ)^35 ≤ (8239171499663/25000000000000 : ℝ)^27 := by
    have hnat : (424744603 : ℕ)^35*25000000000000^27 ≤ 8239171499663^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424744603 1000000000 8239171499663 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1469161589/2000000000 : ℝ)^35 ≤ (4190131063937/6250000000000 : ℝ)^27 := by
    have hnat : (1469161589 : ℕ)^35*6250000000000^27 ≤ 4190131063937^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469161589 2000000000 4190131063937 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202093/1250000000 : ℝ), (-424744603/1000000000 : ℝ), (1469161589/2000000000 : ℝ)] ![(608479161/50000000000000 : ℝ), (8239171499663/25000000000000 : ℝ), (4190131063937/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202093/1250000000 : ℝ)|^35 ≤ (608479161/50000000000000 : ℝ)^27
        have hw : |(-202093/1250000000 : ℝ)|=(202093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424744603/1000000000 : ℝ)|^35 ≤ (8239171499663/25000000000000 : ℝ)^27
        have hw : |(-424744603/1000000000 : ℝ)|=(424744603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1469161589/2000000000 : ℝ)|^35 ≤ (4190131063937/6250000000000 : ℝ)^27
        have hw : |(1469161589/2000000000 : ℝ)|=(1469161589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8630524019/10000000000 : ℝ)*x 0 + (938952953/5000000000 : ℝ)*x 1 + (226482191/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8630524019/10000000000 : ℝ)^35 ≤ (41310002278861/50000000000000 : ℝ)^27 := by
    have hnat : (8630524019 : ℕ)^35*50000000000000^27 ≤ 41310002278861^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8630524019 10000000000 41310002278861 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (938952953/5000000000 : ℝ)^35 ≤ (11441054992151/100000000000000 : ℝ)^27 := by
    have hnat : (938952953 : ℕ)^35*100000000000000^27 ≤ 11441054992151^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938952953 5000000000 11441054992151 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226482191/2000000000 : ℝ)^35 ≤ (371183777081/6250000000000 : ℝ)^27 := by
    have hnat : (226482191 : ℕ)^35*6250000000000^27 ≤ 371183777081^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226482191 2000000000 371183777081 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8630524019/10000000000 : ℝ), (938952953/5000000000 : ℝ), (226482191/2000000000 : ℝ)] ![(41310002278861/50000000000000 : ℝ), (11441054992151/100000000000000 : ℝ), (371183777081/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8630524019/10000000000 : ℝ)|^35 ≤ (41310002278861/50000000000000 : ℝ)^27
        have hw : |(8630524019/10000000000 : ℝ)|=(8630524019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(938952953/5000000000 : ℝ)|^35 ≤ (11441054992151/100000000000000 : ℝ)^27
        have hw : |(938952953/5000000000 : ℝ)|=(938952953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226482191/2000000000 : ℝ)|^35 ≤ (371183777081/6250000000000 : ℝ)^27
        have hw : |(226482191/2000000000 : ℝ)|=(226482191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8152898633/10000000000 : ℝ)*x 0 + (-2350537819/10000000000 : ℝ)*x 1 + (-1418440701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8152898633/10000000000 : ℝ)^35 ≤ (76742179545511/100000000000000 : ℝ)^27 := by
    have hnat : (8152898633 : ℕ)^35*100000000000000^27 ≤ 76742179545511^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8152898633 10000000000 76742179545511 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2350537819/10000000000 : ℝ)^35 ≤ (3826365349201/25000000000000 : ℝ)^27 := by
    have hnat : (2350537819 : ℕ)^35*25000000000000^27 ≤ 3826365349201^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2350537819 10000000000 3826365349201 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1418440701/10000000000 : ℝ)^35 ≤ (1590471808619/20000000000000 : ℝ)^27 := by
    have hnat : (1418440701 : ℕ)^35*20000000000000^27 ≤ 1590471808619^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1418440701 10000000000 1590471808619 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8152898633/10000000000 : ℝ), (-2350537819/10000000000 : ℝ), (-1418440701/10000000000 : ℝ)] ![(76742179545511/100000000000000 : ℝ), (3826365349201/25000000000000 : ℝ), (1590471808619/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8152898633/10000000000 : ℝ)|^35 ≤ (76742179545511/100000000000000 : ℝ)^27
        have hw : |(8152898633/10000000000 : ℝ)|=(8152898633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2350537819/10000000000 : ℝ)|^35 ≤ (3826365349201/25000000000000 : ℝ)^27
        have hw : |(-2350537819/10000000000 : ℝ)|=(2350537819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1418440701/10000000000 : ℝ)|^35 ≤ (1590471808619/20000000000000 : ℝ)^27
        have hw : |(-1418440701/10000000000 : ℝ)|=(1418440701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (537642243/2500000000 : ℝ)*x 0 + (-718464461/5000000000 : ℝ)*x 1 + (4139066541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537642243/2500000000 : ℝ)^35 ≤ (13639278986467/100000000000000 : ℝ)^27 := by
    have hnat : (537642243 : ℕ)^35*100000000000000^27 ≤ 13639278986467^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537642243 2500000000 13639278986467 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (718464461/5000000000 : ℝ)^35 ≤ (8086982105123/100000000000000 : ℝ)^27 := by
    have hnat : (718464461 : ℕ)^35*100000000000000^27 ≤ 8086982105123^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718464461 5000000000 8086982105123 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4139066541/5000000000 : ℝ)^35 ≤ (78273738897443/100000000000000 : ℝ)^27 := by
    have hnat : (4139066541 : ℕ)^35*100000000000000^27 ≤ 78273738897443^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139066541 5000000000 78273738897443 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537642243/2500000000 : ℝ), (-718464461/5000000000 : ℝ), (4139066541/5000000000 : ℝ)] ![(13639278986467/100000000000000 : ℝ), (8086982105123/100000000000000 : ℝ), (78273738897443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537642243/2500000000 : ℝ)|^35 ≤ (13639278986467/100000000000000 : ℝ)^27
        have hw : |(537642243/2500000000 : ℝ)|=(537642243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-718464461/5000000000 : ℝ)|^35 ≤ (8086982105123/100000000000000 : ℝ)^27
        have hw : |(-718464461/5000000000 : ℝ)|=(718464461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4139066541/5000000000 : ℝ)|^35 ≤ (78273738897443/100000000000000 : ℝ)^27
        have hw : |(4139066541/5000000000 : ℝ)|=(4139066541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (20104011/10000000000 : ℝ)*x 0 + (-8275998571/10000000000 : ℝ)*x 1 + (769807731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20104011/10000000000 : ℝ)^35 ≤ (31934150593/100000000000000 : ℝ)^27 := by
    have hnat : (20104011 : ℕ)^35*100000000000000^27 ≤ 31934150593^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20104011 10000000000 31934150593 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8275998571/10000000000 : ℝ)^35 ≤ (19561894242131/25000000000000 : ℝ)^27 := by
    have hnat : (8275998571 : ℕ)^35*25000000000000^27 ≤ 19561894242131^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8275998571 10000000000 19561894242131 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (769807731/2500000000 : ℝ)^35 ≤ (10860244434521/50000000000000 : ℝ)^27 := by
    have hnat : (769807731 : ℕ)^35*50000000000000^27 ≤ 10860244434521^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769807731 2500000000 10860244434521 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20104011/10000000000 : ℝ), (-8275998571/10000000000 : ℝ), (769807731/2500000000 : ℝ)] ![(31934150593/100000000000000 : ℝ), (19561894242131/25000000000000 : ℝ), (10860244434521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20104011/10000000000 : ℝ)|^35 ≤ (31934150593/100000000000000 : ℝ)^27
        have hw : |(20104011/10000000000 : ℝ)|=(20104011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8275998571/10000000000 : ℝ)|^35 ≤ (19561894242131/25000000000000 : ℝ)^27
        have hw : |(-8275998571/10000000000 : ℝ)|=(8275998571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(769807731/2500000000 : ℝ)|^35 ≤ (10860244434521/50000000000000 : ℝ)^27
        have hw : |(769807731/2500000000 : ℝ)|=(769807731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1050096867/1250000000 : ℝ)*x 0 + (450677101/2500000000 : ℝ)*x 1 + (160966351/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050096867/1250000000 : ℝ)^35 ≤ (4986266319431/6250000000000 : ℝ)^27 := by
    have hnat : (1050096867 : ℕ)^35*6250000000000^27 ≤ 4986266319431^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050096867 1250000000 4986266319431 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450677101/2500000000 : ℝ)^35 ≤ (10850730072493/100000000000000 : ℝ)^27 := by
    have hnat : (450677101 : ℕ)^35*100000000000000^27 ≤ 10850730072493^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450677101 2500000000 10850730072493 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160966351/1000000000 : ℝ)^35 ≤ (4684504399801/50000000000000 : ℝ)^27 := by
    have hnat : (160966351 : ℕ)^35*50000000000000^27 ≤ 4684504399801^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160966351 1000000000 4684504399801 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050096867/1250000000 : ℝ), (450677101/2500000000 : ℝ), (160966351/1000000000 : ℝ)] ![(4986266319431/6250000000000 : ℝ), (10850730072493/100000000000000 : ℝ), (4684504399801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050096867/1250000000 : ℝ)|^35 ≤ (4986266319431/6250000000000 : ℝ)^27
        have hw : |(1050096867/1250000000 : ℝ)|=(1050096867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450677101/2500000000 : ℝ)|^35 ≤ (10850730072493/100000000000000 : ℝ)^27
        have hw : |(450677101/2500000000 : ℝ)|=(450677101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160966351/1000000000 : ℝ)|^35 ≤ (4684504399801/50000000000000 : ℝ)^27
        have hw : |(160966351/1000000000 : ℝ)|=(160966351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4142514409/10000000000 : ℝ)*x 0 + (-4893986663/10000000000 : ℝ)*x 1 + (-237276247/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4142514409/10000000000 : ℝ)^35 ≤ (31905148963469/100000000000000 : ℝ)^27 := by
    have hnat : (4142514409 : ℕ)^35*100000000000000^27 ≤ 31905148963469^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142514409 10000000000 31905148963469 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4893986663/10000000000 : ℝ)^35 ≤ (39601443179897/100000000000000 : ℝ)^27 := by
    have hnat : (4893986663 : ℕ)^35*100000000000000^27 ≤ 39601443179897^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4893986663 10000000000 39601443179897 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237276247/625000000 : ℝ)^35 ≤ (1139736313763/4000000000000 : ℝ)^27 := by
    have hnat : (237276247 : ℕ)^35*4000000000000^27 ≤ 1139736313763^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237276247 625000000 1139736313763 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4142514409/10000000000 : ℝ), (-4893986663/10000000000 : ℝ), (-237276247/625000000 : ℝ)] ![(31905148963469/100000000000000 : ℝ), (39601443179897/100000000000000 : ℝ), (1139736313763/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4142514409/10000000000 : ℝ)|^35 ≤ (31905148963469/100000000000000 : ℝ)^27
        have hw : |(4142514409/10000000000 : ℝ)|=(4142514409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4893986663/10000000000 : ℝ)|^35 ≤ (39601443179897/100000000000000 : ℝ)^27
        have hw : |(-4893986663/10000000000 : ℝ)|=(4893986663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-237276247/625000000 : ℝ)|^35 ≤ (1139736313763/4000000000000 : ℝ)^27
        have hw : |(-237276247/625000000 : ℝ)|=(237276247/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s1_s1_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3483320391/5000000000 : ℝ)*x 0 + (-9681559/80000000 : ℝ)*x 1 + (505637277/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3483320391/5000000000 : ℝ)^35 ≤ (3911937028249/6250000000000 : ℝ)^27 := by
    have hnat : (3483320391 : ℕ)^35*6250000000000^27 ≤ 3911937028249^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3483320391 5000000000 3911937028249 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9681559/80000000 : ℝ)^35 ≤ (3236523306633/50000000000000 : ℝ)^27 := by
    have hnat : (9681559 : ℕ)^35*50000000000000^27 ≤ 3236523306633^27*80000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9681559 80000000 3236523306633 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505637277/1250000000 : ℝ)^35 ≤ (15467980457409/50000000000000 : ℝ)^27 := by
    have hnat : (505637277 : ℕ)^35*50000000000000^27 ≤ 15467980457409^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505637277 1250000000 15467980457409 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3483320391/5000000000 : ℝ), (-9681559/80000000 : ℝ), (505637277/1250000000 : ℝ)] ![(3911937028249/6250000000000 : ℝ), (3236523306633/50000000000000 : ℝ), (15467980457409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3483320391/5000000000 : ℝ)|^35 ≤ (3911937028249/6250000000000 : ℝ)^27
        have hw : |(3483320391/5000000000 : ℝ)|=(3483320391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9681559/80000000 : ℝ)|^35 ≤ (3236523306633/50000000000000 : ℝ)^27
        have hw : |(-9681559/80000000 : ℝ)|=(9681559/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(505637277/1250000000 : ℝ)|^35 ≤ (15467980457409/50000000000000 : ℝ)^27
        have hw : |(505637277/1250000000 : ℝ)|=(505637277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309086_s1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((84249/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84249/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-45671/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-45671/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(90557/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(90557/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((63741/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63741/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-15951/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-15951/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39463/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39463/50000 : ℝ)*X 1 2) := by
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
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s1_pow0 : (84249/100000 : ℝ) ^ (69/16 : ℝ) ≤ (46633503865283367/97656250000000000 : ℝ) := by
    have hpowers : (84249/100000 : ℝ)^69 ≤ (46633503865283367/97656250000000000 : ℝ)^16 := by
      have hnat : (84249 : ℕ)^69*97656250000000000^16 ≤ 46633503865283367^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84249 100000 46633503865283367 97656250000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (84249/100000 : ℝ)) (X := (46633503865283367/97656250000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (144289753865283367/97656250000000000 : ℝ) ≤ (1094743985672597/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (144289753865283367/97656250000000000 : ℝ)^16 ≤ (1094743985672597/1000000000000000 : ℝ)^69 := by
      have hnat : (144289753865283367 : ℕ)^16*1000000000000000^69 ≤ 1094743985672597^69*97656250000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        144289753865283367 97656250000000000 1094743985672597 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1094743985672597/1000000000000000 : ℝ)) (X := (144289753865283367/97656250000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (95461628865283367/48828125000000000 : ℝ) ≤ (2920485746899689/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (95461628865283367/48828125000000000 : ℝ)^16 ≤ (2920485746899689/2500000000000000 : ℝ)^69 := by
      have hnat : (95461628865283367 : ℕ)^16*2500000000000000^69 ≤ 2920485746899689^69*48828125000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        95461628865283367 48828125000000000 2920485746899689 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2920485746899689/2500000000000000 : ℝ)) (X := (95461628865283367/48828125000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(94743985672597/842490000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(33386505948763/382950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (84249/100000 : ℝ)) (alpha := (94743985672597/842490000000000 : ℝ)) (beta := (33386505948763/382950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (84249/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(94743985672597/842490000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(33386505948763/382950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (45671/50000 : ℝ) ^ (69/16 : ℝ) ≤ (3383464366864194717/5000000000000000000 : ℝ) := by
    have hpowers : (45671/50000 : ℝ)^69 ≤ (3383464366864194717/5000000000000000000 : ℝ)^16 := by
      have hnat : (45671 : ℕ)^69*5000000000000000000^16 ≤ 3383464366864194717^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45671 50000 3383464366864194717 5000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45671/50000 : ℝ)) (X := (3383464366864194717/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (8383464366864194717/5000000000000000000 : ℝ) ≤ (11273199499115357/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (8383464366864194717/5000000000000000000 : ℝ)^16 ≤ (11273199499115357/10000000000000000 : ℝ)^69 := by
      have hnat : (8383464366864194717 : ℕ)^16*10000000000000000^69 ≤ 11273199499115357^69*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8383464366864194717 5000000000000000000 11273199499115357 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11273199499115357/10000000000000000 : ℝ)) (X := (8383464366864194717/5000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5883464366864194717/2500000000000000000 : ℝ) ≤ (12195221948322933/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (5883464366864194717/2500000000000000000 : ℝ)^16 ≤ (12195221948322933/10000000000000000 : ℝ)^69 := by
      have hnat : (5883464366864194717 : ℕ)^16*10000000000000000^69 ≤ 12195221948322933^69*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5883464366864194717 2500000000000000000 12195221948322933 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12195221948322933/10000000000000000 : ℝ)) (X := (5883464366864194717/2500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1273199499115357/9134200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(115252806150947/1141775000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (45671/50000 : ℝ)) (alpha := (1273199499115357/9134200000000000 : ℝ)) (beta := (115252806150947/1141775000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (45671/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1273199499115357/9134200000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(115252806150947/1141775000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (90557/100000 : ℝ) ^ (69/16 : ℝ) ≤ (3259839697893075991/5000000000000000000 : ℝ) := by
    have hpowers : (90557/100000 : ℝ)^69 ≤ (3259839697893075991/5000000000000000000 : ℝ)^16 := by
      have hnat : (90557 : ℕ)^69*5000000000000000000^16 ≤ 3259839697893075991^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90557 100000 3259839697893075991 5000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (90557/100000 : ℝ)) (X := (3259839697893075991/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (8259839697893075991/5000000000000000000 : ℝ) ≤ (2808607865118567/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (8259839697893075991/5000000000000000000 : ℝ)^16 ≤ (2808607865118567/2500000000000000 : ℝ)^69 := by
      have hnat : (8259839697893075991 : ℕ)^16*2500000000000000^69 ≤ 2808607865118567^69*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8259839697893075991 5000000000000000000 2808607865118567 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2808607865118567/2500000000000000 : ℝ)) (X := (8259839697893075991/5000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5759839697893075991/2500000000000000000 : ℝ) ≤ (2427063282520791/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (5759839697893075991/2500000000000000000 : ℝ)^16 ≤ (2427063282520791/2000000000000000 : ℝ)^69 := by
      have hnat : (5759839697893075991 : ℕ)^16*2000000000000000^69 ≤ 2427063282520791^69*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5759839697893075991 2500000000000000000 2427063282520791 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2427063282520791/2000000000000000 : ℝ)) (X := (5759839697893075991/2500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(308607865118567/2263925000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(900884952129687/9055700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (90557/100000 : ℝ)) (alpha := (308607865118567/2263925000000000 : ℝ)) (beta := (900884952129687/9055700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (90557/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(308607865118567/2263925000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(900884952129687/9055700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_2 : ((6193145719/10000000000 : ℝ)*X 2 0+(-3322550897/10000000000 : ℝ)*X 2 1+(-1570896757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3534942833/10000000000 : ℝ)*X 0 0+(-1367352139/5000000000 : ℝ)*X 0 1+(1268142431/2000000000 : ℝ)*X 0 2+(3534942833/10000000000 : ℝ)*X 1 0+(-1367352139/5000000000 : ℝ)*X 1 1+(1268142431/2000000000 : ℝ)*X 1 2+(3534942833/10000000000 : ℝ)*X 2 0+(-1367352139/5000000000 : ℝ)*X 2 1+(1268142431/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((860639/625000000 : ℝ)*X 0 0+(-4126045359/5000000000 : ℝ)*X 0 1+(3112563139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1146191233/2500000000 : ℝ)*X 1 0+(5544152053/10000000000 : ℝ)*X 1 1+(1277883057/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3577317773/5000000000 : ℝ)*X 2 0+(-2351535559/10000000000 : ℝ)*X 2 1+(-1438911303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((319821871/1000000000 : ℝ)*X 0 0+(-1030056027/10000000000 : ℝ)*X 0 1+(7755842443/10000000000 : ℝ)*X 0 2+(319821871/1000000000 : ℝ)*X 1 0+(-1030056027/10000000000 : ℝ)*X 1 1+(7755842443/10000000000 : ℝ)*X 1 2+(319821871/1000000000 : ℝ)*X 2 0+(-1030056027/10000000000 : ℝ)*X 2 1+(7755842443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-202093/1250000000 : ℝ)*X 0 0+(-424744603/1000000000 : ℝ)*X 0 1+(1469161589/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((8630524019/10000000000 : ℝ)*X 1 0+(938952953/5000000000 : ℝ)*X 1 1+(226482191/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((8152898633/10000000000 : ℝ)*X 2 0+(-2350537819/10000000000 : ℝ)*X 2 1+(-1418440701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((537642243/2500000000 : ℝ)*X 0 0+(-718464461/5000000000 : ℝ)*X 0 1+(4139066541/5000000000 : ℝ)*X 0 2+(537642243/2500000000 : ℝ)*X 1 0+(-718464461/5000000000 : ℝ)*X 1 1+(4139066541/5000000000 : ℝ)*X 1 2+(537642243/2500000000 : ℝ)*X 2 0+(-718464461/5000000000 : ℝ)*X 2 1+(4139066541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((20104011/10000000000 : ℝ)*X 0 0+(-8275998571/10000000000 : ℝ)*X 0 1+(769807731/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1050096867/1250000000 : ℝ)*X 1 0+(450677101/2500000000 : ℝ)*X 1 1+(160966351/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4142514409/10000000000 : ℝ)*X 2 0+(-4893986663/10000000000 : ℝ)*X 2 1+(-237276247/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3483320391/5000000000 : ℝ)*X 0 0+(-9681559/80000000 : ℝ)*X 0 1+(505637277/1250000000 : ℝ)*X 0 2+(3483320391/5000000000 : ℝ)*X 1 0+(-9681559/80000000 : ℝ)*X 1 1+(505637277/1250000000 : ℝ)*X 1 2+(3483320391/5000000000 : ℝ)*X 2 0+(-9681559/80000000 : ℝ)*X 2 1+(505637277/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((63741/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63741/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (30245536919082322579472281520779/3871549290066700000000000000000000000 : ℝ) := by norm_num
    linear_combination (61986559027/125000000000 : ℝ)*(base7) + (9550802289/62500000000 : ℝ)*(base43) + (609767343683/1000000000000 : ℝ)*(base54) + (1780786650023/1000000000000 : ℝ)*(major_s1_0) + (1627973813399/1000000000000 : ℝ)*(major_s1_1) + (58550965317/50000000000 : ℝ)*(major_s1_2) + (134798549/1000000000000 : ℝ)*(sp_s1_2) + (13114841/500000000000 : ℝ)*(sp_s1_6) + (994008856599/500000000000 : ℝ)*(sp_s1_7) + (133837937487/62500000000 : ℝ)*(sp_s1_8) + (172336502617/125000000000 : ℝ)*(sp_s1_9) + (251079789631/250000000000 : ℝ)*(sp_s1_13) + (6836311/200000000000 : ℝ)*(sp_s1_20) + (57644997/100000000000 : ℝ)*(sp_s1_21) + (279563610307/250000000000 : ℝ)*(f.failure) + (133837937487/62500000000 : ℝ)*(f.sum) + (19221148977689870711/103395718675000000000000000000000 : ℝ)*base63 + (179894647578871/452785000000000000000000000 : ℝ)*base64 + (3237411309761763/9134200000000000000000000000 : ℝ)*base67 + (167086472501081/452785000000000000000000000 : ℝ)*base69 + (2411848183752258521/76293366930000000000000000000000 : ℝ)*base70 + (142718623407749/382950000000000000000000000 : ℝ)*base73 + (653353074499191/2283550000000000000000000000 : ℝ)*base75 + (6640585498853/16849800000000000000000000 : ℝ)*base76 + (18157374169817671453/69958837800000000000000000000000 : ℝ)*base79 + (16171/25000000000000000 : ℝ)*base86 + (16171/25000000000000000 : ℝ)*base88 + (16171/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-15951/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-15951/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (53697424144881238927839885613/7039180527394000000000000000000000 : ℝ) := by norm_num
    linear_combination (912513787161/1000000000000 : ℝ)*(base7) + (3081989/500000000000 : ℝ)*(base33) + (126009/100000000000 : ℝ)*(base40) + (24156584599/1000000000000 : ℝ)*(base60) + (336171719937/200000000000 : ℝ)*(major_s1_0) + (840432381831/500000000000 : ℝ)*(major_s1_1) + (840432381831/500000000000 : ℝ)*(major_s1_2) + (5300411/500000000000 : ℝ)*(sp_s1_9) + (2193047/1000000000000 : ℝ)*(sp_s1_13) + (350132475799/200000000000 : ℝ)*(sp_s1_14) + (1750570127631/1000000000000 : ℝ)*(sp_s1_15) + (350129122839/200000000000 : ℝ)*(sp_s1_16) + (492004888937/250000000000 : ℝ)*(sp_s1_20) + (43043693/500000000000 : ℝ)*(sp_s1_22) + (1055507961633/1000000000000 : ℝ)*(f.failure) + (350132475799/200000000000 : ℝ)*(f.sum) + (80794062978754135023/103395718675000000000000000000000 : ℝ)*base62 + (506915977043239/2263925000000000000000000000 : ℝ)*base65 + (6079966388860053/4567100000000000000000000000 : ℝ)*base66 + (1911158516715427/4527850000000000000000000000 : ℝ)*base68 + (34108584956197320451/127155611550000000000000000000000 : ℝ)*base70 + (27407038134989/25530000000000000000000000 : ℝ)*base72 + (161227837022913/2283550000000000000000000000 : ℝ)*base75 + (176547926285939/280830000000000000000000000 : ℝ)*base77 + (8136539855028795379/11659806300000000000000000000000 : ℝ)*base78 + (129649/100000000000000000 : ℝ)*base86 + (29649/100000000000000000 : ℝ)*base88 + (29649/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39463/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39463/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11488662400300414292748178409171/1935774645033350000000000000000000000 : ℝ) := by norm_num
    linear_combination (808778304091/1000000000000 : ℝ)*(base7) + (11007990107/100000000000 : ℝ)*(base40) + (578656680201/1000000000000 : ℝ)*(base43) + (527089/500000000000 : ℝ)*(base50) + (1873603562351/1000000000000 : ℝ)*(major_s1_0) + (25898937643/20000000000 : ℝ)*(major_s1_1) + (1873603562351/1000000000000 : ℝ)*(major_s1_2) + (10755257/1000000000000 : ℝ)*(sp_s1_2) + (3189721/40000000000 : ℝ)*(sp_s1_7) + (48870867/1000000000000 : ℝ)*(sp_s1_15) + (1499529001449/1000000000000 : ℝ)*(sp_s1_21) + (2078216553807/1000000000000 : ℝ)*(sp_s1_22) + (1499597989217/1000000000000 : ℝ)*(sp_s1_23) + (1985317618709/1000000000000 : ℝ)*(sp_s1_27) + (1176539314619/1000000000000 : ℝ)*(f.failure) + (83130616987/40000000000 : ℝ)*(f.sum) + (95214638817210090419/206791437350000000000000000000000 : ℝ)*base63 + (342676055502857/9055700000000000000000000000 : ℝ)*base64 + (4094376910107/182684000000000000000000000 : ℝ)*base66 + (4740813064049579/4527850000000000000000000000 : ℝ)*base69 + (79135820471269545473/762933669300000000000000000000000 : ℝ)*base70 + (14608611807413/23934375000000000000000000 : ℝ)*base73 + (133486982211433/228355000000000000000000000 : ℝ)*base75 + (102695192827739/421245000000000000000000000 : ℝ)*base76 + (4431425140498637591/34979418900000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (31893/100000000000000000 : ℝ)*base87 + (31893/100000000000000000 : ℝ)*base89 + (31893/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((84249/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84249/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-45671/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-45671/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(90557/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(90557/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((63741/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63741/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-15951/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-15951/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39463/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39463/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309086_s1 p hpa hpb X hX hprev0

#print axioms solution
