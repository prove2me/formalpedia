-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306076_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:59:41.365479+00:00
-- url     : https://prove2.me/submissions/aef77566-7453-47d2-9194-56f7b16076d5

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
theorem collision_support_c306076_s1_s1_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-343321829/2500000000 : ℝ)*x 0 + (-3220682583/5000000000 : ℝ)*x 1 + (2312754339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343321829/2500000000 : ℝ)^135 ≤ (7411079263301/100000000000000 : ℝ)^103 := by
    have hnat : (343321829 : ℕ)^135*100000000000000^103 ≤ 7411079263301^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343321829 2500000000 7411079263301 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3220682583/5000000000 : ℝ)^135 ≤ (5618640622869/10000000000000 : ℝ)^103 := by
    have hnat : (3220682583 : ℕ)^135*10000000000000^103 ≤ 5618640622869^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3220682583 5000000000 5618640622869 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2312754339/5000000000 : ℝ)^135 ≤ (9100628626431/25000000000000 : ℝ)^103 := by
    have hnat : (2312754339 : ℕ)^135*25000000000000^103 ≤ 9100628626431^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312754339 5000000000 9100628626431 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-343321829/2500000000 : ℝ), (-3220682583/5000000000 : ℝ), (2312754339/5000000000 : ℝ)] ![(7411079263301/100000000000000 : ℝ), (5618640622869/10000000000000 : ℝ), (9100628626431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-343321829/2500000000 : ℝ)|^135 ≤ (7411079263301/100000000000000 : ℝ)^103
        have hw : |(-343321829/2500000000 : ℝ)|=(343321829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3220682583/5000000000 : ℝ)|^135 ≤ (5618640622869/10000000000000 : ℝ)^103
        have hw : |(-3220682583/5000000000 : ℝ)|=(3220682583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2312754339/5000000000 : ℝ)|^135 ≤ (9100628626431/25000000000000 : ℝ)^103
        have hw : |(2312754339/5000000000 : ℝ)|=(2312754339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2378499893/5000000000 : ℝ)*x 0 + (-985605573/2000000000 : ℝ)*x 1 + (-3223990333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2378499893/5000000000 : ℝ)^135 ≤ (18882396763487/50000000000000 : ℝ)^103 := by
    have hnat : (2378499893 : ℕ)^135*50000000000000^103 ≤ 18882396763487^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2378499893 5000000000 18882396763487 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (985605573/2000000000 : ℝ)^135 ≤ (791084664453/2000000000000 : ℝ)^103 := by
    have hnat : (985605573 : ℕ)^135*2000000000000^103 ≤ 791084664453^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985605573 2000000000 791084664453 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3223990333/10000000000 : ℝ)^135 ≤ (22680973238573/100000000000000 : ℝ)^103 := by
    have hnat : (3223990333 : ℕ)^135*100000000000000^103 ≤ 22680973238573^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3223990333 10000000000 22680973238573 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2378499893/5000000000 : ℝ), (-985605573/2000000000 : ℝ), (-3223990333/10000000000 : ℝ)] ![(18882396763487/50000000000000 : ℝ), (791084664453/2000000000000 : ℝ), (22680973238573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2378499893/5000000000 : ℝ)|^135 ≤ (18882396763487/50000000000000 : ℝ)^103
        have hw : |(2378499893/5000000000 : ℝ)|=(2378499893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-985605573/2000000000 : ℝ)|^135 ≤ (791084664453/2000000000000 : ℝ)^103
        have hw : |(-985605573/2000000000 : ℝ)|=(985605573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3223990333/10000000000 : ℝ)|^135 ≤ (22680973238573/100000000000000 : ℝ)^103
        have hw : |(-3223990333/10000000000 : ℝ)|=(3223990333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070789603/10000000000 : ℝ)*x 0 + (-7732088787/10000000000 : ℝ)*x 1 + (657503999/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070789603/10000000000 : ℝ)^135 ≤ (5348758707239/100000000000000 : ℝ)^103 := by
    have hnat : (1070789603 : ℕ)^135*100000000000000^103 ≤ 5348758707239^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070789603 10000000000 5348758707239 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7732088787/10000000000 : ℝ)^135 ≤ (71382694214629/100000000000000 : ℝ)^103 := by
    have hnat : (7732088787 : ℕ)^135*100000000000000^103 ≤ 71382694214629^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7732088787 10000000000 71382694214629 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657503999/2000000000 : ℝ)^135 ≤ (23268547068187/100000000000000 : ℝ)^103 := by
    have hnat : (657503999 : ℕ)^135*100000000000000^103 ≤ 23268547068187^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657503999 2000000000 23268547068187 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070789603/10000000000 : ℝ), (-7732088787/10000000000 : ℝ), (657503999/2000000000 : ℝ)] ![(5348758707239/100000000000000 : ℝ), (71382694214629/100000000000000 : ℝ), (23268547068187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070789603/10000000000 : ℝ)|^135 ≤ (5348758707239/100000000000000 : ℝ)^103
        have hw : |(-1070789603/10000000000 : ℝ)|=(1070789603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7732088787/10000000000 : ℝ)|^135 ≤ (71382694214629/100000000000000 : ℝ)^103
        have hw : |(-7732088787/10000000000 : ℝ)|=(7732088787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657503999/2000000000 : ℝ)|^135 ≤ (23268547068187/100000000000000 : ℝ)^103
        have hw : |(657503999/2000000000 : ℝ)|=(657503999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2565215869/5000000000 : ℝ)*x 0 + (154207663/312500000 : ℝ)*x 1 + (1390088749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2565215869/5000000000 : ℝ)^135 ≤ (5212123011909/12500000000000 : ℝ)^103 := by
    have hnat : (2565215869 : ℕ)^135*12500000000000^103 ≤ 5212123011909^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565215869 5000000000 5212123011909 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154207663/312500000 : ℝ)^135 ≤ (39623862370851/100000000000000 : ℝ)^103 := by
    have hnat : (154207663 : ℕ)^135*100000000000000^103 ≤ 39623862370851^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154207663 312500000 39623862370851 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1390088749/5000000000 : ℝ)^135 ≤ (18679153524277/100000000000000 : ℝ)^103 := by
    have hnat : (1390088749 : ℕ)^135*100000000000000^103 ≤ 18679153524277^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390088749 5000000000 18679153524277 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2565215869/5000000000 : ℝ), (154207663/312500000 : ℝ), (1390088749/5000000000 : ℝ)] ![(5212123011909/12500000000000 : ℝ), (39623862370851/100000000000000 : ℝ), (18679153524277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2565215869/5000000000 : ℝ)|^135 ≤ (5212123011909/12500000000000 : ℝ)^103
        have hw : |(2565215869/5000000000 : ℝ)|=(2565215869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(154207663/312500000 : ℝ)|^135 ≤ (39623862370851/100000000000000 : ℝ)^103
        have hw : |(154207663/312500000 : ℝ)|=(154207663/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1390088749/5000000000 : ℝ)|^135 ≤ (18679153524277/100000000000000 : ℝ)^103
        have hw : |(1390088749/5000000000 : ℝ)|=(1390088749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5883471567/10000000000 : ℝ)*x 0 + (-2789077453/5000000000 : ℝ)*x 1 + (-157467399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5883471567/10000000000 : ℝ)^135 ≤ (49895747539119/100000000000000 : ℝ)^103 := by
    have hnat : (5883471567 : ℕ)^135*100000000000000^103 ≤ 49895747539119^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5883471567 10000000000 49895747539119 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2789077453/5000000000 : ℝ)^135 ≤ (46529711460491/100000000000000 : ℝ)^103 := by
    have hnat : (2789077453 : ℕ)^135*100000000000000^103 ≤ 46529711460491^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2789077453 5000000000 46529711460491 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157467399/2000000000 : ℝ)^135 ≤ (3574540979851/100000000000000 : ℝ)^103 := by
    have hnat : (157467399 : ℕ)^135*100000000000000^103 ≤ 3574540979851^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157467399 2000000000 3574540979851 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5883471567/10000000000 : ℝ), (-2789077453/5000000000 : ℝ), (-157467399/2000000000 : ℝ)] ![(49895747539119/100000000000000 : ℝ), (46529711460491/100000000000000 : ℝ), (3574540979851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5883471567/10000000000 : ℝ)|^135 ≤ (49895747539119/100000000000000 : ℝ)^103
        have hw : |(5883471567/10000000000 : ℝ)|=(5883471567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2789077453/5000000000 : ℝ)|^135 ≤ (46529711460491/100000000000000 : ℝ)^103
        have hw : |(-2789077453/5000000000 : ℝ)|=(2789077453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-157467399/2000000000 : ℝ)|^135 ≤ (3574540979851/100000000000000 : ℝ)^103
        have hw : |(-157467399/2000000000 : ℝ)|=(157467399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3099080397/10000000000 : ℝ)*x 0 + (57348179/5000000000 : ℝ)*x 1 + (1657508167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3099080397/10000000000 : ℝ)^135 ≤ (861448365867/4000000000000 : ℝ)^103 := by
    have hnat : (3099080397 : ℕ)^135*4000000000000^103 ≤ 861448365867^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3099080397 10000000000 861448365867 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57348179/5000000000 : ℝ)^135 ≤ (143107127361/50000000000000 : ℝ)^103 := by
    have hnat : (57348179 : ℕ)^135*50000000000000^103 ≤ 143107127361^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57348179 5000000000 143107127361 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1657508167/2000000000 : ℝ)^135 ≤ (19544394145321/25000000000000 : ℝ)^103 := by
    have hnat : (1657508167 : ℕ)^135*25000000000000^103 ≤ 19544394145321^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1657508167 2000000000 19544394145321 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3099080397/10000000000 : ℝ), (57348179/5000000000 : ℝ), (1657508167/2000000000 : ℝ)] ![(861448365867/4000000000000 : ℝ), (143107127361/50000000000000 : ℝ), (19544394145321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3099080397/10000000000 : ℝ)|^135 ≤ (861448365867/4000000000000 : ℝ)^103
        have hw : |(3099080397/10000000000 : ℝ)|=(3099080397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57348179/5000000000 : ℝ)|^135 ≤ (143107127361/50000000000000 : ℝ)^103
        have hw : |(57348179/5000000000 : ℝ)|=(57348179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1657508167/2000000000 : ℝ)|^135 ≤ (19544394145321/25000000000000 : ℝ)^103
        have hw : |(1657508167/2000000000 : ℝ)|=(1657508167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-320271921/2500000000 : ℝ)*x 0 + (-3887917651/10000000000 : ℝ)*x 1 + (7134826207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (320271921/2500000000 : ℝ)^135 ≤ (6765841219967/100000000000000 : ℝ)^103 := by
    have hnat : (320271921 : ℕ)^135*100000000000000^103 ≤ 6765841219967^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320271921 2500000000 6765841219967 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3887917651/10000000000 : ℝ)^135 ≤ (14495076668989/50000000000000 : ℝ)^103 := by
    have hnat : (3887917651 : ℕ)^135*50000000000000^103 ≤ 14495076668989^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3887917651 10000000000 14495076668989 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7134826207/10000000000 : ℝ)^135 ≤ (64244005432931/100000000000000 : ℝ)^103 := by
    have hnat : (7134826207 : ℕ)^135*100000000000000^103 ≤ 64244005432931^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7134826207 10000000000 64244005432931 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-320271921/2500000000 : ℝ), (-3887917651/10000000000 : ℝ), (7134826207/10000000000 : ℝ)] ![(6765841219967/100000000000000 : ℝ), (14495076668989/50000000000000 : ℝ), (64244005432931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-320271921/2500000000 : ℝ)|^135 ≤ (6765841219967/100000000000000 : ℝ)^103
        have hw : |(-320271921/2500000000 : ℝ)|=(320271921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3887917651/10000000000 : ℝ)|^135 ≤ (14495076668989/50000000000000 : ℝ)^103
        have hw : |(-3887917651/10000000000 : ℝ)|=(3887917651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7134826207/10000000000 : ℝ)|^135 ≤ (64244005432931/100000000000000 : ℝ)^103
        have hw : |(7134826207/10000000000 : ℝ)|=(7134826207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7721499151/10000000000 : ℝ)*x 0 + (130658241/500000000 : ℝ)*x 1 + (1923141129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7721499151/10000000000 : ℝ)^135 ≤ (71254584741591/100000000000000 : ℝ)^103 := by
    have hnat : (7721499151 : ℕ)^135*100000000000000^103 ≤ 71254584741591^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7721499151 10000000000 71254584741591 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130658241/500000000 : ℝ)^135 ≤ (8611175011167/50000000000000 : ℝ)^103 := by
    have hnat : (130658241 : ℕ)^135*50000000000000^103 ≤ 8611175011167^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130658241 500000000 8611175011167 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1923141129/10000000000 : ℝ)^135 ≤ (11523065218771/100000000000000 : ℝ)^103 := by
    have hnat : (1923141129 : ℕ)^135*100000000000000^103 ≤ 11523065218771^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923141129 10000000000 11523065218771 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7721499151/10000000000 : ℝ), (130658241/500000000 : ℝ), (1923141129/10000000000 : ℝ)] ![(71254584741591/100000000000000 : ℝ), (8611175011167/50000000000000 : ℝ), (11523065218771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7721499151/10000000000 : ℝ)|^135 ≤ (71254584741591/100000000000000 : ℝ)^103
        have hw : |(7721499151/10000000000 : ℝ)|=(7721499151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130658241/500000000 : ℝ)|^135 ≤ (8611175011167/50000000000000 : ℝ)^103
        have hw : |(130658241/500000000 : ℝ)|=(130658241/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1923141129/10000000000 : ℝ)|^135 ≤ (11523065218771/100000000000000 : ℝ)^103
        have hw : |(1923141129/10000000000 : ℝ)|=(1923141129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (131516609/312500000 : ℝ)*x 0 + (-3307573199/5000000000 : ℝ)*x 1 + (-1680443729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131516609/312500000 : ℝ)^135 ≤ (4020366344471/12500000000000 : ℝ)^103 := by
    have hnat : (131516609 : ℕ)^135*12500000000000^103 ≤ 4020366344471^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131516609 312500000 4020366344471 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3307573199/5000000000 : ℝ)^135 ≤ (7272684405361/12500000000000 : ℝ)^103 := by
    have hnat : (3307573199 : ℕ)^135*12500000000000^103 ≤ 7272684405361^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3307573199 5000000000 7272684405361 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1680443729/10000000000 : ℝ)^135 ≤ (4827796992459/50000000000000 : ℝ)^103 := by
    have hnat : (1680443729 : ℕ)^135*50000000000000^103 ≤ 4827796992459^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680443729 10000000000 4827796992459 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131516609/312500000 : ℝ), (-3307573199/5000000000 : ℝ), (-1680443729/10000000000 : ℝ)] ![(4020366344471/12500000000000 : ℝ), (7272684405361/12500000000000 : ℝ), (4827796992459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131516609/312500000 : ℝ)|^135 ≤ (4020366344471/12500000000000 : ℝ)^103
        have hw : |(131516609/312500000 : ℝ)|=(131516609/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3307573199/5000000000 : ℝ)|^135 ≤ (7272684405361/12500000000000 : ℝ)^103
        have hw : |(-3307573199/5000000000 : ℝ)|=(3307573199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1680443729/10000000000 : ℝ)|^135 ≤ (4827796992459/50000000000000 : ℝ)^103
        have hw : |(-1680443729/10000000000 : ℝ)|=(1680443729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (985101769/5000000000 : ℝ)*x 0 + (0 : ℝ)*x 1 + (9079062403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (985101769/5000000000 : ℝ)^135 ≤ (92922333157/781250000000 : ℝ)^103 := by
    have hnat : (985101769 : ℕ)^135*781250000000^103 ≤ 92922333157^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985101769 5000000000 92922333157 781250000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^135 ≤ (0 : ℝ)^103 := by
    have hnat : (0 : ℕ)^135*1^103 ≤ 0^103*1^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9079062403/10000000000 : ℝ)^135 ≤ (44052970673519/50000000000000 : ℝ)^103 := by
    have hnat : (9079062403 : ℕ)^135*50000000000000^103 ≤ 44052970673519^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9079062403 10000000000 44052970673519 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(985101769/5000000000 : ℝ), (0 : ℝ), (9079062403/10000000000 : ℝ)] ![(92922333157/781250000000 : ℝ), (0 : ℝ), (44052970673519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(985101769/5000000000 : ℝ)|^135 ≤ (92922333157/781250000000 : ℝ)^103
        have hw : |(985101769/5000000000 : ℝ)|=(985101769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^135 ≤ (0 : ℝ)^103
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9079062403/10000000000 : ℝ)|^135 ≤ (44052970673519/50000000000000 : ℝ)^103
        have hw : |(9079062403/10000000000 : ℝ)|=(9079062403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-21471173/500000000 : ℝ)*x 0 + (-7920845889/10000000000 : ℝ)*x 1 + (860441499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21471173/500000000 : ℝ)^135 ≤ (807460436421/50000000000000 : ℝ)^103 := by
    have hnat : (21471173 : ℕ)^135*50000000000000^103 ≤ 807460436421^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21471173 500000000 807460436421 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7920845889/10000000000 : ℝ)^135 ≤ (4604706666871/6250000000000 : ℝ)^103 := by
    have hnat : (7920845889 : ℕ)^135*6250000000000^103 ≤ 4604706666871^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7920845889 10000000000 4604706666871 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (860441499/2500000000 : ℝ)^135 ≤ (24709772446323/100000000000000 : ℝ)^103 := by
    have hnat : (860441499 : ℕ)^135*100000000000000^103 ≤ 24709772446323^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860441499 2500000000 24709772446323 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21471173/500000000 : ℝ), (-7920845889/10000000000 : ℝ), (860441499/2500000000 : ℝ)] ![(807460436421/50000000000000 : ℝ), (4604706666871/6250000000000 : ℝ), (24709772446323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21471173/500000000 : ℝ)|^135 ≤ (807460436421/50000000000000 : ℝ)^103
        have hw : |(-21471173/500000000 : ℝ)|=(21471173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7920845889/10000000000 : ℝ)|^135 ≤ (4604706666871/6250000000000 : ℝ)^103
        have hw : |(-7920845889/10000000000 : ℝ)|=(7920845889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(860441499/2500000000 : ℝ)|^135 ≤ (24709772446323/100000000000000 : ℝ)^103
        have hw : |(860441499/2500000000 : ℝ)|=(860441499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1571424093/2000000000 : ℝ)*x 0 + (151464933/625000000 : ℝ)*x 1 + (1919992569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1571424093/2000000000 : ℝ)^135 ≤ (728993891499/1000000000000 : ℝ)^103 := by
    have hnat : (1571424093 : ℕ)^135*1000000000000^103 ≤ 728993891499^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1571424093 2000000000 728993891499 1000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151464933/625000000 : ℝ)^135 ≤ (1950283247723/12500000000000 : ℝ)^103 := by
    have hnat : (151464933 : ℕ)^135*12500000000000^103 ≤ 1950283247723^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151464933 625000000 1950283247723 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1919992569/10000000000 : ℝ)^135 ≤ (2874586213493/25000000000000 : ℝ)^103 := by
    have hnat : (1919992569 : ℕ)^135*25000000000000^103 ≤ 2874586213493^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919992569 10000000000 2874586213493 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1571424093/2000000000 : ℝ), (151464933/625000000 : ℝ), (1919992569/10000000000 : ℝ)] ![(728993891499/1000000000000 : ℝ), (1950283247723/12500000000000 : ℝ), (2874586213493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1571424093/2000000000 : ℝ)|^135 ≤ (728993891499/1000000000000 : ℝ)^103
        have hw : |(1571424093/2000000000 : ℝ)|=(1571424093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(151464933/625000000 : ℝ)|^135 ≤ (1950283247723/12500000000000 : ℝ)^103
        have hw : |(151464933/625000000 : ℝ)|=(151464933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1919992569/10000000000 : ℝ)|^135 ≤ (2874586213493/25000000000000 : ℝ)^103
        have hw : |(1919992569/10000000000 : ℝ)|=(1919992569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (413576049/1250000000 : ℝ)*x 0 + (-70041447/100000000 : ℝ)*x 1 + (-2210378917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413576049/1250000000 : ℝ)^135 ≤ (586609355189/2500000000000 : ℝ)^103 := by
    have hnat : (413576049 : ℕ)^135*2500000000000^103 ≤ 586609355189^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413576049 1250000000 586609355189 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70041447/100000000 : ℝ)^135 ≤ (12541228793107/20000000000000 : ℝ)^103 := by
    have hnat : (70041447 : ℕ)^135*20000000000000^103 ≤ 12541228793107^103*100000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70041447 100000000 12541228793107 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210378917/10000000000 : ℝ)^135 ≤ (2765896363517/20000000000000 : ℝ)^103 := by
    have hnat : (2210378917 : ℕ)^135*20000000000000^103 ≤ 2765896363517^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210378917 10000000000 2765896363517 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(413576049/1250000000 : ℝ), (-70041447/100000000 : ℝ), (-2210378917/10000000000 : ℝ)] ![(586609355189/2500000000000 : ℝ), (12541228793107/20000000000000 : ℝ), (2765896363517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(413576049/1250000000 : ℝ)|^135 ≤ (586609355189/2500000000000 : ℝ)^103
        have hw : |(413576049/1250000000 : ℝ)|=(413576049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70041447/100000000 : ℝ)|^135 ≤ (12541228793107/20000000000000 : ℝ)^103
        have hw : |(-70041447/100000000 : ℝ)|=(70041447/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2210378917/10000000000 : ℝ)|^135 ≤ (2765896363517/20000000000000 : ℝ)^103
        have hw : |(-2210378917/10000000000 : ℝ)|=(2210378917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306076_s1_s1_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6582449101/10000000000 : ℝ)*x 0 + (2885587/10000000000 : ℝ)*x 1 + (5176917599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6582449101/10000000000 : ℝ)^135 ≤ (28902420544351/50000000000000 : ℝ)^103 := by
    have hnat : (6582449101 : ℕ)^135*50000000000000^103 ≤ 28902420544351^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6582449101 10000000000 28902420544351 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2885587/10000000000 : ℝ)^135 ≤ (2293512441/100000000000000 : ℝ)^103 := by
    have hnat : (2885587 : ℕ)^135*100000000000000^103 ≤ 2293512441^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2885587 10000000000 2293512441 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176917599/10000000000 : ℝ)^135 ≤ (5274108174119/12500000000000 : ℝ)^103 := by
    have hnat : (5176917599 : ℕ)^135*12500000000000^103 ≤ 5274108174119^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176917599 10000000000 5274108174119 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6582449101/10000000000 : ℝ), (2885587/10000000000 : ℝ), (5176917599/10000000000 : ℝ)] ![(28902420544351/50000000000000 : ℝ), (2293512441/100000000000000 : ℝ), (5274108174119/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6582449101/10000000000 : ℝ)|^135 ≤ (28902420544351/50000000000000 : ℝ)^103
        have hw : |(6582449101/10000000000 : ℝ)|=(6582449101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2885587/10000000000 : ℝ)|^135 ≤ (2293512441/100000000000000 : ℝ)^103
        have hw : |(2885587/10000000000 : ℝ)|=(2885587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176917599/10000000000 : ℝ)|^135 ≤ (5274108174119/12500000000000 : ℝ)^103
        have hw : |(5176917599/10000000000 : ℝ)|=(5176917599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306076_s1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((88261/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(88261/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-91481/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-91481/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11877/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11877/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((73703/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73703/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-39129/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-39129/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8267/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8267/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s1_pow0 : (88261/100000 : ℝ) ^ (67/16 : ℝ) ≤ (2963992069949943579/5000000000000000000 : ℝ) := by
    have hpowers : (88261/100000 : ℝ)^67 ≤ (2963992069949943579/5000000000000000000 : ℝ)^16 := by
      have hnat : (88261 : ℕ)^67*5000000000000000000^16 ≤ 2963992069949943579^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88261 100000 2963992069949943579 5000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88261/100000 : ℝ)) (X := (2963992069949943579/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (7963992069949943579/5000000000000000000 : ℝ) ≤ (11175763673155213/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (7963992069949943579/5000000000000000000 : ℝ)^16 ≤ (11175763673155213/10000000000000000 : ℝ)^67 := by
      have hnat : (7963992069949943579 : ℕ)^16*10000000000000000^67 ≤ 11175763673155213^67*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7963992069949943579 5000000000000000000 11175763673155213 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11175763673155213/10000000000000000 : ℝ)) (X := (7963992069949943579/5000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5463992069949943579/2500000000000000000 : ℝ) ≤ (12052894512973979/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (5463992069949943579/2500000000000000000 : ℝ)^16 ≤ (12052894512973979/10000000000000000 : ℝ)^67 := by
      have hnat : (5463992069949943579 : ℕ)^16*10000000000000000^67 ≤ 12052894512973979^67*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5463992069949943579 2500000000000000000 12052894512973979 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12052894512973979/10000000000000000 : ℝ)) (X := (5463992069949943579/2500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1175763673155213/8826100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(438565419909383/4413050000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (88261/100000 : ℝ)) (alpha := (1175763673155213/8826100000000000 : ℝ)) (beta := (438565419909383/4413050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (88261/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1175763673155213/8826100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(438565419909383/4413050000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (91481/100000 : ℝ) ^ (67/16 : ℝ) ≤ (1377536621747590009/2000000000000000000 : ℝ) := by
    have hpowers : (91481/100000 : ℝ)^67 ≤ (1377536621747590009/2000000000000000000 : ℝ)^16 := by
      have hnat : (91481 : ℕ)^67*2000000000000000000^16 ≤ 1377536621747590009^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91481 100000 1377536621747590009 2000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91481/100000 : ℝ)) (X := (1377536621747590009/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (3377536621747590009/2000000000000000000 : ℝ) ≤ (2833251323116869/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3377536621747590009/2000000000000000000 : ℝ)^16 ≤ (2833251323116869/2500000000000000 : ℝ)^67 := by
      have hnat : (3377536621747590009 : ℕ)^16*2500000000000000^67 ≤ 2833251323116869^67*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3377536621747590009 2000000000000000000 2833251323116869 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2833251323116869/2500000000000000 : ℝ)) (X := (3377536621747590009/2000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (2377536621747590009/1000000000000000000 : ℝ) ≤ (12297630064582197/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2377536621747590009/1000000000000000000 : ℝ)^16 ≤ (12297630064582197/10000000000000000 : ℝ)^67 := by
      have hnat : (2377536621747590009 : ℕ)^16*10000000000000000^67 ≤ 12297630064582197^67*1000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2377536621747590009 1000000000000000000 12297630064582197 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12297630064582197/10000000000000000 : ℝ)) (X := (2377536621747590009/1000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(333251323116869/2287025000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(964624772114721/9148100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (91481/100000 : ℝ)) (alpha := (333251323116869/2287025000000000 : ℝ)) (beta := (964624772114721/9148100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (91481/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(333251323116869/2287025000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(964624772114721/9148100000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (11877/12500 : ℝ) ^ (67/16 : ℝ) ≤ (2018198466878941191/2500000000000000000 : ℝ) := by
    have hpowers : (11877/12500 : ℝ)^67 ≤ (2018198466878941191/2500000000000000000 : ℝ)^16 := by
      have hnat : (11877 : ℕ)^67*2500000000000000000^16 ≤ 2018198466878941191^16*12500^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11877 12500 2018198466878941191 2500000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11877/12500 : ℝ)) (X := (2018198466878941191/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (4518198466878941191/2500000000000000000 : ℝ) ≤ (11518055715257057/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (4518198466878941191/2500000000000000000 : ℝ)^16 ≤ (11518055715257057/10000000000000000 : ℝ)^67 := by
      have hnat : (4518198466878941191 : ℕ)^16*10000000000000000^67 ≤ 11518055715257057^67*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4518198466878941191 2500000000000000000 11518055715257057 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11518055715257057/10000000000000000 : ℝ)) (X := (4518198466878941191/2500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (3268198466878941191/1250000000000000000 : ℝ) ≤ (6289950624900689/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3268198466878941191/1250000000000000000 : ℝ)^16 ≤ (6289950624900689/5000000000000000 : ℝ)^67 := by
      have hnat : (3268198466878941191 : ℕ)^16*5000000000000000^67 ≤ 6289950624900689^67*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3268198466878941191 1250000000000000000 6289950624900689 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6289950624900689/5000000000000000 : ℝ)) (X := (3268198466878941191/1250000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1518055715257057/9501600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1061845534544321/9501600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (11877/12500 : ℝ)) (alpha := (1518055715257057/9501600000000000 : ℝ)) (beta := (1061845534544321/9501600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (11877/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1518055715257057/9501600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1061845534544321/9501600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-343321829/2500000000 : ℝ)*X 0 0+(-3220682583/5000000000 : ℝ)*X 0 1+(2312754339/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2378499893/5000000000 : ℝ)*X 2 0+(-985605573/2000000000 : ℝ)*X 2 1+(-3223990333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1070789603/10000000000 : ℝ)*X 0 0+(-7732088787/10000000000 : ℝ)*X 0 1+(657503999/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2565215869/5000000000 : ℝ)*X 1 0+(154207663/312500000 : ℝ)*X 1 1+(1390088749/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5883471567/10000000000 : ℝ)*X 2 0+(-2789077453/5000000000 : ℝ)*X 2 1+(-157467399/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3099080397/10000000000 : ℝ)*X 0 0+(57348179/5000000000 : ℝ)*X 0 1+(1657508167/2000000000 : ℝ)*X 0 2+(3099080397/10000000000 : ℝ)*X 1 0+(57348179/5000000000 : ℝ)*X 1 1+(1657508167/2000000000 : ℝ)*X 1 2+(3099080397/10000000000 : ℝ)*X 2 0+(57348179/5000000000 : ℝ)*X 2 1+(1657508167/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-320271921/2500000000 : ℝ)*X 0 0+(-3887917651/10000000000 : ℝ)*X 0 1+(7134826207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7721499151/10000000000 : ℝ)*X 1 0+(130658241/500000000 : ℝ)*X 1 1+(1923141129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((131516609/312500000 : ℝ)*X 2 0+(-3307573199/5000000000 : ℝ)*X 2 1+(-1680443729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((985101769/5000000000 : ℝ)*X 0 0+(9079062403/10000000000 : ℝ)*X 0 2+(985101769/5000000000 : ℝ)*X 1 0+(9079062403/10000000000 : ℝ)*X 1 2+(985101769/5000000000 : ℝ)*X 2 0+(9079062403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-21471173/500000000 : ℝ)*X 0 0+(-7920845889/10000000000 : ℝ)*X 0 1+(860441499/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1571424093/2000000000 : ℝ)*X 1 0+(151464933/625000000 : ℝ)*X 1 1+(1919992569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((413576049/1250000000 : ℝ)*X 2 0+(-70041447/100000000 : ℝ)*X 2 1+(-2210378917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((6582449101/10000000000 : ℝ)*X 0 0+(2885587/10000000000 : ℝ)*X 0 1+(5176917599/10000000000 : ℝ)*X 0 2+(6582449101/10000000000 : ℝ)*X 1 0+(2885587/10000000000 : ℝ)*X 1 1+(5176917599/10000000000 : ℝ)*X 1 2+(6582449101/10000000000 : ℝ)*X 2 0+(2885587/10000000000 : ℝ)*X 2 1+(5176917599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306076_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((73703/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73703/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4720262362328874478895990018823/491781165812600000000000000000000000 : ℝ) := by norm_num
    linear_combination (127224646919/1000000000000 : ℝ)*(base3) + (98793590301/200000000000 : ℝ)*(base7) + (1809737/1000000000000 : ℝ)*(base40) + (1005371032359/1000000000000 : ℝ)*(base54) + (2290222305501/1000000000000 : ℝ)*(major_s1_0) + (2290222305501/1000000000000 : ℝ)*(major_s1_1) + (642425636571/500000000000 : ℝ)*(major_s1_2) + (9649/7812500000 : ℝ)*(sp_s1_0) + (1394413297469/500000000000 : ℝ)*(sp_s1_7) + (2916052476929/1000000000000 : ℝ)*(sp_s1_8) + (1783439345409/1000000000000 : ℝ)*(sp_s1_9) + (846735493659/1000000000000 : ℝ)*(sp_s1_13) + (8726121/500000000000 : ℝ)*(sp_s1_16) + (54773/500000000000 : ℝ)*(sp_s1_20) + (1485363330977/1000000000000 : ℝ)*(f.failure) + (278882783001/100000000000 : ℝ)*(f.sum) + (886819467533860399/11143793200000000000000000000000 : ℝ)*base62 + (735049858825943/1583600000000000000000000000 : ℝ)*base64 + (82714799180461/351850000000000000000000000 : ℝ)*base67 + (513792064979569/1583600000000000000000000000 : ℝ)*base69 + (1130261875100833567/5590804784000000000000000000000 : ℝ)*base70 + (1025255263123829/2206525000000000000000000000 : ℝ)*base73 + (289392389243083/703700000000000000000000000 : ℝ)*base75 + (6226694522399007/8826100000000000000000000000 : ℝ)*base76 + (7431586879756176207/31054632850000000000000000000000 : ℝ)*base79 + (40139/50000000000000000 : ℝ)*base86 + (40139/50000000000000000 : ℝ)*base88 + (40139/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-39129/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-39129/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1633574659322672113995402219/403710227050000000000000000000000 : ℝ) := by norm_num
    linear_combination (1779071/500000000000 : ℝ)*(base3) + (125598475837/200000000000 : ℝ)*(base7) + (693990254113/1000000000000 : ℝ)*(base33) + (1543381/500000000000 : ℝ)*(base40) + (31076272561/1000000000000 : ℝ)*(base54) + (20723232559/20000000000 : ℝ)*(major_s1_0) + (1730151882063/1000000000000 : ℝ)*(major_s1_1) + (849537804751/500000000000 : ℝ)*(major_s1_2) + (63979823/1000000000000 : ℝ)*(sp_s1_9) + (2137327/200000000000 : ℝ)*(sp_s1_13) + (1948839739723/1000000000000 : ℝ)*(sp_s1_14) + (1254853043751/1000000000000 : ℝ)*(sp_s1_15) + (611854616613/500000000000 : ℝ)*(sp_s1_16) + (1719021822197/1000000000000 : ℝ)*(sp_s1_20) + (1122119960349/1000000000000 : ℝ)*(f.failure) + (1948839739723/1000000000000 : ℝ)*(f.sum) + (58716454345181146237/434607934800000000000000000000000 : ℝ)*base62 + (117812556178489/4750800000000000000000000000 : ℝ)*base64 + (3668245327659691/4574050000000000000000000000 : ℝ)*base66 + (1718106295329247/4750800000000000000000000000 : ℝ)*base69 + (35364303198211645331/419310358800000000000000000000000 : ℝ)*base71 + (27329079194089/35304400000000000000000000 : ℝ)*base72 + (2566549803302477/9148100000000000000000000000 : ℝ)*base75 + (15663987561151/882610000000000000000000000 : ℝ)*base77 + (151812201757330483001/403710227050000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (35457/50000000000000000 : ℝ)*base87 + (35457/50000000000000000 : ℝ)*base89 + (35457/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8267/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8267/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3980792077488143993253/1103262500000000000000000000 : ℝ) := by norm_num
    linear_combination (132998631447/250000000000 : ℝ)*(base3) + (220079604419/250000000000 : ℝ)*(base7) + (96648029293/500000000000 : ℝ)*(base40) + (2375642498007/1000000000000 : ℝ)*(major_s1_0) + (2375642498007/1000000000000 : ℝ)*(major_s1_1) + (2375642498007/1000000000000 : ℝ)*(major_s1_2) + (120447/62500000000 : ℝ)*(sp_s1_0) + (155177/500000000000 : ℝ)*(sp_s1_2) + (8903487/1000000000000 : ℝ)*(sp_s1_15) + (14830877/1000000000000 : ℝ)*(sp_s1_16) + (106589519107/40000000000 : ℝ)*(sp_s1_21) + (399590690891/125000000000 : ℝ)*(sp_s1_22) + (666181190899/250000000000 : ℝ)*(sp_s1_23) + (1889087967749/1000000000000 : ℝ)*(sp_s1_27) + (1540764075861/1000000000000 : ℝ)*(f.failure) + (2664739904827/1000000000000 : ℝ)*(f.sum) + (43435262348461309949/289738623200000000000000000000000 : ℝ)*base63 + (760787391510429/3167200000000000000000000000 : ℝ)*base65 + (427954299036669/4574050000000000000000000000 : ℝ)*base66 + (174509666249187/3167200000000000000000000000 : ℝ)*base68 + (100652135209144784599/279540239200000000000000000000000 : ℝ)*base70 + (1280794748945351/4413050000000000000000000000 : ℝ)*base73 + (554507424980857/9148100000000000000000000000 : ℝ)*base74 + (807304899209779/8826100000000000000000000000 : ℝ)*base76 + (169308686430978903567/403710227050000000000000000000000 : ℝ)*base79 + (2073/50000000000000000 : ℝ)*base87 + (2073/50000000000000000 : ℝ)*base89 + (2073/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((88261/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(88261/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-91481/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-91481/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11877/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11877/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((73703/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73703/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-39129/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-39129/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8267/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8267/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306076_s1 p hpa hpb X hX hprev0

#print axioms solution
