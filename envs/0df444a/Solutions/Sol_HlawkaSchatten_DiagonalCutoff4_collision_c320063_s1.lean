-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c320063_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:37:17.581901+00:00
-- url     : https://prove2.me/submissions/e6967662-3717-483f-8bc7-2a8df59c6b83

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
theorem collision_support_c320063_s1_s1_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-866877957/10000000000 : ℝ)*x 0 + (5470925497/10000000000 : ℝ)*x 1 + (5557301467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866877957/10000000000 : ℝ)^81 ≤ (4748235239721/100000000000000 : ℝ)^65 := by
    have hnat : (866877957 : ℕ)^81*100000000000000^65 ≤ 4748235239721^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866877957 10000000000 4748235239721 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470925497/10000000000 : ℝ)^81 ≤ (23580524646427/50000000000000 : ℝ)^65 := by
    have hnat : (5470925497 : ℕ)^81*50000000000000^65 ≤ 23580524646427^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470925497 10000000000 23580524646427 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5557301467/10000000000 : ℝ)^81 ≤ (48090715457397/100000000000000 : ℝ)^65 := by
    have hnat : (5557301467 : ℕ)^81*100000000000000^65 ≤ 48090715457397^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5557301467 10000000000 48090715457397 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-866877957/10000000000 : ℝ), (5470925497/10000000000 : ℝ), (5557301467/10000000000 : ℝ)] ![(4748235239721/100000000000000 : ℝ), (23580524646427/50000000000000 : ℝ), (48090715457397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-866877957/10000000000 : ℝ)|^81 ≤ (4748235239721/100000000000000 : ℝ)^65
        have hw : |(-866877957/10000000000 : ℝ)|=(866877957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470925497/10000000000 : ℝ)|^81 ≤ (23580524646427/50000000000000 : ℝ)^65
        have hw : |(5470925497/10000000000 : ℝ)|=(5470925497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5557301467/10000000000 : ℝ)|^81 ≤ (48090715457397/100000000000000 : ℝ)^65
        have hw : |(5557301467/10000000000 : ℝ)|=(5557301467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (547064043/1000000000 : ℝ)*x 0 + (-215527511/2500000000 : ℝ)*x 1 + (5560601051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547064043/1000000000 : ℝ)^81 ≤ (47157987058101/100000000000000 : ℝ)^65 := by
    have hnat : (547064043 : ℕ)^81*100000000000000^65 ≤ 47157987058101^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547064043 1000000000 47157987058101 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215527511/2500000000 : ℝ)^81 ≤ (2357856525889/50000000000000 : ℝ)^65 := by
    have hnat : (215527511 : ℕ)^81*50000000000000^65 ≤ 2357856525889^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215527511 2500000000 2357856525889 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5560601051/10000000000 : ℝ)^81 ≤ (1203157496877/2500000000000 : ℝ)^65 := by
    have hnat : (5560601051 : ℕ)^81*2500000000000^65 ≤ 1203157496877^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5560601051 10000000000 1203157496877 2500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547064043/1000000000 : ℝ), (-215527511/2500000000 : ℝ), (5560601051/10000000000 : ℝ)] ![(47157987058101/100000000000000 : ℝ), (2357856525889/50000000000000 : ℝ), (1203157496877/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547064043/1000000000 : ℝ)|^81 ≤ (47157987058101/100000000000000 : ℝ)^65
        have hw : |(547064043/1000000000 : ℝ)|=(547064043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215527511/2500000000 : ℝ)|^81 ≤ (2357856525889/50000000000000 : ℝ)^65
        have hw : |(-215527511/2500000000 : ℝ)|=(215527511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5560601051/10000000000 : ℝ)|^81 ≤ (1203157496877/2500000000000 : ℝ)^65
        have hw : |(5560601051/10000000000 : ℝ)|=(5560601051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1377389859/2500000000 : ℝ)*x 0 + (2774035977/5000000000 : ℝ)*x 1 + (-164057871/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377389859/2500000000 : ℝ)^81 ≤ (2378821194733/5000000000000 : ℝ)^65 := by
    have hnat : (1377389859 : ℕ)^81*5000000000000^65 ≤ 2378821194733^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377389859 2500000000 2378821194733 5000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2774035977/5000000000 : ℝ)^81 ≤ (11997801811987/25000000000000 : ℝ)^65 := by
    have hnat : (2774035977 : ℕ)^81*25000000000000^65 ≤ 11997801811987^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2774035977 5000000000 11997801811987 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164057871/2000000000 : ℝ)^81 ≤ (277023053293/6250000000000 : ℝ)^65 := by
    have hnat : (164057871 : ℕ)^81*6250000000000^65 ≤ 277023053293^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164057871 2000000000 277023053293 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377389859/2500000000 : ℝ), (2774035977/5000000000 : ℝ), (-164057871/2000000000 : ℝ)] ![(2378821194733/5000000000000 : ℝ), (11997801811987/25000000000000 : ℝ), (277023053293/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377389859/2500000000 : ℝ)|^81 ≤ (2378821194733/5000000000000 : ℝ)^65
        have hw : |(1377389859/2500000000 : ℝ)|=(1377389859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2774035977/5000000000 : ℝ)|^81 ≤ (11997801811987/25000000000000 : ℝ)^65
        have hw : |(2774035977/5000000000 : ℝ)|=(2774035977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-164057871/2000000000 : ℝ)|^81 ≤ (277023053293/6250000000000 : ℝ)^65
        have hw : |(-164057871/2000000000 : ℝ)|=(164057871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4258058147/10000000000 : ℝ)*x 0 + (4162447227/10000000000 : ℝ)*x 1 + (2001030559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4258058147/10000000000 : ℝ)^81 ≤ (17254826562231/50000000000000 : ℝ)^65 := by
    have hnat : (4258058147 : ℕ)^81*50000000000000^65 ≤ 17254826562231^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258058147 10000000000 17254826562231 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4162447227/10000000000 : ℝ)^81 ≤ (8386678165119/25000000000000 : ℝ)^65 := by
    have hnat : (4162447227 : ℕ)^81*25000000000000^65 ≤ 8386678165119^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162447227 10000000000 8386678165119 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2001030559/5000000000 : ℝ)^81 ≤ (31943634200479/100000000000000 : ℝ)^65 := by
    have hnat : (2001030559 : ℕ)^81*100000000000000^65 ≤ 31943634200479^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001030559 5000000000 31943634200479 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4258058147/10000000000 : ℝ), (4162447227/10000000000 : ℝ), (2001030559/5000000000 : ℝ)] ![(17254826562231/50000000000000 : ℝ), (8386678165119/25000000000000 : ℝ), (31943634200479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4258058147/10000000000 : ℝ)|^81 ≤ (17254826562231/50000000000000 : ℝ)^65
        have hw : |(4258058147/10000000000 : ℝ)|=(4258058147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4162447227/10000000000 : ℝ)|^81 ≤ (8386678165119/25000000000000 : ℝ)^65
        have hw : |(4162447227/10000000000 : ℝ)|=(4162447227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2001030559/5000000000 : ℝ)|^81 ≤ (31943634200479/100000000000000 : ℝ)^65
        have hw : |(2001030559/5000000000 : ℝ)|=(2001030559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1046222379/10000000000 : ℝ)*x 0 + (997282557/2500000000 : ℝ)*x 1 + (1366020247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046222379/10000000000 : ℝ)^81 ≤ (375129053339/6250000000000 : ℝ)^65 := by
    have hnat : (1046222379 : ℕ)^81*6250000000000^65 ≤ 375129053339^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046222379 10000000000 375129053339 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (997282557/2500000000 : ℝ)^81 ≤ (15907533852393/50000000000000 : ℝ)^65 := by
    have hnat : (997282557 : ℕ)^81*50000000000000^65 ≤ 15907533852393^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997282557 2500000000 15907533852393 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366020247/2000000000 : ℝ)^81 ≤ (62182867422959/100000000000000 : ℝ)^65 := by
    have hnat : (1366020247 : ℕ)^81*100000000000000^65 ≤ 62182867422959^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366020247 2000000000 62182867422959 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1046222379/10000000000 : ℝ), (997282557/2500000000 : ℝ), (1366020247/2000000000 : ℝ)] ![(375129053339/6250000000000 : ℝ), (15907533852393/50000000000000 : ℝ), (62182867422959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1046222379/10000000000 : ℝ)|^81 ≤ (375129053339/6250000000000 : ℝ)^65
        have hw : |(-1046222379/10000000000 : ℝ)|=(1046222379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(997282557/2500000000 : ℝ)|^81 ≤ (15907533852393/50000000000000 : ℝ)^65
        have hw : |(997282557/2500000000 : ℝ)|=(997282557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366020247/2000000000 : ℝ)|^81 ≤ (62182867422959/100000000000000 : ℝ)^65
        have hw : |(1366020247/2000000000 : ℝ)|=(1366020247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1126908817/2500000000 : ℝ)*x 0 + (-192535579/10000000000 : ℝ)*x 1 + (6833694719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1126908817/2500000000 : ℝ)^81 ≤ (18524092067379/50000000000000 : ℝ)^65 := by
    have hnat : (1126908817 : ℕ)^81*50000000000000^65 ≤ 18524092067379^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126908817 2500000000 18524092067379 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192535579/10000000000 : ℝ)^81 ≤ (45511043793/6250000000000 : ℝ)^65 := by
    have hnat : (192535579 : ℕ)^81*6250000000000^65 ≤ 45511043793^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192535579 10000000000 45511043793 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6833694719/10000000000 : ℝ)^81 ≤ (15555909787293/25000000000000 : ℝ)^65 := by
    have hnat : (6833694719 : ℕ)^81*25000000000000^65 ≤ 15555909787293^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6833694719 10000000000 15555909787293 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1126908817/2500000000 : ℝ), (-192535579/10000000000 : ℝ), (6833694719/10000000000 : ℝ)] ![(18524092067379/50000000000000 : ℝ), (45511043793/6250000000000 : ℝ), (15555909787293/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1126908817/2500000000 : ℝ)|^81 ≤ (18524092067379/50000000000000 : ℝ)^65
        have hw : |(1126908817/2500000000 : ℝ)|=(1126908817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192535579/10000000000 : ℝ)|^81 ≤ (45511043793/6250000000000 : ℝ)^65
        have hw : |(-192535579/10000000000 : ℝ)|=(192535579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6833694719/10000000000 : ℝ)|^81 ≤ (15555909787293/25000000000000 : ℝ)^65
        have hw : |(6833694719/10000000000 : ℝ)|=(6833694719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1049096141/2500000000 : ℝ)*x 0 + (1428228021/2000000000 : ℝ)*x 1 + (-14306963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049096141/2500000000 : ℝ)^81 ≤ (33887894060619/100000000000000 : ℝ)^65 := by
    have hnat : (1049096141 : ℕ)^81*100000000000000^65 ≤ 33887894060619^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049096141 2500000000 33887894060619 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1428228021/2000000000 : ℝ)^81 ≤ (32865623745713/50000000000000 : ℝ)^65 := by
    have hnat : (1428228021 : ℕ)^81*50000000000000^65 ≤ 32865623745713^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428228021 2000000000 32865623745713 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14306963/1250000000 : ℝ)^81 ≤ (23803652287/6250000000000 : ℝ)^65 := by
    have hnat : (14306963 : ℕ)^81*6250000000000^65 ≤ 23803652287^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14306963 1250000000 23803652287 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049096141/2500000000 : ℝ), (1428228021/2000000000 : ℝ), (-14306963/1250000000 : ℝ)] ![(33887894060619/100000000000000 : ℝ), (32865623745713/50000000000000 : ℝ), (23803652287/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049096141/2500000000 : ℝ)|^81 ≤ (33887894060619/100000000000000 : ℝ)^65
        have hw : |(1049096141/2500000000 : ℝ)|=(1049096141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1428228021/2000000000 : ℝ)|^81 ≤ (32865623745713/50000000000000 : ℝ)^65
        have hw : |(1428228021/2000000000 : ℝ)|=(1428228021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14306963/1250000000 : ℝ)|^81 ≤ (23803652287/6250000000000 : ℝ)^65
        have hw : |(-14306963/1250000000 : ℝ)|=(14306963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4153674009/10000000000 : ℝ)*x 0 + (3182787301/5000000000 : ℝ)*x 1 + (1523054777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4153674009/10000000000 : ℝ)^81 ≤ (33458624188429/100000000000000 : ℝ)^65 := by
    have hnat : (4153674009 : ℕ)^81*100000000000000^65 ≤ 33458624188429^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153674009 10000000000 33458624188429 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3182787301/5000000000 : ℝ)^81 ≤ (5695757439109/10000000000000 : ℝ)^65 := by
    have hnat : (3182787301 : ℕ)^81*10000000000000^65 ≤ 5695757439109^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3182787301 5000000000 5695757439109 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1523054777/10000000000 : ℝ)^81 ≤ (4791900702651/50000000000000 : ℝ)^65 := by
    have hnat : (1523054777 : ℕ)^81*50000000000000^65 ≤ 4791900702651^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523054777 10000000000 4791900702651 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4153674009/10000000000 : ℝ), (3182787301/5000000000 : ℝ), (1523054777/10000000000 : ℝ)] ![(33458624188429/100000000000000 : ℝ), (5695757439109/10000000000000 : ℝ), (4791900702651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4153674009/10000000000 : ℝ)|^81 ≤ (33458624188429/100000000000000 : ℝ)^65
        have hw : |(4153674009/10000000000 : ℝ)|=(4153674009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3182787301/5000000000 : ℝ)|^81 ≤ (5695757439109/10000000000000 : ℝ)^65
        have hw : |(3182787301/5000000000 : ℝ)|=(3182787301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1523054777/10000000000 : ℝ)|^81 ≤ (4791900702651/50000000000000 : ℝ)^65
        have hw : |(1523054777/10000000000 : ℝ)|=(1523054777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-96548397/5000000000 : ℝ)*x 0 + (222785101/500000000 : ℝ)*x 1 + (1376046671/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96548397/5000000000 : ℝ)^81 ≤ (182705663807/25000000000000 : ℝ)^65 := by
    have hnat : (96548397 : ℕ)^81*25000000000000^65 ≤ 182705663807^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96548397 5000000000 182705663807 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222785101/500000000 : ℝ)^81 ≤ (36517034057987/100000000000000 : ℝ)^65 := by
    have hnat : (222785101 : ℕ)^81*100000000000000^65 ≤ 36517034057987^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222785101 500000000 36517034057987 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1376046671/2000000000 : ℝ)^81 ≤ (3137607164109/5000000000000 : ℝ)^65 := by
    have hnat : (1376046671 : ℕ)^81*5000000000000^65 ≤ 3137607164109^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376046671 2000000000 3137607164109 5000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-96548397/5000000000 : ℝ), (222785101/500000000 : ℝ), (1376046671/2000000000 : ℝ)] ![(182705663807/25000000000000 : ℝ), (36517034057987/100000000000000 : ℝ), (3137607164109/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-96548397/5000000000 : ℝ)|^81 ≤ (182705663807/25000000000000 : ℝ)^65
        have hw : |(-96548397/5000000000 : ℝ)|=(96548397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(222785101/500000000 : ℝ)|^81 ≤ (36517034057987/100000000000000 : ℝ)^65
        have hw : |(222785101/500000000 : ℝ)|=(222785101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1376046671/2000000000 : ℝ)|^81 ≤ (3137607164109/5000000000000 : ℝ)^65
        have hw : |(1376046671/2000000000 : ℝ)|=(1376046671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3908709427/10000000000 : ℝ)*x 0 + (-1072261823/10000000000 : ℝ)*x 1 + (1720966251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3908709427/10000000000 : ℝ)^81 ≤ (31017788843431/100000000000000 : ℝ)^65 := by
    have hnat : (3908709427 : ℕ)^81*100000000000000^65 ≤ 31017788843431^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3908709427 10000000000 31017788843431 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072261823/10000000000 : ℝ)^81 ≤ (618878886389/10000000000000 : ℝ)^65 := by
    have hnat : (1072261823 : ℕ)^81*10000000000000^65 ≤ 618878886389^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072261823 10000000000 618878886389 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1720966251/2500000000 : ℝ)^81 ≤ (62793422278953/100000000000000 : ℝ)^65 := by
    have hnat : (1720966251 : ℕ)^81*100000000000000^65 ≤ 62793422278953^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720966251 2500000000 62793422278953 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3908709427/10000000000 : ℝ), (-1072261823/10000000000 : ℝ), (1720966251/2500000000 : ℝ)] ![(31017788843431/100000000000000 : ℝ), (618878886389/10000000000000 : ℝ), (62793422278953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3908709427/10000000000 : ℝ)|^81 ≤ (31017788843431/100000000000000 : ℝ)^65
        have hw : |(3908709427/10000000000 : ℝ)|=(3908709427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072261823/10000000000 : ℝ)|^81 ≤ (618878886389/10000000000000 : ℝ)^65
        have hw : |(-1072261823/10000000000 : ℝ)|=(1072261823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1720966251/2500000000 : ℝ)|^81 ≤ (62793422278953/100000000000000 : ℝ)^65
        have hw : |(1720966251/2500000000 : ℝ)|=(1720966251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6825188327/10000000000 : ℝ)*x 0 + (283788481/625000000 : ℝ)*x 1 + (-139321749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6825188327/10000000000 : ℝ)^81 ≤ (3882945877211/6250000000000 : ℝ)^65 := by
    have hnat : (6825188327 : ℕ)^81*6250000000000^65 ≤ 3882945877211^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6825188327 10000000000 3882945877211 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283788481/625000000 : ℝ)^81 ≤ (233664232673/625000000000 : ℝ)^65 := by
    have hnat : (283788481 : ℕ)^81*625000000000^65 ≤ 233664232673^65*625000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283788481 625000000 233664232673 625000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139321749/10000000000 : ℝ)^81 ≤ (15205897467/3125000000000 : ℝ)^65 := by
    have hnat : (139321749 : ℕ)^81*3125000000000^65 ≤ 15205897467^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139321749 10000000000 15205897467 3125000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6825188327/10000000000 : ℝ), (283788481/625000000 : ℝ), (-139321749/10000000000 : ℝ)] ![(3882945877211/6250000000000 : ℝ), (233664232673/625000000000 : ℝ), (15205897467/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6825188327/10000000000 : ℝ)|^81 ≤ (3882945877211/6250000000000 : ℝ)^65
        have hw : |(6825188327/10000000000 : ℝ)|=(6825188327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283788481/625000000 : ℝ)|^81 ≤ (233664232673/625000000000 : ℝ)^65
        have hw : |(283788481/625000000 : ℝ)|=(283788481/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139321749/10000000000 : ℝ)|^81 ≤ (15205897467/3125000000000 : ℝ)^65
        have hw : |(-139321749/10000000000 : ℝ)|=(139321749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (444444969/625000000 : ℝ)*x 0 + (1649552571/5000000000 : ℝ)*x 1 + (302545119/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (444444969/625000000 : ℝ)^81 ≤ (65387079589417/100000000000000 : ℝ)^65 := by
    have hnat : (444444969 : ℕ)^81*100000000000000^65 ≤ 65387079589417^65*625000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444444969 625000000 65387079589417 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1649552571/5000000000 : ℝ)^81 ≤ (3138755822241/12500000000000 : ℝ)^65 := by
    have hnat : (1649552571 : ℕ)^81*12500000000000^65 ≤ 3138755822241^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649552571 5000000000 3138755822241 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302545119/2000000000 : ℝ)^81 ≤ (4751436908313/50000000000000 : ℝ)^65 := by
    have hnat : (302545119 : ℕ)^81*50000000000000^65 ≤ 4751436908313^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302545119 2000000000 4751436908313 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(444444969/625000000 : ℝ), (1649552571/5000000000 : ℝ), (302545119/2000000000 : ℝ)] ![(65387079589417/100000000000000 : ℝ), (3138755822241/12500000000000 : ℝ), (4751436908313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(444444969/625000000 : ℝ)|^81 ≤ (65387079589417/100000000000000 : ℝ)^65
        have hw : |(444444969/625000000 : ℝ)|=(444444969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1649552571/5000000000 : ℝ)|^81 ≤ (3138755822241/12500000000000 : ℝ)^65
        have hw : |(1649552571/5000000000 : ℝ)|=(1649552571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(302545119/2000000000 : ℝ)|^81 ≤ (4751436908313/50000000000000 : ℝ)^65
        have hw : |(302545119/2000000000 : ℝ)|=(302545119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-148505699/10000000000 : ℝ)*x 0 + (3168252989/5000000000 : ℝ)*x 1 + (5064847667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (148505699/10000000000 : ℝ)^81 ≤ (263439359581/50000000000000 : ℝ)^65 := by
    have hnat : (148505699 : ℕ)^81*50000000000000^65 ≤ 263439359581^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148505699 10000000000 263439359581 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3168252989/5000000000 : ℝ)^81 ≤ (11326726729881/20000000000000 : ℝ)^65 := by
    have hnat : (3168252989 : ℕ)^81*20000000000000^65 ≤ 11326726729881^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168252989 5000000000 11326726729881 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5064847667/10000000000 : ℝ)^81 ≤ (10709871906889/25000000000000 : ℝ)^65 := by
    have hnat : (5064847667 : ℕ)^81*25000000000000^65 ≤ 10709871906889^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5064847667 10000000000 10709871906889 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-148505699/10000000000 : ℝ), (3168252989/5000000000 : ℝ), (5064847667/10000000000 : ℝ)] ![(263439359581/50000000000000 : ℝ), (11326726729881/20000000000000 : ℝ), (10709871906889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-148505699/10000000000 : ℝ)|^81 ≤ (263439359581/50000000000000 : ℝ)^65
        have hw : |(-148505699/10000000000 : ℝ)|=(148505699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3168252989/5000000000 : ℝ)|^81 ≤ (11326726729881/20000000000000 : ℝ)^65
        have hw : |(3168252989/5000000000 : ℝ)|=(3168252989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5064847667/10000000000 : ℝ)|^81 ≤ (10709871906889/25000000000000 : ℝ)^65
        have hw : |(5064847667/10000000000 : ℝ)|=(5064847667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (685354133/1000000000 : ℝ)*x 0 + (-11245161/1000000000 : ℝ)*x 1 + (282522269/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685354133/1000000000 : ℝ)^81 ≤ (12489782824623/20000000000000 : ℝ)^65 := by
    have hnat : (685354133 : ℕ)^81*20000000000000^65 ≤ 12489782824623^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685354133 1000000000 12489782824623 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11245161/1000000000 : ℝ)^81 ≤ (186283070313/50000000000000 : ℝ)^65 := by
    have hnat : (11245161 : ℕ)^81*50000000000000^65 ≤ 186283070313^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11245161 1000000000 186283070313 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282522269/625000000 : ℝ)^81 ≤ (37178519722741/100000000000000 : ℝ)^65 := by
    have hnat : (282522269 : ℕ)^81*100000000000000^65 ≤ 37178519722741^65*625000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282522269 625000000 37178519722741 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685354133/1000000000 : ℝ), (-11245161/1000000000 : ℝ), (282522269/625000000 : ℝ)] ![(12489782824623/20000000000000 : ℝ), (186283070313/50000000000000 : ℝ), (37178519722741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685354133/1000000000 : ℝ)|^81 ≤ (12489782824623/20000000000000 : ℝ)^65
        have hw : |(685354133/1000000000 : ℝ)|=(685354133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11245161/1000000000 : ℝ)|^81 ≤ (186283070313/50000000000000 : ℝ)^65
        have hw : |(-11245161/1000000000 : ℝ)|=(11245161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282522269/625000000 : ℝ)|^81 ≤ (37178519722741/100000000000000 : ℝ)^65
        have hw : |(282522269/625000000 : ℝ)|=(282522269/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_23 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (238926089/625000000 : ℝ)*x 0 + (1742469759/2500000000 : ℝ)*x 1 + (-1053846789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (238926089/625000000 : ℝ)^81 ≤ (30170719215943/100000000000000 : ℝ)^65 := by
    have hnat : (238926089 : ℕ)^81*100000000000000^65 ≤ 30170719215943^65*625000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238926089 625000000 30170719215943 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1742469759/2500000000 : ℝ)^81 ≤ (63772659832393/100000000000000 : ℝ)^65 := by
    have hnat : (1742469759 : ℕ)^81*100000000000000^65 ≤ 63772659832393^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742469759 2500000000 63772659832393 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053846789/10000000000 : ℝ)^81 ≤ (757077617813/12500000000000 : ℝ)^65 := by
    have hnat : (1053846789 : ℕ)^81*12500000000000^65 ≤ 757077617813^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053846789 10000000000 757077617813 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(238926089/625000000 : ℝ), (1742469759/2500000000 : ℝ), (-1053846789/10000000000 : ℝ)] ![(30170719215943/100000000000000 : ℝ), (63772659832393/100000000000000 : ℝ), (757077617813/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(238926089/625000000 : ℝ)|^81 ≤ (30170719215943/100000000000000 : ℝ)^65
        have hw : |(238926089/625000000 : ℝ)|=(238926089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1742469759/2500000000 : ℝ)|^81 ≤ (63772659832393/100000000000000 : ℝ)^65
        have hw : |(1742469759/2500000000 : ℝ)|=(1742469759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1053846789/10000000000 : ℝ)|^81 ≤ (757077617813/12500000000000 : ℝ)^65
        have hw : |(-1053846789/10000000000 : ℝ)|=(1053846789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s1_s1_27 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1457672483/2000000000 : ℝ)*x 0 + (622145059/2500000000 : ℝ)*x 1 + (108539587/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1457672483/2000000000 : ℝ)^81 ≤ (4214012441439/6250000000000 : ℝ)^65 := by
    have hnat : (1457672483 : ℕ)^81*6250000000000^65 ≤ 4214012441439^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1457672483 2000000000 4214012441439 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (622145059/2500000000 : ℝ)^81 ≤ (17671068993317/100000000000000 : ℝ)^65 := by
    have hnat : (622145059 : ℕ)^81*100000000000000^65 ≤ 17671068993317^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622145059 2500000000 17671068993317 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108539587/500000000 : ℝ)^81 ≤ (14904731919589/100000000000000 : ℝ)^65 := by
    have hnat : (108539587 : ℕ)^81*100000000000000^65 ≤ 14904731919589^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108539587 500000000 14904731919589 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1457672483/2000000000 : ℝ), (622145059/2500000000 : ℝ), (108539587/500000000 : ℝ)] ![(4214012441439/6250000000000 : ℝ), (17671068993317/100000000000000 : ℝ), (14904731919589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1457672483/2000000000 : ℝ)|^81 ≤ (4214012441439/6250000000000 : ℝ)^65
        have hw : |(1457672483/2000000000 : ℝ)|=(1457672483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(622145059/2500000000 : ℝ)|^81 ≤ (17671068993317/100000000000000 : ℝ)^65
        have hw : |(622145059/2500000000 : ℝ)|=(622145059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108539587/500000000 : ℝ)|^81 ≤ (14904731919589/100000000000000 : ℝ)^65
        have hw : |(108539587/500000000 : ℝ)|=(108539587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320063_s1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((72819/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72819/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72561/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(72561/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17557/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17557/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12407/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12407/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(251/500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(251/500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48013/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48013/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (1059/625 : ℝ) := by
    linarith only [f.Tcap]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (72819/100000 : ℝ) ^ (5 : ℝ) ≤ (409499663030005237/2000000000000000000 : ℝ) := by
    have hpowers : (72819/100000 : ℝ)^5 ≤ (409499663030005237/2000000000000000000 : ℝ)^1 := by
      have hnat : (72819 : ℕ)^5*2000000000000000000^1 ≤ 409499663030005237^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72819 100000 409499663030005237 2000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72819/100000 : ℝ)) (X := (409499663030005237/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0a : (2409499663030005237/2000000000000000000 : ℝ) ≤ (129744628797729/125000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2409499663030005237/2000000000000000000 : ℝ)^1 ≤ (129744628797729/125000000000000 : ℝ)^5 := by
      have hnat : (2409499663030005237 : ℕ)^1*125000000000000^5 ≤ 129744628797729^5*2000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2409499663030005237 2000000000000000000 129744628797729 125000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (129744628797729/125000000000000 : ℝ)) (X := (2409499663030005237/2000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0b : (1409499663030005237/1000000000000000000 : ℝ) ≤ (10710580144653541/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (1409499663030005237/1000000000000000000 : ℝ)^1 ≤ (10710580144653541/10000000000000000 : ℝ)^5 := by
      have hnat : (1409499663030005237 : ℕ)^1*10000000000000000^5 ≤ 10710580144653541^5*1000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409499663030005237 1000000000000000000 10710580144653541 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10710580144653541/10000000000000000 : ℝ)) (X := (1409499663030005237/1000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(4744628797729/91023750000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(331009840835221/7281900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (72819/100000 : ℝ)) (alpha := (4744628797729/91023750000000 : ℝ)) (beta := (331009840835221/7281900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (72819/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(4744628797729/91023750000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(331009840835221/7281900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (72561/100000 : ℝ) ^ (5 : ℝ) ≤ (4022965352846105049/20000000000000000000 : ℝ) := by
    have hpowers : (72561/100000 : ℝ)^5 ≤ (4022965352846105049/20000000000000000000 : ℝ)^1 := by
      have hnat : (72561 : ℕ)^5*20000000000000000000^1 ≤ 4022965352846105049^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72561 100000 4022965352846105049 20000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72561/100000 : ℝ)) (X := (4022965352846105049/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1a : (24022965352846105049/20000000000000000000 : ℝ) ≤ (10373356986071887/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (24022965352846105049/20000000000000000000 : ℝ)^1 ≤ (10373356986071887/10000000000000000 : ℝ)^5 := by
      have hnat : (24022965352846105049 : ℕ)^1*10000000000000000^5 ≤ 10373356986071887^5*20000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24022965352846105049 20000000000000000000 10373356986071887 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10373356986071887/10000000000000000 : ℝ)) (X := (24022965352846105049/20000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1b : (14022965352846105049/10000000000000000000 : ℝ) ≤ (2139922119387403/2000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (14022965352846105049/10000000000000000000 : ℝ)^1 ≤ (2139922119387403/2000000000000000 : ℝ)^5 := by
      have hnat : (14022965352846105049 : ℕ)^1*2000000000000000^5 ≤ 2139922119387403^5*10000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14022965352846105049 10000000000000000000 2139922119387403 2000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2139922119387403/2000000000000000 : ℝ)) (X := (14022965352846105049/10000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(124452328690629/2418700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(32035900517/712500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (72561/100000 : ℝ)) (alpha := (124452328690629/2418700000000000 : ℝ)) (beta := (32035900517/712500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (72561/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(124452328690629/2418700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(32035900517/712500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (17557/25000 : ℝ) ^ (5 : ℝ) ≤ (17082502868316818223/100000000000000000000 : ℝ) := by
    have hpowers : (17557/25000 : ℝ)^5 ≤ (17082502868316818223/100000000000000000000 : ℝ)^1 := by
      have hnat : (17557 : ℕ)^5*100000000000000000000^1 ≤ 17082502868316818223^1*25000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17557 25000 17082502868316818223 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17557/25000 : ℝ)) (X := (17082502868316818223/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2a : (117082502868316818223/100000000000000000000 : ℝ) ≤ (322513888292629/312500000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (117082502868316818223/100000000000000000000 : ℝ)^1 ≤ (322513888292629/312500000000000 : ℝ)^5 := by
      have hnat : (117082502868316818223 : ℕ)^1*312500000000000^5 ≤ 322513888292629^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117082502868316818223 100000000000000000000 322513888292629 312500000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (322513888292629/312500000000000 : ℝ)) (X := (117082502868316818223/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2b : (67082502868316818223/50000000000000000000 : ℝ) ≤ (10605419472972487/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (67082502868316818223/50000000000000000000 : ℝ)^1 ≤ (10605419472972487/10000000000000000 : ℝ)^5 := by
      have hnat : (67082502868316818223 : ℕ)^1*10000000000000000^5 ≤ 10605419472972487^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67082502868316818223 50000000000000000000 10605419472972487 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10605419472972487/10000000000000000 : ℝ)) (X := (67082502868316818223/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(10013888292629/219462500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(284975047608359/7022800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (17557/25000 : ℝ)) (alpha := (10013888292629/219462500000000 : ℝ)) (beta := (284975047608359/7022800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (17557/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(10013888292629/219462500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(284975047608359/7022800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-866877957/10000000000 : ℝ)*X 0 0+(5470925497/10000000000 : ℝ)*X 0 1+(5557301467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((547064043/1000000000 : ℝ)*X 1 0+(-215527511/2500000000 : ℝ)*X 1 1+(5560601051/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1377389859/2500000000 : ℝ)*X 2 0+(2774035977/5000000000 : ℝ)*X 2 1+(-164057871/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4258058147/10000000000 : ℝ)*X 0 0+(4162447227/10000000000 : ℝ)*X 0 1+(2001030559/5000000000 : ℝ)*X 0 2+(4258058147/10000000000 : ℝ)*X 1 0+(4162447227/10000000000 : ℝ)*X 1 1+(2001030559/5000000000 : ℝ)*X 1 2+(4258058147/10000000000 : ℝ)*X 2 0+(4162447227/10000000000 : ℝ)*X 2 1+(2001030559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1046222379/10000000000 : ℝ)*X 0 0+(997282557/2500000000 : ℝ)*X 0 1+(1366020247/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1126908817/2500000000 : ℝ)*X 1 0+(-192535579/10000000000 : ℝ)*X 1 1+(6833694719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1049096141/2500000000 : ℝ)*X 2 0+(1428228021/2000000000 : ℝ)*X 2 1+(-14306963/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((4153674009/10000000000 : ℝ)*X 0 0+(3182787301/5000000000 : ℝ)*X 0 1+(1523054777/10000000000 : ℝ)*X 0 2+(4153674009/10000000000 : ℝ)*X 1 0+(3182787301/5000000000 : ℝ)*X 1 1+(1523054777/10000000000 : ℝ)*X 1 2+(4153674009/10000000000 : ℝ)*X 2 0+(3182787301/5000000000 : ℝ)*X 2 1+(1523054777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-96548397/5000000000 : ℝ)*X 0 0+(222785101/500000000 : ℝ)*X 0 1+(1376046671/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3908709427/10000000000 : ℝ)*X 1 0+(-1072261823/10000000000 : ℝ)*X 1 1+(1720966251/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6825188327/10000000000 : ℝ)*X 2 0+(283788481/625000000 : ℝ)*X 2 1+(-139321749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((444444969/625000000 : ℝ)*X 0 0+(1649552571/5000000000 : ℝ)*X 0 1+(302545119/2000000000 : ℝ)*X 0 2+(444444969/625000000 : ℝ)*X 1 0+(1649552571/5000000000 : ℝ)*X 1 1+(302545119/2000000000 : ℝ)*X 1 2+(444444969/625000000 : ℝ)*X 2 0+(1649552571/5000000000 : ℝ)*X 2 1+(302545119/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-148505699/10000000000 : ℝ)*X 0 0+(3168252989/5000000000 : ℝ)*X 0 1+(5064847667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((685354133/1000000000 : ℝ)*X 1 0+(-11245161/1000000000 : ℝ)*X 1 1+(282522269/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((238926089/625000000 : ℝ)*X 2 0+(1742469759/2500000000 : ℝ)*X 2 1+(-1053846789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1457672483/2000000000 : ℝ)*X 0 0+(622145059/2500000000 : ℝ)*X 0 1+(108539587/500000000 : ℝ)*X 0 2+(1457672483/2000000000 : ℝ)*X 1 0+(622145059/2500000000 : ℝ)*X 1 1+(108539587/500000000 : ℝ)*X 1 2+(1457672483/2000000000 : ℝ)*X 2 0+(622145059/2500000000 : ℝ)*X 2 1+(108539587/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((12407/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12407/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1679042815128613876944711638039/103075575824070000000000000000000000 : ℝ) := by norm_num
    linear_combination (88047854861/200000000000 : ℝ)*(base7) + (1461717/1000000000000 : ℝ)*(base50) + (26056554573/200000000000 : ℝ)*(base60) + (536058396667/200000000000 : ℝ)*(major_s1_0) + (536058396667/200000000000 : ℝ)*(major_s1_1) + (536058396667/200000000000 : ℝ)*(major_s1_2) + (13561487/1000000000000 : ℝ)*(sp_s1_0) + (2009637/1000000000000 : ℝ)*(sp_s1_6) + (3684009508127/1000000000000 : ℝ)*(sp_s1_7) + (1842058819209/500000000000 : ℝ)*(sp_s1_8) + (1842058737691/500000000000 : ℝ)*(sp_s1_9) + (467012755243/250000000000 : ℝ)*(sp_s1_13) + (23642201/250000000000 : ℝ)*(sp_s1_14) + (40759/250000000000 : ℝ)*(sp_s1_23) + (89238359769/62500000000 : ℝ)*(f.failure) + (1842058819209/500000000000 : ℝ)*(f.sum) + (2903669732231652337/8493023180000000000000000000000 : ℝ)*base63 + (40026227817289/280912000000000000000000000 : ℝ)*base65 + (92064585107/142500000000000000000000 : ℝ)*base67 + (29054969533849/35114000000000000000000000 : ℝ)*base69 + (7514545686427299217/102278654640000000000000000000000 : ℝ)*base70 + (543566116503031/1456380000000000000000000000 : ℝ)*base73 + (96256560716517/483740000000000000000000000 : ℝ)*base75 + (410267825147689/728190000000000000000000000 : ℝ)*base77 + (8203798087574593/27671220000000000000000000000 : ℝ)*base79 + (707/625000000000000 : ℝ)*base86 + (707/625000000000000 : ℝ)*base88 + (707/625000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(251/500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(251/500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (244348912684922104971/24187000000000000000000000 : ℝ) := by norm_num
    linear_combination (486873970421/1000000000000 : ℝ)*(base7) + (982023/1000000000000 : ℝ)*(base49) + (1279538879463/500000000000 : ℝ)*(major_s1_0) + (1279538879463/500000000000 : ℝ)*(major_s1_1) + (1279538879463/500000000000 : ℝ)*(major_s1_2) + (3131393/250000000000 : ℝ)*(sp_s1_1) + (3896497/1000000000000 : ℝ)*(sp_s1_2) + (6596913/125000000000 : ℝ)*(sp_s1_8) + (1739959243677/500000000000 : ℝ)*(sp_s1_14) + (1739929248377/500000000000 : ℝ)*(sp_s1_15) + (1739959950567/500000000000 : ℝ)*(sp_s1_16) + (1850083684849/1000000000000 : ℝ)*(sp_s1_20) + (5310277/1000000000000 : ℝ)*(sp_s1_21) + (8054949/250000000000 : ℝ)*(sp_s1_27) + (85202620889/62500000000 : ℝ)*(f.failure) + (3479923797631/1000000000000 : ℝ)*(f.sum) + (460634195121137721/5308139487500000000000000000000 : ℝ)*base62 + (63853420735217/3511400000000000000000000000 : ℝ)*base65 + (7421916707/29687500000000000000000 : ℝ)*base66 + (200075670628703/438925000000000000000000000 : ℝ)*base69 + (615155836196340551/9470245800000000000000000000000 : ℝ)*base70 + (48831806583967/67425000000000000000000000 : ℝ)*base73 + (58596558765283/1209350000000000000000000000 : ℝ)*base74 + (443891647783/3371250000000000000000000 : ℝ)*base77 + (1062835686360547/2562150000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (221/312500000000000 : ℝ)*base86 + (221/312500000000000 : ℝ)*base88 + (221/312500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48013/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48013/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (704060664590438734931553919889/64422234890043750000000000000000000 : ℝ) := by norm_num
    linear_combination (478879708203/1000000000000 : ℝ)*(base7) + (89164526503/500000000000 : ℝ)*(base40) + (1290203/1000000000000 : ℝ)*(base49) + (600406463453/250000000000 : ℝ)*(major_s1_0) + (600406463453/250000000000 : ℝ)*(major_s1_1) + (600406463453/250000000000 : ℝ)*(major_s1_2) + (5368917/500000000000 : ℝ)*(sp_s1_1) + (5309603/200000000000 : ℝ)*(sp_s1_2) + (71276891/1000000000000 : ℝ)*(sp_s1_9) + (13532849/1000000000000 : ℝ)*(sp_s1_20) + (1626705403109/500000000000 : ℝ)*(sp_s1_21) + (101668752137/31250000000 : ℝ)*(sp_s1_22) + (50833015333/15625000000 : ℝ)*(sp_s1_23) + (879116087307/500000000000 : ℝ)*(sp_s1_27) + (1279365999261/1000000000000 : ℝ)*(f.failure) + (1626705403109/500000000000 : ℝ)*(f.sum) + (2090403513138294371/10616278975000000000000000000000 : ℝ)*base63 + (106503364744007/1755700000000000000000000000 : ℝ)*base65 + (193723914269/2850000000000000000000000 : ℝ)*base66 + (79562365126941/438925000000000000000000000 : ℝ)*base69 + (32881792284284764813/127848318300000000000000000000000 : ℝ)*base71 + (758481320788349/3640950000000000000000000000 : ℝ)*base72 + (52651615649911/302337500000000000000000000 : ℝ)*base75 + (178279137075763/728190000000000000000000000 : ℝ)*base77 + (2069545490999491/8647256250000000000000000000 : ℝ)*base78 + (1873/2500000000000000 : ℝ)*base87 + (1873/2500000000000000 : ℝ)*base89 + (1873/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((72819/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72819/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72561/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(72561/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17557/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17557/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12407/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12407/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(251/500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(251/500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48013/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48013/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c320063_s1 p hpa hpb X hX hprev0

#print axioms solution
