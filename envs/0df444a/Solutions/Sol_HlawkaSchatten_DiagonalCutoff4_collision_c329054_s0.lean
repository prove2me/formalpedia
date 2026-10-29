-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c329054_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:28:07.130129+00:00
-- url     : https://prove2.me/submissions/c87172a4-36e5-4664-9017-8350f4dcaeb7

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
theorem collision_support_c329054_s0_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-348897/625000000 : ℝ)*x 0 + (461109099/1000000000 : ℝ)*x 1 + (-6590500463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (348897/625000000 : ℝ)^95 ≤ (76528777/625000000000 : ℝ)^79 := by
    have hnat : (348897 : ℕ)^95*625000000000^79 ≤ 76528777^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348897 625000000 76528777 625000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (461109099/1000000000 : ℝ)^95 ≤ (39419698721899/100000000000000 : ℝ)^79 := by
    have hnat : (461109099 : ℕ)^95*100000000000000^79 ≤ 39419698721899^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461109099 1000000000 39419698721899 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6590500463/10000000000 : ℝ)^95 ≤ (12113611330903/20000000000000 : ℝ)^79 := by
    have hnat : (6590500463 : ℕ)^95*20000000000000^79 ≤ 12113611330903^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6590500463 10000000000 12113611330903 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-348897/625000000 : ℝ), (461109099/1000000000 : ℝ), (-6590500463/10000000000 : ℝ)] ![(76528777/625000000000 : ℝ), (39419698721899/100000000000000 : ℝ), (12113611330903/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-348897/625000000 : ℝ)|^95 ≤ (76528777/625000000000 : ℝ)^79
        have hw : |(-348897/625000000 : ℝ)|=(348897/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(461109099/1000000000 : ℝ)|^95 ≤ (39419698721899/100000000000000 : ℝ)^79
        have hw : |(461109099/1000000000 : ℝ)|=(461109099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6590500463/10000000000 : ℝ)|^95 ≤ (12113611330903/20000000000000 : ℝ)^79
        have hw : |(-6590500463/10000000000 : ℝ)|=(6590500463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2842026969/5000000000 : ℝ)*x 0 + (-1078545893/10000000000 : ℝ)*x 1 + (-4902522313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2842026969/5000000000 : ℝ)^95 ≤ (50695418202033/100000000000000 : ℝ)^79 := by
    have hnat : (2842026969 : ℕ)^95*100000000000000^79 ≤ 50695418202033^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842026969 5000000000 50695418202033 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078545893/10000000000 : ℝ)^95 ≤ (3435008767063/50000000000000 : ℝ)^79 := by
    have hnat : (1078545893 : ℕ)^95*50000000000000^79 ≤ 3435008767063^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078545893 10000000000 3435008767063 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4902522313/10000000000 : ℝ)^95 ≤ (21217282124011/50000000000000 : ℝ)^79 := by
    have hnat : (4902522313 : ℕ)^95*50000000000000^79 ≤ 21217282124011^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4902522313 10000000000 21217282124011 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2842026969/5000000000 : ℝ), (-1078545893/10000000000 : ℝ), (-4902522313/10000000000 : ℝ)] ![(50695418202033/100000000000000 : ℝ), (3435008767063/50000000000000 : ℝ), (21217282124011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2842026969/5000000000 : ℝ)|^95 ≤ (50695418202033/100000000000000 : ℝ)^79
        have hw : |(2842026969/5000000000 : ℝ)|=(2842026969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1078545893/10000000000 : ℝ)|^95 ≤ (3435008767063/50000000000000 : ℝ)^79
        have hw : |(-1078545893/10000000000 : ℝ)|=(1078545893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4902522313/10000000000 : ℝ)|^95 ≤ (21217282124011/50000000000000 : ℝ)^79
        have hw : |(-4902522313/10000000000 : ℝ)|=(4902522313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2647491261/5000000000 : ℝ)*x 0 + (5294983429/10000000000 : ℝ)*x 1 + (108193519/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647491261/5000000000 : ℝ)^95 ≤ (46552001689099/100000000000000 : ℝ)^79 := by
    have hnat : (2647491261 : ℕ)^95*100000000000000^79 ≤ 46552001689099^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647491261 5000000000 46552001689099 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5294983429/10000000000 : ℝ)^95 ≤ (23276005639097/50000000000000 : ℝ)^79 := by
    have hnat : (5294983429 : ℕ)^95*50000000000000^79 ≤ 23276005639097^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294983429 10000000000 23276005639097 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108193519/1000000000 : ℝ)^95 ≤ (430999189017/6250000000000 : ℝ)^79 := by
    have hnat : (108193519 : ℕ)^95*6250000000000^79 ≤ 430999189017^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108193519 1000000000 430999189017 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647491261/5000000000 : ℝ), (5294983429/10000000000 : ℝ), (108193519/1000000000 : ℝ)] ![(46552001689099/100000000000000 : ℝ), (23276005639097/50000000000000 : ℝ), (430999189017/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647491261/5000000000 : ℝ)|^95 ≤ (46552001689099/100000000000000 : ℝ)^79
        have hw : |(2647491261/5000000000 : ℝ)|=(2647491261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5294983429/10000000000 : ℝ)|^95 ≤ (23276005639097/50000000000000 : ℝ)^79
        have hw : |(5294983429/10000000000 : ℝ)|=(5294983429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108193519/1000000000 : ℝ)|^95 ≤ (430999189017/6250000000000 : ℝ)^79
        have hw : |(108193519/1000000000 : ℝ)|=(108193519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (328927787/625000000 : ℝ)*x 0 + (2631422599/5000000000 : ℝ)*x 1 + (-1169832723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328927787/625000000 : ℝ)^95 ≤ (46212438348589/100000000000000 : ℝ)^79 := by
    have hnat : (328927787 : ℕ)^95*100000000000000^79 ≤ 46212438348589^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328927787 625000000 46212438348589 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631422599/5000000000 : ℝ)^95 ≤ (46212444747521/100000000000000 : ℝ)^79 := by
    have hnat : (2631422599 : ℕ)^95*100000000000000^79 ≤ 46212444747521^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631422599 5000000000 46212444747521 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1169832723/10000000000 : ℝ)^95 ≤ (1893779220159/25000000000000 : ℝ)^79 := by
    have hnat : (1169832723 : ℕ)^95*25000000000000^79 ≤ 1893779220159^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169832723 10000000000 1893779220159 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328927787/625000000 : ℝ), (2631422599/5000000000 : ℝ), (-1169832723/10000000000 : ℝ)] ![(46212438348589/100000000000000 : ℝ), (46212444747521/100000000000000 : ℝ), (1893779220159/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328927787/625000000 : ℝ)|^95 ≤ (46212438348589/100000000000000 : ℝ)^79
        have hw : |(328927787/625000000 : ℝ)|=(328927787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631422599/5000000000 : ℝ)|^95 ≤ (46212444747521/100000000000000 : ℝ)^79
        have hw : |(2631422599/5000000000 : ℝ)|=(2631422599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1169832723/10000000000 : ℝ)|^95 ≤ (1893779220159/25000000000000 : ℝ)^79
        have hw : |(-1169832723/10000000000 : ℝ)|=(1169832723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-179542123/2500000000 : ℝ)*x 0 + (576169027/5000000000 : ℝ)*x 1 + (-1127635041/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179542123/2500000000 : ℝ)^95 ≤ (263303119751/6250000000000 : ℝ)^79 := by
    have hnat : (179542123 : ℕ)^95*6250000000000^79 ≤ 263303119751^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179542123 2500000000 263303119751 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (576169027/5000000000 : ℝ)^95 ≤ (7439095562249/100000000000000 : ℝ)^79 := by
    have hnat : (576169027 : ℕ)^95*100000000000000^79 ≤ 7439095562249^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576169027 5000000000 7439095562249 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127635041/1250000000 : ℝ)^95 ≤ (22087013630013/25000000000000 : ℝ)^79 := by
    have hnat : (1127635041 : ℕ)^95*25000000000000^79 ≤ 22087013630013^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127635041 1250000000 22087013630013 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-179542123/2500000000 : ℝ), (576169027/5000000000 : ℝ), (-1127635041/1250000000 : ℝ)] ![(263303119751/6250000000000 : ℝ), (7439095562249/100000000000000 : ℝ), (22087013630013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-179542123/2500000000 : ℝ)|^95 ≤ (263303119751/6250000000000 : ℝ)^79
        have hw : |(-179542123/2500000000 : ℝ)|=(179542123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(576169027/5000000000 : ℝ)|^95 ≤ (7439095562249/100000000000000 : ℝ)^79
        have hw : |(576169027/5000000000 : ℝ)|=(576169027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1127635041/1250000000 : ℝ)|^95 ≤ (22087013630013/25000000000000 : ℝ)^79
        have hw : |(-1127635041/1250000000 : ℝ)|=(1127635041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3296553341/10000000000 : ℝ)*x 0 + (-41441701/1250000000 : ℝ)*x 1 + (-7610190917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3296553341/10000000000 : ℝ)^95 ≤ (6582517714691/25000000000000 : ℝ)^79 := by
    have hnat : (3296553341 : ℕ)^95*25000000000000^79 ≤ 6582517714691^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3296553341 10000000000 6582517714691 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41441701/1250000000 : ℝ)^95 ≤ (1662982090573/100000000000000 : ℝ)^79 := by
    have hnat : (41441701 : ℕ)^95*100000000000000^79 ≤ 1662982090573^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41441701 1250000000 1662982090573 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7610190917/10000000000 : ℝ)^95 ≤ (36003473520929/50000000000000 : ℝ)^79 := by
    have hnat : (7610190917 : ℕ)^95*50000000000000^79 ≤ 36003473520929^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7610190917 10000000000 36003473520929 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3296553341/10000000000 : ℝ), (-41441701/1250000000 : ℝ), (-7610190917/10000000000 : ℝ)] ![(6582517714691/25000000000000 : ℝ), (1662982090573/100000000000000 : ℝ), (36003473520929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3296553341/10000000000 : ℝ)|^95 ≤ (6582517714691/25000000000000 : ℝ)^79
        have hw : |(3296553341/10000000000 : ℝ)|=(3296553341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41441701/1250000000 : ℝ)|^95 ≤ (1662982090573/100000000000000 : ℝ)^79
        have hw : |(-41441701/1250000000 : ℝ)|=(41441701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7610190917/10000000000 : ℝ)|^95 ≤ (36003473520929/50000000000000 : ℝ)^79
        have hw : |(-7610190917/10000000000 : ℝ)|=(7610190917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (741405393/2500000000 : ℝ)*x 0 + (790461369/1000000000 : ℝ)*x 1 + (295024583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (741405393/2500000000 : ℝ)^95 ≤ (23184752422171/100000000000000 : ℝ)^79 := by
    have hnat : (741405393 : ℕ)^95*100000000000000^79 ≤ 23184752422171^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741405393 2500000000 23184752422171 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (790461369/1000000000 : ℝ)^95 ≤ (37684977000601/50000000000000 : ℝ)^79 := by
    have hnat : (790461369 : ℕ)^95*50000000000000^79 ≤ 37684977000601^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790461369 1000000000 37684977000601 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (295024583/10000000000 : ℝ)^95 ≤ (180661695829/12500000000000 : ℝ)^79 := by
    have hnat : (295024583 : ℕ)^95*12500000000000^79 ≤ 180661695829^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295024583 10000000000 180661695829 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(741405393/2500000000 : ℝ), (790461369/1000000000 : ℝ), (295024583/10000000000 : ℝ)] ![(23184752422171/100000000000000 : ℝ), (37684977000601/50000000000000 : ℝ), (180661695829/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(741405393/2500000000 : ℝ)|^95 ≤ (23184752422171/100000000000000 : ℝ)^79
        have hw : |(741405393/2500000000 : ℝ)|=(741405393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(790461369/1000000000 : ℝ)|^95 ≤ (37684977000601/50000000000000 : ℝ)^79
        have hw : |(790461369/1000000000 : ℝ)|=(790461369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(295024583/10000000000 : ℝ)|^95 ≤ (180661695829/12500000000000 : ℝ)^79
        have hw : |(295024583/10000000000 : ℝ)|=(295024583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3189141897/10000000000 : ℝ)*x 0 + (1931607531/2500000000 : ℝ)*x 1 + (-17600007/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3189141897/10000000000 : ℝ)^95 ≤ (2530183910851/10000000000000 : ℝ)^79 := by
    have hnat : (3189141897 : ℕ)^95*10000000000000^79 ≤ 2530183910851^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3189141897 10000000000 2530183910851 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1931607531/2500000000 : ℝ)^95 ≤ (73331582937413/100000000000000 : ℝ)^79 := by
    have hnat : (1931607531 : ℕ)^95*100000000000000^79 ≤ 73331582937413^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931607531 2500000000 73331582937413 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17600007/625000000 : ℝ)^95 ≤ (683288972843/50000000000000 : ℝ)^79 := by
    have hnat : (17600007 : ℕ)^95*50000000000000^79 ≤ 683288972843^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17600007 625000000 683288972843 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3189141897/10000000000 : ℝ), (1931607531/2500000000 : ℝ), (-17600007/625000000 : ℝ)] ![(2530183910851/10000000000000 : ℝ), (73331582937413/100000000000000 : ℝ), (683288972843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3189141897/10000000000 : ℝ)|^95 ≤ (2530183910851/10000000000000 : ℝ)^79
        have hw : |(3189141897/10000000000 : ℝ)|=(3189141897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1931607531/2500000000 : ℝ)|^95 ≤ (73331582937413/100000000000000 : ℝ)^79
        have hw : |(1931607531/2500000000 : ℝ)|=(1931607531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17600007/625000000 : ℝ)|^95 ≤ (683288972843/50000000000000 : ℝ)^79
        have hw : |(-17600007/625000000 : ℝ)|=(17600007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-39729/10000000000 : ℝ)*x 0 + (977794681/5000000000 : ℝ)*x 1 + (-8816812569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39729/10000000000 : ℝ)^95 ≤ (6401563/20000000000000 : ℝ)^79 := by
    have hnat : (39729 : ℕ)^95*20000000000000^79 ≤ 6401563^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39729 10000000000 6401563 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977794681/5000000000 : ℝ)^95 ≤ (14052026676681/100000000000000 : ℝ)^79 := by
    have hnat : (977794681 : ℕ)^95*100000000000000^79 ≤ 14052026676681^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977794681 5000000000 14052026676681 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8816812569/10000000000 : ℝ)^95 ≤ (21486985326443/25000000000000 : ℝ)^79 := by
    have hnat : (8816812569 : ℕ)^95*25000000000000^79 ≤ 21486985326443^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8816812569 10000000000 21486985326443 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-39729/10000000000 : ℝ), (977794681/5000000000 : ℝ), (-8816812569/10000000000 : ℝ)] ![(6401563/20000000000000 : ℝ), (14052026676681/100000000000000 : ℝ), (21486985326443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-39729/10000000000 : ℝ)|^95 ≤ (6401563/20000000000000 : ℝ)^79
        have hw : |(-39729/10000000000 : ℝ)|=(39729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(977794681/5000000000 : ℝ)|^95 ≤ (14052026676681/100000000000000 : ℝ)^79
        have hw : |(977794681/5000000000 : ℝ)|=(977794681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8816812569/10000000000 : ℝ)|^95 ≤ (21486985326443/25000000000000 : ℝ)^79
        have hw : |(-8816812569/10000000000 : ℝ)|=(8816812569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1765555117/10000000000 : ℝ)*x 0 + (-56949953/200000000 : ℝ)*x 1 + (-7033325669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1765555117/10000000000 : ℝ)^95 ≤ (3106639893429/25000000000000 : ℝ)^79 := by
    have hnat : (1765555117 : ℕ)^95*25000000000000^79 ≤ 3106639893429^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765555117 10000000000 3106639893429 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56949953/200000000 : ℝ)^95 ≤ (11039386740479/50000000000000 : ℝ)^79 := by
    have hnat : (56949953 : ℕ)^95*50000000000000^79 ≤ 11039386740479^79*200000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56949953 200000000 11039386740479 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7033325669/10000000000 : ℝ)^95 ≤ (65494666932893/100000000000000 : ℝ)^79 := by
    have hnat : (7033325669 : ℕ)^95*100000000000000^79 ≤ 65494666932893^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7033325669 10000000000 65494666932893 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1765555117/10000000000 : ℝ), (-56949953/200000000 : ℝ), (-7033325669/10000000000 : ℝ)] ![(3106639893429/25000000000000 : ℝ), (11039386740479/50000000000000 : ℝ), (65494666932893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1765555117/10000000000 : ℝ)|^95 ≤ (3106639893429/25000000000000 : ℝ)^79
        have hw : |(1765555117/10000000000 : ℝ)|=(1765555117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56949953/200000000 : ℝ)|^95 ≤ (11039386740479/50000000000000 : ℝ)^79
        have hw : |(-56949953/200000000 : ℝ)|=(56949953/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7033325669/10000000000 : ℝ)|^95 ≤ (65494666932893/100000000000000 : ℝ)^79
        have hw : |(-7033325669/10000000000 : ℝ)|=(7033325669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7889416479/10000000000 : ℝ)*x 0 + (1261842323/5000000000 : ℝ)*x 1 + (36985737/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7889416479/10000000000 : ℝ)^95 ≤ (300782943397/400000000000 : ℝ)^79 := by
    have hnat : (7889416479 : ℕ)^95*400000000000^79 ≤ 300782943397^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7889416479 10000000000 300782943397 400000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1261842323/5000000000 : ℝ)^95 ≤ (9547689166043/50000000000000 : ℝ)^79 := by
    have hnat : (1261842323 : ℕ)^95*50000000000000^79 ≤ 9547689166043^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261842323 5000000000 9547689166043 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36985737/400000000 : ℝ)^95 ≤ (570888581109/10000000000000 : ℝ)^79 := by
    have hnat : (36985737 : ℕ)^95*10000000000000^79 ≤ 570888581109^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36985737 400000000 570888581109 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7889416479/10000000000 : ℝ), (1261842323/5000000000 : ℝ), (36985737/400000000 : ℝ)] ![(300782943397/400000000000 : ℝ), (9547689166043/50000000000000 : ℝ), (570888581109/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7889416479/10000000000 : ℝ)|^95 ≤ (300782943397/400000000000 : ℝ)^79
        have hw : |(7889416479/10000000000 : ℝ)|=(7889416479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1261842323/5000000000 : ℝ)|^95 ≤ (9547689166043/50000000000000 : ℝ)^79
        have hw : |(1261842323/5000000000 : ℝ)|=(1261842323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36985737/400000000 : ℝ)|^95 ≤ (570888581109/10000000000000 : ℝ)^79
        have hw : |(36985737/400000000 : ℝ)|=(36985737/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7458855541/10000000000 : ℝ)*x 0 + (3173950309/10000000000 : ℝ)*x 1 + (-47892729/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7458855541/10000000000 : ℝ)^95 ≤ (70288501795687/100000000000000 : ℝ)^79 := by
    have hnat : (7458855541 : ℕ)^95*100000000000000^79 ≤ 70288501795687^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7458855541 10000000000 70288501795687 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3173950309/10000000000 : ℝ)^95 ≤ (25156972557181/100000000000000 : ℝ)^79 := by
    have hnat : (3173950309 : ℕ)^95*100000000000000^79 ≤ 25156972557181^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3173950309 10000000000 25156972557181 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47892729/625000000 : ℝ)^95 ≤ (2277262815143/50000000000000 : ℝ)^79 := by
    have hnat : (47892729 : ℕ)^95*50000000000000^79 ≤ 2277262815143^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47892729 625000000 2277262815143 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7458855541/10000000000 : ℝ), (3173950309/10000000000 : ℝ), (-47892729/625000000 : ℝ)] ![(70288501795687/100000000000000 : ℝ), (25156972557181/100000000000000 : ℝ), (2277262815143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7458855541/10000000000 : ℝ)|^95 ≤ (70288501795687/100000000000000 : ℝ)^79
        have hw : |(7458855541/10000000000 : ℝ)|=(7458855541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3173950309/10000000000 : ℝ)|^95 ≤ (25156972557181/100000000000000 : ℝ)^79
        have hw : |(3173950309/10000000000 : ℝ)|=(3173950309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47892729/625000000 : ℝ)|^95 ≤ (2277262815143/50000000000000 : ℝ)^79
        have hw : |(-47892729/625000000 : ℝ)|=(47892729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (317/10000000000 : ℝ)*x 0 + (1595612727/2500000000 : ℝ)*x 1 + (-2417069559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (317/10000000000 : ℝ)^95 ≤ (24001/25000000000000 : ℝ)^79 := by
    have hnat : (317 : ℕ)^95*25000000000000^79 ≤ 24001^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317 10000000000 24001 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1595612727/2500000000 : ℝ)^95 ≤ (58276206970567/100000000000000 : ℝ)^79 := by
    have hnat : (1595612727 : ℕ)^95*100000000000000^79 ≤ 58276206970567^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595612727 2500000000 58276206970567 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2417069559/5000000000 : ℝ)^95 ≤ (41723792925303/100000000000000 : ℝ)^79 := by
    have hnat : (2417069559 : ℕ)^95*100000000000000^79 ≤ 41723792925303^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417069559 5000000000 41723792925303 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(317/10000000000 : ℝ), (1595612727/2500000000 : ℝ), (-2417069559/5000000000 : ℝ)] ![(24001/25000000000000 : ℝ), (58276206970567/100000000000000 : ℝ), (41723792925303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(317/10000000000 : ℝ)|^95 ≤ (24001/25000000000000 : ℝ)^79
        have hw : |(317/10000000000 : ℝ)|=(317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1595612727/2500000000 : ℝ)|^95 ≤ (58276206970567/100000000000000 : ℝ)^79
        have hw : |(1595612727/2500000000 : ℝ)|=(1595612727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2417069559/5000000000 : ℝ)|^95 ≤ (41723792925303/100000000000000 : ℝ)^79
        have hw : |(-2417069559/5000000000 : ℝ)|=(2417069559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8002523029/10000000000 : ℝ)*x 0 + (-810036197/5000000000 : ℝ)*x 1 + (-218827781/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8002523029/10000000000 : ℝ)^95 ≤ (38246995816899/50000000000000 : ℝ)^79 := by
    have hnat : (8002523029 : ℕ)^95*50000000000000^79 ≤ 38246995816899^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8002523029 10000000000 38246995816899 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (810036197/5000000000 : ℝ)^95 ≤ (11205729312671/100000000000000 : ℝ)^79 := by
    have hnat : (810036197 : ℕ)^95*100000000000000^79 ≤ 11205729312671^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810036197 5000000000 11205729312671 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218827781/1250000000 : ℝ)^95 ≤ (6150139517659/50000000000000 : ℝ)^79 := by
    have hnat : (218827781 : ℕ)^95*50000000000000^79 ≤ 6150139517659^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218827781 1250000000 6150139517659 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8002523029/10000000000 : ℝ), (-810036197/5000000000 : ℝ), (-218827781/1250000000 : ℝ)] ![(38246995816899/50000000000000 : ℝ), (11205729312671/100000000000000 : ℝ), (6150139517659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8002523029/10000000000 : ℝ)|^95 ≤ (38246995816899/50000000000000 : ℝ)^79
        have hw : |(8002523029/10000000000 : ℝ)|=(8002523029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-810036197/5000000000 : ℝ)|^95 ≤ (11205729312671/100000000000000 : ℝ)^79
        have hw : |(-810036197/5000000000 : ℝ)|=(810036197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-218827781/1250000000 : ℝ)|^95 ≤ (6150139517659/50000000000000 : ℝ)^79
        have hw : |(-218827781/1250000000 : ℝ)|=(218827781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1636810003/10000000000 : ℝ)*x 0 + (6797118587/10000000000 : ℝ)*x 1 + (16204379/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1636810003/10000000000 : ℝ)^95 ≤ (11345092646217/100000000000000 : ℝ)^79 := by
    have hnat : (1636810003 : ℕ)^95*100000000000000^79 ≤ 11345092646217^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636810003 10000000000 11345092646217 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6797118587/10000000000 : ℝ)^95 ≤ (3928668092483/6250000000000 : ℝ)^79 := by
    have hnat : (6797118587 : ℕ)^95*6250000000000^79 ≤ 3928668092483^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6797118587 10000000000 3928668092483 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16204379/50000000 : ℝ)^95 ≤ (3224527232457/12500000000000 : ℝ)^79 := by
    have hnat : (16204379 : ℕ)^95*12500000000000^79 ≤ 3224527232457^79*50000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16204379 50000000 3224527232457 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1636810003/10000000000 : ℝ), (6797118587/10000000000 : ℝ), (16204379/50000000 : ℝ)] ![(11345092646217/100000000000000 : ℝ), (3928668092483/6250000000000 : ℝ), (3224527232457/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1636810003/10000000000 : ℝ)|^95 ≤ (11345092646217/100000000000000 : ℝ)^79
        have hw : |(1636810003/10000000000 : ℝ)|=(1636810003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6797118587/10000000000 : ℝ)|^95 ≤ (3928668092483/6250000000000 : ℝ)^79
        have hw : |(6797118587/10000000000 : ℝ)|=(6797118587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16204379/50000000 : ℝ)|^95 ≤ (3224527232457/12500000000000 : ℝ)^79
        have hw : |(16204379/50000000 : ℝ)|=(16204379/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329054_s0_s0_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (452699413/625000000 : ℝ)*x 0 + (18377667/62500000 : ℝ)*x 1 + (-1375030769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (452699413/625000000 : ℝ)^95 ≤ (67851786832399/100000000000000 : ℝ)^79 := by
    have hnat : (452699413 : ℕ)^95*100000000000000^79 ≤ 67851786832399^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452699413 625000000 67851786832399 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18377667/62500000 : ℝ)^95 ≤ (22948094843807/100000000000000 : ℝ)^79 := by
    have hnat : (18377667 : ℕ)^95*100000000000000^79 ≤ 22948094843807^79*62500000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18377667 62500000 22948094843807 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1375030769/10000000000 : ℝ)^95 ≤ (1150014788643/12500000000000 : ℝ)^79 := by
    have hnat : (1375030769 : ℕ)^95*12500000000000^79 ≤ 1150014788643^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375030769 10000000000 1150014788643 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(452699413/625000000 : ℝ), (18377667/62500000 : ℝ), (-1375030769/10000000000 : ℝ)] ![(67851786832399/100000000000000 : ℝ), (22948094843807/100000000000000 : ℝ), (1150014788643/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(452699413/625000000 : ℝ)|^95 ≤ (67851786832399/100000000000000 : ℝ)^79
        have hw : |(452699413/625000000 : ℝ)|=(452699413/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(18377667/62500000 : ℝ)|^95 ≤ (22948094843807/100000000000000 : ℝ)^79
        have hw : |(18377667/62500000 : ℝ)|=(18377667/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1375030769/10000000000 : ℝ)|^95 ≤ (1150014788643/12500000000000 : ℝ)^79
        have hw : |(-1375030769/10000000000 : ℝ)|=(1375030769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329054_s0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : (0 : ℝ) ≤ ((58043/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58043/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61069/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61069/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10763/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10763/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-348897/625000000 : ℝ)*X 0 0+(461109099/1000000000 : ℝ)*X 0 1+(-6590500463/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2842026969/5000000000 : ℝ)*X 1 0+(-1078545893/10000000000 : ℝ)*X 1 1+(-4902522313/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2647491261/5000000000 : ℝ)*X 2 0+(5294983429/10000000000 : ℝ)*X 2 1+(108193519/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((328927787/625000000 : ℝ)*X 0 0+(2631422599/5000000000 : ℝ)*X 0 1+(-1169832723/10000000000 : ℝ)*X 0 2+(328927787/625000000 : ℝ)*X 1 0+(2631422599/5000000000 : ℝ)*X 1 1+(-1169832723/10000000000 : ℝ)*X 1 2+(328927787/625000000 : ℝ)*X 2 0+(2631422599/5000000000 : ℝ)*X 2 1+(-1169832723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-179542123/2500000000 : ℝ)*X 0 0+(576169027/5000000000 : ℝ)*X 0 1+(-1127635041/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3296553341/10000000000 : ℝ)*X 1 0+(-41441701/1250000000 : ℝ)*X 1 1+(-7610190917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((741405393/2500000000 : ℝ)*X 2 0+(790461369/1000000000 : ℝ)*X 2 1+(295024583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3189141897/10000000000 : ℝ)*X 0 0+(1931607531/2500000000 : ℝ)*X 0 1+(-17600007/625000000 : ℝ)*X 0 2+(3189141897/10000000000 : ℝ)*X 1 0+(1931607531/2500000000 : ℝ)*X 1 1+(-17600007/625000000 : ℝ)*X 1 2+(3189141897/10000000000 : ℝ)*X 2 0+(1931607531/2500000000 : ℝ)*X 2 1+(-17600007/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-39729/10000000000 : ℝ)*X 0 0+(977794681/5000000000 : ℝ)*X 0 1+(-8816812569/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1765555117/10000000000 : ℝ)*X 1 0+(-56949953/200000000 : ℝ)*X 1 1+(-7033325669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7889416479/10000000000 : ℝ)*X 2 0+(1261842323/5000000000 : ℝ)*X 2 1+(36985737/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7458855541/10000000000 : ℝ)*X 0 0+(3173950309/10000000000 : ℝ)*X 0 1+(-47892729/625000000 : ℝ)*X 0 2+(7458855541/10000000000 : ℝ)*X 1 0+(3173950309/10000000000 : ℝ)*X 1 1+(-47892729/625000000 : ℝ)*X 1 2+(7458855541/10000000000 : ℝ)*X 2 0+(3173950309/10000000000 : ℝ)*X 2 1+(-47892729/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((317/10000000000 : ℝ)*X 0 0+(1595612727/2500000000 : ℝ)*X 0 1+(-2417069559/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8002523029/10000000000 : ℝ)*X 1 0+(-810036197/5000000000 : ℝ)*X 1 1+(-218827781/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1636810003/10000000000 : ℝ)*X 2 0+(6797118587/10000000000 : ℝ)*X 2 1+(16204379/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((452699413/625000000 : ℝ)*X 0 0+(18377667/62500000 : ℝ)*X 0 1+(-1375030769/10000000000 : ℝ)*X 0 2+(452699413/625000000 : ℝ)*X 1 0+(18377667/62500000 : ℝ)*X 1 1+(-1375030769/10000000000 : ℝ)*X 1 2+(452699413/625000000 : ℝ)*X 2 0+(18377667/62500000 : ℝ)*X 2 1+(-1375030769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329054_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((58043/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58043/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3876606353017687107669/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (103692612211/100000000000 : ℝ)*(base7) + (1554709/500000000000 : ℝ)*(base12) + (410840663/250000000000 : ℝ)*(base39) + (27433082079/500000000000 : ℝ)*(base60) + (1426709967003/1000000000000 : ℝ)*(major_s0_0) + (1426709967003/1000000000000 : ℝ)*(major_s0_1) + (1426709967003/1000000000000 : ℝ)*(major_s0_2) + (7833603/1000000000000 : ℝ)*(sp_s0_1) + (1657780286663/1000000000000 : ℝ)*(sp_s0_7) + (1657859178229/1000000000000 : ℝ)*(sp_s0_8) + (1657865449643/1000000000000 : ℝ)*(sp_s0_9) + (839279672031/500000000000 : ℝ)*(sp_s0_13) + (83615751/1000000000000 : ℝ)*(sp_s0_14) + (390547/250000000000 : ℝ)*(sp_s0_23) + (10025519093/15625000000 : ℝ)*(f.failure) + (1657867011831/1000000000000 : ℝ)*(f.sum) + (1620782049359971/5000000000000000000000000000 : ℝ)*base63 + (6560910811452403/10000000000000000000000000000 : ℝ)*base64 + (10967747186452403/10000000000000000000000000000 : ℝ)*base67 + (4197989298140029/10000000000000000000000000000 : ℝ)*base68 + (63622838599527/625000000000000000000000000 : ℝ)*base70 + (5135592216547597/10000000000000000000000000000 : ℝ)*base73 + (3598162955140029/10000000000000000000000000000 : ℝ)*base74 + (402256695140029/10000000000000000000000000000 : ℝ)*base76 + (72483573/400000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1841/3125000000000000 : ℝ)*base87 + (1841/3125000000000000 : ℝ)*base89 + (1841/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61069/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61069/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15080759140745018049141/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48526744609/40000000000 : ℝ)*(base7) + (31613/125000000000 : ℝ)*(base40) + (123512711871/500000000000 : ℝ)*(base53) + (25751623367/500000000000 : ℝ)*(base60) + (351034302773/250000000000 : ℝ)*(major_s0_0) + (351034302773/250000000000 : ℝ)*(major_s0_1) + (23142235747/20000000000 : ℝ)*(major_s0_2) + (69721/250000000000 : ℝ)*(sp_s0_0) + (3243927/200000000000 : ℝ)*(sp_s0_8) + (256340514629/200000000000 : ℝ)*(sp_s0_14) + (640843316197/500000000000 : ℝ)*(sp_s0_15) + (1528728275771/1000000000000 : ℝ)*(sp_s0_16) + (922320375229/500000000000 : ℝ)*(sp_s0_20) + (9457839/1000000000000 : ℝ)*(sp_s0_27) + (39467599567/62500000000 : ℝ)*(f.failure) + (1528728275771/1000000000000 : ℝ)*(f.sum) + (687681573861197/5000000000000000000000000000 : ℝ)*base63 + (29793262740347/200000000000000000000000000 : ℝ)*base64 + (978824942374173/2500000000000000000000000000 : ℝ)*base67 + (12120101363221/200000000000000000000000000 : ℝ)*base68 + (604866298566953/5000000000000000000000000000 : ℝ)*base70 + (1033298128625827/2500000000000000000000000000 : ℝ)*base73 + (425417372279139/2500000000000000000000000000 : ℝ)*base74 + (1011509239529139/2500000000000000000000000000 : ℝ)*base76 + (264302657/2500000000000000000000 : ℝ)*base79 + (1287/1562500000000000 : ℝ)*base86 + (1287/1562500000000000 : ℝ)*base88 + (1287/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10763/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10763/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10164794883675842144421/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1236642793917/1000000000000 : ℝ)*(base7) + (256207/1000000000000 : ℝ)*(base15) + (125029422161/500000000000 : ℝ)*(base39) + (719720011951/500000000000 : ℝ)*(major_s0_0) + (719720011951/500000000000 : ℝ)*(major_s0_1) + (719720011951/500000000000 : ℝ)*(major_s0_2) + (2716303/1000000000000 : ℝ)*(sp_s0_2) + (871141/1000000000000 : ℝ)*(sp_s0_6) + (459003/125000000000 : ℝ)*(sp_s0_9) + (11265507/500000000000 : ℝ)*(sp_s0_20) + (785459088677/500000000000 : ℝ)*(sp_s0_21) + (1570917921147/1000000000000 : ℝ)*(sp_s0_22) + (1570911789027/1000000000000 : ℝ)*(sp_s0_23) + (1883977692821/1000000000000 : ℝ)*(sp_s0_27) + (647358301059/1000000000000 : ℝ)*(f.failure) + (785459088677/500000000000 : ℝ)*(f.sum) + (1002019563285193/2500000000000000000000000000 : ℝ)*base62 + (745907325516249/5000000000000000000000000000 : ℝ)*base65 + (1091249043516249/5000000000000000000000000000 : ℝ)*base66 + (202940306214807/5000000000000000000000000000 : ℝ)*base69 + (83364497173059/312500000000000000000000000 : ℝ)*base70 + (153133254483751/5000000000000000000000000000 : ℝ)*base72 + (1218260049785193/5000000000000000000000000000 : ℝ)*base74 + (840090164714807/5000000000000000000000000000 : ℝ)*base77 + (1126748213/5000000000000000000000 : ℝ)*base79 + (18751/25000000000000000 : ℝ)*base87 + (18751/25000000000000000 : ℝ)*base89 + (18751/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : (0 : ℝ) ≤ ((58043/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58043/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61069/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61069/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10763/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10763/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c329054_s0 p hpa hpb X hX

#print axioms solution
