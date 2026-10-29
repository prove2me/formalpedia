-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312056_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:19:27.662219+00:00
-- url     : https://prove2.me/submissions/274dbaaf-a34f-4911-b895-e7ee25f692d3

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
theorem collision_support_c312056_s1_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1618307767/5000000000 : ℝ)*x 0 + (-809153891/2500000000 : ℝ)*x 1 + (-1519158417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1618307767/5000000000 : ℝ)^73 ≤ (1473848513607/6250000000000 : ℝ)^57 := by
    have hnat : (1618307767 : ℕ)^73*6250000000000^57 ≤ 1473848513607^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1618307767 5000000000 1473848513607 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (809153891/2500000000 : ℝ)^73 ≤ (23581576497643/100000000000000 : ℝ)^57 := by
    have hnat : (809153891 : ℕ)^73*100000000000000^57 ≤ 23581576497643^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809153891 2500000000 23581576497643 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1519158417/2500000000 : ℝ)^73 ≤ (52836847265309/100000000000000 : ℝ)^57 := by
    have hnat : (1519158417 : ℕ)^73*100000000000000^57 ≤ 52836847265309^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519158417 2500000000 52836847265309 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1618307767/5000000000 : ℝ), (-809153891/2500000000 : ℝ), (-1519158417/2500000000 : ℝ)] ![(1473848513607/6250000000000 : ℝ), (23581576497643/100000000000000 : ℝ), (52836847265309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1618307767/5000000000 : ℝ)|^73 ≤ (1473848513607/6250000000000 : ℝ)^57
        have hw : |(1618307767/5000000000 : ℝ)|=(1618307767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-809153891/2500000000 : ℝ)|^73 ≤ (23581576497643/100000000000000 : ℝ)^57
        have hw : |(-809153891/2500000000 : ℝ)|=(809153891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1519158417/2500000000 : ℝ)|^73 ≤ (52836847265309/100000000000000 : ℝ)^57
        have hw : |(-1519158417/2500000000 : ℝ)|=(1519158417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1358344323/2500000000 : ℝ)*x 0 + (5433377319/10000000000 : ℝ)*x 1 + (1450206127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1358344323/2500000000 : ℝ)^73 ≤ (4578292221487/10000000000000 : ℝ)^57 := by
    have hnat : (1358344323 : ℕ)^73*10000000000000^57 ≤ 4578292221487^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358344323 2500000000 4578292221487 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433377319/10000000000 : ℝ)^73 ≤ (2235494263/4882812500 : ℝ)^57 := by
    have hnat : (5433377319 : ℕ)^73*4882812500^57 ≤ 2235494263^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433377319 10000000000 2235494263 4882812500 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1450206127/10000000000 : ℝ)^73 ≤ (843415525651/10000000000000 : ℝ)^57 := by
    have hnat : (1450206127 : ℕ)^73*10000000000000^57 ≤ 843415525651^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1450206127 10000000000 843415525651 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1358344323/2500000000 : ℝ), (5433377319/10000000000 : ℝ), (1450206127/10000000000 : ℝ)] ![(4578292221487/10000000000000 : ℝ), (2235494263/4882812500 : ℝ), (843415525651/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1358344323/2500000000 : ℝ)|^73 ≤ (4578292221487/10000000000000 : ℝ)^57
        have hw : |(1358344323/2500000000 : ℝ)|=(1358344323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433377319/10000000000 : ℝ)|^73 ≤ (2235494263/4882812500 : ℝ)^57
        have hw : |(5433377319/10000000000 : ℝ)|=(5433377319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1450206127/10000000000 : ℝ)|^73 ≤ (843415525651/10000000000000 : ℝ)^57
        have hw : |(1450206127/10000000000 : ℝ)|=(1450206127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-24476271/80000000 : ℝ)*x 0 + (1388118651/5000000000 : ℝ)*x 1 + (-6595548131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24476271/80000000 : ℝ)^73 ≤ (5485520034343/25000000000000 : ℝ)^57 := by
    have hnat : (24476271 : ℕ)^73*25000000000000^57 ≤ 5485520034343^57*80000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24476271 80000000 5485520034343 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1388118651/5000000000 : ℝ)^73 ≤ (19374650288079/100000000000000 : ℝ)^57 := by
    have hnat : (1388118651 : ℕ)^73*100000000000000^57 ≤ 19374650288079^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388118651 5000000000 19374650288079 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6595548131/10000000000 : ℝ)^73 ≤ (29341634783763/50000000000000 : ℝ)^57 := by
    have hnat : (6595548131 : ℕ)^73*50000000000000^57 ≤ 29341634783763^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6595548131 10000000000 29341634783763 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24476271/80000000 : ℝ), (1388118651/5000000000 : ℝ), (-6595548131/10000000000 : ℝ)] ![(5485520034343/25000000000000 : ℝ), (19374650288079/100000000000000 : ℝ), (29341634783763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24476271/80000000 : ℝ)|^73 ≤ (5485520034343/25000000000000 : ℝ)^57
        have hw : |(-24476271/80000000 : ℝ)|=(24476271/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1388118651/5000000000 : ℝ)|^73 ≤ (19374650288079/100000000000000 : ℝ)^57
        have hw : |(1388118651/5000000000 : ℝ)|=(1388118651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6595548131/10000000000 : ℝ)|^73 ≤ (29341634783763/50000000000000 : ℝ)^57
        have hw : |(-6595548131/10000000000 : ℝ)|=(6595548131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (24476271/80000000 : ℝ)*x 0 + (-1388118651/5000000000 : ℝ)*x 1 + (-6595548131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24476271/80000000 : ℝ)^73 ≤ (5485520034343/25000000000000 : ℝ)^57 := by
    have hnat : (24476271 : ℕ)^73*25000000000000^57 ≤ 5485520034343^57*80000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24476271 80000000 5485520034343 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1388118651/5000000000 : ℝ)^73 ≤ (19374650288079/100000000000000 : ℝ)^57 := by
    have hnat : (1388118651 : ℕ)^73*100000000000000^57 ≤ 19374650288079^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388118651 5000000000 19374650288079 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6595548131/10000000000 : ℝ)^73 ≤ (29341634783763/50000000000000 : ℝ)^57 := by
    have hnat : (6595548131 : ℕ)^73*50000000000000^57 ≤ 29341634783763^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6595548131 10000000000 29341634783763 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(24476271/80000000 : ℝ), (-1388118651/5000000000 : ℝ), (-6595548131/10000000000 : ℝ)] ![(5485520034343/25000000000000 : ℝ), (19374650288079/100000000000000 : ℝ), (29341634783763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(24476271/80000000 : ℝ)|^73 ≤ (5485520034343/25000000000000 : ℝ)^57
        have hw : |(24476271/80000000 : ℝ)|=(24476271/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1388118651/5000000000 : ℝ)|^73 ≤ (19374650288079/100000000000000 : ℝ)^57
        have hw : |(-1388118651/5000000000 : ℝ)|=(1388118651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6595548131/10000000000 : ℝ)|^73 ≤ (29341634783763/50000000000000 : ℝ)^57
        have hw : |(-6595548131/10000000000 : ℝ)|=(6595548131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5182468363/10000000000 : ℝ)*x 0 + (1222161879/2000000000 : ℝ)*x 1 + (76039217/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5182468363/10000000000 : ℝ)^73 ≤ (43092987074363/100000000000000 : ℝ)^57 := by
    have hnat : (5182468363 : ℕ)^73*100000000000000^57 ≤ 43092987074363^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182468363 10000000000 43092987074363 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1222161879/2000000000 : ℝ)^73 ≤ (13304430424627/25000000000000 : ℝ)^57 := by
    have hnat : (1222161879 : ℕ)^73*25000000000000^57 ≤ 13304430424627^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222161879 2000000000 13304430424627 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76039217/1000000000 : ℝ)^73 ≤ (1844645606711/50000000000000 : ℝ)^57 := by
    have hnat : (76039217 : ℕ)^73*50000000000000^57 ≤ 1844645606711^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76039217 1000000000 1844645606711 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5182468363/10000000000 : ℝ), (1222161879/2000000000 : ℝ), (76039217/1000000000 : ℝ)] ![(43092987074363/100000000000000 : ℝ), (13304430424627/25000000000000 : ℝ), (1844645606711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5182468363/10000000000 : ℝ)|^73 ≤ (43092987074363/100000000000000 : ℝ)^57
        have hw : |(5182468363/10000000000 : ℝ)|=(5182468363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1222161879/2000000000 : ℝ)|^73 ≤ (13304430424627/25000000000000 : ℝ)^57
        have hw : |(1222161879/2000000000 : ℝ)|=(1222161879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(76039217/1000000000 : ℝ)|^73 ≤ (1844645606711/50000000000000 : ℝ)^57
        have hw : |(76039217/1000000000 : ℝ)|=(76039217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_12 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5182468363/10000000000 : ℝ)*x 0 + (1222161879/2000000000 : ℝ)*x 1 + (-76039217/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5182468363/10000000000 : ℝ)^73 ≤ (43092987074363/100000000000000 : ℝ)^57 := by
    have hnat : (5182468363 : ℕ)^73*100000000000000^57 ≤ 43092987074363^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182468363 10000000000 43092987074363 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1222161879/2000000000 : ℝ)^73 ≤ (13304430424627/25000000000000 : ℝ)^57 := by
    have hnat : (1222161879 : ℕ)^73*25000000000000^57 ≤ 13304430424627^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222161879 2000000000 13304430424627 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76039217/1000000000 : ℝ)^73 ≤ (1844645606711/50000000000000 : ℝ)^57 := by
    have hnat : (76039217 : ℕ)^73*50000000000000^57 ≤ 1844645606711^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76039217 1000000000 1844645606711 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5182468363/10000000000 : ℝ), (1222161879/2000000000 : ℝ), (-76039217/1000000000 : ℝ)] ![(43092987074363/100000000000000 : ℝ), (13304430424627/25000000000000 : ℝ), (1844645606711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5182468363/10000000000 : ℝ)|^73 ≤ (43092987074363/100000000000000 : ℝ)^57
        have hw : |(5182468363/10000000000 : ℝ)|=(5182468363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1222161879/2000000000 : ℝ)|^73 ≤ (13304430424627/25000000000000 : ℝ)^57
        have hw : |(1222161879/2000000000 : ℝ)|=(1222161879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-76039217/1000000000 : ℝ)|^73 ≤ (1844645606711/50000000000000 : ℝ)^57
        have hw : |(-76039217/1000000000 : ℝ)|=(76039217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1388118621/5000000000 : ℝ)*x 0 + (122381353/400000000 : ℝ)*x 1 + (-3297774109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1388118621/5000000000 : ℝ)^73 ≤ (19374649751817/100000000000000 : ℝ)^57 := by
    have hnat : (1388118621 : ℕ)^73*100000000000000^57 ≤ 19374649751817^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388118621 5000000000 19374649751817 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122381353/400000000 : ℝ)^73 ≤ (21942079678131/100000000000000 : ℝ)^57 := by
    have hnat : (122381353 : ℕ)^73*100000000000000^57 ≤ 21942079678131^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122381353 400000000 21942079678131 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3297774109/5000000000 : ℝ)^73 ≤ (14670817639721/25000000000000 : ℝ)^57 := by
    have hnat : (3297774109 : ℕ)^73*25000000000000^57 ≤ 14670817639721^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3297774109 5000000000 14670817639721 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1388118621/5000000000 : ℝ), (122381353/400000000 : ℝ), (-3297774109/5000000000 : ℝ)] ![(19374649751817/100000000000000 : ℝ), (21942079678131/100000000000000 : ℝ), (14670817639721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1388118621/5000000000 : ℝ)|^73 ≤ (19374649751817/100000000000000 : ℝ)^57
        have hw : |(-1388118621/5000000000 : ℝ)|=(1388118621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(122381353/400000000 : ℝ)|^73 ≤ (21942079678131/100000000000000 : ℝ)^57
        have hw : |(122381353/400000000 : ℝ)|=(122381353/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3297774109/5000000000 : ℝ)|^73 ≤ (14670817639721/25000000000000 : ℝ)^57
        have hw : |(-3297774109/5000000000 : ℝ)|=(3297774109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1388118621/5000000000 : ℝ)*x 0 + (-122381353/400000000 : ℝ)*x 1 + (-3297774109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1388118621/5000000000 : ℝ)^73 ≤ (19374649751817/100000000000000 : ℝ)^57 := by
    have hnat : (1388118621 : ℕ)^73*100000000000000^57 ≤ 19374649751817^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388118621 5000000000 19374649751817 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122381353/400000000 : ℝ)^73 ≤ (21942079678131/100000000000000 : ℝ)^57 := by
    have hnat : (122381353 : ℕ)^73*100000000000000^57 ≤ 21942079678131^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122381353 400000000 21942079678131 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3297774109/5000000000 : ℝ)^73 ≤ (14670817639721/25000000000000 : ℝ)^57 := by
    have hnat : (3297774109 : ℕ)^73*25000000000000^57 ≤ 14670817639721^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3297774109 5000000000 14670817639721 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1388118621/5000000000 : ℝ), (-122381353/400000000 : ℝ), (-3297774109/5000000000 : ℝ)] ![(19374649751817/100000000000000 : ℝ), (21942079678131/100000000000000 : ℝ), (14670817639721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1388118621/5000000000 : ℝ)|^73 ≤ (19374649751817/100000000000000 : ℝ)^57
        have hw : |(1388118621/5000000000 : ℝ)|=(1388118621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122381353/400000000 : ℝ)|^73 ≤ (21942079678131/100000000000000 : ℝ)^57
        have hw : |(-122381353/400000000 : ℝ)|=(122381353/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3297774109/5000000000 : ℝ)|^73 ≤ (14670817639721/25000000000000 : ℝ)^57
        have hw : |(-3297774109/5000000000 : ℝ)|=(3297774109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3055404761/5000000000 : ℝ)*x 0 + (161952131/312500000 : ℝ)*x 1 + (190098059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3055404761/5000000000 : ℝ)^73 ≤ (6652215389373/12500000000000 : ℝ)^57 := by
    have hnat : (3055404761 : ℕ)^73*12500000000000^57 ≤ 6652215389373^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3055404761 5000000000 6652215389373 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161952131/312500000 : ℝ)^73 ≤ (8618597050669/20000000000000 : ℝ)^57 := by
    have hnat : (161952131 : ℕ)^73*20000000000000^57 ≤ 8618597050669^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161952131 312500000 8618597050669 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190098059/2500000000 : ℝ)^73 ≤ (3689291623529/100000000000000 : ℝ)^57 := by
    have hnat : (190098059 : ℕ)^73*100000000000000^57 ≤ 3689291623529^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190098059 2500000000 3689291623529 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3055404761/5000000000 : ℝ), (161952131/312500000 : ℝ), (190098059/2500000000 : ℝ)] ![(6652215389373/12500000000000 : ℝ), (8618597050669/20000000000000 : ℝ), (3689291623529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3055404761/5000000000 : ℝ)|^73 ≤ (6652215389373/12500000000000 : ℝ)^57
        have hw : |(3055404761/5000000000 : ℝ)|=(3055404761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161952131/312500000 : ℝ)|^73 ≤ (8618597050669/20000000000000 : ℝ)^57
        have hw : |(161952131/312500000 : ℝ)|=(161952131/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190098059/2500000000 : ℝ)|^73 ≤ (3689291623529/100000000000000 : ℝ)^57
        have hw : |(190098059/2500000000 : ℝ)|=(190098059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_18 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3055404761/5000000000 : ℝ)*x 0 + (161952131/312500000 : ℝ)*x 1 + (-190098059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3055404761/5000000000 : ℝ)^73 ≤ (6652215389373/12500000000000 : ℝ)^57 := by
    have hnat : (3055404761 : ℕ)^73*12500000000000^57 ≤ 6652215389373^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3055404761 5000000000 6652215389373 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161952131/312500000 : ℝ)^73 ≤ (8618597050669/20000000000000 : ℝ)^57 := by
    have hnat : (161952131 : ℕ)^73*20000000000000^57 ≤ 8618597050669^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161952131 312500000 8618597050669 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190098059/2500000000 : ℝ)^73 ≤ (3689291623529/100000000000000 : ℝ)^57 := by
    have hnat : (190098059 : ℕ)^73*100000000000000^57 ≤ 3689291623529^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190098059 2500000000 3689291623529 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3055404761/5000000000 : ℝ), (161952131/312500000 : ℝ), (-190098059/2500000000 : ℝ)] ![(6652215389373/12500000000000 : ℝ), (8618597050669/20000000000000 : ℝ), (3689291623529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3055404761/5000000000 : ℝ)|^73 ≤ (6652215389373/12500000000000 : ℝ)^57
        have hw : |(3055404761/5000000000 : ℝ)|=(3055404761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161952131/312500000 : ℝ)|^73 ≤ (8618597050669/20000000000000 : ℝ)^57
        have hw : |(161952131/312500000 : ℝ)|=(161952131/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-190098059/2500000000 : ℝ)|^73 ≤ (3689291623529/100000000000000 : ℝ)^57
        have hw : |(-190098059/2500000000 : ℝ)|=(190098059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_19 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-108017499/312500000 : ℝ)*x 0 + (3184817589/10000000000 : ℝ)*x 1 + (-5933434549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108017499/312500000 : ℝ)^73 ≤ (6413287257959/25000000000000 : ℝ)^57 := by
    have hnat : (108017499 : ℕ)^73*25000000000000^57 ≤ 6413287257959^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108017499 312500000 6413287257959 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3184817589/10000000000 : ℝ)^73 ≤ (4619867541153/20000000000000 : ℝ)^57 := by
    have hnat : (3184817589 : ℕ)^73*20000000000000^57 ≤ 4619867541153^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3184817589 10000000000 4619867541153 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5933434549/10000000000 : ℝ)^73 ≤ (51247513247539/100000000000000 : ℝ)^57 := by
    have hnat : (5933434549 : ℕ)^73*100000000000000^57 ≤ 51247513247539^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5933434549 10000000000 51247513247539 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108017499/312500000 : ℝ), (3184817589/10000000000 : ℝ), (-5933434549/10000000000 : ℝ)] ![(6413287257959/25000000000000 : ℝ), (4619867541153/20000000000000 : ℝ), (51247513247539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108017499/312500000 : ℝ)|^73 ≤ (6413287257959/25000000000000 : ℝ)^57
        have hw : |(-108017499/312500000 : ℝ)|=(108017499/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3184817589/10000000000 : ℝ)|^73 ≤ (4619867541153/20000000000000 : ℝ)^57
        have hw : |(3184817589/10000000000 : ℝ)|=(3184817589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5933434549/10000000000 : ℝ)|^73 ≤ (51247513247539/100000000000000 : ℝ)^57
        have hw : |(-5933434549/10000000000 : ℝ)|=(5933434549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3041891601/10000000000 : ℝ)*x 0 + (-3313637787/10000000000 : ℝ)*x 1 + (-3086715703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3041891601/10000000000 : ℝ)^73 ≤ (680630324751/3125000000000 : ℝ)^57 := by
    have hnat : (3041891601 : ℕ)^73*3125000000000^57 ≤ 680630324751^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3041891601 10000000000 680630324751 3125000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3313637787/10000000000 : ℝ)^73 ≤ (12151330125387/50000000000000 : ℝ)^57 := by
    have hnat : (3313637787 : ℕ)^73*50000000000000^57 ≤ 12151330125387^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3313637787 10000000000 12151330125387 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3086715703/5000000000 : ℝ)^73 ≤ (26958584675859/50000000000000 : ℝ)^57 := by
    have hnat : (3086715703 : ℕ)^73*50000000000000^57 ≤ 26958584675859^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3086715703 5000000000 26958584675859 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3041891601/10000000000 : ℝ), (-3313637787/10000000000 : ℝ), (-3086715703/5000000000 : ℝ)] ![(680630324751/3125000000000 : ℝ), (12151330125387/50000000000000 : ℝ), (26958584675859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3041891601/10000000000 : ℝ)|^73 ≤ (680630324751/3125000000000 : ℝ)^57
        have hw : |(3041891601/10000000000 : ℝ)|=(3041891601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3313637787/10000000000 : ℝ)|^73 ≤ (12151330125387/50000000000000 : ℝ)^57
        have hw : |(-3313637787/10000000000 : ℝ)|=(3313637787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3086715703/5000000000 : ℝ)|^73 ≤ (26958584675859/50000000000000 : ℝ)^57
        have hw : |(-3086715703/5000000000 : ℝ)|=(3086715703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2724102241/5000000000 : ℝ)*x 0 + (1362051541/2500000000 : ℝ)*x 1 + (87940067/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2724102241/5000000000 : ℝ)^73 ≤ (45942991018649/100000000000000 : ℝ)^57 := by
    have hnat : (2724102241 : ℕ)^73*100000000000000^57 ≤ 45942991018649^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724102241 5000000000 45942991018649 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362051541/2500000000 : ℝ)^73 ≤ (11485752295959/25000000000000 : ℝ)^57 := by
    have hnat : (1362051541 : ℕ)^73*25000000000000^57 ≤ 11485752295959^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362051541 2500000000 11485752295959 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87940067/625000000 : ℝ)^73 ≤ (1622799958697/20000000000000 : ℝ)^57 := by
    have hnat : (87940067 : ℕ)^73*20000000000000^57 ≤ 1622799958697^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87940067 625000000 1622799958697 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2724102241/5000000000 : ℝ), (1362051541/2500000000 : ℝ), (87940067/625000000 : ℝ)] ![(45942991018649/100000000000000 : ℝ), (11485752295959/25000000000000 : ℝ), (1622799958697/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2724102241/5000000000 : ℝ)|^73 ≤ (45942991018649/100000000000000 : ℝ)^57
        have hw : |(2724102241/5000000000 : ℝ)|=(2724102241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362051541/2500000000 : ℝ)|^73 ≤ (11485752295959/25000000000000 : ℝ)^57
        have hw : |(1362051541/2500000000 : ℝ)|=(1362051541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(87940067/625000000 : ℝ)|^73 ≤ (1622799958697/20000000000000 : ℝ)^57
        have hw : |(87940067/625000000 : ℝ)|=(87940067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312056_s1_s1_25 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5160897457/10000000000 : ℝ)*x 0 + (2844539211/5000000000 : ℝ)*x 1 + (-734624091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5160897457/10000000000 : ℝ)^73 ≤ (42863408002343/100000000000000 : ℝ)^57 := by
    have hnat : (5160897457 : ℕ)^73*100000000000000^57 ≤ 42863408002343^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5160897457 10000000000 42863408002343 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2844539211/5000000000 : ℝ)^73 ≤ (971206886957/2000000000000 : ℝ)^57 := by
    have hnat : (2844539211 : ℕ)^73*2000000000000^57 ≤ 971206886957^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2844539211 5000000000 971206886957 2000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (734624091/5000000000 : ℝ)^73 ≤ (1715249527673/20000000000000 : ℝ)^57 := by
    have hnat : (734624091 : ℕ)^73*20000000000000^57 ≤ 1715249527673^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734624091 5000000000 1715249527673 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5160897457/10000000000 : ℝ), (2844539211/5000000000 : ℝ), (-734624091/5000000000 : ℝ)] ![(42863408002343/100000000000000 : ℝ), (971206886957/2000000000000 : ℝ), (1715249527673/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5160897457/10000000000 : ℝ)|^73 ≤ (42863408002343/100000000000000 : ℝ)^57
        have hw : |(5160897457/10000000000 : ℝ)|=(5160897457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2844539211/5000000000 : ℝ)|^73 ≤ (971206886957/2000000000000 : ℝ)^57
        have hw : |(2844539211/5000000000 : ℝ)|=(2844539211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-734624091/5000000000 : ℝ)|^73 ≤ (1715249527673/20000000000000 : ℝ)^57
        have hw : |(-734624091/5000000000 : ℝ)|=(734624091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312056_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((79957/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79957/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79957/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79957/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-6587/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-6587/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20053/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20053/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20053/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20053/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1973/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1973/100000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (79957/100000 : ℝ) ^ (9/2 : ℝ) ≤ (36547208366675052041/100000000000000000000 : ℝ) := by
    have hpowers : (79957/100000 : ℝ)^9 ≤ (36547208366675052041/100000000000000000000 : ℝ)^2 := by
      have hnat : (79957 : ℕ)^9*100000000000000000000^2 ≤ 36547208366675052041^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79957 100000 36547208366675052041 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79957/100000 : ℝ)) (X := (36547208366675052041/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (136547208366675052041/100000000000000000000 : ℝ) ≤ (214334876876513/200000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (136547208366675052041/100000000000000000000 : ℝ)^2 ≤ (214334876876513/200000000000000 : ℝ)^9 := by
      have hnat : (136547208366675052041 : ℕ)^2*200000000000000^9 ≤ 214334876876513^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        136547208366675052041 100000000000000000000 214334876876513 200000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (214334876876513/200000000000000 : ℝ)) (X := (136547208366675052041/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (86547208366675052041/50000000000000000000 : ℝ) ≤ (5648352541835031/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (86547208366675052041/50000000000000000000 : ℝ)^2 ≤ (5648352541835031/5000000000000000 : ℝ)^9 := by
      have hnat : (86547208366675052041 : ℕ)^2*5000000000000000^9 ≤ 5648352541835031^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86547208366675052041 50000000000000000000 5648352541835031 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5648352541835031/5000000000000000 : ℝ)) (X := (86547208366675052041/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(14334876876513/159914000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(144990309961103/1998925000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (79957/100000 : ℝ)) (alpha := (14334876876513/159914000000000 : ℝ)) (beta := (144990309961103/1998925000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (79957/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(14334876876513/159914000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(144990309961103/1998925000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (79957/100000 : ℝ) ^ (9/2 : ℝ) ≤ (36547208366675052041/100000000000000000000 : ℝ) := by
    have hpowers : (79957/100000 : ℝ)^9 ≤ (36547208366675052041/100000000000000000000 : ℝ)^2 := by
      have hnat : (79957 : ℕ)^9*100000000000000000000^2 ≤ 36547208366675052041^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79957 100000 36547208366675052041 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79957/100000 : ℝ)) (X := (36547208366675052041/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (136547208366675052041/100000000000000000000 : ℝ) ≤ (214334876876513/200000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (136547208366675052041/100000000000000000000 : ℝ)^2 ≤ (214334876876513/200000000000000 : ℝ)^9 := by
      have hnat : (136547208366675052041 : ℕ)^2*200000000000000^9 ≤ 214334876876513^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        136547208366675052041 100000000000000000000 214334876876513 200000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (214334876876513/200000000000000 : ℝ)) (X := (136547208366675052041/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (86547208366675052041/50000000000000000000 : ℝ) ≤ (5648352541835031/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (86547208366675052041/50000000000000000000 : ℝ)^2 ≤ (5648352541835031/5000000000000000 : ℝ)^9 := by
      have hnat : (86547208366675052041 : ℕ)^2*5000000000000000^9 ≤ 5648352541835031^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86547208366675052041 50000000000000000000 5648352541835031 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5648352541835031/5000000000000000 : ℝ)) (X := (86547208366675052041/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(14334876876513/159914000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(144990309961103/1998925000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (79957/100000 : ℝ)) (alpha := (14334876876513/159914000000000 : ℝ)) (beta := (144990309961103/1998925000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (79957/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(14334876876513/159914000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(144990309961103/1998925000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (6587/25000 : ℝ) ^ (9/2 : ℝ) ≤ (247379920981883843/100000000000000000000 : ℝ) := by
    have hpowers : (6587/25000 : ℝ)^9 ≤ (247379920981883843/100000000000000000000 : ℝ)^2 := by
      have hnat : (6587 : ℕ)^9*100000000000000000000^2 ≤ 247379920981883843^2*25000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6587 25000 247379920981883843 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6587/25000 : ℝ)) (X := (247379920981883843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100247379920981883843/100000000000000000000 : ℝ) ≤ (10005492050702421/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (100247379920981883843/100000000000000000000 : ℝ)^2 ≤ (10005492050702421/10000000000000000 : ℝ)^9 := by
      have hnat : (100247379920981883843 : ℕ)^2*10000000000000000^9 ≤ 10005492050702421^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100247379920981883843 100000000000000000000 10005492050702421 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005492050702421/10000000000000000 : ℝ)) (X := (100247379920981883843/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50247379920981883843/50000000000000000000 : ℝ) ≤ (2002194714101457/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (50247379920981883843/50000000000000000000 : ℝ)^2 ≤ (2002194714101457/2000000000000000 : ℝ)^9 := by
      have hnat : (50247379920981883843 : ℕ)^2*2000000000000000^9 ≤ 2002194714101457^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50247379920981883843 50000000000000000000 2002194714101457 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002194714101457/2000000000000000 : ℝ)) (X := (50247379920981883843/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(5492050702421/2634800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(85648746951/41168750000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (6587/25000 : ℝ)) (alpha := (5492050702421/2634800000000000 : ℝ)) (beta := (85648746951/41168750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (6587/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(5492050702421/2634800000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(85648746951/41168750000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((1618307767/5000000000 : ℝ)*X 1 0+(-809153891/2500000000 : ℝ)*X 1 1+(-1519158417/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1358344323/2500000000 : ℝ)*X 2 0+(5433377319/10000000000 : ℝ)*X 2 1+(1450206127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-24476271/80000000 : ℝ)*X 0 0+(1388118651/5000000000 : ℝ)*X 0 1+(-6595548131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((24476271/80000000 : ℝ)*X 1 0+(-1388118651/5000000000 : ℝ)*X 1 1+(-6595548131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5182468363/10000000000 : ℝ)*X 2 0+(1222161879/2000000000 : ℝ)*X 2 1+(76039217/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((5182468363/10000000000 : ℝ)*X 0 0+(1222161879/2000000000 : ℝ)*X 0 1+(-76039217/1000000000 : ℝ)*X 0 2+(5182468363/10000000000 : ℝ)*X 1 0+(1222161879/2000000000 : ℝ)*X 1 1+(-76039217/1000000000 : ℝ)*X 1 2+(5182468363/10000000000 : ℝ)*X 2 0+(1222161879/2000000000 : ℝ)*X 2 1+(-76039217/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-1388118621/5000000000 : ℝ)*X 0 0+(122381353/400000000 : ℝ)*X 0 1+(-3297774109/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((1388118621/5000000000 : ℝ)*X 1 0+(-122381353/400000000 : ℝ)*X 1 1+(-3297774109/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3055404761/5000000000 : ℝ)*X 2 0+(161952131/312500000 : ℝ)*X 2 1+(190098059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((3055404761/5000000000 : ℝ)*X 0 0+(161952131/312500000 : ℝ)*X 0 1+(-190098059/2500000000 : ℝ)*X 0 2+(3055404761/5000000000 : ℝ)*X 1 0+(161952131/312500000 : ℝ)*X 1 1+(-190098059/2500000000 : ℝ)*X 1 2+(3055404761/5000000000 : ℝ)*X 2 0+(161952131/312500000 : ℝ)*X 2 1+(-190098059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-108017499/312500000 : ℝ)*X 0 0+(3184817589/10000000000 : ℝ)*X 0 1+(-5933434549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3041891601/10000000000 : ℝ)*X 1 0+(-3313637787/10000000000 : ℝ)*X 1 1+(-3086715703/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((2724102241/5000000000 : ℝ)*X 2 0+(1362051541/2500000000 : ℝ)*X 2 1+(87940067/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((5160897457/10000000000 : ℝ)*X 0 0+(2844539211/5000000000 : ℝ)*X 0 1+(-734624091/5000000000 : ℝ)*X 0 2+(5160897457/10000000000 : ℝ)*X 1 0+(2844539211/5000000000 : ℝ)*X 1 1+(-734624091/5000000000 : ℝ)*X 1 2+(5160897457/10000000000 : ℝ)*X 2 0+(2844539211/5000000000 : ℝ)*X 2 1+(-734624091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312056_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((20053/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20053/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (319859686433301932095377/22387960000000000000000000000 : ℝ) := by norm_num
    linear_combination (2086694690677/500000000000 : ℝ)*(base5) + (3800609/250000000000 : ℝ)*(base39) + (4049034483969/500000000000 : ℝ)*(base59) + (3714877841459/1000000000000 : ℝ)*(base60) + (301844441083/40000000000 : ℝ)*(major_s1_0) + (301844441083/40000000000 : ℝ)*(major_s1_1) + (301844441083/40000000000 : ℝ)*(major_s1_2) + (298477/10000000000 : ℝ)*(sp_s1_1) + (5285616345379/500000000000 : ℝ)*(sp_s1_7) + (10570879387613/1000000000000 : ℝ)*(sp_s1_8) + (921538879507/62500000000 : ℝ)*(sp_s1_9) + (4341048809/12500000000 : ℝ)*(sp_s1_12) + (161727723/500000000000 : ℝ)*(sp_s1_20) + (31131493/100000000000 : ℝ)*(sp_s1_25) + (1130246150251/250000000000 : ℝ)*(f.failure) + (5285616345379/500000000000 : ℝ)*(f.sum) + (422402919502681/8955184000000000000000000000 : ℝ)*base63 + (5639839131/8750000000000000000000 : ℝ)*base65 + (58697035993963/99946250000000000000000000 : ℝ)*base66 + (146380363289/560000000000000000000000 : ℝ)*base69 + (2562536037961517/5596990000000000000000000000 : ℝ)*base71 + (316347345395013/799570000000000000000000000 : ℝ)*base73 + (652053557125493/799570000000000000000000000 : ℝ)*base75 + (28214505686507/31982800000000000000000000 : ℝ)*base77 + (2005106765727/4997312500000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (29837/25000000000000000 : ℝ)*base86 + (29837/25000000000000000 : ℝ)*base88 + (29837/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20053/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20053/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (70987454379122908732341/5596990000000000000000000000 : ℝ) := by norm_num
    linear_combination (2086525233761/500000000000 : ℝ)*(base5) + (16425597/1000000000000 : ℝ)*(base21) + (1/500000000000 : ℝ)*(base39) + (2024404291243/250000000000 : ℝ)*(base59) + (4382911164941/1000000000000 : ℝ)*(base60) + (377300616999/50000000000 : ℝ)*(major_s1_0) + (377300616999/50000000000 : ℝ)*(major_s1_1) + (377300616999/50000000000 : ℝ)*(major_s1_2) + (20541243/200000000000 : ℝ)*(sp_s1_2) + (97221963/500000000000 : ℝ)*(sp_s1_8) + (1321386872013/125000000000 : ℝ)*(sp_s1_13) + (5285450266089/500000000000 : ℝ)*(sp_s1_14) + (7372013155907/500000000000 : ℝ)*(sp_s1_15) + (347875008613/1000000000000 : ℝ)*(sp_s1_18) + (2260462738067/500000000000 : ℝ)*(f.failure) + (1321386872013/125000000000 : ℝ)*(f.sum) + (3143887288928676973/10533535180000000000000000000000 : ℝ)*base63 + (453288364843/1646750000000000000000000 : ℝ)*base64 + (8044509217111/199892500000000000000000000 : ℝ)*base66 + (46371079889133/131740000000000000000000000 : ℝ)*base69 + (928409208721553961/2633383795000000000000000000000 : ℝ)*base70 + (107179826449361/399785000000000000000000000 : ℝ)*base73 + (165553165758659/399785000000000000000000000 : ℝ)*base74 + (236414847161833/799570000000000000000000000 : ℝ)*base76 + (49614390441643/159914000000000000000000000 : ℝ)*base79 + (22829/50000000000000000 : ℝ)*base86 + (22829/50000000000000000 : ℝ)*base88 + (22829/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1973/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1973/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4385768715360029721009/999462500000000000000000000 : ℝ) := by norm_num
    linear_combination (104780431019/100000000000 : ℝ)*(base5) + (1544069/1000000000000 : ℝ)*(base16) + (8982309033/100000000000 : ℝ)*(base39) + (37155349601/250000000000 : ℝ)*(base49) + (964990862981/1000000000000 : ℝ)*(base59) + (1748921608267/1000000000000 : ℝ)*(major_s1_0) + (1748921608267/1000000000000 : ℝ)*(major_s1_1) + (1748921608267/1000000000000 : ℝ)*(major_s1_2) + (89599761/1000000000000 : ℝ)*(sp_s1_1) + (10615143/500000000000 : ℝ)*(sp_s1_9) + (13783849/500000000000 : ℝ)*(sp_s1_15) + (153127340227/62500000000 : ℝ)*(sp_s1_19) + (2449946299801/1000000000000 : ℝ)*(sp_s1_20) + (1748896477919/500000000000 : ℝ)*(sp_s1_21) + (104780431019/100000000000 : ℝ)*(f.failure) + (153127340227/62500000000 : ℝ)*(f.sum) + (9307456545852434261/210670703600000000000000000000000 : ℝ)*base63 + (1309779809473/41168750000000000000000000 : ℝ)*base65 + (308684366326941/1998925000000000000000000000 : ℝ)*base67 + (115651984551407/2634800000000000000000000000 : ℝ)*base68 + (2655620375174925141/13166918975000000000000000000000 : ℝ)*base70 + (111711268203223/999462500000000000000000000 : ℝ)*base73 + (13184171081091/31982800000000000000000000 : ℝ)*base74 + (324827352245171/799570000000000000000000000 : ℝ)*base76 + (11938282572879/249865625000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (4347/10000000000000000 : ℝ)*base87 + (4347/10000000000000000 : ℝ)*base89 + (4347/10000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((79957/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79957/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79957/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79957/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-6587/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-6587/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20053/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20053/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20053/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20053/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1973/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1973/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312056_s1 p hpa hpb X hX hprev0

#print axioms solution
