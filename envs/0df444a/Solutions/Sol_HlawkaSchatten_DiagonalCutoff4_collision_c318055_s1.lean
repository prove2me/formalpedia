-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c318055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:23:26.393144+00:00
-- url     : https://prove2.me/submissions/187d0e94-71a3-464a-8e01-45d15219be7c

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
theorem collision_support_c318055_s1_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-393817959/2500000000 : ℝ)*x 0 + (5725958893/10000000000 : ℝ)*x 1 + (4858728809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393817959/2500000000 : ℝ)^79 ≤ (2462914281133/25000000000000 : ℝ)^63 := by
    have hnat : (393817959 : ℕ)^79*25000000000000^63 ≤ 2462914281133^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393817959 2500000000 2462914281133 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5725958893/10000000000 : ℝ)^79 ≤ (24849597973241/50000000000000 : ℝ)^63 := by
    have hnat : (5725958893 : ℕ)^79*50000000000000^63 ≤ 24849597973241^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5725958893 10000000000 24849597973241 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4858728809/10000000000 : ℝ)^79 ≤ (40449146918091/100000000000000 : ℝ)^63 := by
    have hnat : (4858728809 : ℕ)^79*100000000000000^63 ≤ 40449146918091^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4858728809 10000000000 40449146918091 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393817959/2500000000 : ℝ), (5725958893/10000000000 : ℝ), (4858728809/10000000000 : ℝ)] ![(2462914281133/25000000000000 : ℝ), (24849597973241/50000000000000 : ℝ), (40449146918091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393817959/2500000000 : ℝ)|^79 ≤ (2462914281133/25000000000000 : ℝ)^63
        have hw : |(-393817959/2500000000 : ℝ)|=(393817959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5725958893/10000000000 : ℝ)|^79 ≤ (24849597973241/50000000000000 : ℝ)^63
        have hw : |(5725958893/10000000000 : ℝ)|=(5725958893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4858728809/10000000000 : ℝ)|^79 ≤ (40449146918091/100000000000000 : ℝ)^63
        have hw : |(4858728809/10000000000 : ℝ)|=(4858728809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4808517569/10000000000 : ℝ)*x 0 + (-601498959/10000000000 : ℝ)*x 1 + (3199397523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4808517569/10000000000 : ℝ)^79 ≤ (7985132820249/20000000000000 : ℝ)^63 := by
    have hnat : (4808517569 : ℕ)^79*20000000000000^63 ≤ 7985132820249^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4808517569 10000000000 7985132820249 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601498959/10000000000 : ℝ)^79 ≤ (736443278463/25000000000000 : ℝ)^63 := by
    have hnat : (601498959 : ℕ)^79*25000000000000^63 ≤ 736443278463^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601498959 10000000000 736443278463 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3199397523/5000000000 : ℝ)^79 ≤ (3570535173043/6250000000000 : ℝ)^63 := by
    have hnat : (3199397523 : ℕ)^79*6250000000000^63 ≤ 3570535173043^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3199397523 5000000000 3570535173043 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4808517569/10000000000 : ℝ), (-601498959/10000000000 : ℝ), (3199397523/5000000000 : ℝ)] ![(7985132820249/20000000000000 : ℝ), (736443278463/25000000000000 : ℝ), (3570535173043/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4808517569/10000000000 : ℝ)|^79 ≤ (7985132820249/20000000000000 : ℝ)^63
        have hw : |(4808517569/10000000000 : ℝ)|=(4808517569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-601498959/10000000000 : ℝ)|^79 ≤ (736443278463/25000000000000 : ℝ)^63
        have hw : |(-601498959/10000000000 : ℝ)|=(601498959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3199397523/5000000000 : ℝ)|^79 ≤ (3570535173043/6250000000000 : ℝ)^63
        have hw : |(3199397523/5000000000 : ℝ)|=(3199397523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1599761901/2500000000 : ℝ)*x 0 + (3767918237/10000000000 : ℝ)*x 1 + (252582301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1599761901/2500000000 : ℝ)^79 ≤ (28565695141939/50000000000000 : ℝ)^63 := by
    have hnat : (1599761901 : ℕ)^79*50000000000000^63 ≤ 28565695141939^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1599761901 2500000000 28565695141939 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3767918237/10000000000 : ℝ)^79 ≤ (1837912019617/6250000000000 : ℝ)^63 := by
    have hnat : (3767918237 : ℕ)^79*6250000000000^63 ≤ 1837912019617^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3767918237 10000000000 1837912019617 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252582301/1250000000 : ℝ)^79 ≤ (13462017393027/100000000000000 : ℝ)^63 := by
    have hnat : (252582301 : ℕ)^79*100000000000000^63 ≤ 13462017393027^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252582301 1250000000 13462017393027 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1599761901/2500000000 : ℝ), (3767918237/10000000000 : ℝ), (252582301/1250000000 : ℝ)] ![(28565695141939/50000000000000 : ℝ), (1837912019617/6250000000000 : ℝ), (13462017393027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1599761901/2500000000 : ℝ)|^79 ≤ (28565695141939/50000000000000 : ℝ)^63
        have hw : |(1599761901/2500000000 : ℝ)|=(1599761901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3767918237/10000000000 : ℝ)|^79 ≤ (1837912019617/6250000000000 : ℝ)^63
        have hw : |(3767918237/10000000000 : ℝ)|=(3767918237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252582301/1250000000 : ℝ)|^79 ≤ (13462017393027/100000000000000 : ℝ)^63
        have hw : |(252582301/1250000000 : ℝ)|=(252582301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-726317793/5000000000 : ℝ)*x 0 + (4388342853/10000000000 : ℝ)*x 1 + (6252892623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (726317793/5000000000 : ℝ)^79 ≤ (8899612017433/100000000000000 : ℝ)^63 := by
    have hnat : (726317793 : ℕ)^79*100000000000000^63 ≤ 8899612017433^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726317793 5000000000 8899612017433 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4388342853/10000000000 : ℝ)^79 ≤ (3560051219123/10000000000000 : ℝ)^63 := by
    have hnat : (4388342853 : ℕ)^79*10000000000000^63 ≤ 3560051219123^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388342853 10000000000 3560051219123 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6252892623/10000000000 : ℝ)^79 ≤ (2774993789107/5000000000000 : ℝ)^63 := by
    have hnat : (6252892623 : ℕ)^79*5000000000000^63 ≤ 2774993789107^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6252892623 10000000000 2774993789107 5000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-726317793/5000000000 : ℝ), (4388342853/10000000000 : ℝ), (6252892623/10000000000 : ℝ)] ![(8899612017433/100000000000000 : ℝ), (3560051219123/10000000000000 : ℝ), (2774993789107/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-726317793/5000000000 : ℝ)|^79 ≤ (8899612017433/100000000000000 : ℝ)^63
        have hw : |(-726317793/5000000000 : ℝ)|=(726317793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4388342853/10000000000 : ℝ)|^79 ≤ (3560051219123/10000000000000 : ℝ)^63
        have hw : |(4388342853/10000000000 : ℝ)|=(4388342853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6252892623/10000000000 : ℝ)|^79 ≤ (2774993789107/5000000000000 : ℝ)^63
        have hw : |(6252892623/10000000000 : ℝ)|=(6252892623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4181284069/10000000000 : ℝ)*x 0 + (-5268647/5000000000 : ℝ)*x 1 + (7220605951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4181284069/10000000000 : ℝ)^79 ≤ (16753453983723/50000000000000 : ℝ)^63 := by
    have hnat : (4181284069 : ℕ)^79*50000000000000^63 ≤ 16753453983723^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4181284069 10000000000 16753453983723 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5268647/5000000000 : ℝ)^79 ≤ (3695105141/20000000000000 : ℝ)^63 := by
    have hnat : (5268647 : ℕ)^79*20000000000000^63 ≤ 3695105141^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268647 5000000000 3695105141 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7220605951/10000000000 : ℝ)^79 ≤ (33237308248997/50000000000000 : ℝ)^63 := by
    have hnat : (7220605951 : ℕ)^79*50000000000000^63 ≤ 33237308248997^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7220605951 10000000000 33237308248997 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4181284069/10000000000 : ℝ), (-5268647/5000000000 : ℝ), (7220605951/10000000000 : ℝ)] ![(16753453983723/50000000000000 : ℝ), (3695105141/20000000000000 : ℝ), (33237308248997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4181284069/10000000000 : ℝ)|^79 ≤ (16753453983723/50000000000000 : ℝ)^63
        have hw : |(4181284069/10000000000 : ℝ)|=(4181284069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5268647/5000000000 : ℝ)|^79 ≤ (3695105141/20000000000000 : ℝ)^63
        have hw : |(-5268647/5000000000 : ℝ)|=(5268647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7220605951/10000000000 : ℝ)|^79 ≤ (33237308248997/50000000000000 : ℝ)^63
        have hw : |(7220605951/10000000000 : ℝ)|=(7220605951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (129948453/312500000 : ℝ)*x 0 + (3472568229/5000000000 : ℝ)*x 1 + (-676480843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129948453/312500000 : ℝ)^79 ≤ (415957692349/1250000000000 : ℝ)^63 := by
    have hnat : (129948453 : ℕ)^79*1250000000000^63 ≤ 415957692349^63*312500000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129948453 312500000 415957692349 1250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3472568229/5000000000 : ℝ)^79 ≤ (63310060436729/100000000000000 : ℝ)^63 := by
    have hnat : (3472568229 : ℕ)^79*100000000000000^63 ≤ 63310060436729^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3472568229 5000000000 63310060436729 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676480843/10000000000 : ℝ)^79 ≤ (3413324160913/100000000000000 : ℝ)^63 := by
    have hnat : (676480843 : ℕ)^79*100000000000000^63 ≤ 3413324160913^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676480843 10000000000 3413324160913 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129948453/312500000 : ℝ), (3472568229/5000000000 : ℝ), (-676480843/10000000000 : ℝ)] ![(415957692349/1250000000000 : ℝ), (63310060436729/100000000000000 : ℝ), (3413324160913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129948453/312500000 : ℝ)|^79 ≤ (415957692349/1250000000000 : ℝ)^63
        have hw : |(129948453/312500000 : ℝ)|=(129948453/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3472568229/5000000000 : ℝ)|^79 ≤ (63310060436729/100000000000000 : ℝ)^63
        have hw : |(3472568229/5000000000 : ℝ)|=(3472568229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-676480843/10000000000 : ℝ)|^79 ≤ (3413324160913/100000000000000 : ℝ)^63
        have hw : |(-676480843/10000000000 : ℝ)|=(676480843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (898499519/2000000000 : ℝ)*x 0 + (1611974613/2500000000 : ℝ)*x 1 + (506120541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898499519/2000000000 : ℝ)^79 ≤ (36663236488561/100000000000000 : ℝ)^63 := by
    have hnat : (898499519 : ℕ)^79*100000000000000^63 ≤ 36663236488561^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898499519 2000000000 36663236488561 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1611974613/2500000000 : ℝ)^79 ≤ (7209854034747/12500000000000 : ℝ)^63 := by
    have hnat : (1611974613 : ℕ)^79*12500000000000^63 ≤ 7209854034747^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1611974613 2500000000 7209854034747 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506120541/5000000000 : ℝ)^79 ≤ (565793121339/10000000000000 : ℝ)^63 := by
    have hnat : (506120541 : ℕ)^79*10000000000000^63 ≤ 565793121339^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506120541 5000000000 565793121339 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(898499519/2000000000 : ℝ), (1611974613/2500000000 : ℝ), (506120541/5000000000 : ℝ)] ![(36663236488561/100000000000000 : ℝ), (7209854034747/12500000000000 : ℝ), (565793121339/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(898499519/2000000000 : ℝ)|^79 ≤ (36663236488561/100000000000000 : ℝ)^63
        have hw : |(898499519/2000000000 : ℝ)|=(898499519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1611974613/2500000000 : ℝ)|^79 ≤ (7209854034747/12500000000000 : ℝ)^63
        have hw : |(1611974613/2500000000 : ℝ)|=(1611974613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(506120541/5000000000 : ℝ)|^79 ≤ (565793121339/10000000000000 : ℝ)^63
        have hw : |(506120541/5000000000 : ℝ)|=(506120541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-125620183/2500000000 : ℝ)*x 0 + (2405509873/5000000000 : ℝ)*x 1 + (6449546851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125620183/2500000000 : ℝ)^79 ≤ (2350958583493/100000000000000 : ℝ)^63 := by
    have hnat : (125620183 : ℕ)^79*100000000000000^63 ≤ 2350958583493^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125620183 2500000000 2350958583493 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2405509873/5000000000 : ℝ)^79 ≤ (39951718088939/100000000000000 : ℝ)^63 := by
    have hnat : (2405509873 : ℕ)^79*100000000000000^63 ≤ 39951718088939^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405509873 5000000000 39951718088939 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6449546851/10000000000 : ℝ)^79 ≤ (7212165414289/12500000000000 : ℝ)^63 := by
    have hnat : (6449546851 : ℕ)^79*12500000000000^63 ≤ 7212165414289^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6449546851 10000000000 7212165414289 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-125620183/2500000000 : ℝ), (2405509873/5000000000 : ℝ), (6449546851/10000000000 : ℝ)] ![(2350958583493/100000000000000 : ℝ), (39951718088939/100000000000000 : ℝ), (7212165414289/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-125620183/2500000000 : ℝ)|^79 ≤ (2350958583493/100000000000000 : ℝ)^63
        have hw : |(-125620183/2500000000 : ℝ)|=(125620183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2405509873/5000000000 : ℝ)|^79 ≤ (39951718088939/100000000000000 : ℝ)^63
        have hw : |(2405509873/5000000000 : ℝ)|=(2405509873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6449546851/10000000000 : ℝ)|^79 ≤ (7212165414289/12500000000000 : ℝ)^63
        have hw : |(6449546851/10000000000 : ℝ)|=(6449546851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (738111159/2000000000 : ℝ)*x 0 + (-313858387/5000000000 : ℝ)*x 1 + (7373196303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (738111159/2000000000 : ℝ)^79 ≤ (14325732384537/50000000000000 : ℝ)^63 := by
    have hnat : (738111159 : ℕ)^79*50000000000000^63 ≤ 14325732384537^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738111159 2000000000 14325732384537 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (313858387/5000000000 : ℝ)^79 ≤ (3107662797789/100000000000000 : ℝ)^63 := by
    have hnat : (313858387 : ℕ)^79*100000000000000^63 ≤ 3107662797789^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313858387 5000000000 3107662797789 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7373196303/10000000000 : ℝ)^79 ≤ (68240872421779/100000000000000 : ℝ)^63 := by
    have hnat : (7373196303 : ℕ)^79*100000000000000^63 ≤ 68240872421779^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7373196303 10000000000 68240872421779 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(738111159/2000000000 : ℝ), (-313858387/5000000000 : ℝ), (7373196303/10000000000 : ℝ)] ![(14325732384537/50000000000000 : ℝ), (3107662797789/100000000000000 : ℝ), (68240872421779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(738111159/2000000000 : ℝ)|^79 ≤ (14325732384537/50000000000000 : ℝ)^63
        have hw : |(738111159/2000000000 : ℝ)|=(738111159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-313858387/5000000000 : ℝ)|^79 ≤ (3107662797789/100000000000000 : ℝ)^63
        have hw : |(-313858387/5000000000 : ℝ)|=(313858387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7373196303/10000000000 : ℝ)|^79 ≤ (68240872421779/100000000000000 : ℝ)^63
        have hw : |(7373196303/10000000000 : ℝ)|=(7373196303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1274815293/2000000000 : ℝ)*x 0 + (196519449/400000000 : ℝ)*x 1 + (-232369033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1274815293/2000000000 : ℝ)^79 ≤ (56851962957191/100000000000000 : ℝ)^63 := by
    have hnat : (1274815293 : ℕ)^79*100000000000000^63 ≤ 56851962957191^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274815293 2000000000 56851962957191 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196519449/400000000 : ℝ)^79 ≤ (41016359770969/100000000000000 : ℝ)^63 := by
    have hnat : (196519449 : ℕ)^79*100000000000000^63 ≤ 41016359770969^63*400000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196519449 400000000 41016359770969 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (232369033/5000000000 : ℝ)^79 ≤ (2131677257299/100000000000000 : ℝ)^63 := by
    have hnat : (232369033 : ℕ)^79*100000000000000^63 ≤ 2131677257299^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232369033 5000000000 2131677257299 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1274815293/2000000000 : ℝ), (196519449/400000000 : ℝ), (-232369033/5000000000 : ℝ)] ![(56851962957191/100000000000000 : ℝ), (41016359770969/100000000000000 : ℝ), (2131677257299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1274815293/2000000000 : ℝ)|^79 ≤ (56851962957191/100000000000000 : ℝ)^63
        have hw : |(1274815293/2000000000 : ℝ)|=(1274815293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(196519449/400000000 : ℝ)|^79 ≤ (41016359770969/100000000000000 : ℝ)^63
        have hw : |(196519449/400000000 : ℝ)|=(196519449/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-232369033/5000000000 : ℝ)|^79 ≤ (2131677257299/100000000000000 : ℝ)^63
        have hw : |(-232369033/5000000000 : ℝ)|=(232369033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1593439803/2000000000 : ℝ)*x 0 + (2912689741/10000000000 : ℝ)*x 1 + (345295487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1593439803/2000000000 : ℝ)^79 ≤ (75203912925833/100000000000000 : ℝ)^63 := by
    have hnat : (1593439803 : ℕ)^79*100000000000000^63 ≤ 75203912925833^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593439803 2000000000 75203912925833 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2912689741/10000000000 : ℝ)^79 ≤ (5323312659711/25000000000000 : ℝ)^63 := by
    have hnat : (2912689741 : ℕ)^79*25000000000000^63 ≤ 5323312659711^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2912689741 10000000000 5323312659711 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345295487/5000000000 : ℝ)^79 ≤ (1751418207877/50000000000000 : ℝ)^63 := by
    have hnat : (345295487 : ℕ)^79*50000000000000^63 ≤ 1751418207877^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345295487 5000000000 1751418207877 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1593439803/2000000000 : ℝ), (2912689741/10000000000 : ℝ), (345295487/5000000000 : ℝ)] ![(75203912925833/100000000000000 : ℝ), (5323312659711/25000000000000 : ℝ), (1751418207877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1593439803/2000000000 : ℝ)|^79 ≤ (75203912925833/100000000000000 : ℝ)^63
        have hw : |(1593439803/2000000000 : ℝ)|=(1593439803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2912689741/10000000000 : ℝ)|^79 ≤ (5323312659711/25000000000000 : ℝ)^63
        have hw : |(2912689741/10000000000 : ℝ)|=(2912689741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345295487/5000000000 : ℝ)|^79 ≤ (1751418207877/50000000000000 : ℝ)^63
        have hw : |(345295487/5000000000 : ℝ)|=(345295487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-304929929/5000000000 : ℝ)*x 0 + (1669085877/2500000000 : ℝ)*x 1 + (4500975211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (304929929/5000000000 : ℝ)^79 ≤ (2997209115093/100000000000000 : ℝ)^63 := by
    have hnat : (304929929 : ℕ)^79*100000000000000^63 ≤ 2997209115093^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304929929 5000000000 2997209115093 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1669085877/2500000000 : ℝ)^79 ≤ (30126388432959/50000000000000 : ℝ)^63 := by
    have hnat : (1669085877 : ℕ)^79*50000000000000^63 ≤ 30126388432959^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669085877 2500000000 30126388432959 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500975211/10000000000 : ℝ)^79 ≤ (4593751751137/12500000000000 : ℝ)^63 := by
    have hnat : (4500975211 : ℕ)^79*12500000000000^63 ≤ 4593751751137^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500975211 10000000000 4593751751137 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-304929929/5000000000 : ℝ), (1669085877/2500000000 : ℝ), (4500975211/10000000000 : ℝ)] ![(2997209115093/100000000000000 : ℝ), (30126388432959/50000000000000 : ℝ), (4593751751137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-304929929/5000000000 : ℝ)|^79 ≤ (2997209115093/100000000000000 : ℝ)^63
        have hw : |(-304929929/5000000000 : ℝ)|=(304929929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1669085877/2500000000 : ℝ)|^79 ≤ (30126388432959/50000000000000 : ℝ)^63
        have hw : |(1669085877/2500000000 : ℝ)|=(1669085877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500975211/10000000000 : ℝ)|^79 ≤ (4593751751137/12500000000000 : ℝ)^63
        have hw : |(4500975211/10000000000 : ℝ)|=(4500975211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6552271597/10000000000 : ℝ)*x 0 + (-3920999/1000000000 : ℝ)*x 1 + (4916391491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6552271597/10000000000 : ℝ)^79 ≤ (58852004583789/100000000000000 : ℝ)^63 := by
    have hnat : (6552271597 : ℕ)^79*100000000000000^63 ≤ 58852004583789^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6552271597 10000000000 58852004583789 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3920999/1000000000 : ℝ)^79 ≤ (19196669907/20000000000000 : ℝ)^63 := by
    have hnat : (3920999 : ℕ)^79*20000000000000^63 ≤ 19196669907^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3920999 1000000000 19196669907 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4916391491/10000000000 : ℝ)^79 ≤ (4105201205579/10000000000000 : ℝ)^63 := by
    have hnat : (4916391491 : ℕ)^79*10000000000000^63 ≤ 4105201205579^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4916391491 10000000000 4105201205579 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6552271597/10000000000 : ℝ), (-3920999/1000000000 : ℝ), (4916391491/10000000000 : ℝ)] ![(58852004583789/100000000000000 : ℝ), (19196669907/20000000000000 : ℝ), (4105201205579/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6552271597/10000000000 : ℝ)|^79 ≤ (58852004583789/100000000000000 : ℝ)^63
        have hw : |(6552271597/10000000000 : ℝ)|=(6552271597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3920999/1000000000 : ℝ)|^79 ≤ (19196669907/20000000000000 : ℝ)^63
        have hw : |(-3920999/1000000000 : ℝ)|=(3920999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4916391491/10000000000 : ℝ)|^79 ≤ (4105201205579/10000000000000 : ℝ)^63
        have hw : |(4916391491/10000000000 : ℝ)|=(4916391491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (421192789/1250000000 : ℝ)*x 0 + (716557367/1000000000 : ℝ)*x 1 + (-706647523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421192789/1250000000 : ℝ)^79 ≤ (1597603272919/6250000000000 : ℝ)^63 := by
    have hnat : (421192789 : ℕ)^79*6250000000000^63 ≤ 1597603272919^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421192789 1250000000 1597603272919 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (716557367/1000000000 : ℝ)^79 ≤ (65839921712681/100000000000000 : ℝ)^63 := by
    have hnat : (716557367 : ℕ)^79*100000000000000^63 ≤ 65839921712681^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716557367 1000000000 65839921712681 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706647523/5000000000 : ℝ)^79 ≤ (8598425918771/100000000000000 : ℝ)^63 := by
    have hnat : (706647523 : ℕ)^79*100000000000000^63 ≤ 8598425918771^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706647523 5000000000 8598425918771 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(421192789/1250000000 : ℝ), (716557367/1000000000 : ℝ), (-706647523/5000000000 : ℝ)] ![(1597603272919/6250000000000 : ℝ), (65839921712681/100000000000000 : ℝ), (8598425918771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(421192789/1250000000 : ℝ)|^79 ≤ (1597603272919/6250000000000 : ℝ)^63
        have hw : |(421192789/1250000000 : ℝ)|=(421192789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(716557367/1000000000 : ℝ)|^79 ≤ (65839921712681/100000000000000 : ℝ)^63
        have hw : |(716557367/1000000000 : ℝ)|=(716557367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-706647523/5000000000 : ℝ)|^79 ≤ (8598425918771/100000000000000 : ℝ)^63
        have hw : |(-706647523/5000000000 : ℝ)|=(706647523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318055_s1_s1_27 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1562192129/2000000000 : ℝ)*x 0 + (2204303021/10000000000 : ℝ)*x 1 + (449455651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1562192129/2000000000 : ℝ)^79 ≤ (73359233692921/100000000000000 : ℝ)^63 := by
    have hnat : (1562192129 : ℕ)^79*100000000000000^63 ≤ 73359233692921^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562192129 2000000000 73359233692921 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2204303021/10000000000 : ℝ)^79 ≤ (15013538207473/100000000000000 : ℝ)^63 := by
    have hnat : (2204303021 : ℕ)^79*100000000000000^63 ≤ 15013538207473^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204303021 10000000000 15013538207473 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449455651/2500000000 : ℝ)^79 ≤ (11627228083393/100000000000000 : ℝ)^63 := by
    have hnat : (449455651 : ℕ)^79*100000000000000^63 ≤ 11627228083393^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449455651 2500000000 11627228083393 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1562192129/2000000000 : ℝ), (2204303021/10000000000 : ℝ), (449455651/2500000000 : ℝ)] ![(73359233692921/100000000000000 : ℝ), (15013538207473/100000000000000 : ℝ), (11627228083393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1562192129/2000000000 : ℝ)|^79 ≤ (73359233692921/100000000000000 : ℝ)^63
        have hw : |(1562192129/2000000000 : ℝ)|=(1562192129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2204303021/10000000000 : ℝ)|^79 ≤ (15013538207473/100000000000000 : ℝ)^63
        have hw : |(2204303021/10000000000 : ℝ)|=(2204303021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449455651/2500000000 : ℝ)|^79 ≤ (11627228083393/100000000000000 : ℝ)^63
        have hw : |(449455651/2500000000 : ℝ)|=(449455651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318055_s1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((76471/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76471/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14711/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14711/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37339/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(37339/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((52171/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52171/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51723/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(51723/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52127/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(52127/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34269/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (76471/100000 : ℝ) ^ (39/8 : ℝ) ≤ (27042494557590582069/100000000000000000000 : ℝ) := by
    have hpowers : (76471/100000 : ℝ)^39 ≤ (27042494557590582069/100000000000000000000 : ℝ)^8 := by
      have hnat : (76471 : ℕ)^39*100000000000000000000^8 ≤ 27042494557590582069^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76471 100000 27042494557590582069 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76471/100000 : ℝ)) (X := (27042494557590582069/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (127042494557590582069/100000000000000000000 : ℝ) ≤ (10503229967139591/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (127042494557590582069/100000000000000000000 : ℝ)^8 ≤ (10503229967139591/10000000000000000 : ℝ)^39 := by
      have hnat : (127042494557590582069 : ℕ)^8*10000000000000000^39 ≤ 10503229967139591^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127042494557590582069 100000000000000000000 10503229967139591 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10503229967139591/10000000000000000 : ℝ)) (X := (127042494557590582069/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (77042494557590582069/50000000000000000000 : ℝ) ≤ (10927352170658059/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (77042494557590582069/50000000000000000000 : ℝ)^8 ≤ (10927352170658059/10000000000000000 : ℝ)^39 := by
      have hnat : (77042494557590582069 : ℕ)^8*10000000000000000^39 ≤ 10927352170658059^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77042494557590582069 50000000000000000000 10927352170658059 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10927352170658059/10000000000000000 : ℝ)) (X := (77042494557590582069/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(503229967139591/7647100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(106030550879617/1911775000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (76471/100000 : ℝ)) (alpha := (503229967139591/7647100000000000 : ℝ)) (beta := (106030550879617/1911775000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (76471/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(503229967139591/7647100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(106030550879617/1911775000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (14711/20000 : ℝ) ^ (39/8 : ℝ) ≤ (22373528118734839051/100000000000000000000 : ℝ) := by
    have hpowers : (14711/20000 : ℝ)^39 ≤ (22373528118734839051/100000000000000000000 : ℝ)^8 := by
      have hnat : (14711 : ℕ)^39*100000000000000000000^8 ≤ 22373528118734839051^8*20000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14711 20000 22373528118734839051 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14711/20000 : ℝ)) (X := (22373528118734839051/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (122373528118734839051/100000000000000000000 : ℝ) ≤ (1302858313836511/1250000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (122373528118734839051/100000000000000000000 : ℝ)^8 ≤ (1302858313836511/1250000000000000 : ℝ)^39 := by
      have hnat : (122373528118734839051 : ℕ)^8*1250000000000000^39 ≤ 1302858313836511^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        122373528118734839051 100000000000000000000 1302858313836511 1250000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1302858313836511/1250000000000000 : ℝ)) (X := (122373528118734839051/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (72373528118734839051/50000000000000000000 : ℝ) ≤ (10788115506356427/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (72373528118734839051/50000000000000000000 : ℝ)^8 ≤ (10788115506356427/10000000000000000 : ℝ)^39 := by
      have hnat : (72373528118734839051 : ℕ)^8*10000000000000000^39 ≤ 10788115506356427^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72373528118734839051 50000000000000000000 10788115506356427 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10788115506356427/10000000000000000 : ℝ)) (X := (72373528118734839051/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(52858313836511/919437500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(365248995664339/7355500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (14711/20000 : ℝ)) (alpha := (52858313836511/919437500000000 : ℝ)) (beta := (365248995664339/7355500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (14711/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(52858313836511/919437500000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(365248995664339/7355500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (37339/50000 : ℝ) ^ (39/8 : ℝ) ≤ (4817750469768880339/20000000000000000000 : ℝ) := by
    have hpowers : (37339/50000 : ℝ)^39 ≤ (4817750469768880339/20000000000000000000 : ℝ)^8 := by
      have hnat : (37339 : ℕ)^39*20000000000000000000^8 ≤ 4817750469768880339^8*50000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37339 50000 4817750469768880339 20000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37339/50000 : ℝ)) (X := (4817750469768880339/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (24817750469768880339/20000000000000000000 : ℝ) ≤ (5226334074664993/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (24817750469768880339/20000000000000000000 : ℝ)^8 ≤ (5226334074664993/5000000000000000 : ℝ)^39 := by
      have hnat : (24817750469768880339 : ℕ)^8*5000000000000000^39 ≤ 5226334074664993^39*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24817750469768880339 20000000000000000000 5226334074664993 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5226334074664993/5000000000000000 : ℝ)) (X := (24817750469768880339/20000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (14817750469768880339/10000000000000000000 : ℝ) ≤ (5420037187418507/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (14817750469768880339/10000000000000000000 : ℝ)^8 ≤ (5420037187418507/5000000000000000 : ℝ)^39 := by
      have hnat : (14817750469768880339 : ℕ)^8*5000000000000000^39 ≤ 5420037187418507^39*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14817750469768880339 10000000000000000000 5420037187418507 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5420037187418507/5000000000000000 : ℝ)) (X := (14817750469768880339/10000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(226334074664993/3733900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(96851556376757/1866950000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (37339/50000 : ℝ)) (alpha := (226334074664993/3733900000000000 : ℝ)) (beta := (96851556376757/1866950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (37339/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(226334074664993/3733900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(96851556376757/1866950000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-393817959/2500000000 : ℝ)*X 0 0+(5725958893/10000000000 : ℝ)*X 0 1+(4858728809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4808517569/10000000000 : ℝ)*X 1 0+(-601498959/10000000000 : ℝ)*X 1 1+(3199397523/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1599761901/2500000000 : ℝ)*X 0 0+(3767918237/10000000000 : ℝ)*X 0 1+(252582301/1250000000 : ℝ)*X 0 2+(1599761901/2500000000 : ℝ)*X 1 0+(3767918237/10000000000 : ℝ)*X 1 1+(252582301/1250000000 : ℝ)*X 1 2+(1599761901/2500000000 : ℝ)*X 2 0+(3767918237/10000000000 : ℝ)*X 2 1+(252582301/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-726317793/5000000000 : ℝ)*X 0 0+(4388342853/10000000000 : ℝ)*X 0 1+(6252892623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4181284069/10000000000 : ℝ)*X 1 0+(-5268647/5000000000 : ℝ)*X 1 1+(7220605951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((129948453/312500000 : ℝ)*X 2 0+(3472568229/5000000000 : ℝ)*X 2 1+(-676480843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((898499519/2000000000 : ℝ)*X 0 0+(1611974613/2500000000 : ℝ)*X 0 1+(506120541/5000000000 : ℝ)*X 0 2+(898499519/2000000000 : ℝ)*X 1 0+(1611974613/2500000000 : ℝ)*X 1 1+(506120541/5000000000 : ℝ)*X 1 2+(898499519/2000000000 : ℝ)*X 2 0+(1611974613/2500000000 : ℝ)*X 2 1+(506120541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-125620183/2500000000 : ℝ)*X 0 0+(2405509873/5000000000 : ℝ)*X 0 1+(6449546851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((738111159/2000000000 : ℝ)*X 1 0+(-313858387/5000000000 : ℝ)*X 1 1+(7373196303/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1274815293/2000000000 : ℝ)*X 2 0+(196519449/400000000 : ℝ)*X 2 1+(-232369033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1593439803/2000000000 : ℝ)*X 0 0+(2912689741/10000000000 : ℝ)*X 0 1+(345295487/5000000000 : ℝ)*X 0 2+(1593439803/2000000000 : ℝ)*X 1 0+(2912689741/10000000000 : ℝ)*X 1 1+(345295487/5000000000 : ℝ)*X 1 2+(1593439803/2000000000 : ℝ)*X 2 0+(2912689741/10000000000 : ℝ)*X 2 1+(345295487/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-304929929/5000000000 : ℝ)*X 0 0+(1669085877/2500000000 : ℝ)*X 0 1+(4500975211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6552271597/10000000000 : ℝ)*X 1 0+(-3920999/1000000000 : ℝ)*X 1 1+(4916391491/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((421192789/1250000000 : ℝ)*X 2 0+(716557367/1000000000 : ℝ)*X 2 1+(-706647523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1562192129/2000000000 : ℝ)*X 0 0+(2204303021/10000000000 : ℝ)*X 0 1+(449455651/2500000000 : ℝ)*X 0 2+(1562192129/2000000000 : ℝ)*X 1 0+(2204303021/10000000000 : ℝ)*X 1 1+(449455651/2500000000 : ℝ)*X 1 2+(1562192129/2000000000 : ℝ)*X 2 0+(2204303021/10000000000 : ℝ)*X 2 1+(449455651/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((52171/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52171/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19505923056767221745661/1866950000000000000000000000 : ℝ) := by norm_num
    linear_combination (116282608171/250000000000 : ℝ)*(base7) + (20017644857/250000000000 : ℝ)*(base49) + (607489/1000000000000 : ℝ)*(base60) + (1494394347807/500000000000 : ℝ)*(major_s1_0) + (1494394347807/500000000000 : ℝ)*(major_s1_1) + (1494394347807/500000000000 : ℝ)*(major_s1_2) + (883387/62500000000 : ℝ)*(sp_s1_0) + (68249/1000000000000 : ℝ)*(sp_s1_6) + (814788078163/200000000000 : ℝ)*(sp_s1_7) + (1018499463451/250000000000 : ℝ)*(sp_s1_8) + (4073986402777/1000000000000 : ℝ)*(sp_s1_9) + (1051523586277/500000000000 : ℝ)*(sp_s1_13) + (43328797/1000000000000 : ℝ)*(sp_s1_14) + (11451027/1000000000000 : ℝ)*(sp_s1_23) + (818958404059/500000000000 : ℝ)*(f.failure) + (1018499463451/250000000000 : ℝ)*(f.sum) + (67983076419796722771/137323507250000000000000000000000 : ℝ)*base62 + (89647188830521/233368750000000000000000000 : ℝ)*base65 + (731230630851927/3677750000000000000000000000 : ℝ)*base67 + (204060081295539/1866950000000000000000000000 : ℝ)*base68 + (773545853279961003/17845941681250000000000000000000 : ℝ)*base70 + (409727909555039/955887500000000000000000000 : ℝ)*base73 + (87010610767233/1838875000000000000000000000 : ℝ)*base75 + (483679105624551/1911775000000000000000000000 : ℝ)*base77 + (35192672863294400939/140620610125000000000000000000000 : ℝ)*base78 + (1359/2000000000000000 : ℝ)*base86 + (1359/2000000000000000 : ℝ)*base88 + (1359/2000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51723/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(51723/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (67366743052037998860748863/13732350725000000000000000000000 : ℝ) := by norm_num
    linear_combination (4068541713/10000000000 : ℝ)*(base7) + (1194847/500000000000 : ℝ)*(base13) + (56956442741/1000000000000 : ℝ)*(base49) + (540961168971/200000000000 : ℝ)*(major_s1_0) + (540961168971/200000000000 : ℝ)*(major_s1_1) + (540961168971/200000000000 : ℝ)*(major_s1_2) + (10801471/1000000000000 : ℝ)*(sp_s1_1) + (265639/200000000000 : ℝ)*(sp_s1_7) + (10894221/500000000000 : ℝ)*(sp_s1_8) + (115466972781/31250000000 : ℝ)*(sp_s1_14) + (1847457128483/500000000000 : ℝ)*(sp_s1_15) + (23093417793/6250000000 : ℝ)*(sp_s1_16) + (1889129976141/1000000000000 : ℝ)*(sp_s1_20) + (3160703/250000000000 : ℝ)*(sp_s1_27) + (1482288447653/1000000000000 : ℝ)*(f.failure) + (23093417793/6250000000 : ℝ)*(f.sum) + (11461032083839340647/54929402900000000000000000000000 : ℝ)*base63 + (36534999321947/373390000000000000000000000 : ℝ)*base65 + (868837789678659/1471100000000000000000000000 : ℝ)*base66 + (638801396579887/746780000000000000000000000 : ℝ)*base69 + (616424031459998503/57107013380000000000000000000000 : ℝ)*base70 + (437123072169683/382355000000000000000000000 : ℝ)*base73 + (379712154085199/735550000000000000000000000 : ℝ)*base75 + (21288115230751/61176800000000000000000000 : ℝ)*base77 + (19226869295147191679/112496488100000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base82 + (753/4000000000000000 : ℝ)*base86 + (753/4000000000000000 : ℝ)*base88 + (753/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52127/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(52127/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (148291064678407503067665236241261/10501265922914750000000000000000000000 : ℝ) := by norm_num
    linear_combination (286428944113/500000000000 : ℝ)*(base7) + (121361528079/1000000000000 : ℝ)*(base40) + (695657/1000000000000 : ℝ)*(base59) + (1202773190293/500000000000 : ℝ)*(major_s1_0) + (1202773190293/500000000000 : ℝ)*(major_s1_1) + (1202773190293/500000000000 : ℝ)*(major_s1_2) + (2334571/1000000000000 : ℝ)*(sp_s1_0) + (7470737/1000000000000 : ℝ)*(sp_s1_1) + (91321651/1000000000000 : ℝ)*(sp_s1_9) + (16178131/500000000000 : ℝ)*(sp_s1_20) + (49462652241/15625000000 : ℝ)*(sp_s1_21) + (1582802303629/500000000000 : ℝ)*(sp_s1_22) + (395690094543/125000000000 : ℝ)*(sp_s1_23) + (1891113725189/1000000000000 : ℝ)*(sp_s1_27) + (164786024153/125000000000 : ℝ)*(f.failure) + (633122415599/200000000000 : ℝ)*(f.sum) + (4877155448539267901/34330876812500000000000000000000 : ℝ)*base62 + (27651488732299/58342187500000000000000000 : ℝ)*base64 + (309231172441063/919437500000000000000000000 : ℝ)*base66 + (895495497049781/1866950000000000000000000000 : ℝ)*base68 + (72525015440424121461/142767533450000000000000000000000 : ℝ)*base70 + (6103618047513/477943750000000000000000000 : ℝ)*base73 + (1853363014071941/3677750000000000000000000000 : ℝ)*base74 + (882625603770933/955887500000000000000000000 : ℝ)*base76 + (32944069116060175407/70310305062500000000000000000000 : ℝ)*base79 + (253/500000000000000 : ℝ)*base86 + (253/500000000000000 : ℝ)*base88 + (253/500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((76471/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76471/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14711/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14711/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37339/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(37339/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((52171/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52171/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51723/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(51723/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52127/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(52127/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c318055_s1 p hpa hpb X hX hprev0

#print axioms solution
